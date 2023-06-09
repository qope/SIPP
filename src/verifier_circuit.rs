use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::{AlgebraicHasher, GenericConfig},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_bn254_pairing::aggregation::{
    fq12_exp::{
        generate_fq12_exp_aggregation_proof, generate_fq12_exp_proof,
        Fq12ExpAggregationPublicInputs, Fq12ExpAggregationTarget, Fq12ExpAggregationWitness,
        PartialFq12ExpStatement,
    },
    g1_exp::G1ExpTarget,
    g2_exp::{
        generate_g2_exp_proof, G2ExpAggregationPublicInputs, G2ExpAggregationTarget,
        G2ExpAggregationWitness, PartialG2ExpStatement,
    },
    g2_exp_witness::get_num_statements,
};
use plonky2_bn254_pairing::aggregation::{
    fq12_exp_witness::generate_fq12exp_witness_from_x, g2_exp::generate_g2_exp_aggregation_proof,
};
use plonky2_bn254_pairing::{
    aggregation::{
        fq12_exp::{build_fq12_exp_aggregation_circuit, build_fq12_exp_circuit},
        g1_exp::{build_g1_exp_circuit, generate_g1_exp_proof, G1ExpWitness},
        g2_exp::{build_g2_exp_aggregation_circuit, build_g2_exp_circuit},
        g2_exp_witness::generate_g2exp_witness_from_x,
    },
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, fq_target::FqTarget, fr_target::FrTarget},
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};
use rayon::prelude::*;

use crate::{
    statements::{Fq12ExpStatement, G1ExpStatement, G2ExpStatement},
    transcript_circuit::TranscriptCircuit,
    verifier_witness::VerifierCircuitWitness,
};

const LOG_N: usize = 2;
const NUM_BITS_G2: usize = 6;
const NUM_BITS_FQ12: usize = 5;

#[allow(non_snake_case)]
pub struct VerifierCircuitTarget<F: RichField + Extendable<D>, const D: usize> {
    pub A: Vec<G1Target<F, D>>,
    pub B: Vec<G2Target<F, D>>,
    pub final_A: G1Target<F, D>,
    pub final_B: G2Target<F, D>,
    pub Z: Fq12Target<F, D>,
    pub proof: Vec<Fq12Target<F, D>>,
    pub g1exp: Vec<G1ExpStatement<F, D>>,
    pub g2exp: Vec<G2ExpStatement<F, D>>,
    pub fq12exp: Vec<Fq12ExpStatement<F, D>>,
}

#[allow(non_snake_case)]
pub struct VerifierCircuitPublicInputs<F: RichField + Extendable<D>, const D: usize> {
    pub A: Vec<G1Target<F, D>>,
    pub B: Vec<G2Target<F, D>>,
    pub final_A: G1Target<F, D>,
    pub final_B: G2Target<F, D>,
    pub Z: Fq12Target<F, D>,
    pub g1exp: Vec<G1ExpStatement<F, D>>,
    pub g2exp: Vec<G2ExpStatement<F, D>>,
    pub fq12exp: Vec<Fq12ExpStatement<F, D>>,
}

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, VerifierCircuitPublicInputs<F, D>, VerifierCircuitWitness>
    for VerifierCircuitTarget<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        let a_vec = self.A.iter().flat_map(|g1| g1.to_vec()).collect_vec();
        let b_vec = self.B.iter().flat_map(|g2| g2.to_vec()).collect_vec();
        let final_a_vec = self.final_A.to_vec();
        let final_b_vec = self.final_B.to_vec();
        let z_vec = self.Z.to_vec();
        let g1exp_vec = self
            .g1exp
            .iter()
            .flat_map(|g1exp| g1exp.to_vec())
            .collect_vec();
        let g2exp_vec = self
            .g2exp
            .iter()
            .flat_map(|g2exp| g2exp.to_vec())
            .collect_vec();
        let fq12exp_vec = self
            .fq12exp
            .iter()
            .flat_map(|fq12exp| fq12exp.to_vec())
            .collect_vec();
        vec![
            a_vec,
            b_vec,
            final_a_vec,
            final_b_vec,
            z_vec,
            g1exp_vec,
            g2exp_vec,
            fq12exp_vec,
        ]
        .concat()
    }

    #[allow(non_snake_case)]
    fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> VerifierCircuitPublicInputs<F, D> {
        let n = 1 << LOG_N;
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let num_g1_limbs = 2 * num_limbs;
        let num_g2_limbs = 4 * num_limbs;
        let num_fq12_limbs = 12 * num_limbs;
        let num_g1_statement_limbs = 2 * num_g1_limbs + num_fr_limbs;
        let num_g2_statement_limbs = 2 * num_g2_limbs + num_fr_limbs;
        let num_fq12_statement_limbs = 2 * num_fq12_limbs + num_fr_limbs;

        let num_a_limbs = n * num_g1_limbs;
        let num_b_limbs = n * num_g2_limbs;
        let num_final_a_limbs = num_g1_limbs;
        let num_final_b_limbs = num_g2_limbs;
        let num_z_limbs = num_fq12_limbs;
        let num_g1exp_limbs = (n - 1) * num_g1_statement_limbs;
        let num_g2exp_limbs = (n - 1) * num_g2_statement_limbs;
        let num_fq12exp_limbs = 2 * LOG_N * num_fq12_statement_limbs;

        let mut input = input.to_vec();
        let a_raw = input.drain(0..num_a_limbs).collect_vec();
        let b_raw = input.drain(0..num_b_limbs).collect_vec();
        let final_a_raw = input.drain(0..num_final_a_limbs).collect_vec();
        let final_b_raw = input.drain(0..num_final_b_limbs).collect_vec();
        let z_raw = input.drain(0..num_z_limbs).collect_vec();
        let g1exp_raw = input.drain(0..num_g1exp_limbs).collect_vec();
        let g2exp_raw = input.drain(0..num_g2exp_limbs).collect_vec();
        let fq12exp_raw = input.drain(0..num_fq12exp_limbs).collect_vec();

        assert_eq!(input.len(), 0);

        let A = a_raw
            .chunks_exact(num_g1_limbs)
            .map(|x| G1Target::from_vec(builder, x))
            .collect_vec();
        let B = b_raw
            .chunks_exact(num_g2_limbs)
            .map(|x| G2Target::from_vec(builder, x))
            .collect_vec();
        let final_A = G1Target::from_vec(builder, &final_a_raw);
        let final_B = G2Target::from_vec(builder, &final_b_raw);
        let Z = Fq12Target::from_vec(builder, &z_raw);
        let g1exp = g1exp_raw
            .chunks_exact(num_g1_statement_limbs)
            .map(|x| G1ExpStatement::from_vec(builder, x))
            .collect_vec();
        let g2exp = g2exp_raw
            .chunks_exact(num_g2_statement_limbs)
            .map(|x| G2ExpStatement::from_vec(builder, x))
            .collect_vec();
        let fq12exp = fq12exp_raw
            .chunks_exact(num_fq12_statement_limbs)
            .map(|x| Fq12ExpStatement::from_vec(builder, x))
            .collect_vec();

        VerifierCircuitPublicInputs {
            A,
            B,
            final_A,
            final_B,
            Z,
            g1exp,
            g2exp,
            fq12exp,
        }
    }

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &VerifierCircuitWitness) {
        self.A.iter().zip(value.A.iter()).for_each(|(a, a_w)| {
            a.set_witness(pw, a_w);
        });
        self.B.iter().zip(value.B.iter()).for_each(|(b, b_w)| {
            b.set_witness(pw, b_w);
        });
        self.final_A.set_witness(pw, &value.final_A);
        self.final_B.set_witness(pw, &value.final_B);
        self.Z.set_witness(pw, &value.Z);
        self.proof
            .iter()
            .zip(value.proof.iter())
            .for_each(|(p, p_w)| {
                p.set_witness(pw, p_w);
            });
        self.g1exp
            .iter()
            .zip(value.g1exp.iter())
            .for_each(|(g1exp, g1exp_w)| {
                g1exp.set_witness(pw, g1exp_w);
            });
        self.g2exp
            .iter()
            .zip(value.g2exp.iter())
            .for_each(|(g2exp, g2exp_w)| {
                g2exp.set_witness(pw, g2exp_w);
            });
        self.fq12exp
            .iter()
            .zip(value.fq12exp.iter())
            .for_each(|(fq12exp, fq12exp_w)| {
                fq12exp.set_witness(pw, fq12exp_w);
            });
    }
}

#[allow(non_snake_case)]
pub fn verifier_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    A_t: &[G1Target<F, D>],
    B_t: &[G2Target<F, D>],
    proof_t: &[Fq12Target<F, D>],
) -> VerifierCircuitTarget<F, D> {
    let mut g1exp_t: Vec<G1ExpStatement<F, D>> = vec![];
    let mut g2exp_t: Vec<G2ExpStatement<F, D>> = vec![];
    let mut fq12exp_t: Vec<Fq12ExpStatement<F, D>> = vec![];

    let original_A = A_t.to_vec();
    let original_B = B_t.to_vec();

    let mut n = A_t.len();
    let mut A_t = A_t.to_vec();
    let mut B_t = B_t.to_vec();
    let mut transcript_c = TranscriptCircuit::<F, D>::new(builder);
    let original_proof = proof_t.to_vec();
    let mut proof_t = proof_t.to_vec();

    // register A and B
    A_t.iter().zip(B_t.iter()).for_each(|(a, b)| {
        transcript_c.append_g1(builder, a.clone());
        transcript_c.append_g2(builder, b.clone());
    });

    // receive Z
    let mut Z_t = proof_t.pop().unwrap();
    transcript_c.append_fq12(builder, Z_t.clone());

    while n > 1 {
        let (A1_t, A2_t) = A_t.split_at(n / 2);
        let (B1_t, B2_t) = B_t.split_at(n / 2);

        // receive Z_L and Z_R
        let Z_L_t = proof_t.pop().unwrap();
        transcript_c.append_fq12(builder, Z_L_t.clone());
        let Z_R_t = proof_t.pop().unwrap();
        transcript_c.append_fq12(builder, Z_R_t.clone());

        let x_t = transcript_c.get_challenge(builder);
        let inv_x_t = x_t.inv(builder);

        let mut new_A_t = vec![];
        let mut new_B_t = vec![];

        for i in 0..(n / 2) {
            let a1_t = A1_t[i].clone();
            let a2_t = A2_t[i].clone();

            let b1_t = B1_t[i].clone();
            let b2_t = B2_t[i].clone();

            let x_a2_t = G1Target::new(builder);
            g1exp_t.push(G1ExpStatement {
                p: a2_t,
                x: x_t.clone(),
                p_x: x_a2_t.clone(),
            });
            new_A_t.push(a1_t.add(builder, &x_a2_t));

            let inv_x_b2_t = G2Target::new(builder);
            g2exp_t.push(G2ExpStatement {
                p: b2_t,
                x: inv_x_t.clone(),
                p_x: inv_x_b2_t.clone(),
            });
            new_B_t.push(b1_t.add(builder, &inv_x_b2_t));
        }

        let Z_L_x_t = Fq12Target::new(builder);
        fq12exp_t.push(Fq12ExpStatement {
            p: Z_L_t,
            x: x_t,
            p_x: Z_L_x_t.clone(),
        });

        let Z_R_inv_x_t = Fq12Target::new(builder);
        fq12exp_t.push(Fq12ExpStatement {
            p: Z_R_t,
            x: inv_x_t,
            p_x: Z_R_inv_x_t.clone(),
        });

        let new_Z_t = Z_L_x_t.mul(builder, &Z_t).mul(builder, &Z_R_inv_x_t);

        // update
        A_t = new_A_t;
        B_t = new_B_t;
        Z_t = new_Z_t;
        n = n / 2;
    }

    VerifierCircuitTarget {
        A: original_A,
        B: original_B,
        final_A: A_t[0].clone(),
        final_B: B_t[0].clone(),
        Z: Z_t,
        proof: original_proof,
        g1exp: g1exp_t,
        g2exp: g2exp_t,
        fq12exp: fq12exp_t,
    }
}

#[allow(non_snake_case)]
pub fn build_verifier_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>() -> (CircuitData<F, C, D>, VerifierCircuitTarget<F, D>) {
    let n = 1 << LOG_N;
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let A = (0..n).map(|_| G1Target::new(&mut builder)).collect_vec();
    let B = (0..n).map(|_| G2Target::new(&mut builder)).collect_vec();
    let proof = (0..2 * LOG_N + 1)
        .map(|_| Fq12Target::new(&mut builder))
        .collect_vec();
    let t = verifier_circuit(&mut builder, &A, &B, &proof);
    builder.register_public_inputs(&t.to_vec());
    let data = builder.build::<C>();
    (data, t)
}

pub fn generate_verifier_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    data: &CircuitData<F, C, D>,
    verifier_t: &VerifierCircuitTarget<F, D>,
    verifier_w: &VerifierCircuitWitness,
) -> ProofWithPublicInputs<F, C, D> {
    let mut pw = PartialWitness::<F>::new();
    verifier_t.set_witness(&mut pw, verifier_w);
    data.prove(pw).unwrap()
}

pub struct WitnessProofs<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize> {
    pub g1exp: Vec<ProofWithPublicInputs<F, C, D>>,
    pub g2exp: Vec<ProofWithPublicInputs<F, C, D>>,
    pub fq12exp: Vec<ProofWithPublicInputs<F, C, D>>,
}

pub struct StatementProofs<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
{
    pub g1exp_proofs: Vec<ProofWithPublicInputs<F, C, D>>,
    pub g2exp_proofs: Vec<ProofWithPublicInputs<F, C, D>>,
    pub fq12exp_proofs: Vec<ProofWithPublicInputs<F, C, D>>,
}

pub struct StatementDataAndTarget<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub g1exp_data: CircuitData<F, C, D>,
    pub g2exp_data: CircuitData<F, C, D>,
    pub g2exp_aggregation_data: CircuitData<F, C, D>,
    pub fq12exp_data: CircuitData<F, C, D>,
    pub fq12exp_aggregation_data: CircuitData<F, C, D>,
    pub g1exp_t: G1ExpTarget<F, D>,
    pub g2exp_t: PartialG2ExpStatement<F, D>,
    pub g2exp_aggregation_t: G2ExpAggregationTarget<F, D>,
    pub fq12exp_t: PartialFq12ExpStatement<F, D>,
    pub fq12exp_aggregation_t: Fq12ExpAggregationTarget<F, D>,
}

pub fn build_statementdata_and_target<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>() -> StatementDataAndTarget<F, C, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let g2_num_statements = get_num_statements(256, NUM_BITS_G2);
    let fq12_num_statements = get_num_statements(256, NUM_BITS_FQ12);
    let (g1exp_data, g1exp_t) = build_g1_exp_circuit::<F, C, D>();
    let (g2exp_data, g2exp_t) = build_g2_exp_circuit::<F, C, D>();
    let (g2exp_aggregation_data, g2exp_aggregation_t) =
        build_g2_exp_aggregation_circuit::<F, C, D>(&g2exp_data, g2_num_statements);
    let (fq12exp_data, fq12exp_t) = build_fq12_exp_circuit::<F, C, D>();
    let (fq12exp_aggregation_data, fq12exp_aggregation_t) =
        build_fq12_exp_aggregation_circuit::<F, C, D>(&fq12exp_data, fq12_num_statements);
    StatementDataAndTarget {
        g1exp_data,
        g2exp_data,
        g2exp_aggregation_data,
        fq12exp_data,
        fq12exp_aggregation_data,
        g1exp_t,
        g2exp_t,
        g2exp_aggregation_t,
        fq12exp_t,
        fq12exp_aggregation_t,
    }
}

pub fn generate_witness_proofs<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    dt: &StatementDataAndTarget<F, C, D>,
    witness: &VerifierCircuitWitness,
) -> StatementProofs<F, C, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    println!("Start: g1exp_proofs");
    let g1exp_proofs: Vec<_> = witness
        .g1exp
        .par_iter()
        .map(|g1exp_w| {
            let g1exp_w = G1ExpWitness {
                p: g1exp_w.p,
                p_x: g1exp_w.p_x,
                x: g1exp_w.x,
            };
            let proof = generate_g1_exp_proof(&dt.g1exp_data, &dt.g1exp_t, &g1exp_w);
            proof.unwrap()
        })
        .collect();
    println!("Start: g2exp_proofs");
    let g2exp_proofs: Vec<_> = witness
        .g2exp
        .iter()
        .map(|g2exp_w| {
            let partial_g2exp_w = generate_g2exp_witness_from_x(g2exp_w.p, g2exp_w.x, NUM_BITS_G2);
            let proofs: Vec<_> = partial_g2exp_w
                .par_iter()
                .map(|sw| generate_g2_exp_proof(&dt.g2exp_data, &dt.g2exp_t, sw).unwrap())
                .collect();
            let aggregation_witness = G2ExpAggregationWitness {
                proofs,
                p: g2exp_w.p,
                p_x: g2exp_w.p_x,
                x: g2exp_w.x,
            };
            let proof = generate_g2_exp_aggregation_proof(
                &dt.g2exp_aggregation_data,
                &dt.g2exp_aggregation_t,
                &aggregation_witness,
            )
            .unwrap();
            proof
        })
        .collect();
    println!("Start: fq12exp_proofs");
    let fq12exp_proofs: Vec<_> = witness
        .fq12exp
        .iter()
        .map(|fq12exp_w| {
            let partial_fq12exp_w =
                generate_fq12exp_witness_from_x(fq12exp_w.p, fq12exp_w.x, NUM_BITS_FQ12);
            let proofs: Vec<_> = partial_fq12exp_w
                .par_iter()
                .map(|sw| generate_fq12_exp_proof(&dt.fq12exp_data, &dt.fq12exp_t, sw).unwrap())
                .collect();
            let aggregation_witness = Fq12ExpAggregationWitness {
                proofs,
                p: fq12exp_w.p,
                p_x: fq12exp_w.p_x,
                x: fq12exp_w.x,
            };
            let proof = generate_fq12_exp_aggregation_proof(
                &dt.fq12exp_aggregation_data,
                &dt.fq12exp_aggregation_t,
                &aggregation_witness,
            )
            .unwrap();
            proof
        })
        .collect();
    StatementProofs {
        g1exp_proofs,
        g2exp_proofs,
        fq12exp_proofs,
    }
}

pub fn add_recursive_constraint<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inner_data: &CircuitData<F, C, D>,
) -> ProofWithPublicInputsTarget<D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let vt = builder.constant_verifier_data(&inner_data.verifier_only);
    let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
    builder.verify_proof::<C>(&proof_t, &vt, &inner_data.common);
    proof_t
}

pub struct ProofTargets<const D: usize> {
    pub sipp_proof_target: ProofWithPublicInputsTarget<D>,
    pub g1exp_proof_targets: Vec<ProofWithPublicInputsTarget<D>>,
    pub g2exp_proof_targets: Vec<ProofWithPublicInputsTarget<D>>,
    pub fq12exp_proof_targets: Vec<ProofWithPublicInputsTarget<D>>,
}

pub fn build_wrapper_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    sipp_data: &CircuitData<F, C, D>,
    dt: &StatementDataAndTarget<F, C, D>,
) -> (CircuitData<F, C, D>, ProofTargets<D>)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let n = 1 << LOG_N;
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let sipp_proof_target = add_recursive_constraint(&mut builder, &sipp_data);
    let g1exp_proof_targets = (0..n - 1)
        .map(|_| add_recursive_constraint(&mut builder, &dt.g1exp_data))
        .collect_vec();
    let g2exp_proof_targets = (0..n - 1)
        .map(|_| add_recursive_constraint(&mut builder, &dt.g2exp_aggregation_data))
        .collect_vec();
    let fq12exp_proof_targets = (0..2 * LOG_N)
        .map(|_| add_recursive_constraint(&mut builder, &dt.fq12exp_aggregation_data))
        .collect_vec();

    // constrain public inputs
    let verifier_circuit_pi =
        VerifierCircuitTarget::from_vec(&mut builder, &sipp_proof_target.public_inputs);

    verifier_circuit_pi
        .g1exp
        .iter()
        .zip(g1exp_proof_targets.iter())
        .for_each(|(sipp_g1exp, proof)| {
            let pi = G1ExpTarget::from_vec(&mut builder, &proof.public_inputs);
            G1Target::connect(&mut builder, &sipp_g1exp.p, &pi.p);
            G1Target::connect(&mut builder, &sipp_g1exp.p_x, &pi.p_x);
            FrTarget::connect(&mut builder, &sipp_g1exp.x, &pi.x);
        });

    verifier_circuit_pi
        .g2exp
        .iter()
        .zip(g2exp_proof_targets.iter())
        .for_each(|(sipp_g2exp, proof)| {
            let pi = <G2ExpAggregationTarget<F, D> as RecursiveCircuitTarget<
                F,
                D,
                G2ExpAggregationPublicInputs<F, D>,
                G2ExpAggregationWitness<F, C, D>,
            >>::from_vec(&mut builder, &proof.public_inputs);
            G2Target::connect(&mut builder, &sipp_g2exp.p, &pi.p);
            G2Target::connect(&mut builder, &sipp_g2exp.p_x, &pi.p_x);
            FrTarget::connect(&mut builder, &sipp_g2exp.x, &pi.x);
        });

    verifier_circuit_pi
        .fq12exp
        .iter()
        .zip(fq12exp_proof_targets.iter())
        .for_each(|(sipp_fq12exp, proof)| {
            let pi = <Fq12ExpAggregationTarget<F, D> as RecursiveCircuitTarget<
                F,
                D,
                Fq12ExpAggregationPublicInputs<F, D>,
                Fq12ExpAggregationWitness<F, C, D>,
            >>::from_vec(&mut builder, &proof.public_inputs);
            Fq12Target::connect(&mut builder, &sipp_fq12exp.p, &pi.p);
            Fq12Target::connect(&mut builder, &sipp_fq12exp.p_x, &pi.p_x);
            FrTarget::connect(&mut builder, &sipp_fq12exp.x, &pi.x);
        });
    let prooftargets = ProofTargets {
        sipp_proof_target,
        g1exp_proof_targets,
        g2exp_proof_targets,
        fq12exp_proof_targets,
    };
    let data = builder.build::<C>();
    (data, prooftargets)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        prover_native::prove, verifier_native::verify, verifier_witness::generate_verifier_witness,
    };

    use super::*;
    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::goldilocks_field::GoldilocksField, iop::witness::WitnessWrite,
        plonk::config::PoseidonGoldilocksConfig,
    };

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    #[allow(non_snake_case)]
    fn test_sipp_circuit() {
        let rng = &mut ark_std::test_rng();
        let n = 1 << LOG_N;
        let A = (0..n).map(|_| G1Affine::rand(rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(rng)).collect_vec();
        let proof = prove(&A, &B);
        let witness = generate_verifier_witness::<F>(&A, &B, &proof);
        assert!(verify(&A, &B, &proof).is_ok());

        let (data, t) = build_verifier_circuit::<F, C, D>();
        let mut pw = PartialWitness::<F>::new();
        t.set_witness(&mut pw, &witness);
        let _proof = data.prove(pw).unwrap();
        dbg!(data.common.degree_bits());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_recursive_sipp_circuit() {
        let rng = &mut ark_std::test_rng();
        let n = 1 << LOG_N;
        let A = (0..n).map(|_| G1Affine::rand(rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(rng)).collect_vec();
        let sipp_proof = prove(&A, &B);
        let witness = generate_verifier_witness::<F>(&A, &B, &sipp_proof);
        assert!(verify(&A, &B, &sipp_proof).is_ok());

        let (data, t) = build_verifier_circuit::<F, C, D>();
        let proof = generate_verifier_proof(&data, &t, &witness);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let verifier_target = builder.constant_verifier_data(&data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&data.common);
        let verifier_pi = VerifierCircuitTarget::from_vec(&mut builder, &proof_t.public_inputs);
        builder.verify_proof::<C>(&proof_t, &verifier_target, &data.common);

        let mut pw = PartialWitness::<F>::new();
        pw.set_proof_with_pis_target(&proof_t, &proof);

        // set witness to verifier_pi for test purpose
        verifier_pi
            .g1exp
            .iter()
            .zip(witness.g1exp.iter())
            .for_each(|(t, w)| {
                t.set_witness(&mut pw, w);
            });
        verifier_pi
            .g2exp
            .iter()
            .zip(witness.g2exp.iter())
            .for_each(|(t, w)| {
                t.set_witness(&mut pw, w);
            });
        verifier_pi
            .fq12exp
            .iter()
            .zip(witness.fq12exp.iter())
            .for_each(|(t, w)| {
                t.set_witness(&mut pw, w);
            });

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_wrap_sipp_circuit() {
        let rng = &mut ark_std::test_rng();
        let n = 1 << LOG_N;
        let A = (0..n).map(|_| G1Affine::rand(rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(rng)).collect_vec();
        let sipp_proof = prove(&A, &B);
        let witness = generate_verifier_witness::<F>(&A, &B, &sipp_proof);
        assert!(verify(&A, &B, &sipp_proof).is_ok());

        let now = Instant::now();
        println!("Start: cirucit build");
        let (sipp_data, sipp_t) = build_verifier_circuit::<F, C, D>();
        let dt = build_statementdata_and_target::<F, C, D>();
        let (data, proof_targets) = build_wrapper_circuit(&sipp_data, &dt);
        println!("End: circuit build. {} s", now.elapsed().as_secs());

        // proof witness generation
        let now = Instant::now();
        println!("Start: proof generation");
        let proofs = generate_witness_proofs(&dt, &witness);
        let sipp_proof = generate_verifier_proof(&sipp_data, &sipp_t, &witness);
        println!("End: proof generation. {} s", now.elapsed().as_secs());

        // set witness
        let mut pw = PartialWitness::<F>::new();
        pw.set_proof_with_pis_target(&proof_targets.sipp_proof_target, &sipp_proof);
        proof_targets
            .g1exp_proof_targets
            .iter()
            .zip(proofs.g1exp_proofs.iter())
            .for_each(|(t, w)| pw.set_proof_with_pis_target(t, w));
        proof_targets
            .g2exp_proof_targets
            .iter()
            .zip(proofs.g2exp_proofs.iter())
            .for_each(|(t, w)| pw.set_proof_with_pis_target(t, w));
        proof_targets
            .fq12exp_proof_targets
            .iter()
            .zip(proofs.fq12exp_proofs.iter())
            .for_each(|(t, w)| pw.set_proof_with_pis_target(t, w));

        let now = Instant::now();
        println!("Start: wrap proof");
        let _wrap_proof = data.prove(pw).unwrap();
        println!("End: wrap proof. {} s", now.elapsed().as_secs());
    }
}

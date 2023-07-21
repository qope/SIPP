use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField},
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_bn254_pairing::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::fq12_target::Fq12Target,
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};
use starky::proof::StarkProofWithPublicInputsTarget;

use crate::{
    starky_prover::{
        build_fq12_exp_circuit, build_g1_exp_circuit, build_g2_exp_circuit,
        generate_fq12_exp_proof, generate_g1_exp_proof, generate_g2_exp_proof,
    },
    statements::{
        Fq12ExpStatement, G1ExpStatement, G2ExpStatement, FQ12_EXP_STATEMENT_LEN,
        G1_EXP_STATEMENT_LEN, G2_EXP_STATEMENT_LEN,
    },
    transcript_circuit::TranscriptCircuit,
    verifier_witness::VerifierCircuitWitness,
};

const LOG_N: usize = 7;

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
        let num_limbs = 8;
        let num_g1_limbs = 2 * num_limbs;
        let num_g2_limbs = 4 * num_limbs;
        let num_fq12_limbs = 12 * num_limbs;

        let num_a_limbs = n * num_g1_limbs;
        let num_b_limbs = n * num_g2_limbs;
        let num_final_a_limbs = num_g1_limbs;
        let num_final_b_limbs = num_g2_limbs;
        let num_z_limbs = num_fq12_limbs;
        let num_g1exp_limbs = (n - 1) * G1_EXP_STATEMENT_LEN;
        let num_g2exp_limbs = (n - 1) * G2_EXP_STATEMENT_LEN;
        let num_fq12exp_limbs = 2 * LOG_N * FQ12_EXP_STATEMENT_LEN;

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
            .chunks_exact(G1_EXP_STATEMENT_LEN)
            .map(|x| G1ExpStatement::from_vec(builder, x))
            .collect_vec();
        let g2exp = g2exp_raw
            .chunks_exact(G2_EXP_STATEMENT_LEN)
            .map(|x| G2ExpStatement::from_vec(builder, x))
            .collect_vec();
        let fq12exp = fq12exp_raw
            .chunks_exact(FQ12_EXP_STATEMENT_LEN)
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

            let a1_x_a2_t = G1Target::new(builder);
            g1exp_t.push(G1ExpStatement {
                x: a2_t,
                offset: a1_t,
                exp_val: x_t.clone(),
                output: a1_x_a2_t.clone(),
            });
            new_A_t.push(a1_x_a2_t);

            let b1_inv_x_b2_t = G2Target::new(builder);
            g2exp_t.push(G2ExpStatement {
                x: b2_t,
                offset: b1_t,
                exp_val: inv_x_t.clone(),
                output: b1_inv_x_b2_t.clone(),
            });
            new_B_t.push(b1_inv_x_b2_t);
        }

        let Z_Z_L_x_t = Fq12Target::new(builder);
        fq12exp_t.push(Fq12ExpStatement {
            x: Z_L_t,
            offset: Z_t,
            exp_val: x_t,
            output: Z_Z_L_x_t.clone(),
        });

        let new_Z_t = Fq12Target::new(builder);
        fq12exp_t.push(Fq12ExpStatement {
            x: Z_R_t,
            offset: Z_Z_L_x_t,
            exp_val: inv_x_t,
            output: new_Z_t.clone(),
        });

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
    pub g1_exp_proof: ProofWithPublicInputs<F, C, D>,
    pub g2_exp_proof: ProofWithPublicInputs<F, C, D>,
    pub fq12_exp_proof: ProofWithPublicInputs<F, C, D>,
}

pub struct DataAndTarget<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize> {
    pub g1exp_data: CircuitData<F, C, D>,
    pub g2exp_data: CircuitData<F, C, D>,
    pub fq12exp_data: CircuitData<F, C, D>,
    pub g1exp_proof_t: StarkProofWithPublicInputsTarget<D>,
    pub g2exp_proof_t: StarkProofWithPublicInputsTarget<D>,
    pub fq12exp_proof_t: StarkProofWithPublicInputsTarget<D>,
}

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

pub fn build_data_and_target() -> DataAndTarget<F, C, D> {
    let (g1exp_data, g1exp_proof_t) = build_g1_exp_circuit();
    let (g2exp_data, g2exp_proof_t) = build_g2_exp_circuit();
    let (fq12exp_data, fq12exp_proof_t) = build_fq12_exp_circuit();
    DataAndTarget {
        g1exp_data,
        g2exp_data,
        fq12exp_data,
        g1exp_proof_t,
        g2exp_proof_t,
        fq12exp_proof_t,
    }
}

pub fn generate_witness_proofs(
    dt: &DataAndTarget<F, C, D>,
    witness: &VerifierCircuitWitness,
) -> StatementProofs<F, C, D> {
    let mut ws = witness.g1exp.clone();
    ws.push(ws.last().unwrap().clone());
    let g1_exp_proof = generate_g1_exp_proof(&ws, &dt.g1exp_data, &dt.g1exp_proof_t);
    let mut ws = witness.g2exp.clone();
    ws.push(ws.last().unwrap().to_owned());
    let g2_exp_proof = generate_g2_exp_proof(&ws, &dt.g2exp_data, &dt.g2exp_proof_t);
    let mut ws = witness.fq12exp.clone();
    ws.push(ws.last().unwrap().to_owned());
    ws.push(ws.last().unwrap().to_owned());
    let fq12_exp_proof = generate_fq12_exp_proof(&ws, &dt.fq12exp_data, &dt.fq12exp_proof_t);
    StatementProofs {
        g1_exp_proof,
        g2_exp_proof,
        fq12_exp_proof,
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
    pub g1_exp_proof_target: ProofWithPublicInputsTarget<D>,
    pub g2_exp_proof_target: ProofWithPublicInputsTarget<D>,
    pub fq12_exp_proof_target: ProofWithPublicInputsTarget<D>,
}

pub fn build_wrapper_circuit(
    sipp_data: &CircuitData<F, C, D>,
    dt: &DataAndTarget<F, C, D>,
) -> (CircuitData<F, C, D>, ProofTargets<D>) {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let sipp_proof_target = add_recursive_constraint(&mut builder, &sipp_data);
    let g1_exp_proof_target = add_recursive_constraint(&mut builder, &dt.g1exp_data);
    let g2_exp_proof_target = add_recursive_constraint(&mut builder, &dt.g2exp_data);
    let fq12_exp_proof_target = add_recursive_constraint(&mut builder, &dt.fq12exp_data);

    let mut g1_statements = g1_exp_proof_target
        .public_inputs
        .chunks(G1_EXP_STATEMENT_LEN)
        .map(|x| G1ExpStatement::from_vec(&mut builder, x))
        .collect_vec();
    g1_statements.pop();
    let mut g2_statements = g2_exp_proof_target
        .public_inputs
        .chunks(G2_EXP_STATEMENT_LEN)
        .map(|x| G2ExpStatement::from_vec(&mut builder, x))
        .collect_vec();
    g2_statements.pop();
    let mut fq12_statements = fq12_exp_proof_target
        .public_inputs
        .chunks(FQ12_EXP_STATEMENT_LEN)
        .map(|x| Fq12ExpStatement::from_vec(&mut builder, x))
        .collect_vec();
    fq12_statements.pop();
    fq12_statements.pop();

    // constrain public inputs
    let verifier_circuit_pi =
        VerifierCircuitTarget::from_vec(&mut builder, &sipp_proof_target.public_inputs);

    verifier_circuit_pi
        .g1exp
        .iter()
        .zip(g1_statements)
        .for_each(|(lhs, rhs)| {
            G1ExpStatement::connect(&mut builder, lhs, &rhs);
        });

    verifier_circuit_pi
        .g2exp
        .iter()
        .zip(g2_statements.iter())
        .for_each(|(lhs, rhs)| {
            G2ExpStatement::connect(&mut builder, lhs, rhs);
        });

    verifier_circuit_pi
        .fq12exp
        .iter()
        .zip(fq12_statements.iter())
        .for_each(|(lhs, rhs)| {
            Fq12ExpStatement::connect(&mut builder, lhs, rhs);
        });

    let prooftargets = ProofTargets {
        sipp_proof_target,
        g1_exp_proof_target,
        g2_exp_proof_target,
        fq12_exp_proof_target,
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
    fn test_sipp_circuit_without_proving_statements() {
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
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_recursive_sipp_circuit_without_proving_statements() {
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
    fn test_sipp_circuit() {
        println!("Start: aggregate {} pairings into 1", 1 << LOG_N);

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
        let dt = build_data_and_target();
        let (data, proof_targets) = build_wrapper_circuit(&sipp_data, &dt);
        println!("End: circuit build. took {:?}", now.elapsed());

        // proof witness generation
        let now = Instant::now();
        println!("Start: proof generation");
        let proofs = generate_witness_proofs(&dt, &witness);
        let sipp_proof = generate_verifier_proof(&sipp_data, &sipp_t, &witness);
        println!("End: proof generation. took {:?}", now.elapsed());

        // set witness
        let mut pw = PartialWitness::<F>::new();
        pw.set_proof_with_pis_target(&proof_targets.sipp_proof_target, &sipp_proof);
        pw.set_proof_with_pis_target(&proof_targets.g1_exp_proof_target, &proofs.g1_exp_proof);
        pw.set_proof_with_pis_target(&proof_targets.g2_exp_proof_target, &proofs.g2_exp_proof);
        pw.set_proof_with_pis_target(&proof_targets.fq12_exp_proof_target, &proofs.fq12_exp_proof);

        let now = Instant::now();
        println!("Start: wrap proof");
        let _wrap_proof = data.prove(pw).unwrap();
        println!("End: wrap proof. took {:?}", now.elapsed());
    }
}

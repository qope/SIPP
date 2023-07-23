use ark_bn254::{G1Affine, G2Affine};
use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField},
    hash::hash_types::RichField,
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::PoseidonGoldilocksConfig,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_bn254_pairing::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::fq12_target::Fq12Target,
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

use crate::{
    prover_native::sipp_prove_native,
    starky_prover::{
        generate_fq12_exp_proof, generate_g1_exp_proof, generate_g2_exp_proof, StarkyCircuits,
    },
    statements::{
        Fq12ExpStatement, G1ExpStatement, G2ExpStatement, SIPPStatementTarget, SIPPWitnessTarget,
        FQ12_EXP_STATEMENT_LEN, G1_EXP_STATEMENT_LEN, G2_EXP_STATEMENT_LEN,
    },
    transcript_circuit::TranscriptCircuit,
    utils::add_recursive_constraint,
    verifier_witness::generate_sipp_verifier_witness,
};

const LOG_N: usize = 7;

#[allow(non_snake_case)]
pub fn sipp_verifier_constraint<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    A_t: &[G1Target<F, D>],
    B_t: &[G2Target<F, D>],
    proof_t: &[Fq12Target<F, D>],
) -> (SIPPStatementTarget<F, D>, SIPPWitnessTarget<F, D>) {
    let mut g1exp_t: Vec<G1ExpStatement<F, D>> = vec![];
    let mut g2exp_t: Vec<G2ExpStatement<F, D>> = vec![];
    let mut fq12exp_t: Vec<Fq12ExpStatement<F, D>> = vec![];

    let original_A = A_t.to_vec();
    let original_B = B_t.to_vec();

    let mut n = A_t.len();
    let mut A_t = A_t.to_vec();
    let mut B_t = B_t.to_vec();
    let mut transcript_c = TranscriptCircuit::<F, D>::new(builder);
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

    let statement = SIPPStatementTarget {
        A: original_A,
        B: original_B,
        final_A: A_t[0].clone(),
        final_B: B_t[0].clone(),
        Z: Z_t,
    };

    let witness = SIPPWitnessTarget {
        g1exp: g1exp_t,
        g2exp: g2exp_t,
        fq12exp: fq12exp_t,
    };

    (statement, witness)
}

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

pub struct WitnessProofsTarget {
    pub sipp_proof: Vec<Fq12Target<F, D>>,
    pub g1_exp_proof: ProofWithPublicInputsTarget<D>,
    pub g2_exp_proof: ProofWithPublicInputsTarget<D>,
    pub fq12_exp_proof: ProofWithPublicInputsTarget<D>,
}

#[allow(non_snake_case)]
pub fn build_sipp_snark_verifier_circuit(
    starky_circuits: &StarkyCircuits,
) -> (
    CircuitData<F, C, D>,
    SIPPStatementTarget<F, D>,
    WitnessProofsTarget,
) {
    let n = 1 << LOG_N;
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let A = (0..n).map(|_| G1Target::new(&mut builder)).collect_vec();
    let B = (0..n).map(|_| G2Target::new(&mut builder)).collect_vec();
    let sipp_proof = (0..2 * LOG_N + 1)
        .map(|_| Fq12Target::new(&mut builder))
        .collect_vec();
    let (statement_target, witness_target) =
        sipp_verifier_constraint(&mut builder, &A, &B, &sipp_proof);
    let g1_exp_proof_target = add_recursive_constraint(&mut builder, &starky_circuits.g1_exp_data);
    let g2_exp_proof_target = add_recursive_constraint(&mut builder, &starky_circuits.g2_exp_data);
    let fq12_exp_proof_target =
        add_recursive_constraint(&mut builder, &starky_circuits.fq12_exp_data);
    let mut g1_statements = g1_exp_proof_target
        .public_inputs
        .chunks(G1_EXP_STATEMENT_LEN)
        .map(|x| G1ExpStatement::from_vec(&mut builder, x))
        .collect_vec();
    g1_statements.drain(n - 1..);
    let mut g2_statements = g2_exp_proof_target
        .public_inputs
        .chunks(G2_EXP_STATEMENT_LEN)
        .map(|x| G2ExpStatement::from_vec(&mut builder, x))
        .collect_vec();
    g2_statements.drain(n - 1..);
    let mut fq12_statements = fq12_exp_proof_target
        .public_inputs
        .chunks(FQ12_EXP_STATEMENT_LEN)
        .map(|x| Fq12ExpStatement::from_vec(&mut builder, x))
        .collect_vec();
    fq12_statements.drain(2 * LOG_N..);
    witness_target
        .g1exp
        .iter()
        .zip(g1_statements)
        .for_each(|(lhs, rhs)| {
            G1ExpStatement::connect(&mut builder, lhs, &rhs);
        });
    witness_target
        .g2exp
        .iter()
        .zip(g2_statements.iter())
        .for_each(|(lhs, rhs)| {
            G2ExpStatement::connect(&mut builder, lhs, rhs);
        });
    witness_target
        .fq12exp
        .iter()
        .zip(fq12_statements.iter())
        .for_each(|(lhs, rhs)| {
            Fq12ExpStatement::connect(&mut builder, lhs, rhs);
        });
    builder.register_public_inputs(&statement_target.to_vec());
    let data = builder.build::<C>();
    let witness_proofs_target = WitnessProofsTarget {
        sipp_proof,
        g1_exp_proof: g1_exp_proof_target,
        g2_exp_proof: g2_exp_proof_target,
        fq12_exp_proof: fq12_exp_proof_target,
    };
    (data, statement_target, witness_proofs_target)
}

#[allow(non_snake_case)]
pub fn generate_sipp_snark_verifier_proof(
    verifier_data: &CircuitData<F, C, D>,
    starky_circuits: &StarkyCircuits,
    statement_target: &SIPPStatementTarget<F, D>,
    witness_proofs_target: &WitnessProofsTarget,
    A: &[G1Affine],
    B: &[G2Affine],
) -> ProofWithPublicInputs<F, C, D> {
    let n = A.len();
    assert!(B.len() == n);
    let sipp_proof = sipp_prove_native(&A, &B);
    let (statement, witness) = generate_sipp_verifier_witness::<F>(&A, &B, &sipp_proof);
    let g1_exp_proof = generate_g1_exp_proof(
        &witness.g1_exp,
        &starky_circuits.g1_exp_data,
        &starky_circuits.g1_exp_starky_proof,
    );
    let g2_exp_proof = generate_g2_exp_proof(
        &witness.g2_exp,
        &starky_circuits.g2_exp_data,
        &starky_circuits.g2_exp_starky_proof,
    );
    let fq12_exp_proof = generate_fq12_exp_proof(
        &witness.fq12_exp,
        &starky_circuits.fq12_exp_data,
        &starky_circuits.fq12_exp_starky_proof,
    );

    let mut pw = PartialWitness::<F>::new();

    statement_target
        .A
        .iter()
        .zip(statement.A.iter())
        .for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
    statement_target
        .B
        .iter()
        .zip(statement.B.iter())
        .for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
    statement_target
        .final_A
        .set_witness(&mut pw, &statement.final_A);
    statement_target
        .final_B
        .set_witness(&mut pw, &statement.final_B);
    statement_target.Z.set_witness(&mut pw, &statement.Z);

    witness_proofs_target
        .sipp_proof
        .iter()
        .zip(sipp_proof.iter())
        .for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });

    pw.set_proof_with_pis_target(&witness_proofs_target.g1_exp_proof, &g1_exp_proof);
    pw.set_proof_with_pis_target(&witness_proofs_target.g2_exp_proof, &g2_exp_proof);
    pw.set_proof_with_pis_target(&witness_proofs_target.fq12_exp_proof, &fq12_exp_proof);

    let proof = verifier_data.prove(pw).unwrap();
    proof
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        prover_native::sipp_prove_native, starky_prover::build_starky_circuits,
        verifier_native::sipp_verify_native,
    };

    use super::*;
    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;

    #[test]
    #[allow(non_snake_case)]
    fn test_sipp_circuit() {
        println!("Aggregating {} pairings into 1", 1 << LOG_N);
        let mut rng = rand::thread_rng();
        let n = 1 << LOG_N;
        let A = (0..n).map(|_| G1Affine::rand(&mut rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(&mut rng)).collect_vec();

        let sipp_proof = sipp_prove_native(&A, &B);
        assert!(sipp_verify_native(&A, &B, &sipp_proof).is_ok());

        println!("Start: cirucit build");
        let now = Instant::now();
        let starky_circuits = build_starky_circuits();
        let (sipp_snark_circuit, statement_target, witness_proofs_target) =
            build_sipp_snark_verifier_circuit(&starky_circuits);
        println!("End: circuit build. took {:?}", now.elapsed());

        println!("Start: proof generation");
        let now = Instant::now();
        let _proof = generate_sipp_snark_verifier_proof(
            &sipp_snark_circuit,
            &starky_circuits,
            &statement_target,
            &witness_proofs_target,
            &A,
            &B,
        );
        println!("End: proof generation. took {:?}", now.elapsed());
    }
}

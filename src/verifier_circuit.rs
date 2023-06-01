use ark_bn254::{Fq12, G1Affine, G2Affine};
use ark_ff::Field;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bn254_pairing::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, fr_target::FrTarget},
};

use crate::{transcript_circuit::TranscriptCircuit, transcript_native::Transcript};

#[allow(non_snake_case)]
pub struct SMG1Statement<F: RichField + Extendable<D>, const D: usize> {
    pub G: G1Target<F, D>,
    pub s: FrTarget<F, D>,
    pub sG: G1Target<F, D>,
}

#[allow(non_snake_case)]
pub struct SMG2Statement<F: RichField + Extendable<D>, const D: usize> {
    pub G: G2Target<F, D>,
    pub s: FrTarget<F, D>,
    pub sG: G2Target<F, D>,
}

pub struct ExpFq12Statement<F: RichField + Extendable<D>, const D: usize> {
    pub p: Fq12Target<F, D>,
    pub x: FrTarget<F, D>,
    pub px: Fq12Target<F, D>,
}

#[allow(non_snake_case)]
pub struct VerifyCircuitOutput<F: RichField + Extendable<D>, const D: usize> {
    pub A: G1Target<F, D>,
    pub B: G2Target<F, D>,
    pub Z: Fq12Target<F, D>,
    pub smg1: Vec<SMG1Statement<F, D>>,
    pub smg2: Vec<SMG2Statement<F, D>>,
    pub expf12: Vec<ExpFq12Statement<F, D>>,
}

#[allow(non_snake_case)]
pub fn verify_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    A_t: &[G1Target<F, D>],
    B_t: &[G2Target<F, D>],
    proof_t: &[Fq12Target<F, D>],
    witness_A: &[G1Affine],
    witness_B: &[G2Affine],
    witness_proof: &[Fq12],
) -> VerifyCircuitOutput<F, D> {
    let mut smg1: Vec<SMG1Statement<F, D>> = vec![];
    let mut smg2: Vec<SMG2Statement<F, D>> = vec![];
    let mut expf12: Vec<ExpFq12Statement<F, D>> = vec![];

    let mut n = A_t.len();
    let mut A_t = A_t.to_vec();
    let mut B_t = B_t.to_vec();
    let mut A = witness_A.to_vec();
    let mut B = witness_B.to_vec();
    let mut transcript_c = TranscriptCircuit::<F, D>::new(builder);
    let mut transcript = Transcript::<F>::new();
    let mut proof_t = proof_t.to_vec();
    let mut proof = witness_proof.to_vec();

    // register A and B
    A_t.iter().zip(B_t.iter()).for_each(|(a, b)| {
        transcript_c.append_g1(builder, a.clone());
        transcript_c.append_g2(builder, b.clone());
    });
    A.iter().zip(B.iter()).for_each(|(a, b)| {
        transcript.append_g1(*a);
        transcript.append_g2(*b);
    });

    // receive Z
    let mut Z_t = proof_t.pop().unwrap();
    transcript_c.append_fq12(builder, Z_t.clone());
    let mut Z = proof.pop().unwrap();
    transcript.append_fq12(Z);

    while n > 1 {
        let (A1_t, A2_t) = A_t.split_at(n / 2);
        let (B1_t, B2_t) = B_t.split_at(n / 2);
        let (A1, A2) = A.split_at(n / 2);
        let (B1, B2) = B.split_at(n / 2);

        // receive Z_L and Z_R
        let Z_L_t = proof_t.pop().unwrap();
        transcript_c.append_fq12(builder, Z_L_t.clone());
        let Z_R_t = proof_t.pop().unwrap();
        transcript_c.append_fq12(builder, Z_R_t.clone());
        let Z_L = proof.pop().unwrap();
        transcript.append_fq12(Z_L);
        let Z_R = proof.pop().unwrap();
        transcript.append_fq12(Z_R);

        let x_t = transcript_c.get_challenge(builder);
        let inv_x_t = x_t.inv(builder);
        let x = transcript.get_challenge();
        let inv_x = x.inverse().unwrap();

        let mut new_A_t = vec![];
        let mut new_B_t = vec![];
        let mut new_A = vec![];
        let mut new_B = vec![];

        for i in 0..(n / 2) {
            let a1_t = A1_t[i].clone();
            let a2_t = A2_t[i].clone();
            let a1 = A1[i];
            let a2 = A2[i];

            let b1_t = B1_t[i].clone();
            let b2_t = B2_t[i].clone();
            let b1 = B1[i];
            let b2 = B2[i];

            let x_a2: G1Affine = (a2 * x).into();
            let x_a2_t = G1Target::constant(builder, x_a2);
            smg1.push(SMG1Statement {
                G: a2_t,
                s: x_t.clone(),
                sG: x_a2_t.clone(),
            });
            new_A_t.push(a1_t.add(builder, &x_a2_t));

            let inv_x_b2: G2Affine = (b2 * inv_x).into();
            let inv_x_b2_t = G2Target::constant(builder, inv_x_b2);
            smg2.push(SMG2Statement {
                G: b2_t,
                s: inv_x_t.clone(),
                sG: inv_x_b2_t.clone(),
            });
            new_B_t.push(b1_t.add(builder, &inv_x_b2_t));

            new_A.push((a1 + x_a2).into());
            new_B.push((b1 + inv_x_b2).into());
        }

        let x: BigUint = x.into();
        let inv_x: BigUint = inv_x.into();
        let Z_L_x = Z_L.pow(&x.to_u64_digits());
        let Z_R_inv_x = Z_R.pow(&inv_x.to_u64_digits());

        let Z_L_x_t = Fq12Target::constant(builder, Z_L_x);
        expf12.push(ExpFq12Statement {
            p: Z_L_t,
            x: x_t,
            px: Z_L_x_t.clone(),
        });

        let Z_R_inv_x_t = Fq12Target::constant(builder, Z_R_inv_x);
        expf12.push(ExpFq12Statement {
            p: Z_R_t,
            x: inv_x_t,
            px: Z_R_inv_x_t.clone(),
        });

        let new_Z_t = Z_L_x_t.mul(builder, &Z_t).mul(builder, &Z_R_inv_x_t);

        let new_Z = Z_L_x * Z * Z_R_inv_x;

        // update
        A_t = new_A_t;
        B_t = new_B_t;
        Z_t = new_Z_t;
        A = new_A;
        B = new_B;
        Z = new_Z;
        n = n / 2;
    }

    VerifyCircuitOutput {
        A: A_t[0].clone(),
        B: B_t[0].clone(),
        Z: Z_t,
        smg1,
        smg2,
        expf12,
    }
}

// statementを作りたい。例えば、a.mul(x)が現れる度に、a.mul(x)の値を直接設定する代わりに、(a, x, a.mul(x))のタプルを公開入力に加える。

#[cfg(test)]
mod tests {
    use crate::{prover_native::prove, verifier_native::verify};

    use super::*;
    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{circuit_data::CircuitConfig, config::PoseidonGoldilocksConfig},
    };

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    #[allow(non_snake_case)]
    fn test_sipp_circuit() {
        let rng = &mut ark_std::test_rng();
        let n = 64;
        let A = (0..n).map(|_| G1Affine::rand(rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(rng)).collect_vec();
        let proof = prove(&A, &B);
        assert!(verify(&A, &B, &proof).is_ok());

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let A_t = A
            .iter()
            .map(|x| G1Target::<F, D>::constant(&mut builder, x.clone()))
            .collect_vec();
        let B_t = B
            .iter()
            .map(|x| G2Target::<F, D>::constant(&mut builder, x.clone()))
            .collect_vec();
        let proof_t = proof
            .iter()
            .map(|x| Fq12Target::<F, D>::constant(&mut builder, x.clone()))
            .collect_vec();
        let output = verify_circuit(&mut builder, &A_t, &B_t, &proof_t, &A, &B, &proof);
        println!("num of SMG1Statement: {}", output.smg1.len());
        println!("num of SMG2Statement: {}", output.smg2.len());
        println!("num of ExpFq12Statement: {}", output.expf12.len());

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
        dbg!(data.common.degree_bits());
    }
}

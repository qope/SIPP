use ark_bn254::{Fq12, Fr, G1Affine, G2Affine};
use ark_ff::Field;
use num_bigint::BigUint;
use plonky2::hash::hash_types::RichField;

use crate::transcript_native::Transcript;

pub struct G1ExpWitness {
    pub x: G1Affine,
    pub offset: G1Affine,
    pub exp_val: Fr,
    pub output: G1Affine,
}

pub struct G2ExpWitness {
    pub x: G2Affine,
    pub offset: G2Affine,
    pub exp_val: Fr,
    pub output: G2Affine,
}

pub struct Fq12ExpWitness {
    pub x: Fq12,
    pub offset: Fq12,
    pub exp_val: Fr,
    pub output: Fq12,
}

#[allow(non_snake_case)]
pub struct VerifierCircuitWitness {
    pub n: usize,
    pub A: Vec<G1Affine>,
    pub B: Vec<G2Affine>,
    pub final_A: G1Affine,
    pub final_B: G2Affine,
    pub Z: Fq12,
    pub proof: Vec<Fq12>,
    pub g1exp: Vec<G1ExpWitness>,
    pub g2exp: Vec<G2ExpWitness>,
    pub fq12exp: Vec<Fq12ExpWitness>,
}

#[allow(non_snake_case)]
pub fn generate_verifier_witness<F: RichField>(
    A: &[G1Affine],
    B: &[G2Affine],
    proof: &[Fq12],
) -> VerifierCircuitWitness {
    let mut g1exp_w: Vec<G1ExpWitness> = vec![];
    let mut g2exp_w: Vec<G2ExpWitness> = vec![];
    let mut fq12exp_w: Vec<Fq12ExpWitness> = vec![];

    let original_n = A.len();
    let original_A = A.to_vec();
    let original_B = B.to_vec();
    let original_proof = proof.to_vec();

    let mut n = original_n;
    let mut A = original_A.clone();
    let mut B = original_B.to_vec();
    let mut transcript = Transcript::<F>::new();
    let mut proof = original_proof.clone();

    // register A and B
    A.iter().zip(B.iter()).for_each(|(a, b)| {
        transcript.append_g1(*a);
        transcript.append_g2(*b);
    });

    // receive Z
    let mut Z = proof.pop().unwrap();
    transcript.append_fq12(Z);

    while n > 1 {
        let (A1, A2) = A.split_at(n / 2);
        let (B1, B2) = B.split_at(n / 2);

        // receive Z_L and Z_R
        let Z_L = proof.pop().unwrap();
        transcript.append_fq12(Z_L);
        let Z_R = proof.pop().unwrap();
        transcript.append_fq12(Z_R);

        let x: Fr = transcript.get_challenge();
        let inv_x: Fr = x.inverse().unwrap();

        let mut new_A = vec![];
        let mut new_B = vec![];

        for i in 0..(n / 2) {
            let a1: G1Affine = A1[i];
            let a2: G1Affine = A2[i];

            let b1 = B1[i];
            let b2 = B2[i];

            let a1_x_a2: G1Affine = (a1 + a2 * x).into();

            g1exp_w.push(G1ExpWitness {
                x: a2,
                offset: a1,
                exp_val: x,
                output: a1_x_a2,
            });

            let b1_inv_x_b2: G2Affine = (b1 + b2 * inv_x).into();
            g2exp_w.push(G2ExpWitness {
                x: b2,
                offset: b1,
                exp_val: inv_x,
                output: b1_inv_x_b2,
            });

            new_A.push(a1_x_a2);
            new_B.push(b1_inv_x_b2);
        }

        let x_biguint: BigUint = x.into();
        let inv_x_biguint: BigUint = inv_x.into();
        let Z_Z_L_x = Z * Z_L.pow(&x_biguint.to_u64_digits());
        let new_Z = Z_Z_L_x * Z_R.pow(&inv_x_biguint.to_u64_digits());

        fq12exp_w.push(Fq12ExpWitness {
            x: Z_L,
            offset: Z,
            exp_val: x,
            output: Z_Z_L_x,
        });
        fq12exp_w.push(Fq12ExpWitness {
            x: Z_R,
            offset: Z_Z_L_x,
            exp_val: inv_x,
            output: new_Z,
        });

        A = new_A;
        B = new_B;
        Z = new_Z;
        n = n / 2;
    }

    VerifierCircuitWitness {
        n: original_n,
        A: original_A,
        B: original_B,
        final_A: A[0],
        final_B: B[0],
        Z,
        proof: original_proof,
        g1exp: g1exp_w,
        g2exp: g2exp_w,
        fq12exp: fq12exp_w,
    }
}

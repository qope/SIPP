use ark_bn254::{Fq12, Fr, G1Affine, G2Affine};
use ark_ff::Field;
use num_bigint::BigUint;
use plonky2::hash::hash_types::RichField;

use crate::transcript_native::Transcript;

pub struct G1ExpWitness {
    pub p: G1Affine,
    pub p_x: G1Affine,
    pub x: Fr,
}

pub struct G2ExpWitness {
    pub p: G2Affine,
    pub p_x: G2Affine,
    pub x: Fr,
}

pub struct Fq12ExpWitness {
    pub p: Fq12,
    pub p_x: Fq12,
    pub x: Fr,
}

#[allow(non_snake_case)]
pub struct VerifyCircuitOutputWitness {
    pub A: G1Affine,
    pub B: G2Affine,
    pub Z: Fq12,
    pub g1exp: Vec<G1ExpWitness>,
    pub g2exp: Vec<G2ExpWitness>,
    pub fq12exp: Vec<Fq12ExpWitness>,
}

#[allow(non_snake_case)]
pub fn generate_verifier_witness<F: RichField>(
    A: &[G1Affine],
    B: &[G2Affine],
    proof: &[Fq12],
) -> VerifyCircuitOutputWitness {
    let mut g1exp_w: Vec<G1ExpWitness> = vec![];
    let mut g2exp_w: Vec<G2ExpWitness> = vec![];
    let mut fq12exp_w: Vec<Fq12ExpWitness> = vec![];

    let mut n = A.len();
    let mut A = A.to_vec();
    let mut B = B.to_vec();
    let mut transcript = Transcript::<F>::new();
    let mut proof = proof.to_vec();

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

            let x_a2: G1Affine = (a2 * x).into();

            g1exp_w.push(G1ExpWitness {
                p: a2,
                x,
                p_x: x_a2,
            });

            let inv_x_b2: G2Affine = (b2 * inv_x).into();
            g2exp_w.push(G2ExpWitness {
                p: b2,
                x: inv_x,
                p_x: inv_x_b2,
            });
            new_A.push((a1 + x_a2).into());
            new_B.push((b1 + inv_x_b2).into());
        }

        let x_biguint: BigUint = x.into();
        let inv_x_biguint: BigUint = inv_x.into();
        let Z_L_x = Z_L.pow(&x_biguint.to_u64_digits());
        let Z_R_inv_x = Z_R.pow(&inv_x_biguint.to_u64_digits());

        fq12exp_w.push(Fq12ExpWitness {
            p: Z_L,
            x,
            p_x: Z_L_x,
        });

        fq12exp_w.push(Fq12ExpWitness {
            p: Z_R,
            x: inv_x,
            p_x: Z_R_inv_x,
        });

        let new_Z = Z_L_x * Z * Z_R_inv_x;

        A = new_A;
        B = new_B;
        Z = new_Z;
        n = n / 2;
    }

    VerifyCircuitOutputWitness {
        A: A[0],
        B: B[0],
        Z,
        g1exp: g1exp_w,
        g2exp: g2exp_w,
        fq12exp: fq12exp_w,
    }
}

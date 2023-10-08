use crate::{statements::SIPPStatement, transcript_native::Transcript};
use anyhow::Result;
use ark_bn254::{Fq12, G1Affine, G2Affine};
use ark_ff::Field;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2_bn254_pairing::pairing::pairing;
use std::ops::Mul;

type F = GoldilocksField;

#[allow(non_snake_case)]
pub fn sipp_verify_native(A: &[G1Affine], B: &[G2Affine], proof: &[Fq12]) -> Result<SIPPStatement> {
    let mut n = A.len();
    let original_A = A.to_vec();
    let original_B = B.to_vec();

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
    let original_Z = proof.pop().unwrap();
    let mut Z = original_Z.clone();
    transcript.append_fq12(Z);

    while n > 1 {
        let (A1, A2) = A.split_at(n / 2);
        let (B1, B2) = B.split_at(n / 2);

        // receive Z_L and Z_R
        let Z_L = proof.pop().unwrap();
        transcript.append_fq12(Z_L);
        let Z_R = proof.pop().unwrap();
        transcript.append_fq12(Z_R);

        let x = transcript.get_challenge();
        let inv_x = x.inverse().unwrap();

        let new_A = A1
            .iter()
            .zip(A2.iter())
            .map(|(&a1, &a2)| (a1 + a2.mul(x)).into())
            .collect_vec();
        let new_B = B1
            .iter()
            .zip(B2.iter())
            .map(|(&b1, &b2)| (b1 + b2.mul(inv_x)).into())
            .collect_vec();

        let x: BigUint = x.into();
        let inv_x: BigUint = inv_x.into();
        let new_Z = Z_L.pow(&x.to_u64_digits()) * Z * Z_R.pow(&inv_x.to_u64_digits());

        // update
        A = new_A;
        B = new_B;
        Z = new_Z;
        n = n / 2;
    }

    let statement = SIPPStatement {
        A: original_A,
        B: original_B,
        Z: original_Z,
        final_A: A[0],
        final_B: B[0],
        final_Z: Z,
    };

    // check if Z == e(A, B)
    if pairing(statement.final_A, statement.final_B) == statement.final_Z {
        Ok(statement)
    } else {
        Err(anyhow::anyhow!("Verification failed"))
    }
}

#[cfg(test)]
mod tests {
    use crate::prover_native::{inner_product, sipp_prove_native};

    use super::*;
    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;

    #[test]
    #[allow(non_snake_case)]
    fn test_sipp_native() {
        let rng = &mut ark_std::test_rng();
        let n = 64;
        let A = (0..n).map(|_| G1Affine::rand(rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(rng)).collect_vec();
        let proof = sipp_prove_native(&A, &B);
        assert!(sipp_verify_native(&A, &B, &proof).is_ok());
        assert!(&inner_product(&A, &B) == proof.last().unwrap());
    }
}

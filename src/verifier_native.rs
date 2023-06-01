use crate::transcript_native::Transcript;
use anyhow::Result;
use ark_bn254::{Bn254, Fq12, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ff::Field;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::field::goldilocks_field::GoldilocksField;
use std::ops::Mul;

type F = GoldilocksField;

#[allow(non_snake_case)]
pub fn verify(A: &[G1Affine], B: &[G2Affine], proof: &[Fq12]) -> Result<()> {
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

    // check if Z == e(A, B)
    let e = Bn254::pairing(A[0], B[0]).0;

    if Z == e {
        Ok(())
    } else {
        Err(anyhow::anyhow!("Verification failed"))
    }
}

#[cfg(test)]
mod tests {
    use crate::prover_native::prove;

    use super::*;
    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;

    #[test]
    #[allow(non_snake_case)]
    fn test_sipp() {
        let rng = &mut ark_std::test_rng();
        let n = 64;
        let A = (0..n).map(|_| G1Affine::rand(rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(rng)).collect_vec();
        let proof = prove(&A, &B);
        assert!(verify(&A, &B, &proof).is_ok());
    }
}

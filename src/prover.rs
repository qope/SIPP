use std::ops::Mul;

use ark_bn254::{Bn254, Fq12, Fr, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ff::fields::Field;
use itertools::Itertools;
use num_traits::One;

use crate::transcript::Transcript;

#[allow(non_snake_case)]
pub fn inner_product(A: &[G1Affine], B: &[G2Affine]) -> Fq12 {
    assert_eq!(A.len(), B.len());
    let r_vec = A
        .iter()
        .zip(B.iter())
        .map(|(a, b)| Bn254::pairing(*a, *b).0)
        .collect_vec();
    r_vec.iter().fold(Fq12::one(), |acc, x| acc * x)
}

#[allow(non_snake_case)]
pub fn prove(A: &[G1Affine], B: &[G2Affine]) -> Vec<Fq12> {
    assert_eq!(A.len(), B.len());
    let mut n = A.len();
    let Z = inner_product(A, B);
    let mut A = A.to_vec();
    let mut B = B.to_vec();
    let mut transcript = Transcript::new();
    let mut proof: Vec<Fq12> = Vec::new();

    // register A and B
    A.iter().zip(B.iter()).for_each(|(a, b)| {
        transcript.append_g1(*a);
        transcript.append_g2(*b);
    });

    // send Z
    proof.push(Z);
    transcript.append_fq12(Z);

    while n > 1 {
        let (A1, A2) = A.split_at(n / 2);
        let (B1, B2) = B.split_at(n / 2);
        let Z_L = inner_product(A2, B1);
        let Z_R = inner_product(A1, B2);

        // send Z_L, Z_R to the verifier
        proof.push(Z_L);
        transcript.append_fq12(Z_L);
        proof.push(Z_R);
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

        // update
        A = new_A;
        B = new_B;
        n = n / 2;
    }

    // reverse the message because the verifier reads the message in reverse order
    proof.reverse();
    proof
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, G1Affine, G2Affine};
    use ark_ec::pairing::Pairing;
    use ark_std::UniformRand;

    #[test]
    fn test_pairing_bilinearity() {
        let rng = &mut ark_std::test_rng();
        let a = G1Affine::rand(rng);
        let b = G1Affine::rand(rng);
        let c = G2Affine::rand(rng);
        let res1 = Bn254::pairing(a + b, c).0;
        let res2 = Bn254::pairing(a, c).0 * Bn254::pairing(b, c).0;
        assert_eq!(res1, res2);
    }
}

use ark_bn254::{Fq2, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::AffineRepr;
use ark_std::UniformRand;
use itertools::Itertools;
use num_traits::Zero;
use plonky2_bn254::curves::map_to_g2::map_to_g2_without_cofactor_mul;
use plonky2_bn254_pairing::pairing::pairing;
use sipp::{
    prover_native::{inner_product, sipp_prove_native},
    verifier_native::sipp_verify_native,
};

#[allow(non_snake_case)]
fn main() {
    let n = 128;
    let mut rng = rand::thread_rng();
    let private_keys: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect_vec();
    let public_keys: Vec<G1Affine> = private_keys
        .iter()
        .map(|pk| (G1Affine::generator() * pk).into())
        .collect_vec();
    let messages: Vec<G2Affine> = (0..n)
        .map(|_| {
            map_to_g2_without_cofactor_mul(Fq2::rand(&mut rng))
                .mul_by_cofactor_to_group()
                .into()
        })
        .collect_vec();
    let signatures: Vec<G2Affine> = private_keys
        .iter()
        .zip(messages.iter())
        .map(|(&sk, &m)| (m * sk).into())
        .collect_vec();
    let aggregated_signature: G2Affine = signatures
        .iter()
        .fold(G2Projective::zero(), |acc, &s| acc + s)
        .into();

    let Z = inner_product(&public_keys, &messages);
    assert_eq!(Z, pairing(G1Affine::generator(), aggregated_signature));

    let sipp_proof = sipp_prove_native(&public_keys, &messages);
    let statement = sipp_verify_native(&public_keys, &messages, &sipp_proof).unwrap();

    dbg!(&statement);
}

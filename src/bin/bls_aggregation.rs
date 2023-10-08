use std::time::Instant;

use ark_bn254::{Fq12, Fq2, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::AffineRepr;
use ark_std::UniformRand;
use itertools::Itertools;
use num_traits::{One, Zero};
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField},
    hash::hash_types::RichField,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitConfig,
        config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig},
    },
};
use plonky2_bn254::{
    curves::{
        g1curve_target::G1Target, g2curve_target::G2Target,
        map_to_g2::map_to_g2_without_cofactor_mul,
    },
    fields::{fq12_target::Fq12Target, fq2_target::Fq2Target},
};
use plonky2_bn254_pairing::pairing::{pairing, pairing_circuit};
use sipp::{
    prover_native::{inner_product, sipp_prove_native},
    verifier_circuit::sipp_verifier_circuit,
    verifier_native::sipp_verify_native,
};
use starky_bn254::curves::g2::batch_map_to_g2::batch_map_to_g2_circuit;

pub struct BLSTarget<F: RichField + Extendable<D>, const D: usize> {
    pub public_keys: Vec<G1Target<F, D>>,
    pub messages: Vec<Fq2Target<F, D>>,
    pub aggregated_signature: G2Target<F, D>,
    pub sipp_proof: Vec<Fq12Target<F, D>>,
}

pub fn verify_bls_aggregation<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    n: usize,
) -> BLSTarget<F, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();
    let public_keys = (0..n - 1)
        .map(|_| G1Target::empty(builder))
        .collect::<Vec<_>>();
    let aggregated_signature = G2Target::empty(builder);
    let sipp_proof = (0..2 * log_n + 1)
        .map(|_| Fq12Target::empty(builder))
        .collect_vec();
    let messages = (0..n - 1)
        .map(|_| Fq2Target::<F, D>::empty(builder))
        .collect::<Vec<_>>();

    // This is heavy process
    let ms = batch_map_to_g2_circuit::<F, C, D>(builder, &messages);

    let mut a = public_keys.clone();
    let mut b = ms;
    let neg_g1 = G1Target::constant(builder, -G1Affine::generator());
    a.push(neg_g1);
    b.push(aggregated_signature.clone());
    // assert!(a.len() == b.len() && a.len() == n);
    let sipp_statement = sipp_verifier_circuit::<F, C, D>(builder, &a, &b, &sipp_proof);

    // final pairing. This also takes much time!
    let z = pairing_circuit::<F, C, D>(builder, sipp_statement.final_A, sipp_statement.final_B);
    Fq12Target::connect(builder, &z, &sipp_statement.final_Z);

    BLSTarget {
        public_keys,
        messages,
        aggregated_signature,
        sipp_proof,
    }
}

#[allow(non_snake_case)]
fn main() {
    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    let n = 128;
    let mut rng = rand::thread_rng();
    let private_keys: Vec<Fr> = (0..n - 1).map(|_| Fr::rand(&mut rng)).collect_vec();
    let public_keys: Vec<G1Affine> = private_keys
        .iter()
        .map(|pk| (G1Affine::generator() * pk).into())
        .collect_vec();
    let messages = (0..n - 1).map(|_| Fq2::rand(&mut rng)).collect::<Vec<_>>();
    let ms: Vec<G2Affine> = messages
        .iter()
        .map(|u| map_to_g2_without_cofactor_mul(*u).mul_by_cofactor())
        .collect_vec();
    let signatures: Vec<G2Affine> = private_keys
        .iter()
        .zip(ms.iter())
        .map(|(&sk, &m)| (m * sk).into())
        .collect_vec();
    let aggregated_signature: G2Affine = signatures
        .iter()
        .fold(G2Projective::zero(), |acc, &s| acc + s)
        .into();
    let mut a = public_keys.clone();
    let mut b = ms.clone();
    a.push(-G1Affine::generator());
    b.push(aggregated_signature);

    assert_eq!(inner_product(&a, &b), Fq12::one());
    let sipp_proof = sipp_prove_native(&a, &b);
    let sipp_statement = sipp_verify_native(&a, &b, &sipp_proof).unwrap();
    assert!(pairing(sipp_statement.final_A, sipp_statement.final_B) == sipp_statement.final_Z);

    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let bls_target = verify_bls_aggregation::<F, C, D>(&mut builder, n);
    println!("start circuit building");
    let data = builder.build::<C>();
    println!("end circuit building");

    println!("start proving");
    let now = Instant::now();
    let mut pw = PartialWitness::new();
    bls_target
        .aggregated_signature
        .set_witness(&mut pw, &aggregated_signature);
    bls_target
        .messages
        .iter()
        .zip_eq(messages.iter())
        .for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
    bls_target
        .public_keys
        .iter()
        .zip_eq(public_keys.iter())
        .for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
    bls_target
        .sipp_proof
        .iter()
        .zip_eq(sipp_proof.iter())
        .for_each(|(t, w)| {
            t.set_witness(&mut pw, w);
        });
    let _proof = data.prove(pw).unwrap();
    println!("end proving in {:?}", now.elapsed());
}

use std::{str::FromStr, time::Instant};

use ark_bn254::{Fq12, Fq2, Fr, G1Affine, G2Affine, G2Projective};
use ark_ec::AffineRepr;
use ark_std::UniformRand;
use itertools::Itertools;
use num_bigint::BigUint;
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
    fields::fq12_target::Fq12Target,
};
use plonky2_bn254_pairing::pairing::pairing_circuit;
use sipp::{
    prover_native::{inner_product, sipp_prove_native},
    verifier_circuit::sipp_verifier_circuit,
};
use starky_bn254::{circuits::g2_exp_circuit, input_target::G2ExpInputTarget};

pub struct BLSTarget<F: RichField + Extendable<D>, const D: usize> {
    pub m_before_cofactor_muls: Vec<G2Target<F, D>>,
    pub public_keys: Vec<G1Target<F, D>>,
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
    let m_before_cofactor_muls = (0..n - 1)
        .map(|_| G2Target::empty(builder))
        .collect::<Vec<_>>();
    let public_keys = (0..n - 1)
        .map(|_| G1Target::empty(builder))
        .collect::<Vec<_>>();
    let aggregated_signature = G2Target::empty(builder);
    let sipp_proof = (0..2 * log_n + 1)
        .map(|_| Fq12Target::empty(builder))
        .collect_vec();
    let g2_gen = G2Target::constant(builder, G2Affine::generator());
    let exp_val_b = BigUint::from_str(
        "21888242871839275222246405745257275088844257914179612981679871602714643921549",
    )
    .unwrap();
    let exp_val_limbs = exp_val_b.to_u32_digits();
    let exp_val_limbs_t = exp_val_limbs
        .into_iter()
        .map(|x| builder.constant(F::from_canonical_u32(x)))
        .collect::<Vec<_>>();
    assert!(exp_val_limbs_t.len() == 8);
    let exp_val =
        plonky2_bn254::fields::u256_target::U256Target::<F, D>::from_vec(&exp_val_limbs_t);
    let mut g2_sm_input = m_before_cofactor_muls
        .iter()
        .map(|m_before_cofactor_mul| G2ExpInputTarget {
            x: m_before_cofactor_mul.clone(),
            offset: g2_gen.clone(),
            exp_val: exp_val.clone(),
        })
        .collect::<Vec<_>>();
    // padd
    g2_sm_input.push(g2_sm_input.last().unwrap().clone());
    let ms = g2_exp_circuit::<F, C, D>(builder, &g2_sm_input);
    let neg_g2_gen = G2Target::constant(builder, -G2Affine::generator());
    let ms = ms[..n - 1]
        .iter()
        .map(|m| m.add(builder, &neg_g2_gen))
        .collect::<Vec<_>>();
    let mut a = public_keys.clone();
    let mut b = ms;
    let neg_g1 = G1Target::constant(builder, -G1Affine::generator());
    a.push(neg_g1);
    b.push(aggregated_signature.clone());
    assert!(a.len() == b.len() && a.len() == n);
    let sipp_statement = sipp_verifier_circuit::<F, C, D>(builder, &a, &b, &sipp_proof);

    // final pairing. This takes much time!
    let r = pairing_circuit::<F, C, D>(builder, sipp_statement.final_A, sipp_statement.final_B);
    Fq12Target::connect(builder, &r, &sipp_statement.final_Z);

    BLSTarget {
        m_before_cofactor_muls,
        public_keys,
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
    let m_before_cofactor_muls = (0..n - 1)
        .map(|_| map_to_g2_without_cofactor_mul(Fq2::rand(&mut rng)))
        .collect::<Vec<_>>();
    let messages: Vec<G2Affine> = m_before_cofactor_muls
        .iter()
        .map(|m| m.mul_by_cofactor_to_group().into())
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
    let mut a = public_keys.clone();
    let mut b = messages.clone();
    a.push(-G1Affine::generator());
    b.push(aggregated_signature);

    assert_eq!(inner_product(&a, &b), Fq12::one());
    let sipp_proof = sipp_prove_native(&a, &b);

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
        .m_before_cofactor_muls
        .iter()
        .zip_eq(m_before_cofactor_muls.iter())
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

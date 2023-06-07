use ark_bn254::{Fq12, Fr, G1Affine, G2Affine};
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

use crate::{
    transcript_circuit::TranscriptCircuit,
    transcript_native::Transcript,
    verifier_witness::{Fq12ExpWitness, G1ExpWitness, G2ExpWitness},
};

pub struct G1ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    pub p: G1Target<F, D>,
    pub p_x: G1Target<F, D>,
    pub x: FrTarget<F, D>,
}

pub struct G2ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    pub p: G2Target<F, D>,
    pub p_x: G2Target<F, D>,
    pub x: FrTarget<F, D>,
}

pub struct Fq12ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    pub p: Fq12Target<F, D>,
    pub p_x: Fq12Target<F, D>,
    pub x: FrTarget<F, D>,
}

#[allow(non_snake_case)]
pub struct VerifyCircuitOutputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub A: G1Target<F, D>,
    pub B: G2Target<F, D>,
    pub Z: Fq12Target<F, D>,
    pub g1exp: Vec<G1ExpStatement<F, D>>,
    pub g2exp: Vec<G2ExpStatement<F, D>>,
    pub fq12exp: Vec<Fq12ExpStatement<F, D>>,
}

#[allow(non_snake_case)]
pub fn verifier_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    A_t: &[G1Target<F, D>],
    B_t: &[G2Target<F, D>],
    proof_t: &[Fq12Target<F, D>],
) -> VerifyCircuitOutputTarget<F, D> {
    let mut g1exp_t: Vec<G1ExpStatement<F, D>> = vec![];
    let mut g2exp_t: Vec<G2ExpStatement<F, D>> = vec![];
    let mut fq12exp_t: Vec<Fq12ExpStatement<F, D>> = vec![];

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

            let x_a2_t = G1Target::new(builder);
            g1exp_t.push(G1ExpStatement {
                p: a2_t,
                x: x_t.clone(),
                p_x: x_a2_t.clone(),
            });
            new_A_t.push(a1_t.add(builder, &x_a2_t));

            let inv_x_b2_t = G2Target::new(builder);
            g2exp_t.push(G2ExpStatement {
                p: b2_t,
                x: inv_x_t.clone(),
                p_x: inv_x_b2_t.clone(),
            });
            new_B_t.push(b1_t.add(builder, &inv_x_b2_t));
        }

        let Z_L_x_t = Fq12Target::new(builder);
        fq12exp_t.push(Fq12ExpStatement {
            p: Z_L_t,
            x: x_t,
            p_x: Z_L_x_t.clone(),
        });

        let Z_R_inv_x_t = Fq12Target::new(builder);
        fq12exp_t.push(Fq12ExpStatement {
            p: Z_R_t,
            x: inv_x_t,
            p_x: Z_R_inv_x_t.clone(),
        });

        let new_Z_t = Z_L_x_t.mul(builder, &Z_t).mul(builder, &Z_R_inv_x_t);

        // update
        A_t = new_A_t;
        B_t = new_B_t;
        Z_t = new_Z_t;
        n = n / 2;
    }

    VerifyCircuitOutputTarget {
        A: A_t[0].clone(),
        B: B_t[0].clone(),
        Z: Z_t,
        g1exp: g1exp_t,
        g2exp: g2exp_t,
        fq12exp: fq12exp_t,
    }
}

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
        let n = 1 << 2;
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
        let t = verifier_circuit(&mut builder, &A_t, &B_t, &proof_t);
        println!("num of G1ExpStatement: {}", t.g1exp.len());
        println!("num of G2ExpStatement: {}", t.g2exp.len());
        println!("num of Fq12ExpStatement: {}", t.fq12exp.len());

        // let pw = PartialWitness::new();
        // let data = builder.build::<C>();
        // let _proof = data.prove(pw);
        // dbg!(data.common.degree_bits());
    }
}

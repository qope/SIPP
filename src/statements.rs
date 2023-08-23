#![allow(non_snake_case)]
use ark_bn254::{Fq12, Fq2, G1Affine, G2Affine};
use itertools::Itertools;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::target::Target,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bn254::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, native::MyFq12},
};
use starky_bn254::utils::u32_digits_to_biguint;

pub struct SIPPStatementTarget<F: RichField + Extendable<D>, const D: usize> {
    pub A: Vec<G1Target<F, D>>,
    pub B: Vec<G2Target<F, D>>,
    pub Z: Fq12Target<F, D>,
    pub final_A: G1Target<F, D>,
    pub final_B: G2Target<F, D>,
    pub final_Z: Fq12Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SIPPStatementTarget<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        let mut result = vec![];
        let a_vec = self.A.iter().flat_map(|g1| g1.to_vec()).collect_vec();
        result.extend(a_vec);
        let b_vec = self.B.iter().flat_map(|g2| g2.to_vec()).collect_vec();
        result.extend(b_vec);
        let z_vec = self.Z.to_vec();
        result.extend(&z_vec);
        let final_a_vec = self.final_A.to_vec();
        result.extend(final_a_vec);
        let final_b_vec = self.final_B.to_vec();
        result.extend(final_b_vec);
        let final_z_vec = self.final_Z.to_vec();
        result.extend(final_z_vec);
        result
    }
    pub fn from_vec(builder: &mut CircuitBuilder<F, D>, n: usize, input: &[Target]) -> Self {
        let num_limbs = 8;
        let g1_len = num_limbs * 2;
        let g2_len = num_limbs * 4;
        let fq12_len = num_limbs * 12;
        let total_len = g1_len * n + g2_len * n + fq12_len + g1_len + g2_len + fq12_len;
        assert!(input.len() == total_len);
        let mut input = input.to_vec();
        let a_vec_raw = input.drain(0..g1_len * n).collect_vec();
        let b_vec_raw = input.drain(0..g2_len * n).collect_vec();
        let z_raw = input.drain(0..fq12_len).collect_vec();
        let final_a_raw = input.drain(0..g1_len).collect_vec();
        let final_b_raw = input.drain(0..g2_len).collect_vec();
        let final_z_raw = input.drain(0..fq12_len).collect_vec();
        assert!(input.len() == 0);

        let A = a_vec_raw
            .chunks(g1_len)
            .map(|chunk| G1Target::from_vec(builder, chunk))
            .collect_vec();
        let B = b_vec_raw
            .chunks(g2_len)
            .map(|chunk| G2Target::from_vec(builder, chunk))
            .collect_vec();
        let Z = Fq12Target::from_vec(builder, &z_raw);
        let final_A = G1Target::from_vec(builder, &final_a_raw);
        let final_B = G2Target::from_vec(builder, &final_b_raw);
        let final_Z = Fq12Target::from_vec(builder, &final_z_raw);

        Self {
            A,
            B,
            Z,
            final_A,
            final_B,
            final_Z,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SIPPStatement {
    pub A: Vec<G1Affine>,
    pub B: Vec<G2Affine>,
    pub Z: Fq12,
    pub final_A: G1Affine,
    pub final_B: G2Affine,
    pub final_Z: Fq12,
}

fn u32_array_to_g1(input: &[u32]) -> G1Affine {
    let num_limbs = 8;
    assert!(input.len() == num_limbs * 2);
    let mut input = input.to_vec();
    let x = input.drain(0..num_limbs).collect_vec();
    let y = input.drain(0..num_limbs).collect_vec();
    G1Affine::new(
        u32_digits_to_biguint(&x).into(),
        u32_digits_to_biguint(&y).into(),
    )
}

fn u32_array_to_g2(input: &[u32]) -> G2Affine {
    let num_limbs = 8;
    assert!(input.len() == num_limbs * 4);
    let mut input = input.to_vec();
    let x_c0 = input.drain(0..num_limbs).collect_vec();
    let x_c1 = input.drain(0..num_limbs).collect_vec();
    let y_c0 = input.drain(0..num_limbs).collect_vec();
    let y_c1 = input.drain(0..num_limbs).collect_vec();
    let x = Fq2::new(
        u32_digits_to_biguint(&x_c0).into(),
        u32_digits_to_biguint(&x_c1).into(),
    );
    let y = Fq2::new(
        u32_digits_to_biguint(&y_c0).into(),
        u32_digits_to_biguint(&y_c1).into(),
    );
    G2Affine::new(x, y)
}

fn u32_array_to_fq12(input: &[u32]) -> Fq12 {
    let num_limbs = 8;
    assert!(input.len() == num_limbs * 12);
    let coeffs = input
        .chunks(num_limbs)
        .map(|chunk| u32_digits_to_biguint(chunk).into())
        .collect_vec()
        .try_into()
        .unwrap();
    MyFq12 { coeffs }.into()
}

impl SIPPStatement {
    pub fn from_vec(n: usize, input: &[u32]) -> Self {
        let num_limbs = 8;
        let g1_len = num_limbs * 2;
        let g2_len = num_limbs * 4;
        let fq12_len = num_limbs * 12;
        let total_len = g1_len * n + g2_len * n + fq12_len + g1_len + g2_len + fq12_len;
        assert!(input.len() == total_len);
        let mut input = input.to_vec();
        let a_vec_raw = input.drain(0..g1_len * n).collect_vec();
        let b_vec_raw = input.drain(0..g2_len * n).collect_vec();
        let z_raw = input.drain(0..fq12_len).collect_vec();
        let final_a_raw = input.drain(0..g1_len).collect_vec();
        let final_b_raw = input.drain(0..g2_len).collect_vec();
        let final_z_raw = input.drain(0..fq12_len).collect_vec();
        assert!(input.len() == 0);
        let A = a_vec_raw
            .chunks(g1_len)
            .map(|chunk| u32_array_to_g1(chunk))
            .collect_vec();
        let B = b_vec_raw
            .chunks(g2_len)
            .map(|chunk| u32_array_to_g2(chunk))
            .collect_vec();
        let Z = u32_array_to_fq12(&z_raw);
        let final_A = u32_array_to_g1(&final_a_raw);
        let final_B = u32_array_to_g2(&final_b_raw);
        let final_Z = u32_array_to_fq12(&final_z_raw);
        SIPPStatement {
            A,
            B,
            Z,
            final_A,
            final_B,
            final_Z,
        }
    }
}

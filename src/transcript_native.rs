use ark_bn254::{Fq, Fq12, Fr, G1Affine, G2Affine};
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::types::PrimeField,
    hash::{
        hash_types::{HashOut, RichField},
        hashing::hash_n_to_hash_no_pad,
        poseidon::PoseidonPermutation,
    },
};
use plonky2_bn254_pairing::fields::bn254base::Bn254Base;

pub struct Transcript<F: RichField> {
    state: HashOut<F>,
}

impl<F: RichField> Transcript<F> {
    pub fn new() -> Self {
        Transcript {
            state: HashOut::default(),
        }
    }

    pub fn append(&mut self, message: &[F]) {
        let old_state = self.state;
        self.state = hash_n_to_hash_no_pad::<F, PoseidonPermutation>(
            &[old_state.elements.to_vec(), message.to_vec()].concat(),
        );
    }

    pub fn append_fq12(&mut self, x: Fq12) {
        let fq_vec = vec![
            x.c0.c0.c0, x.c0.c0.c1, x.c0.c1.c0, x.c0.c1.c1, x.c0.c2.c0, x.c0.c2.c1, x.c1.c0.c0,
            x.c1.c0.c1, x.c1.c1.c0, x.c1.c1.c1, x.c1.c2.c0, x.c1.c2.c1,
        ];
        let f_vec = fq_vec
            .iter()
            .flat_map(|&x| from_fq_to_f::<F>(x))
            .collect_vec();
        self.append(&f_vec);
    }

    pub fn append_g1(&mut self, x: G1Affine) {
        let x_f = from_fq_to_f::<F>(x.x);
        let y_f = from_fq_to_f::<F>(x.y);
        self.append(&[x_f, y_f].concat());
    }

    pub fn append_g2(&mut self, x: G2Affine) {
        let x0_f = from_fq_to_f(x.x.c0);
        let x1_f = from_fq_to_f(x.x.c1);
        let y0_f = from_fq_to_f(x.y.c0);
        let y1_f = from_fq_to_f(x.y.c1);
        self.append(&[x0_f, x1_f, y0_f, y1_f].concat());
    }

    pub fn get_challenge(&self) -> Fr {
        let digest = hash_n_to_hash_no_pad::<F, PoseidonPermutation>(&self.state.elements);
        let u32_vec = digest
            .elements
            .iter()
            .flat_map(|&x| x.to_canonical_biguint().to_u32_digits())
            .collect_vec();
        let b = BigUint::from_slice(&u32_vec);
        b.into()
    }
}

fn from_fq_to_f<F: RichField>(x: Fq) -> Vec<F> {
    let x: Bn254Base = x.into();
    let b = x.to_canonical_biguint();
    let f_vec = b
        .to_u32_digits()
        .iter()
        .map(|&x| F::from_canonical_u32(x))
        .collect_vec();
    f_vec
}

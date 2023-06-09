use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bn254_pairing::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, fq_target::FqTarget, fr_target::FrTarget},
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

use crate::verifier_witness::{Fq12ExpWitness, G1ExpWitness, G2ExpWitness};

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

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, G1ExpStatement<F, D>, G1ExpWitness> for G1ExpStatement<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        self.p
            .to_vec()
            .iter()
            .chain(self.p_x.to_vec().iter())
            .chain(self.x.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> G1ExpStatement<F, D> {
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_g1_limbs = 2 * num_limbs;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let p_raw = input.drain(0..num_g1_limbs).collect_vec();
        let p_x_raw = input.drain(0..num_g1_limbs).collect_vec();
        let x_raw = input.drain(0..num_fr_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let p = G1Target::from_vec(builder, &p_raw);
        let p_x = G1Target::from_vec(builder, &p_x_raw);
        let x = FrTarget::from_vec(builder, &x_raw);
        G1ExpStatement { p, p_x, x }
    }
    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G1ExpWitness) {
        self.p.set_witness(pw, &value.p);
        self.p_x.set_witness(pw, &value.p_x);
        self.x.set_witness(pw, &value.x);
    }
}

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, G2ExpStatement<F, D>, G2ExpWitness> for G2ExpStatement<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        self.p
            .to_vec()
            .iter()
            .chain(self.p_x.to_vec().iter())
            .chain(self.x.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> G2ExpStatement<F, D> {
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_g2_limbs = 4 * num_limbs;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let p_raw = input.drain(0..num_g2_limbs).collect_vec();
        let p_x_raw = input.drain(0..num_g2_limbs).collect_vec();
        let x_raw = input.drain(0..num_fr_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let p = G2Target::from_vec(builder, &p_raw);
        let p_x = G2Target::from_vec(builder, &p_x_raw);
        let x = FrTarget::from_vec(builder, &x_raw);
        G2ExpStatement { p, p_x, x }
    }
    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G2ExpWitness) {
        self.p.set_witness(pw, &value.p);
        self.p_x.set_witness(pw, &value.p_x);
        self.x.set_witness(pw, &value.x);
    }
}

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, Fq12ExpStatement<F, D>, Fq12ExpWitness>
    for Fq12ExpStatement<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        self.p
            .to_vec()
            .iter()
            .chain(self.p_x.to_vec().iter())
            .chain(self.x.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Fq12ExpStatement<F, D> {
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_fq12_limbs = 12 * num_limbs;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let p_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let p_x_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let x_raw = input.drain(0..num_fr_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let p = Fq12Target::from_vec(builder, &p_raw);
        let p_x = Fq12Target::from_vec(builder, &p_x_raw);
        let x = FrTarget::from_vec(builder, &x_raw);
        Fq12ExpStatement { p, p_x, x }
    }
    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpWitness) {
        self.p.set_witness(pw, &value.p);
        self.p_x.set_witness(pw, &value.p_x);
        self.x.set_witness(pw, &value.x);
    }
}

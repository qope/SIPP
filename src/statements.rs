use itertools::Itertools;
use plonky2::{field::extension::Extendable, hash::hash_types::RichField, iop::target::Target};
use plonky2_bn254::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::fq12_target::Fq12Target,
};
use starky_bn254::input_target::{Fq12ExpInputTarget, G1ExpInputTarget, G2ExpInputTarget};

#[allow(non_snake_case)]
pub struct SIPPStatementTarget<F: RichField + Extendable<D>, const D: usize> {
    pub A: Vec<G1Target<F, D>>,
    pub B: Vec<G2Target<F, D>>,
    pub final_A: G1Target<F, D>,
    pub final_B: G2Target<F, D>,
    pub Z: Fq12Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SIPPStatementTarget<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        let mut result = vec![];
        let a_vec = self.A.iter().flat_map(|g1| g1.to_vec()).collect_vec();
        result.extend(a_vec);
        let b_vec = self.B.iter().flat_map(|g2| g2.to_vec()).collect_vec();
        result.extend(b_vec);
        let final_a_vec = self.final_A.to_vec();
        result.extend(final_a_vec);
        let final_b_vec = self.final_B.to_vec();
        result.extend(final_b_vec);
        let z_vec = self.Z.to_vec();
        result.extend(z_vec);
        result
    }
}

#[allow(non_snake_case)]
pub struct SIPPWitnessTarget<F: RichField + Extendable<D>, const D: usize> {
    pub g1exp_inputs: Vec<G1ExpInputTarget<F, D>>,
    pub g1exp_outputs: Vec<G1Target<F, D>>,
    pub g2exp_inputs: Vec<G2ExpInputTarget<F, D>>,
    pub g2exp_outputs: Vec<G2Target<F, D>>,
    pub fq12exp_inputs: Vec<Fq12ExpInputTarget<F, D>>,
    pub fq12exp_outputs: Vec<Fq12Target<F, D>>,
}

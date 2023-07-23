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

pub const G1_EXP_STATEMENT_LEN: usize = 7 * 8;
pub const G2_EXP_STATEMENT_LEN: usize = 13 * 8;
pub const FQ12_EXP_STATEMENT_LEN: usize = 12 * 8 * 3 + 8;

pub struct G1ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    pub x: G1Target<F, D>,
    pub offset: G1Target<F, D>,
    pub exp_val: FrTarget<F, D>,
    pub output: G1Target<F, D>,
}

pub struct G2ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    pub x: G2Target<F, D>,
    pub offset: G2Target<F, D>,
    pub exp_val: FrTarget<F, D>,
    pub output: G2Target<F, D>,
}

pub struct Fq12ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq12Target<F, D>,
    pub offset: Fq12Target<F, D>,
    pub exp_val: FrTarget<F, D>,
    pub output: Fq12Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpStatement<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G1Target::connect(builder, &lhs.x, &rhs.x);
        G1Target::connect(builder, &lhs.offset, &rhs.offset);
        FrTarget::connect(builder, &lhs.exp_val, &rhs.exp_val);
        G1Target::connect(builder, &lhs.output, &rhs.output);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G2ExpStatement<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G2Target::connect(builder, &lhs.x, &rhs.x);
        G2Target::connect(builder, &lhs.offset, &rhs.offset);
        FrTarget::connect(builder, &lhs.exp_val, &rhs.exp_val);
        G2Target::connect(builder, &lhs.output, &rhs.output);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpStatement<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        Fq12Target::connect(builder, &lhs.x, &rhs.x);
        Fq12Target::connect(builder, &lhs.offset, &rhs.offset);
        FrTarget::connect(builder, &lhs.exp_val, &rhs.exp_val);
        Fq12Target::connect(builder, &lhs.output, &rhs.output);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpStatement<F, D> {
    // 7*8
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .chain(self.output.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> G1ExpStatement<F, D> {
        assert!(input.len() == G1_EXP_STATEMENT_LEN);
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_g1_limbs = 2 * num_limbs;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g1_limbs).collect_vec();
        let offset_raw = input.drain(0..num_g1_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_fr_limbs).collect_vec();
        let output_raw = input.drain(0..num_g1_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = G1Target::from_vec(builder, &x_raw);
        let offset = G1Target::from_vec(builder, &offset_raw);
        let exp_val = FrTarget::from_vec(builder, &exp_val_raw);
        let output = G1Target::from_vec(builder, &output_raw);
        G1ExpStatement {
            x,
            offset,
            exp_val,
            output,
        }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G1ExpWitness) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
        self.output.set_witness(pw, &value.output);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G2ExpStatement<F, D> {
    //13*8=104
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .chain(self.output.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> G2ExpStatement<F, D> {
        assert!(input.len() == G2_EXP_STATEMENT_LEN);
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_g2_limbs = 4 * num_limbs;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g2_limbs).collect_vec();
        let offset_raw = input.drain(0..num_g2_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_fr_limbs).collect_vec();
        let output_raw = input.drain(0..num_g2_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = G2Target::from_vec(builder, &x_raw);
        let offset = G2Target::from_vec(builder, &offset_raw);
        let exp_val = FrTarget::from_vec(builder, &exp_val_raw);
        let output = G2Target::from_vec(builder, &output_raw);
        G2ExpStatement {
            x,
            offset,
            exp_val,
            output,
        }
    }
    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G2ExpWitness) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
        self.output.set_witness(pw, &value.output);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpStatement<F, D> {
    //12*8*3+8=296
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .chain(self.output.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> Fq12ExpStatement<F, D> {
        assert!(input.len() == FQ12_EXP_STATEMENT_LEN);
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_fq12_limbs = 12 * num_limbs;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let offset_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_fr_limbs).collect_vec();
        let output_raw = input.drain(0..num_fq12_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = Fq12Target::from_vec(builder, &x_raw);
        let offset = Fq12Target::from_vec(builder, &offset_raw);
        let exp_val = FrTarget::from_vec(builder, &exp_val_raw);
        let output = Fq12Target::from_vec(builder, &output_raw);
        Fq12ExpStatement {
            x,
            offset,
            exp_val,
            output,
        }
    }
    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpWitness) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
        self.output.set_witness(pw, &value.output);
    }
}

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
    pub g1exp: Vec<G1ExpStatement<F, D>>,
    pub g2exp: Vec<G2ExpStatement<F, D>>,
    pub fq12exp: Vec<Fq12ExpStatement<F, D>>,
}

// #[allow(non_snake_case)]
// fn from_vec(
//     builder: &mut CircuitBuilder<F, D>,
//     input: &[Target],
// ) -> VerifierCircuitPublicInputs<F, D> {
//     let n = 1 << LOG_N;
//     let num_limbs = 8;
//     let num_g1_limbs = 2 * num_limbs;
//     let num_g2_limbs = 4 * num_limbs;
//     let num_fq12_limbs = 12 * num_limbs;

//     let num_a_limbs = n * num_g1_limbs;
//     let num_b_limbs = n * num_g2_limbs;
//     let num_final_a_limbs = num_g1_limbs;
//     let num_final_b_limbs = num_g2_limbs;
//     let num_z_limbs = num_fq12_limbs;
//     let num_g1exp_limbs = (n - 1) * G1_EXP_STATEMENT_LEN;
//     let num_g2exp_limbs = (n - 1) * G2_EXP_STATEMENT_LEN;
//     let num_fq12exp_limbs = 2 * LOG_N * FQ12_EXP_STATEMENT_LEN;

//     let mut input = input.to_vec();
//     let a_raw = input.drain(0..num_a_limbs).collect_vec();
//     let b_raw = input.drain(0..num_b_limbs).collect_vec();
//     let final_a_raw = input.drain(0..num_final_a_limbs).collect_vec();
//     let final_b_raw = input.drain(0..num_final_b_limbs).collect_vec();
//     let z_raw = input.drain(0..num_z_limbs).collect_vec();
//     let g1exp_raw = input.drain(0..num_g1exp_limbs).collect_vec();
//     let g2exp_raw = input.drain(0..num_g2exp_limbs).collect_vec();
//     let fq12exp_raw = input.drain(0..num_fq12exp_limbs).collect_vec();

//     assert_eq!(input.len(), 0);

//     let A = a_raw
//         .chunks_exact(num_g1_limbs)
//         .map(|x| G1Target::from_vec(builder, x))
//         .collect_vec();
//     let B = b_raw
//         .chunks_exact(num_g2_limbs)
//         .map(|x| G2Target::from_vec(builder, x))
//         .collect_vec();
//     let final_A = G1Target::from_vec(builder, &final_a_raw);
//     let final_B = G2Target::from_vec(builder, &final_b_raw);
//     let Z = Fq12Target::from_vec(builder, &z_raw);
//     let g1exp = g1exp_raw
//         .chunks_exact(G1_EXP_STATEMENT_LEN)
//         .map(|x| G1ExpStatement::from_vec(builder, x))
//         .collect_vec();
//     let g2exp = g2exp_raw
//         .chunks_exact(G2_EXP_STATEMENT_LEN)
//         .map(|x| G2ExpStatement::from_vec(builder, x))
//         .collect_vec();
//     let fq12exp = fq12exp_raw
//         .chunks_exact(FQ12_EXP_STATEMENT_LEN)
//         .map(|x| Fq12ExpStatement::from_vec(builder, x))
//         .collect_vec();

//     VerifierCircuitPublicInputs {
//         A,
//         B,
//         final_A,
//         final_B,
//         Z,
//         g1exp,
//         g2exp,
//         fq12exp,
//     }
// }

// fn set_witness(&self, pw: &mut PartialWitness<F>, value: &VerifierCircuitWitness) {
//     self.A.iter().zip(value.A.iter()).for_each(|(a, a_w)| {
//         a.set_witness(pw, a_w);
//     });
//     self.B.iter().zip(value.B.iter()).for_each(|(b, b_w)| {
//         b.set_witness(pw, b_w);
//     });
//     self.final_A.set_witness(pw, &value.final_A);
//     self.final_B.set_witness(pw, &value.final_B);
//     self.Z.set_witness(pw, &value.Z);
//     self.proof
//         .iter()
//         .zip(value.proof.iter())
//         .for_each(|(p, p_w)| {
//             p.set_witness(pw, p_w);
//         });
//     self.g1exp
//         .iter()
//         .zip(value.g1exp.iter())
//         .for_each(|(g1exp, g1exp_w)| {
//             g1exp.set_witness(pw, g1exp_w);
//         });
//     self.g2exp
//         .iter()
//         .zip(value.g2exp.iter())
//         .for_each(|(g2exp, g2exp_w)| {
//             g2exp.set_witness(pw, g2exp_w);
//         });
//     self.fq12exp
//         .iter()
//         .zip(value.fq12exp.iter())
//         .for_each(|(fq12exp, fq12exp_w)| {
//             fq12exp.set_witness(pw, fq12exp_w);
//         });
// }
// }

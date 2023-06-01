use std::marker::PhantomData;

use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    hash::{
        hash_types::{HashOutTarget, RichField},
        poseidon::PoseidonHash,
    },
    iop::target::Target,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bn254_pairing::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{bn254scalar::Bn254Scalar, fq12_target::Fq12Target, fr_target::FrTarget},
};
use plonky2_ecdsa::gadgets::{biguint::BigUintTarget, nonnative::CircuitBuilderNonNative};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;

pub struct TranscriptCircuit<F: RichField + Extendable<D>, const D: usize> {
    state: HashOutTarget,
    _maker: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> TranscriptCircuit<F, D> {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let state = HashOutTarget::from_vec(vec![builder.zero(); 4]);
        Self {
            state,
            _maker: PhantomData,
        }
    }

    pub fn append(&mut self, builder: &mut CircuitBuilder<F, D>, message: &[Target]) {
        let old_state = self.state;
        self.state = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            [old_state.elements.to_vec(), message.to_vec()].concat(),
        );
    }

    pub fn append_fq12(&mut self, builder: &mut CircuitBuilder<F, D>, x: Fq12Target<F, D>) {
        let f_vec: Vec<Target> = x
            .coeffs
            .iter()
            .cloned()
            .flat_map(|x| x.target().value.limbs)
            .map(|x| x.0)
            .collect_vec();
        self.append(builder, &f_vec);
    }

    pub fn append_g1(&mut self, builder: &mut CircuitBuilder<F, D>, p: G1Target<F, D>) {
        let f_vec =
            p.x.limbs()
                .iter()
                .chain(p.y.limbs().iter())
                .cloned()
                .map(|x| x.0)
                .collect_vec();
        self.append(builder, &f_vec);
    }

    pub fn append_g2(&mut self, builder: &mut CircuitBuilder<F, D>, p: G2Target<F, D>) {
        let f_vec = p.x.coeffs[0]
            .limbs()
            .iter()
            .chain(p.x.coeffs[1].limbs().iter())
            .chain(p.y.coeffs[0].limbs().iter())
            .chain(p.y.coeffs[1].limbs().iter())
            .cloned()
            .map(|x| x.0)
            .collect_vec();
        self.append(builder, &f_vec);
    }

    pub fn get_challenge(&self, builder: &mut CircuitBuilder<F, D>) -> FrTarget<F, D> {
        let digest = builder.hash_n_to_hash_no_pad::<PoseidonHash>(self.state.elements.to_vec());
        let limbs = digest
            .elements
            .iter()
            .cloned()
            .flat_map(|x| {
                let (low, high) = builder.split_low_high(x, 32, 64);
                vec![low, high]
            })
            .map(|x| U32Target(x))
            .collect_vec();
        let bui_t = BigUintTarget { limbs };
        let fr_nonnative = builder.reduce::<Bn254Scalar>(&bui_t);
        FrTarget::construct(fr_nonnative)
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use ark_bn254::{Fq12, G1Affine, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{Field, PrimeField},
        },
        hash::{
            hashing::hash_n_to_hash_no_pad,
            poseidon::{PoseidonHash, PoseidonPermutation},
        },
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254_pairing::{
        curves::{g1curve_target::G1Target, g2curve_target::G2Target},
        fields::{fq12_target::Fq12Target, fr_target::FrTarget},
    };

    use crate::transcript_native::Transcript;

    use super::TranscriptCircuit;

    type F = GoldilocksField;
    const D: usize = 2;

    #[test]
    fn test_split_hashout_target() {
        let z = hash_n_to_hash_no_pad::<F, PoseidonPermutation>(&[F::ONE]);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let z_t = builder.constant_hash(z);

        let a_t = z_t
            .elements
            .iter()
            .cloned()
            .flat_map(|x| {
                let (low, high) = builder.split_low_high(x, 32, 64);
                vec![low, high]
            })
            .collect_vec();

        let a = z
            .elements
            .iter()
            .flat_map(|&x| x.to_canonical_biguint().to_u32_digits())
            .collect_vec();

        let mut pw = PartialWitness::new();
        for i in 0..a.len() {
            pw.set_target(a_t[i], F::from_canonical_u32(a[i]));
        }
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_get_challenge() {
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let zero_t = builder.zero();
        let zero_hash_t = builder.hash_n_to_hash_no_pad::<PoseidonHash>(vec![zero_t]);
        let transcript_c: TranscriptCircuit<F, D> = TranscriptCircuit {
            state: zero_hash_t,
            _maker: PhantomData,
        };
        let c_t = transcript_c.get_challenge(&mut builder);

        let zero_hash = hash_n_to_hash_no_pad::<F, PoseidonPermutation>(&vec![F::ZERO]);
        let transcript = Transcript { state: zero_hash };
        let c = transcript.get_challenge();

        let c_expected_t = FrTarget::constant(&mut builder, c);

        FrTarget::connect(&mut builder, &c_t, &c_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_transcript_circuit() {
        let rng = &mut ark_std::test_rng();
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut transcript_c = TranscriptCircuit::new(&mut builder);
        let a_fq12 = Fq12::rand(rng);
        let b_g1 = G1Affine::rand(rng);
        let c_g2 = G2Affine::rand(rng);

        let a_fq12_t = Fq12Target::constant(&mut builder, a_fq12);
        let b_g1_t = G1Target::constant(&mut builder, b_g1);
        let c_g2_t = G2Target::constant(&mut builder, c_g2);

        transcript_c.append_fq12(&mut builder, a_fq12_t);
        transcript_c.append_g1(&mut builder, b_g1_t);
        transcript_c.append_g2(&mut builder, c_g2_t);

        let r_t = transcript_c.get_challenge(&mut builder);

        let mut transcript = Transcript::<F>::new();
        transcript.append_fq12(a_fq12);
        transcript.append_g1(b_g1);
        transcript.append_g2(c_g2);

        let r_expected = transcript.get_challenge();

        let r_expected_t = FrTarget::constant(&mut builder, r_expected);

        FrTarget::connect(&mut builder, &r_expected_t, &r_t);

        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let _proof = data.prove(pw);
    }
}

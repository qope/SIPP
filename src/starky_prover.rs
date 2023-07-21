use crate::{
    statements::{Fq12ExpStatement, G1ExpStatement, G2ExpStatement},
    verifier_witness::{Fq12ExpWitness, G1ExpWitness, G2ExpWitness},
};
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField, types::Field},
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::PoseidonGoldilocksConfig,
        proof::ProofWithPublicInputs,
    },
    util::timing::TimingTree,
};
use plonky2_bn254_pairing::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{
        bn254base::Bn254Base, bn254scalar::Bn254Scalar, fq12_target::Fq12Target,
        fq2_target::Fq2Target, fq_target::FqTarget, fr_target::FrTarget,
    },
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};
use plonky2_ecdsa::gadgets::{biguint::BigUintTarget, nonnative::CircuitBuilderNonNative};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use starky::{
    config::StarkConfig,
    proof::StarkProofWithPublicInputsTarget,
    prover::prove,
    recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    },
    stark::Stark,
    verifier::verify_stark_proof,
};
use starky_bn254::g1_exp::{read_g1_exp_io, G1ExpIONative, G1ExpStark};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

const G1_DEGREE_BITS: usize = 16;
const G2_DEGREE_BITS: usize = 16;
const FQ12_DEGREE_BITS: usize = 13;

const NUM_G1_IO: usize = 1 << 7;
const NUM_G2_IO: usize = 1 << 7;
const NUM_FQ12_IO: usize = 1 << 4;

// pub fn columns_to_biguint(
//     builder: &mut CircuitBuilder<F, D>,
//     column: [Target; N_LIMBS],
// ) -> BigUintTarget {
//     column
//         .iter()
//         .for_each(|&x| builder.range_check(x, LIMB_BITS));
//     let base = builder.constant(F::from_canonical_u64(1 << LIMB_BITS));
//     let mut limbs = vec![];
//     for i in 0..N_LIMBS / 2 {
//         let z = builder.mul_add(column[2 * i + 1], base, column[2 * i]);
//         limbs.push(U32Target(z));
//     }
//     BigUintTarget { limbs }
// }

// pub fn columns_to_fq(
//     builder: &mut CircuitBuilder<F, D>,
//     column: [Target; N_LIMBS],
// ) -> FqTarget<F, D> {
//     let x = columns_to_biguint(builder, column);
//     let nonnative = builder.biguint_to_nonnative::<Bn254Base>(&x);
//     FqTarget::construct(nonnative)
// }

// pub fn columns_to_fq2(
//     builder: &mut CircuitBuilder<F, D>,
//     column: [[Target; N_LIMBS]; 2],
// ) -> Fq2Target<F, D> {
//     let coeffs = column.map(|c| columns_to_fq(builder, c));
//     Fq2Target::construct(coeffs.to_vec())
// }

// pub fn columns_to_fq12(
//     builder: &mut CircuitBuilder<F, D>,
//     column: Vec<[Target; N_LIMBS]>,
// ) -> Fq12Target<F, D> {
//     assert!(column.len() == 12);
//     let coeffs = column
//         .iter()
//         .map(|&c| columns_to_fq(builder, c))
//         .collect_vec();
//     Fq12Target::construct(coeffs.to_vec())
// }

pub fn u32_limbs_to_fq<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    limbs: [Target; 8],
) -> FqTarget<F, D> {
    let x = limbs.map(|x| U32Target(x));
    let b = BigUintTarget { limbs: x.to_vec() };
    let n = builder.biguint_to_nonnative::<Bn254Base>(&b);
    FqTarget::construct(n)
}
pub fn u32_limbs_to_fr<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    limbs: [Target; 8],
) -> FrTarget<F, D> {
    let x = limbs.map(|x| U32Target(x));
    let b = BigUintTarget { limbs: x.to_vec() };
    let n = builder.biguint_to_nonnative::<Bn254Scalar>(&b);
    FrTarget::construct(n)
}

pub fn build_g1_exp_circuit() -> (CircuitData<F, C, D>, StarkProofWithPublicInputsTarget<D>) {
    type S = G1ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = G1ExpStark::<F, D>::new();
    let circuit_config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
    let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, G1_DEGREE_BITS);
    let pi: [_; S::PUBLIC_INPUTS] = pt.public_inputs.clone().try_into().unwrap();

    let mut cur_col = 0;
    let ios = (0..NUM_G1_IO)
        .map(|_| {
            let io = read_g1_exp_io(&pi, &mut cur_col);
            let x_x = u32_limbs_to_fq(&mut builder, io.x[0]);
            let x_y = u32_limbs_to_fq(&mut builder, io.x[1]);
            let x = G1Target::construct(x_x, x_y);
            let offset_x = u32_limbs_to_fq(&mut builder, io.offset[0]);
            let offset_y = u32_limbs_to_fq(&mut builder, io.offset[1]);
            let offset = G1Target::construct(offset_x, offset_y);
            let exp_val = u32_limbs_to_fr(&mut builder, io.exp_val);
            let output_x = u32_limbs_to_fq(&mut builder, io.output[0]);
            let output_y = u32_limbs_to_fq(&mut builder, io.output[1]);
            let output = G1Target::construct(output_x, output_y);
            G1ExpStatement {
                x,
                offset,
                exp_val,
                output,
            }
        })
        .collect_vec();
    verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
    builder.register_public_inputs(&pi);
    let data = builder.build::<C>();
    (data, pt)
}

pub fn generate_g1_exp_proof(
    ws: &[G1ExpWitness],
    inner_data: &CircuitData<F, C, D>,
    starky_proof_t: &StarkProofWithPublicInputsTarget<D>,
) -> ProofWithPublicInputs<F, C, D> {
    assert!(ws.len() == NUM_G1_IO);
    type S = G1ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = G1ExpStark::<F, D>::new();
    let inputs = ws
        .iter()
        .map(|w| {
            let exp_val_biguint: BigUint = w.exp_val.into();
            let mut exp_val_limbs = exp_val_biguint.to_u32_digits();
            exp_val_limbs.extend(vec![0; 8 - exp_val_limbs.len()]);
            G1ExpIONative {
                x: w.x,
                offset: w.offset,
                exp_val: exp_val_limbs.try_into().unwrap(),
                output: w.output,
            }
        })
        .collect_vec();
    let trace = stark.generate_trace(&inputs);
    let pi = stark.generate_public_inputs(&inputs);
    let stark_proof = prove::<F, C, S, D>(
        stark,
        &inner_config,
        trace,
        pi.try_into().unwrap(),
        &mut TimingTree::default(),
    )
    .unwrap();
    verify_stark_proof::<F, C, S, D>(stark, stark_proof.clone(), &inner_config).unwrap();

    let mut pw = PartialWitness::new();
    set_stark_proof_with_pis_target(&mut pw, starky_proof_t, &stark_proof);

    let proof = inner_data.prove(pw).unwrap();
    proof
}

// pub fn build_g2_exp_circuit() -> (
//     CircuitData<F, C, D>,
//     G2ExpStatement<F, D>,
//     StarkProofWithPublicInputsTarget<D>,
// ) {
//     type S = G2ExpStark<F, D>;
//     let inner_config = StarkConfig::standard_fast_config();
//     let stark = G2ExpStark::<F, D>::new();
//     let circuit_config = CircuitConfig::standard_ecc_config();
//     let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
//     let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, DEGREE_BITS);
//     let pi: [_; 12 * N_LIMBS + BITS_LEN] = pt.public_inputs.clone().try_into().unwrap();

//     let mut cur_col = 0;
//     let x = read_fq2(&pi, &mut cur_col);
//     let y = read_fq2(&pi, &mut cur_col);
//     let offset_x = read_fq2(&pi, &mut cur_col);
//     let offset_y = read_fq2(&pi, &mut cur_col);
//     let x_exp_x = read_fq2(&pi, &mut cur_col);
//     let x_exp_y = read_fq2(&pi, &mut cur_col);
//     let exp_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);

//     let x = columns_to_fq2(&mut builder, x);
//     let y = columns_to_fq2(&mut builder, y);
//     let offset_x = columns_to_fq2(&mut builder, offset_x);
//     let offset_y = columns_to_fq2(&mut builder, offset_y);
//     let x_exp_x = columns_to_fq2(&mut builder, x_exp_x);
//     let x_exp_y = columns_to_fq2(&mut builder, x_exp_y);

//     let p = G2Target::construct(x, y);
//     let offset = G2Target::construct(offset_x, offset_y);
//     let p_x_offset = G2Target::construct(x_exp_x, x_exp_y);
//     let x = bits_to_fr(&mut builder, exp_bits);
//     let neg_offset = offset.neg(&mut builder);
//     let p_x = p_x_offset.add(&mut builder, &neg_offset);
//     let target = G2ExpStatement { p, p_x, x };
//     verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
//     builder.register_public_inputs(&target.to_vec());
//     let data = builder.build::<C>();
//     (data, target, pt)
// }

// pub fn generate_g2_exp_proof(
//     w: &G2ExpWitness,
//     inner_data: &CircuitData<F, C, D>,
//     starky_proof_t: &StarkProofWithPublicInputsTarget<D>,
// ) -> ProofWithPublicInputs<F, C, D> {
//     type S = G2ExpStark<F, D>;
//     let mut rng = rand::thread_rng();
//     let offset = G2Affine::rand(&mut rng);
//     let exp_bits: [bool; BITS_LEN] = biguint_to_bits(&w.x.into(), BITS_LEN).try_into().unwrap();
//     let inner_config = StarkConfig::standard_fast_config();
//     let stark = G2ExpStark::<F, D>::new();
//     let x_exp: G2Affine = (offset + w.p_x).into();
//     let trace = stark.generate_trace(w.p, offset, x_exp, exp_bits);
//     let pi = S::generate_public_inputs(w.p, x_exp, offset, exp_bits);
//     let stark_proof = prove::<F, C, S, D>(
//         stark,
//         &inner_config,
//         trace,
//         pi.try_into().unwrap(),
//         &mut TimingTree::default(),
//     )
//     .unwrap();

//     let mut pw = PartialWitness::new();
//     set_stark_proof_with_pis_target(&mut pw, starky_proof_t, &stark_proof);

//     let proof = inner_data.prove(pw).unwrap();
//     proof
// }

// pub fn build_fq12_exp_circuit() -> (
//     CircuitData<F, C, D>,
//     Fq12ExpStatement<F, D>,
//     StarkProofWithPublicInputsTarget<D>,
// ) {
//     type S = Fq12ExpStark<F, D>;
//     let inner_config = StarkConfig::standard_fast_config();
//     let stark = Fq12ExpStark::<F, D>::new();
//     let circuit_config = CircuitConfig::standard_ecc_config();
//     let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
//     let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, DEGREE_BITS);
//     let pi: [_; 24 * N_LIMBS + BITS_LEN] = pt.public_inputs.clone().try_into().unwrap();

//     let mut cur_col = 0;
//     let p = read_fq12(&pi, &mut cur_col);
//     let p_exp = read_fq12(&pi, &mut cur_col);
//     let exp_bits: [_; BITS_LEN] = read_instruction(&pi, &mut cur_col);

//     let p = columns_to_fq12(&mut builder, p);
//     let p_x = columns_to_fq12(&mut builder, p_exp);
//     let x = bits_to_fr(&mut builder, exp_bits);

//     let target = Fq12ExpStatement { p, p_x, x };
//     verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
//     builder.register_public_inputs(&target.to_vec());
//     let data = builder.build::<C>();
//     (data, target, pt)
// }

// pub fn generate_fq12_exp_proof(
//     w: &Fq12ExpWitness,
//     inner_data: &CircuitData<F, C, D>,
//     starky_proof_t: &StarkProofWithPublicInputsTarget<D>,
// ) -> ProofWithPublicInputs<F, C, D> {
//     type S = Fq12ExpStark<F, D>;
//     let exp_bits: [bool; BITS_LEN] = biguint_to_bits(&w.x.into(), BITS_LEN).try_into().unwrap();
//     let inner_config = StarkConfig::standard_fast_config();
//     let stark = Fq12ExpStark::<F, D>::new();
//     let trace = stark.generate_trace(w.p, w.p_x, exp_bits);
//     let pi = S::generate_public_inputs(w.p, w.p_x, exp_bits);
//     let stark_proof = prove::<F, C, S, D>(
//         stark,
//         &inner_config,
//         trace,
//         pi.try_into().unwrap(),
//         &mut TimingTree::default(),
//     )
//     .unwrap();

//     let mut pw = PartialWitness::new();
//     set_stark_proof_with_pis_target(&mut pw, starky_proof_t, &stark_proof);

//     let proof = inner_data.prove(pw).unwrap();
//     proof
// }

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        starky_prover::{build_g1_exp_circuit, generate_g1_exp_proof, NUM_G1_IO},
        statements::{Fq12ExpStatement, G1ExpStatement, G2ExpStatement},
        verifier_witness::{Fq12ExpWitness, G1ExpWitness, G2ExpWitness},
    };
    use ark_bn254::{Fq12, Fr, G1Affine, G2Affine};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254_pairing::traits::recursive_circuit_target::RecursiveCircuitTarget;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_g1_exp() {
        let (inner_data, proof_t) = build_g1_exp_circuit();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut rng = rand::thread_rng();
        let ws = (0..NUM_G1_IO)
            .map(|_| {
                let x = G1Affine::rand(&mut rng);
                let offset = G1Affine::rand(&mut rng);
                let exp_val = Fr::rand(&mut rng);
                let output: G1Affine = (offset + x * exp_val).into();
                G1ExpWitness {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        let now = Instant::now();
        let proof = generate_g1_exp_proof(&ws, &inner_data, &proof_t);
        println!("proof generation took {} s", now.elapsed().as_secs());

        let verifier_target = builder.constant_verifier_data::<C>(&inner_data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        let statements = proof_t
            .public_inputs
            .chunks(56)
            .into_iter()
            .map(|chunk| G1ExpStatement::from_vec(&mut builder, chunk))
            .collect_vec();
        builder.verify_proof::<C>(&proof_t, &verifier_target, &inner_data.common);

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_t, &proof);
        statements.iter().zip(ws.iter()).for_each(|(t, w)| {
            t.x.set_witness(&mut pw, &w.x);
            t.offset.set_witness(&mut pw, &w.offset);
            t.exp_val.set_witness(&mut pw, &w.exp_val);
            t.output.set_witness(&mut pw, &w.output);
        });

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    // #[test]
    // fn test_g2_exp() {
    //     let (inner_data, _g2exp_t, proof_t) = build_g2_exp_circuit();

    //     let config = CircuitConfig::standard_ecc_config();
    //     let mut builder = CircuitBuilder::<F, D>::new(config);

    //     let mut rng = rand::thread_rng();
    //     let p = G2Affine::rand(&mut rng);
    //     let x = Fr::rand(&mut rng);
    //     let p_x: G2Affine = (p * x).into();
    //     let now = Instant::now();
    //     let proof = generate_g2_exp_proof(&G2ExpWitness { p, x, p_x }, &inner_data, &proof_t);
    //     println!("proof generation took {} s", now.elapsed().as_secs());

    //     let verifier_target = builder.constant_verifier_data::<C>(&inner_data.verifier_only);
    //     let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
    //     let pi = G2ExpStatement::from_vec(&mut builder, &proof_t.public_inputs);
    //     builder.verify_proof::<C>(&proof_t, &verifier_target, &inner_data.common);

    //     let mut pw = PartialWitness::new();
    //     pw.set_proof_with_pis_target(&proof_t, &proof);
    //     pi.p.set_witness(&mut pw, &p);
    //     pi.p_x.set_witness(&mut pw, &p_x);
    //     pi.x.set_witness(&mut pw, &x);

    //     let data = builder.build::<C>();
    //     let _proof = data.prove(pw).unwrap();
    // }

    // #[test]
    // fn test_fq12_exp() {
    //     let (inner_data, _fq12exp_t, proof_t) = build_fq12_exp_circuit();

    //     let config = CircuitConfig::standard_ecc_config();
    //     let mut builder = CircuitBuilder::<F, D>::new(config);

    //     let mut rng = rand::thread_rng();
    //     let p = Fq12::rand(&mut rng);
    //     let x = Fr::rand(&mut rng);
    //     let x_biguint: BigUint = x.into();
    //     let p_x: Fq12 = p.pow(&x_biguint.to_u64_digits());
    //     let now = Instant::now();
    //     let proof = generate_fq12_exp_proof(&Fq12ExpWitness { p, x, p_x }, &inner_data, &proof_t);
    //     println!("proof generation took {} s", now.elapsed().as_secs());

    //     let verifier_target = builder.constant_verifier_data::<C>(&inner_data.verifier_only);
    //     let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
    //     let pi = Fq12ExpStatement::from_vec(&mut builder, &proof_t.public_inputs);
    //     builder.verify_proof::<C>(&proof_t, &verifier_target, &inner_data.common);

    //     let mut pw = PartialWitness::new();
    //     pw.set_proof_with_pis_target(&proof_t, &proof);
    //     pi.p.set_witness(&mut pw, &p);
    //     pi.p_x.set_witness(&mut pw, &p_x);
    //     pi.x.set_witness(&mut pw, &x);

    //     let data = builder.build::<C>();
    //     let _proof = data.prove(pw).unwrap();
    // }
}

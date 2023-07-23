use crate::verifier_witness::{Fq12ExpWitness, G1ExpWitness, G2ExpWitness};
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::goldilocks_field::GoldilocksField,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::PoseidonGoldilocksConfig,
        proof::ProofWithPublicInputs,
    },
    util::timing::TimingTree,
};
use starky::{
    config::StarkConfig,
    proof::StarkProofWithPublicInputsTarget,
    prover::prove,
    recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    },
    verifier::verify_stark_proof,
};
use starky_bn254::{
    fq12_exp::{Fq12ExpIONative, Fq12ExpStark},
    g1_exp::{G1ExpIONative, G1ExpStark},
    g2_exp::{G2ExpIONative, G2ExpStark},
};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

const G1_DEGREE_BITS: usize = 16;
const G2_DEGREE_BITS: usize = 16;
const FQ12_DEGREE_BITS: usize = 13;

const NUM_G1_IO: usize = 1 << 7;
const NUM_G2_IO: usize = 1 << 7;
const NUM_FQ12_IO: usize = 1 << 4;

pub fn build_g1_exp_circuit() -> (CircuitData<F, C, D>, StarkProofWithPublicInputsTarget<D>) {
    type S = G1ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = G1ExpStark::<F, D>::new();
    let circuit_config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
    let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, G1_DEGREE_BITS);
    verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
    builder.register_public_inputs(&pt.public_inputs);
    let data = builder.build::<C>();
    (data, pt)
}

pub fn generate_g1_exp_proof(
    ws: &[G1ExpWitness],
    inner_data: &CircuitData<F, C, D>,
    starky_proof_t: &StarkProofWithPublicInputsTarget<D>,
) -> ProofWithPublicInputs<F, C, D> {
    assert!(ws.len() <= NUM_G1_IO);
    let to_padd = vec![*ws.last().unwrap(); NUM_G1_IO - ws.len()];
    let ws = ws.into_iter().chain(to_padd.iter()).collect_vec();
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

pub fn build_g2_exp_circuit() -> (CircuitData<F, C, D>, StarkProofWithPublicInputsTarget<D>) {
    type S = G2ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = G2ExpStark::<F, D>::new();
    let circuit_config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
    let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, G2_DEGREE_BITS);
    verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
    builder.register_public_inputs(&pt.public_inputs);
    let data = builder.build::<C>();
    (data, pt)
}

pub fn generate_g2_exp_proof(
    ws: &[G2ExpWitness],
    inner_data: &CircuitData<F, C, D>,
    starky_proof_t: &StarkProofWithPublicInputsTarget<D>,
) -> ProofWithPublicInputs<F, C, D> {
    assert!(ws.len() <= NUM_G2_IO);
    let to_padd = vec![*ws.last().unwrap(); NUM_G2_IO - ws.len()];
    let ws = ws.into_iter().chain(to_padd.iter()).collect_vec();
    type S = G2ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = G2ExpStark::<F, D>::new();
    let inputs = ws
        .iter()
        .map(|w| {
            let exp_val_biguint: BigUint = w.exp_val.into();
            let mut exp_val_limbs = exp_val_biguint.to_u32_digits();
            exp_val_limbs.extend(vec![0; 8 - exp_val_limbs.len()]);
            G2ExpIONative {
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

pub fn build_fq12_exp_circuit() -> (CircuitData<F, C, D>, StarkProofWithPublicInputsTarget<D>) {
    type S = Fq12ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = Fq12ExpStark::<F, D>::new();
    let circuit_config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
    let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, FQ12_DEGREE_BITS);
    verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
    builder.register_public_inputs(&pt.public_inputs);
    let data = builder.build::<C>();
    (data, pt)
}

pub fn generate_fq12_exp_proof(
    ws: &[Fq12ExpWitness],
    inner_data: &CircuitData<F, C, D>,
    starky_proof_t: &StarkProofWithPublicInputsTarget<D>,
) -> ProofWithPublicInputs<F, C, D> {
    assert!(ws.len() <= NUM_FQ12_IO);
    let to_padd = vec![*ws.last().unwrap(); NUM_FQ12_IO - ws.len()];
    let ws = ws.into_iter().chain(to_padd.iter()).collect_vec();
    type S = Fq12ExpStark<F, D>;
    let inner_config = StarkConfig::standard_fast_config();
    let stark = Fq12ExpStark::<F, D>::new();
    let inputs = ws
        .iter()
        .map(|w| {
            let exp_val_biguint: BigUint = w.exp_val.into();
            let mut exp_val_limbs = exp_val_biguint.to_u32_digits();
            exp_val_limbs.extend(vec![0; 8 - exp_val_limbs.len()]);
            Fq12ExpIONative {
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

pub struct StarkyCircuits {
    pub g1_exp_data: CircuitData<F, C, D>,
    pub g2_exp_data: CircuitData<F, C, D>,
    pub fq12_exp_data: CircuitData<F, C, D>,
    pub g1_exp_starky_proof: StarkProofWithPublicInputsTarget<D>,
    pub g2_exp_starky_proof: StarkProofWithPublicInputsTarget<D>,
    pub fq12_exp_starky_proof: StarkProofWithPublicInputsTarget<D>,
}

pub fn build_starky_circuits() -> StarkyCircuits {
    let (g1_exp_data, g1_exp_starky_proof) = build_g1_exp_circuit();
    let (g2_exp_data, g2_exp_starky_proof) = build_g2_exp_circuit();
    let (fq12_exp_data, fq12_exp_starky_proof) = build_fq12_exp_circuit();
    StarkyCircuits {
        g1_exp_data,
        g2_exp_data,
        fq12_exp_data,
        g1_exp_starky_proof,
        g2_exp_starky_proof,
        fq12_exp_starky_proof,
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        starky_prover::{
            build_fq12_exp_circuit, build_g1_exp_circuit, build_g2_exp_circuit,
            generate_fq12_exp_proof, generate_g1_exp_proof, generate_g2_exp_proof, NUM_FQ12_IO,
            NUM_G1_IO, NUM_G2_IO,
        },
        statements::{
            Fq12ExpStatement, G1ExpStatement, G2ExpStatement, FQ12_EXP_STATEMENT_LEN,
            G1_EXP_STATEMENT_LEN, G2_EXP_STATEMENT_LEN,
        },
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
            .chunks(G1_EXP_STATEMENT_LEN)
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

    #[test]
    fn test_g2_exp() {
        let (inner_data, proof_t) = build_g2_exp_circuit();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut rng = rand::thread_rng();
        let ws = (0..NUM_G2_IO)
            .map(|_| {
                let x = G2Affine::rand(&mut rng);
                let offset = G2Affine::rand(&mut rng);
                let exp_val = Fr::rand(&mut rng);
                let output: G2Affine = (offset + x * exp_val).into();
                G2ExpWitness {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        let now = Instant::now();
        let proof = generate_g2_exp_proof(&ws, &inner_data, &proof_t);
        println!("proof generation took {} s", now.elapsed().as_secs());

        let verifier_target = builder.constant_verifier_data::<C>(&inner_data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        let statements = proof_t
            .public_inputs
            .chunks(G2_EXP_STATEMENT_LEN)
            .into_iter()
            .map(|chunk| G2ExpStatement::from_vec(&mut builder, chunk))
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

    #[test]
    fn test_fq12_exp() {
        let (inner_data, proof_t) = build_fq12_exp_circuit();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut rng = rand::thread_rng();
        let ws = (0..NUM_FQ12_IO)
            .map(|_| {
                let x = Fq12::rand(&mut rng);
                let offset = Fq12::rand(&mut rng);
                let exp_val = Fr::rand(&mut rng);
                let exp_val_biguint: BigUint = exp_val.into();
                let output: Fq12 = offset * x.pow(exp_val_biguint.to_u64_digits());
                Fq12ExpWitness {
                    x,
                    offset,
                    exp_val,
                    output,
                }
            })
            .collect_vec();

        let now = Instant::now();
        let proof = generate_fq12_exp_proof(&ws, &inner_data, &proof_t);
        println!("proof generation took {} s", now.elapsed().as_secs());

        let verifier_target = builder.constant_verifier_data::<C>(&inner_data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        let statements = proof_t
            .public_inputs
            .chunks(FQ12_EXP_STATEMENT_LEN)
            .into_iter()
            .map(|chunk| Fq12ExpStatement::from_vec(&mut builder, chunk))
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
}

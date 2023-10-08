use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
};
use plonky2_bn254::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, u256_target::U256Target},
};
use starky_bn254::{
    curves::{
        g1::circuit::{g1_exp_circuit, G1ExpInputTarget},
        g2::circuit::{g2_exp_circuit, G2ExpInputTarget},
    },
    fields::fq12::circuit::{fq12_exp_circuit, Fq12ExpInputTarget},
};

use crate::{statements::SIPPStatementTarget, transcript_circuit::TranscriptCircuit};

#[allow(non_snake_case)]
pub fn sipp_verifier_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    A_t: &[G1Target<F, D>],
    B_t: &[G2Target<F, D>],
    proof_t: &[Fq12Target<F, D>],
) -> SIPPStatementTarget<F, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    assert!(A_t.len() == B_t.len());
    let l = A_t.len();
    assert!(l.is_power_of_two() && l >= 128);

    let mut g1exp_inputs_t: Vec<G1ExpInputTarget<F, D>> = vec![];
    let mut g1exp_output_t: Vec<G1Target<F, D>> = vec![];
    let mut g2exp_inputs_t: Vec<G2ExpInputTarget<F, D>> = vec![];
    let mut g2exp_output_t: Vec<G2Target<F, D>> = vec![];
    let mut fq12exp_inputs_t: Vec<Fq12ExpInputTarget<F, D>> = vec![];
    let mut fq12exp_output_t: Vec<Fq12Target<F, D>> = vec![];

    let original_A = A_t.to_vec();
    let original_B = B_t.to_vec();

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
    let original_Z = proof_t.pop().unwrap();
    let mut Z_t = original_Z.clone();
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

            let a1_x_a2_t = G1Target::empty(builder);
            g1exp_inputs_t.push(G1ExpInputTarget {
                x: a2_t,
                offset: a1_t,
                exp_val: U256Target::new(x_t.to_vec().try_into().unwrap()),
            });
            g1exp_output_t.push(a1_x_a2_t.clone());
            new_A_t.push(a1_x_a2_t);

            let b1_inv_x_b2_t: G2Target<F, D> = G2Target::empty(builder);
            g2exp_inputs_t.push(G2ExpInputTarget {
                x: b2_t,
                offset: b1_t,
                exp_val: U256Target::new(inv_x_t.to_vec().try_into().unwrap()),
            });
            g2exp_output_t.push(b1_inv_x_b2_t.clone());
            new_B_t.push(b1_inv_x_b2_t);
        }

        let Z_Z_L_x_t = Fq12Target::empty(builder);
        fq12exp_inputs_t.push(Fq12ExpInputTarget {
            x: Z_L_t,
            offset: Z_t,
            exp_val: U256Target::new(x_t.to_vec().try_into().unwrap()),
        });
        fq12exp_output_t.push(Z_Z_L_x_t.clone());

        let new_Z_t = Fq12Target::empty(builder);
        fq12exp_inputs_t.push(Fq12ExpInputTarget {
            x: Z_R_t,
            offset: Z_Z_L_x_t,
            exp_val: U256Target::new(inv_x_t.to_vec().try_into().unwrap()),
        });
        fq12exp_output_t.push(new_Z_t.clone());

        // update
        A_t = new_A_t;
        B_t = new_B_t;
        Z_t = new_Z_t;
        n = n / 2;
    }

    let contr_g1exp_outputs_t = g1_exp_circuit::<F, C, D>(builder, &g1exp_inputs_t);
    let contr_g2exp_outputs_t = g2_exp_circuit::<F, C, D>(builder, &g2exp_inputs_t);
    let contr_fq12exp_outputs_t = fq12_exp_circuit::<F, C, D>(builder, &fq12exp_inputs_t);
    g1exp_output_t
        .iter()
        .zip(contr_g1exp_outputs_t.iter())
        .for_each(|(a, b)| G1Target::connect(builder, a, b));
    g2exp_output_t
        .iter()
        .zip(contr_g2exp_outputs_t.iter())
        .for_each(|(a, b)| G2Target::connect(builder, a, b));
    fq12exp_output_t
        .iter()
        .zip(contr_fq12exp_outputs_t.iter())
        .for_each(|(a, b)| Fq12Target::connect(builder, a, b));

    SIPPStatementTarget {
        A: original_A,
        B: original_B,
        Z: original_Z,
        final_A: A_t[0].clone(),
        final_B: B_t[0].clone(),
        final_Z: Z_t,
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::{
        prover_native::{inner_product, sipp_prove_native},
        statements::SIPPStatement,
        verifier_circuit::sipp_verifier_circuit,
        verifier_native::sipp_verify_native,
    };

    use ark_bn254::{Fq2, Fr, G1Affine, G2Affine, G2Projective};
    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_traits::{PrimInt, Zero};
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::PrimeField64},
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254::{
        curves::{
            g1curve_target::G1Target, g2curve_target::G2Target,
            map_to_g2::map_to_g2_without_cofactor_mul,
        },
        fields::fq12_target::Fq12Target,
    };
    use plonky2_bn254_pairing::pairing::pairing;

    #[test]
    #[allow(non_snake_case)]
    fn test_sipp_circuit() {
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;

        let log_n = 8;
        let n = 1 << log_n;
        println!("Aggregating {} pairings into 1", n);
        let mut rng = rand::thread_rng();
        let A = (0..n).map(|_| G1Affine::rand(&mut rng)).collect_vec();
        let B = (0..n).map(|_| G2Affine::rand(&mut rng)).collect_vec();
        let sipp_proof = sipp_prove_native(&A, &B);
        let sipp_statement = sipp_verify_native(&A, &B, &sipp_proof).unwrap();
        assert_eq!(inner_product(&A, &B), sipp_statement.Z);
        assert_eq!(
            pairing(sipp_statement.final_A, sipp_statement.final_B),
            sipp_statement.final_Z
        );

        println!("Start: cirucit build");
        let now = Instant::now();
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::new(config.clone());
        let A_t = (0..n).map(|_| G1Target::empty(&mut builder)).collect_vec();
        let B_t = (0..n).map(|_| G2Target::empty(&mut builder)).collect_vec();
        let sipp_proof_t = (0..2 * log_n + 1)
            .map(|_| Fq12Target::empty(&mut builder))
            .collect_vec();
        let sipp_statement_t =
            sipp_verifier_circuit::<F, C, D>(&mut builder, &A_t, &B_t, &sipp_proof_t);
        builder.register_public_inputs(&sipp_statement_t.to_vec());
        let data = builder.build::<C>();
        println!("End: circuit build. took {:?}", now.elapsed());

        println!("Start: proof generation");
        let now = Instant::now();
        let mut pw = PartialWitness::new();
        A_t.iter()
            .zip(A.iter())
            .for_each(|(a_t, a)| a_t.set_witness(&mut pw, a));
        B_t.iter()
            .zip(B.iter())
            .for_each(|(b_t, b)| b_t.set_witness(&mut pw, b));
        sipp_proof_t
            .iter()
            .zip(sipp_proof.iter())
            .for_each(|(p_t, p)| p_t.set_witness(&mut pw, p));

        // The witness asignments below are not mandatory, just for assertion.
        sipp_statement_t.Z.set_witness(&mut pw, &sipp_statement.Z);
        sipp_statement_t
            .final_A
            .set_witness(&mut pw, &sipp_statement.final_A);
        sipp_statement_t
            .final_B
            .set_witness(&mut pw, &sipp_statement.final_B);
        sipp_statement_t
            .final_Z
            .set_witness(&mut pw, &sipp_statement.final_Z);
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();
        println!("End: proof generation. took {:?}", now.elapsed());

        // assertion of public inputs
        let pi_u32 = proof
            .public_inputs
            .into_iter()
            .map(|x| {
                let x = x.to_canonical_u64();
                assert!(x < 1 << 32);
                x as u32
            })
            .collect_vec();
        let recovered_sipp_statement = SIPPStatement::from_vec(n, &pi_u32);
        assert_eq!(sipp_statement, recovered_sipp_statement);
    }
}

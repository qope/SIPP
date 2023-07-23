use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitData,
        config::{AlgebraicHasher, GenericConfig},
        proof::ProofWithPublicInputsTarget,
    },
};

pub fn add_recursive_constraint<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inner_data: &CircuitData<F, C, D>,
) -> ProofWithPublicInputsTarget<D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let vt = builder.constant_verifier_data(&inner_data.verifier_only);
    let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
    builder.verify_proof::<C>(&proof_t, &vt, &inner_data.common);
    proof_t
}

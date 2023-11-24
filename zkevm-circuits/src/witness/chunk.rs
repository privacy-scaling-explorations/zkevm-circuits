use super::{rw::ToVec, ExecStep, Rw, RwMap, Transaction};
use crate::{
    evm_circuit::{detect_fixed_table_tags, EvmCircuit},
    exp_circuit::param::OFFSET_INCREMENT,
    instance::public_data_convert,
    table::BlockContextFieldTag,
    util::{log2_ceil, unwrap_value, word, SubCircuit},
};
use bus_mapping::{
    circuit_input_builder::{self, ChunkContext, CopyEvent, ExpEvent, FixedCParams},
    state_db::CodeDB,
    Error,
};
use eth_types::{Address, Field, ToScalar, Word};
use gadgets::permutation::get_permutation_fingerprints;
use halo2_proofs::circuit::Value;
use crate::witness::Block;

// TODO: Remove fields that are duplicated in`eth_block`
/// Block is the struct used by all circuits, which contains all the needed
/// data for witness generation.
#[derive(Debug, Clone, Default)]
pub struct Chunck<F>{
    /// BeginChunk step to propagate State
    pub begin_chunk: ExecStep,
    /// EndChunk step that appears in the last EVM row for all the chunks other than the last.
    pub end_chunk: Option<ExecStep>,
    /// chunk context
    pub chunk_context: ChunkContext,
    /// permutation challenge alpha
    pub permu_alpha: F,
    /// permutation challenge gamma
    pub permu_gamma: F,
    /// pre rw_table permutation fingerprint
    pub permu_rwtable_prev_continuous_fingerprint: F,
    /// next rw_table permutation fingerprint
    pub permu_rwtable_next_continuous_fingerprint: F,
    /// pre chronological rw_table permutation fingerprint
    pub permu_chronological_rwtable_prev_continuous_fingerprint: F,
    /// next chronological rw_table permutation fingerprint
    pub permu_chronological_rwtable_next_continuous_fingerprint: F,
    /// prev_chunk_last_call
    pub prev_block: Box<Option<Block<F>>>,
}

/// Convert a chunk struct in bus-mapping to a witness chunk used in circuits
pub fn chunk_convert<F: Field>(
    builder: &circuit_input_builder::CircuitInputBuilder<FixedCParams>,
) -> Result<Chunck<F>, Error> {
    let block = &builder.block;
    let code_db = &builder.code_db;
    let rws = RwMap::from(&block.container);
    let chunck_ctx = builder
        .chunk_ctx
        .clone()
        .unwrap_or_else(ChunkContext::new_one_chunk);
    let mut chunck = Chunck {
        permu_alpha: F::from(103),
        permu_gamma: F::from(101),
        permu_rwtable_prev_continuous_fingerprint: F::from(1),
        permu_rwtable_next_continuous_fingerprint: F::from(1),
        permu_chronological_rwtable_prev_continuous_fingerprint: F::from(1),
        permu_chronological_rwtable_next_continuous_fingerprint: F::from(1),
        begin_chunk: builder.cur_chunk().chunk_steps.begin_chunk.clone(),
        end_chunk: builder.cur_chunk().chunk_steps.end_chunk.clone(),
        chunk_context: chunck_ctx,
        prev_block: Box::new(None),
    };

    // Permutation fingerprints
    let (rws_rows, _) = RwMap::table_assignments_padding(
        &rws.table_assignments(false),
        builder.circuits_params.max_rws,
        chunck_ctx.is_first_chunk(),
    );
    let (chronological_rws_rows, _) = RwMap::table_assignments_padding(
        &rws.table_assignments(true),
        builder.circuits_params.max_rws,
        chunck_ctx.is_first_chunk(),
    );
    chunck.permu_rwtable_next_continuous_fingerprint = unwrap_value(
        get_permutation_fingerprints(
            &<dyn ToVec<Value<F>>>::to2dvec(&rws_rows),
            Value::known(chunck.permu_alpha),
            Value::known(chunck.permu_gamma),
            Value::known(chunck.permu_rwtable_prev_continuous_fingerprint),
        )
        .last()
        .cloned()
        .unwrap()
        .0,
    );
    chunck.permu_chronological_rwtable_next_continuous_fingerprint = unwrap_value(
        get_permutation_fingerprints(
            &<dyn ToVec<Value<F>>>::to2dvec(&chronological_rws_rows),
            Value::known(chunck.permu_alpha),
            Value::known(chunck.permu_gamma),
            Value::known(chunck.permu_chronological_rwtable_prev_continuous_fingerprint),
        )
        .last()
        .cloned()
        .unwrap()
        .0,
    );

    Ok(chunck)
}
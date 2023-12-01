///
use super::{rw::ToVec, ExecStep, RwMap};
use crate::{util::unwrap_value, witness::Block};
use bus_mapping::{
    circuit_input_builder::{self, ChunkContext, FixedCParams},
    Error,
};
use eth_types::{Field, ToScalar};
use gadgets::permutation::get_permutation_fingerprints;
use halo2_proofs::circuit::Value;

// TODO: Remove fields that are duplicated in`eth_block`
/// Block is the struct used by all circuits, which contains all the needed
/// data for witness generation.
#[derive(Debug, Clone, Default)]
pub struct Chunk<F> {
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
    pub rw_prev_fingerprint: F,
    /// next rw_table permutation fingerprint
    pub rw_fingerprint: F,
    /// pre chronological rw_table permutation fingerprint
    pub chrono_rw_prev_fingerprint: F,
    /// next chronological rw_table permutation fingerprint
    pub chrono_rw_fingerprint: F,
    /// prev_chunk_last_call
    pub prev_block: Box<Option<Block<F>>>,
}

/// Convert a chunk struct in bus-mapping to a witness chunk used in circuits
pub fn chunk_convert<F: Field>(
    builder: &circuit_input_builder::CircuitInputBuilder<FixedCParams>,
    idx: usize
) -> Result<Chunk<F>, Error> {
    let block = &builder.block;
    let chunk = builder.get_chunk(idx);
    let _code_db = &builder.code_db;
    let rws = RwMap::from(&block.container);

    // Get prev fingerprint if it exists, otherwise start with 1
    let (rw_prev_fingerprint, chrono_rw_prev_fingerprint) = if chunk.ctx.is_first_chunk() {
        (F::from(1), F::from(1))
    } else {
        let last_chunk = builder.prev_chunk();
        (
            last_chunk.rw_fingerprint.to_scalar().unwrap(),
            last_chunk.chrono_rw_fingerprint.to_scalar().unwrap(),
        )
    };
    // Compute fingerprint of this chunk from rw tables
    let (rws_rows, _) = RwMap::table_assignments_padding(
        &rws.table_assignments(false),
        builder.circuits_params.max_rws,
        chunk.ctx.is_first_chunk(),
    );
    let (chrono_rws_rows, _) = RwMap::table_assignments_padding(
        &rws.table_assignments(true),
        builder.circuits_params.max_rws,
        builder.chunk_ctx.is_first_chunk(),
    );

    // Todo: poseidon hash
    let permu_alpha = F::from(103);
    let permu_gamma = F::from(101);

    let rw_fingerprints = [rw_prev_fingerprint, chrono_rw_prev_fingerprint]
        .iter()
        .zip([rws_rows, chrono_rws_rows].iter())
        .map(|(prev, rows)| {
            unwrap_value(
                get_permutation_fingerprints(
                    &<dyn ToVec<Value<F>>>::to2dvec(rows),
                    Value::known(permu_alpha),
                    Value::known(permu_gamma),
                    Value::known(prev.clone()),
                )
                .last()
                .cloned()
                .unwrap()
                .0,
            )
        })
        .collect::<Vec<F>>();

    // Todo(Cecilia): should set prev data from builder.prev_chunk()
    let chunck = Chunk {
        permu_alpha,
        permu_gamma,
        rw_prev_fingerprint,
        rw_fingerprint: rw_fingerprints[0],
        chrono_rw_prev_fingerprint,
        chrono_rw_fingerprint: rw_fingerprints[1],
        begin_chunk: chunk.begin_chunk.clone(),
        end_chunk: chunk.end_chunk.clone(),
        chunk_context: chunk.ctx.clone(),
        prev_block: Box::new(None),
    };

    Ok(chunck)
}

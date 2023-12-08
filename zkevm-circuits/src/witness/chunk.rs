///
use super::{rw::ToVec, ExecStep, Rw, RwMap};
use crate::{util::unwrap_value, witness::Block};
use bus_mapping::{
    circuit_input_builder::{self, ChunkContext, FixedCParams},
    Error,
};
use eth_types::{Field};
use gadgets::permutation::get_permutation_fingerprints;
use halo2_proofs::circuit::Value;

// TODO: Remove fields that are duplicated in`eth_block`
/// Block is the struct used by all circuits, which contains all the needed
/// data for witness generation.
#[derive(Debug, Clone, Default)]
pub struct Chunk<F> {
    /// BeginChunk step to propagate State
    pub begin_chunk: Option<ExecStep>,
    /// EndChunk step that appears in the last EVM row for all the chunks other than the last.
    pub end_chunk: Option<ExecStep>,
    /// chunk context
    pub chunk_context: ChunkContext,
    /// Read write events in the RwTable
    pub rws: RwMap,
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
    /// fixed param for the chunk
    pub fixed_param: FixedCParams,
    /// prev_chunk_last_call
    pub prev_block: Box<Option<Block<F>>>,
}

/// Convert a chunk struct in bus-mapping to a witness chunk used in circuits
pub fn chunk_convert<F: Field>(
    builder: &circuit_input_builder::CircuitInputBuilder<FixedCParams>,
    idx: usize,
) -> Result<Chunk<F>, Error> {
    let block = &builder.block;
    let chunk = builder.get_chunk(idx);
    let mut rws = RwMap::default();
    println!(
        "| {:?} ... {:?} |",
        chunk.ctx.initial_rwc, chunk.ctx.end_rwc
    );

    // Compute fingerprints of all chunks
    let mut permu_rand = Vec::with_capacity(builder.chunks.len());
    let mut fingerprints = Vec::with_capacity(builder.chunks.len() + 1);
    // Prev chunk before the first chunk
    fingerprints.push(vec![F::from(1), F::from(1)]);

    for (i, chunk) in builder.chunks.iter().enumerate() {
        // Compute fingerprint of this chunk from rw tables
        let cur_rws =
            RwMap::from_chunked(&block.container, chunk.ctx.initial_rwc, chunk.ctx.end_rwc);
        cur_rws.check_value();

        let (rws_rows, _) = RwMap::table_assignments_padding(
            &cur_rws.table_assignments(false),
            chunk.fixed_param.max_rws,
            chunk.ctx.is_first_chunk(),
        );
        let (chrono_rws_rows, _) = RwMap::table_assignments_padding(
            &cur_rws.table_assignments(true),
            chunk.fixed_param.max_rws,
            builder.chunk_ctx.is_first_chunk(),
        );

        if i == idx {
            rws = cur_rws;
        }

        // Todo: poseidon hash
        let alpha = F::from(103);
        let gamma = F::from(101);

        // Comupute cur fingerprints from last fingerprints and current rows
        let cur_fingerprints = fingerprints[i]
            .iter()
            .zip([rws_rows, chrono_rws_rows].iter())
            .map(|(prev, rows)| {
                unwrap_value(
                    get_permutation_fingerprints(
                        &<dyn ToVec<Value<F>>>::to2dvec(rows),
                        Value::known(alpha),
                        Value::known(gamma),
                        Value::known(*prev),
                    )
                    .last()
                    .cloned()
                    .unwrap()
                    .0,
                )
            })
            .collect::<Vec<F>>();

        permu_rand.push(vec![alpha, gamma]);
        fingerprints.push(cur_fingerprints);
    }

    // Todo(Cecilia): should set prev data from builder.prev_chunk()
    let chunck = Chunk {
        permu_alpha: permu_rand[idx][0],
        permu_gamma: permu_rand[idx][1],
        rw_prev_fingerprint: fingerprints[idx][0],
        rw_fingerprint: fingerprints[idx + 1][0],
        chrono_rw_prev_fingerprint: fingerprints[idx][1],
        chrono_rw_fingerprint: fingerprints[idx + 1][1],
        begin_chunk: chunk.begin_chunk.clone(),
        end_chunk: chunk.end_chunk.clone(),
        chunk_context: chunk.ctx.clone(),
        rws,
        fixed_param: chunk.fixed_param,
        prev_block: Box::new(None),
    };

    Ok(chunck)
}

impl<F: Field> Chunk<F> {
    /// Get a read-write record
    pub(crate) fn get_rws(&self, step: &ExecStep, index: usize) -> Rw {
        self.rws[step.rw_index(index)]
    }
}

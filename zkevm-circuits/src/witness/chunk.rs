///
use super::{rw::{ToVec, RwFingerprints}, ExecStep, RwMap, Rw};
use crate::{util::unwrap_value, witness::Block};
use bus_mapping::{
    circuit_input_builder::{self, ChunkContext, FixedCParams},
    Error,
};
use eth_types::Field;
use gadgets::permutation::get_permutation_fingerprints;
use halo2_proofs::circuit::Value;

/// [`Chunk`]` is the struct used by all circuits, which contains chunkwise
/// data for witness generation. Used with [`Block`] for blockwise witness.
#[derive(Debug, Clone, Default)]
pub struct Chunk<F> {
    /// BeginChunk step to propagate State
    pub begin_chunk: Option<ExecStep>,
    /// EndChunk step that appears in the last EVM row for all the chunks other than the last.
    pub end_chunk: Option<ExecStep>,
    /// Chunk context
    pub chunk_context: ChunkContext,
    /// Read write events in the RwTable
    pub rws: RwMap,
    /// Permutation challenge alpha
    pub permu_alpha: F,
    /// Permutation challenge gamma
    pub permu_gamma: F,

    /// Current rw_table permutation fingerprint
    pub rw_fingerprints: RwFingerprints<F>,
    /// Current chronological rw_table permutation fingerprint
    pub chrono_rw_fingerprints: RwFingerprints<F>,

    /// Fixed param for the chunk
    pub fixed_param: FixedCParams,
    /// [`Block`] to store prev_chunk_last_call
    pub prev_block: Box<Option<Block<F>>>,
}

/// Convert the idx-th chunk struct in bus-mapping to a witness chunk used in circuits
pub fn chunk_convert<F: Field>(
    builder: &circuit_input_builder::CircuitInputBuilder<FixedCParams>,
    idx: usize,
) -> Result<Chunk<F>, Error> {
    let block = &builder.block;
    let chunk = builder.get_chunk(idx);
    let rws = RwMap::default();

    // FIXME(Cecilia): debug
    println!(
        "| {:?} ... {:?} |",
        chunk.ctx.initial_rwc, chunk.ctx.end_rwc
    );

    // Compute fingerprints of all chunks
    let mut alpha_gamas = Vec::with_capacity(builder.chunks.len());
    let mut rw_fingerprints: Vec<RwFingerprints<F>> = Vec::with_capacity(builder.chunks.len());
    let mut chrono_rw_fingerprints: Vec<RwFingerprints<F>> = Vec::with_capacity(builder.chunks.len());

    for (i, chunk) in builder.chunks.iter().enumerate() {
        // Get the Rws in the i-th chunk
        let cur_rws =
            RwMap::from_chunked(&block.container, chunk.ctx.initial_rwc, chunk.ctx.end_rwc);
        cur_rws.check_value();

        // Generate the padded rw table assignments
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

        // Todo: poseidon hash
        let alpha = F::from(103);
        let gamma = F::from(101);

        // Comupute cur fingerprints from last fingerprints and current Rw rows
        let cur_fingerprints = get_rwtable_fingerprints(
            alpha, 
            gamma, 
            if i == 0 { F::from(1) } else { rw_fingerprints[i-1].acc_next_fingerprints}, 
            &rws_rows
        );
        let cur_chrono_fingerprints = get_rwtable_fingerprints(
            alpha, 
            gamma, 
            if i == 0 { F::from(1) } else { chrono_rw_fingerprints[i-1].acc_next_fingerprints}, 
            &chrono_rws_rows
        );


        alpha_gamas.push(vec![alpha, gamma]);
        rw_fingerprints.push(cur_fingerprints);
        chrono_rw_fingerprints.push(cur_chrono_fingerprints);
    }

    // TODO(Cecilia): if we chunk across blocks then need to store the prev_block
    let chunck = Chunk {
        permu_alpha: alpha_gamas[idx][0],
        permu_gamma: alpha_gamas[idx][1],
        rw_fingerprints: rw_fingerprints[idx].clone(),
        chrono_rw_fingerprints: chrono_rw_fingerprints[idx].clone(),
        begin_chunk: chunk.begin_chunk.clone(),
        end_chunk: chunk.end_chunk.clone(),
        chunk_context: chunk.ctx.clone(),
        rws,
        fixed_param: chunk.fixed_param,
        prev_block: Box::new(None),
    };

    Ok(chunck)
}


fn get_rwtable_fingerprints<F: Field>(
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
    rows: &Vec<Rw>,
) -> RwFingerprints<F> {
    let x = rows.to2dvec();
    let fingerprints = get_permutation_fingerprints(
        &x,
        Value::known(alpha),
        Value::known(gamma),
        Value::known(prev_continuous_fingerprint),
    );

    fingerprints
        .first()
        .zip(fingerprints.last())
        .map(|((first_acc, first_row), (last_acc, last_row))| {
            RwFingerprints::new(
                unwrap_value(*first_row),
                unwrap_value(*last_row),
                unwrap_value(*first_acc),
                unwrap_value(*last_acc),
            )
        })
        .unwrap_or_default()
}

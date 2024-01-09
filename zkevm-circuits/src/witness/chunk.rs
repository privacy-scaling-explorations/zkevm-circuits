///
use super::{
    rw::{RwFingerprints, ToVec},
    ExecStep, Rw, RwMap, RwRow,
};
use crate::util::unwrap_value;
use bus_mapping::{
    circuit_input_builder::{self, Call, ChunkContext, FixedCParams},
    Error,
};
use eth_types::Field;
use gadgets::permutation::get_permutation_fingerprints;
use halo2_proofs::circuit::Value;

/// [`Chunk`]` is the struct used by all circuits, which contains chunkwise
/// data for witness generation. Used with [`Block`] for blockwise witness.
#[derive(Debug, Clone)]
pub struct Chunk<F> {
    /// BeginChunk step to propagate State
    pub begin_chunk: Option<ExecStep>,
    /// EndChunk step that appears in the last EVM row for all the chunks other than the last.
    pub end_chunk: Option<ExecStep>,
    /// Padding step that is repeated before max_rws is reached
    pub padding: Option<ExecStep>,
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

    /// The last call of previous chunk if any, used for assigning continuation
    pub prev_last_call: Option<Call>,
}

impl<F: Field> Default for Chunk<F> {
    fn default() -> Self {
        // One fixed param chunk with randomness = 1
        // RwFingerprints rw acc starts with 0 and fingerprints = 1
        Self {
            begin_chunk: None,
            end_chunk: None,
            padding: None,
            chunk_context: ChunkContext::default(),
            rws: RwMap::default(),
            permu_alpha: F::from(1),
            permu_gamma: F::from(1),
            rw_fingerprints: RwFingerprints::default(),
            chrono_rw_fingerprints: RwFingerprints::default(),
            fixed_param: FixedCParams::default(),
            prev_last_call: None,
        }
    }
}

impl<F: Field> Chunk<F> {
    pub(crate) fn new_from_rw_map(rws: &RwMap) -> Self {
        let (alpha, gamma) = get_permutation_randomness();
        let mut chunk = Chunk::default();
        let rw_fingerprints = get_permutation_fingerprint_of_rwmap(
            rws,
            chunk.fixed_param.max_rws,
            alpha, // TODO
            gamma,
            F::from(1),
            false,
        );
        let chrono_rw_fingerprints = get_permutation_fingerprint_of_rwmap(
            rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            F::from(1),
            true,
        );
        chunk.rws = rws.clone();
        chunk.rw_fingerprints = rw_fingerprints;
        chunk.chrono_rw_fingerprints = chrono_rw_fingerprints;
        chunk
    }
}

/// Convert the idx-th chunk struct in bus-mapping to a witness chunk used in circuits
pub fn chunk_convert<F: Field>(
    builder: &circuit_input_builder::CircuitInputBuilder<FixedCParams>,
    idx: usize,
) -> Result<Chunk<F>, Error> {
    let block = &builder.block;
    let chunk = builder.get_chunk(idx);
    let mut rws = RwMap::default();

    // FIXME(Cecilia): debug
    println!(
        "| {:?} ... {:?} | @chunk_convert",
        chunk.ctx.initial_rwc, chunk.ctx.end_rwc
    );

    // Compute fingerprints of all chunks
    let mut alpha_gamas = Vec::with_capacity(builder.chunks.len());
    let mut rw_fingerprints: Vec<RwFingerprints<F>> = Vec::with_capacity(builder.chunks.len());
    let mut chrono_rw_fingerprints: Vec<RwFingerprints<F>> =
        Vec::with_capacity(builder.chunks.len());

    for (i, chunk) in builder.chunks.iter().enumerate() {
        // Get the Rws in the i-th chunk
        let cur_rws =
            RwMap::from_chunked(&block.container, chunk.ctx.initial_rwc, chunk.ctx.end_rwc);
        cur_rws.check_value();

        // Todo: poseidon hash
        let alpha = F::from(103);
        let gamma = F::from(101);

        // Comupute cur fingerprints from last fingerprints and current Rw rows
        let cur_fingerprints = get_permutation_fingerprint_of_rwmap(
            &cur_rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            if i == 0 {
                F::from(1)
            } else {
                rw_fingerprints[i - 1].mul_acc
            },
            false,
        );
        let cur_chrono_fingerprints = get_permutation_fingerprint_of_rwmap(
            &cur_rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            if i == 0 {
                F::from(1)
            } else {
                chrono_rw_fingerprints[i - 1].mul_acc
            },
            true,
        );

        alpha_gamas.push(vec![alpha, gamma]);
        rw_fingerprints.push(cur_fingerprints);
        chrono_rw_fingerprints.push(cur_chrono_fingerprints);
        if i == idx {
            rws = cur_rws;
        }
    }

    // TODO(Cecilia): if we chunk across blocks then need to store the prev_block
    let chunck = Chunk {
        permu_alpha: alpha_gamas[idx][0],
        permu_gamma: alpha_gamas[idx][1],
        rw_fingerprints: rw_fingerprints[idx].clone(),
        chrono_rw_fingerprints: chrono_rw_fingerprints[idx].clone(),
        begin_chunk: chunk.begin_chunk.clone(),
        end_chunk: chunk.end_chunk.clone(),
        padding: chunk.padding.clone(),
        chunk_context: chunk.ctx.clone(),
        rws,
        fixed_param: chunk.fixed_param,
        prev_last_call: None,
    };

    Ok(chunck)
}

///
pub fn get_rwtable_fingerprints<F: Field>(
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

///
pub fn get_permutation_fingerprint_of_rwmap<F: Field>(
    rwmap: &RwMap,
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
    is_chrono: bool,
) -> RwFingerprints<F> {
    get_permutation_fingerprint_of_rwvec(
        &rwmap.table_assignments(is_chrono),
        max_row,
        alpha,
        gamma,
        prev_continuous_fingerprint,
    )
}

///
pub fn get_permutation_fingerprint_of_rwvec<F: Field>(
    rwvec: &[Rw],
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
) -> RwFingerprints<F> {
    get_permutation_fingerprint_of_rwrowvec(
        &rwvec
            .iter()
            .map(|row| row.table_assignment())
            .collect::<Vec<RwRow<Value<F>>>>(),
        max_row,
        alpha,
        gamma,
        prev_continuous_fingerprint,
    )
}

///
pub fn get_permutation_fingerprint_of_rwrowvec<F: Field>(
    rwrowvec: &[RwRow<Value<F>>],
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
) -> RwFingerprints<F> {
    let (rows, _) = RwRow::padding(rwrowvec, max_row, true);
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

///
pub fn get_permutation_randomness<F: Field>() -> (F, F) {
    // Todo
    (F::from(1), F::from(1))
}

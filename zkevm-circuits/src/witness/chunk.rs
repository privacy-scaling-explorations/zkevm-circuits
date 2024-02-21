use std::{cmp::min, iter};

///
use super::{
    rw::{RwFingerprints, ToVec},
    Block, ExecStep, Rw, RwMap, RwRow,
};
use crate::util::unwrap_value;
use bus_mapping::{
    circuit_input_builder::{self, Call, ChunkContext, FixedCParams},
    Error,
};
use eth_types::Field;
use gadgets::permutation::get_permutation_fingerprints;
use halo2_proofs::circuit::Value;
use itertools::Itertools;

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
    /// Read write events in the chronological sorted RwTable
    pub chrono_rws: RwMap,
    /// Read write events in the by address sorted RwTable
    pub by_address_rws: RwMap,
    /// Permutation challenge alpha
    pub permu_alpha: F,
    /// Permutation challenge gamma
    pub permu_gamma: F,

    /// Current rw_table permutation fingerprint
    pub by_address_rw_fingerprints: RwFingerprints<F>,
    /// Current chronological rw_table permutation fingerprint
    pub chrono_rw_fingerprints: RwFingerprints<F>,

    /// Fixed param for the chunk
    pub fixed_param: FixedCParams,

    /// The last call of previous chunk if any, used for assigning continuation
    pub prev_last_call: Option<Call>,
    ///
    pub prev_chunk_last_chrono_rw: Option<Rw>,
    ///
    pub prev_chunk_last_by_address_rw: Option<Rw>,
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
            chrono_rws: RwMap::default(),
            by_address_rws: RwMap::default(),
            permu_alpha: F::from(1),
            permu_gamma: F::from(1),
            by_address_rw_fingerprints: RwFingerprints::default(),
            chrono_rw_fingerprints: RwFingerprints::default(),
            fixed_param: FixedCParams::default(),
            prev_last_call: None,
            prev_chunk_last_chrono_rw: None,
            prev_chunk_last_by_address_rw: None,
        }
    }
}

impl<F: Field> Chunk<F> {
    #[cfg(test)]
    pub(crate) fn new_from_rw_map(
        rws: &RwMap,
        padding_start_rw: Option<Rw>,
        chrono_padding_start_rw: Option<Rw>,
    ) -> Self {
        let (alpha, gamma) = get_permutation_randomness();
        let mut chunk = Chunk::default();
        let rw_fingerprints = get_permutation_fingerprint_of_rwmap(
            rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            F::from(1),
            false,
            padding_start_rw,
        );
        let chrono_rw_fingerprints = get_permutation_fingerprint_of_rwmap(
            rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            F::from(1),
            true,
            chrono_padding_start_rw,
        );
        chunk.chrono_rws = rws.clone();
        chunk.by_address_rw_fingerprints = rw_fingerprints;
        chunk.chrono_rw_fingerprints = chrono_rw_fingerprints;
        chunk
    }
}

/// Convert the idx-th chunk struct in bus-mapping to a witness chunk used in circuits
pub fn chunk_convert<F: Field>(
    block: &Block<F>,
    builder: &circuit_input_builder::CircuitInputBuilder<FixedCParams>,
) -> Result<Vec<Chunk<F>>, Error> {
    let (by_address_rws, padding_meta) = (&block.by_address_rws, &block.rw_padding_meta);

    // Todo: poseidon hash to compute alpha/gamma
    let alpha = F::from(103);
    let gamma = F::from(101);

    let mut chunks: Vec<Chunk<F>> = Vec::with_capacity(builder.chunks.len());
    for (i, (prev_chunk, chunk)) in iter::once(None) // left append `None` to make iteration easier
        .chain(builder.chunks.iter().map(Some))
        .tuple_windows()
        .enumerate()
    {
        let chunk = chunk.unwrap(); // current chunk always there
        let (prev_chunk_last_chrono_rw, prev_chunk_last_by_address_rw) = prev_chunk
            .map(|prev_chunk| {
                let prev_chunk_last_chrono_rw = {
                    assert!(builder.circuits_params.max_rws > 0);
                    let chunk_inner_rwc = prev_chunk.ctx.rwc.0;
                    if chunk_inner_rwc.saturating_sub(1) == builder.circuits_params.max_rws {
                        // if prev chunk rws are full, then get the last rwc
                        RwMap::get_rw(&builder.block.container, prev_chunk.ctx.end_rwc - 1)
                            .expect("Rw does not exist")
                    } else {
                        // last is the padding row
                        Rw::Padding {
                            rw_counter: builder.circuits_params.max_rws,
                        }
                    }
                };
                // get prev_chunk last by_address sorted rw
                let prev_chunk_by_address_last_rw = {
                    let by_address_last_rwc_index =
                        (prev_chunk.ctx.idx + 1) * builder.circuits_params.max_rws;
                    let prev_chunk_by_address_last_rwc = by_address_rws
                        .get(by_address_last_rwc_index - 1)
                        .cloned()
                        .or_else(|| {
                            let target_padding_count =
                                (by_address_last_rwc_index + 1) - by_address_rws.len();
                            let mut accu_count = 0;
                            padding_meta
                                .iter()
                                .find(|(_, count)| {
                                    accu_count += **count;
                                    target_padding_count <= accu_count.try_into().unwrap()
                                })
                                .map(|(padding_rwc, _)| Rw::Padding {
                                    rw_counter: *padding_rwc,
                                })
                        });

                    prev_chunk_by_address_last_rwc
                };
                (prev_chunk_last_chrono_rw, prev_chunk_by_address_last_rw)
            })
            .map(|(prev_chunk_last_rwc, prev_chunk_by_address_last_rwc)| {
                (Some(prev_chunk_last_rwc), prev_chunk_by_address_last_rwc)
            })
            .unwrap_or_else(|| (None, None));

        println!(
            "| {:?} ... {:?} | @chunk_convert",
            chunk.ctx.initial_rwc, chunk.ctx.end_rwc
        );

        // Get the rws in the i-th chunk
        let chrono_rws = RwMap::from(&builder.block.container)
            .take_rw_counter_range(chunk.ctx.initial_rwc, chunk.ctx.end_rwc);

        chrono_rws.check_value();

        let by_address_rws = RwMap::from({
            // by_address_rws
            let start = min(
                chunk.ctx.idx * builder.circuits_params.max_rws,
                by_address_rws.len() - 1,
            );
            let end = min(
                (chunk.ctx.idx + 1) * builder.circuits_params.max_rws,
                by_address_rws.len(),
            );
            by_address_rws[start..end].to_vec()
        })
        .take_rw_counter_range(chunk.ctx.initial_rwc, chunk.ctx.end_rwc);

        // Comupute cur fingerprints from last fingerprints and current Rw rows
        let by_address_rw_fingerprints = get_permutation_fingerprint_of_rwmap(
            &by_address_rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            if i == 0 {
                F::from(1)
            } else {
                chunks[i - 1].by_address_rw_fingerprints.mul_acc
            },
            false,
            prev_chunk_last_by_address_rw,
        );

        let chrono_rw_fingerprints = get_permutation_fingerprint_of_rwmap(
            &chrono_rws,
            chunk.fixed_param.max_rws,
            alpha,
            gamma,
            if i == 0 {
                F::from(1)
            } else {
                chunks[i - 1].chrono_rw_fingerprints.mul_acc
            },
            true,
            prev_chunk_last_chrono_rw,
        );

        chunks.push(Chunk {
            permu_alpha: alpha,
            permu_gamma: gamma,
            by_address_rw_fingerprints,
            chrono_rw_fingerprints,
            begin_chunk: chunk.begin_chunk.clone(),
            end_chunk: chunk.end_chunk.clone(),
            padding: chunk.padding.clone(),
            chunk_context: chunk.ctx.clone(),
            chrono_rws,
            by_address_rws,
            fixed_param: chunk.fixed_param,
            prev_last_call: chunk.prev_last_call.clone(),
            prev_chunk_last_chrono_rw,
            prev_chunk_last_by_address_rw,
        });
    }

    Ok(chunks)
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
    padding_start_rw: Option<Rw>,
) -> RwFingerprints<F> {
    get_permutation_fingerprint_of_rwvec(
        &rwmap.table_assignments(is_chrono),
        max_row,
        alpha,
        gamma,
        prev_continuous_fingerprint,
        padding_start_rw,
    )
}

///
pub fn get_permutation_fingerprint_of_rwvec<F: Field>(
    rwvec: &[Rw],
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
    padding_start_rw: Option<Rw>,
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
        padding_start_rw.map(|r| r.table_assignment()),
    )
}

///
pub fn get_permutation_fingerprint_of_rwrowvec<F: Field>(
    rwrowvec: &[RwRow<Value<F>>],
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
    padding_start_rwrow: Option<RwRow<Value<F>>>,
) -> RwFingerprints<F> {
    let (rows, _) = RwRow::padding(rwrowvec, max_row, padding_start_rwrow);
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

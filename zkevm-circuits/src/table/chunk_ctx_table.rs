use bus_mapping::circuit_input_builder::ChunkContext;
use gadgets::util::Expr;
use halo2_proofs::circuit::AssignedCell;

use super::*;

/// Tag to identify the field in a Chunk Context row
// Keep the sequence consistent with OpcodeId for scalar
#[derive(Clone, Copy, Debug)]
pub enum ChunkCtxFieldTag {
    /// Coinbase field
    CurrentChunkIndex = 1,
    /// NextChunk field
    NextChunkIndex,
    /// Total Chunks field
    TotalChunks,
    /// initial rw counter
    InitialRWC,
    /// end rw counter
    EndRWC,
}
impl_expr!(ChunkCtxFieldTag);

/// Table with Chunk context fields
#[derive(Clone, Debug)]
pub struct ChunkCtxTable {
    q_enable: Selector,
    /// Tag
    pub tag: Column<Fixed>,
    /// Value
    pub value: Column<Advice>,
}

type ChunkCtxTableAssignedCells<F> = (
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
);

impl ChunkCtxTable {
    /// Construct a new ChunkCtxTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let (q_enable, tag, value) = (meta.selector(), meta.fixed_column(), meta.advice_column());

        // constraint NextChunkIndex = CurrentChunkIndex + 1
        meta.create_gate("NextChunkIndex = CurrentChunkIndex + 1", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let value_cur = meta.query_advice(value, Rotation::cur());
            let value_next = meta.query_advice(value, Rotation::next());
            [q_enable * (value_next - value_cur - 1.expr())]
        });

        meta.enable_equality(value);

        Self {
            q_enable,
            tag,
            value,
        }
    }

    /// Assign the `ChunkCtxTable` from a `BlockContext`.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        chunk_ctx: &ChunkContext,
    ) -> Result<ChunkCtxTableAssignedCells<F>, Error> {
        layouter.assign_region(
            || "chunkctx table",
            |mut region| {
                let mut offset = 0;

                self.q_enable.enable(&mut region, offset)?;

                let assigned_cells = [
                    // CurrentChunkIndex
                    (
                        F::from(ChunkCtxFieldTag::CurrentChunkIndex as u64),
                        F::from(chunk_ctx.idx as u64),
                    ),
                    // NextChunkIndex
                    (
                        F::from(ChunkCtxFieldTag::NextChunkIndex as u64),
                        F::from(chunk_ctx.idx as u64 + 1u64),
                    ),
                    // TotalChunks
                    (
                        F::from(ChunkCtxFieldTag::TotalChunks as u64),
                        F::from(chunk_ctx.total_chunks as u64),
                    ),
                    // InitialRWC
                    (
                        F::from(ChunkCtxFieldTag::InitialRWC as u64),
                        F::from(chunk_ctx.initial_rwc as u64),
                    ),
                    // EndRWC
                    (
                        F::from(ChunkCtxFieldTag::EndRWC as u64),
                        F::from(chunk_ctx.end_rwc as u64),
                    ),
                    // Empty row for disable lookup
                    (F::ZERO, F::ZERO),
                ]
                .iter()
                .map(|(tag, value)| {
                    region.assign_fixed(
                        || format!("chunkctx table tag {}", offset),
                        self.tag,
                        offset,
                        || Value::known(*tag),
                    )?;

                    let assigned_value = region.assign_advice(
                        || format!("chunkctx table value {}", offset),
                        self.value,
                        offset,
                        || Value::known(*value),
                    )?;

                    offset += 1;

                    Ok(assigned_value)
                })
                .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;

                // remove last empty cell
                let assigned_cells = assigned_cells.split_last().unwrap().1;

                Ok(assigned_cells.iter().cloned().collect_tuple().unwrap())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for ChunkCtxTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![self.tag.into(), self.value.into()]
    }

    fn annotations(&self) -> Vec<String> {
        vec![String::from("tag"), String::from("value")]
    }
}

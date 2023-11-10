use std::iter;

use super::*;

/// Tag to identify the field in a Block Table row
// Keep the sequence consistent with OpcodeId for scalar
#[derive(Clone, Copy, Debug)]
pub enum BlockContextFieldTag {
    /// Coinbase field
    Coinbase = 1,
    /// Timestamp field
    Timestamp,
    /// Number field
    Number,
    /// Difficulty field
    Difficulty,
    /// Gas Limit field
    GasLimit,
    /// Base Fee field
    BaseFee = 8,
    /// Block Hash field
    BlockHash,
    /// Chain ID field.  Although this is not a field in the block header, we
    /// add it here for convenience.
    ChainId,
    /// Withdrawal Root field
    WithdrawalRoot,
}
impl_expr!(BlockContextFieldTag);

/// Table with Block header fields
#[derive(Clone, Debug)]
pub struct BlockTable {
    /// Tag
    pub tag: Column<Fixed>,
    /// Index
    pub index: Column<Fixed>,
    /// Value
    pub value: word::Word<Column<Advice>>,
}

impl BlockTable {
    /// Construct a new BlockTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.fixed_column(),
            index: meta.fixed_column(),
            value: word::Word::new([meta.advice_column(), meta.advice_column()]),
        }
    }

    /// Assign the `BlockTable` from a `BlockContext`.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &BlockContext,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "block table",
            |mut region| {
                for (offset, row) in iter::once([Value::known(F::ZERO); 4])
                    .chain(block.table_assignments::<F>())
                    .enumerate()
                {
                    region.assign_fixed(
                        || format!("block table tag {}", offset),
                        self.tag,
                        offset,
                        || row[0],
                    )?;
                    region.assign_fixed(
                        || format!("block table index {}", offset),
                        self.index,
                        offset,
                        || row[1],
                    )?;

                    word::Word::new([row[2], row[3]]).assign_advice(
                        &mut region,
                        || format!("block table value {}", offset),
                        self.value,
                        offset,
                    )?;
                }
                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for BlockTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.tag.into(),
            self.index.into(),
            self.value.lo().into(),
            self.value.hi().into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("tag"),
            String::from("index"),
            String::from("value_lo"),
            String::from("value_hi"),
        ]
    }
}

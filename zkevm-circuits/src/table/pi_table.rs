use crate::witness::ProtocolInstance;

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PiFieldTag {
    Null = 0,
    MethodSign,
    L1Hash,
    L1SignalRoot,
    L1Height,
    ParentGasUsed,
}
impl_expr!(PiFieldTag);

#[derive(Clone, Debug)]
pub struct PiTable {
    pub tag: Column<Fixed>,
    pub value: Column<Advice>,
}

impl PiTable {
    /// Construct a new TxTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.fixed_column(),
            value: meta.advice_column_in(SecondPhase),
        }
    }

    /// Assign the `TxTable` from a list of block `Transaction`s, followig the
    /// same layout that the Tx Circuit uses.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        protocol_instance: &ProtocolInstance,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "pi table",
            |mut region| {
                let randomness = challenges.evm_word();
                for (offset, [tag, value]) in protocol_instance
                    .table_assignments(randomness)
                    .into_iter()
                    .enumerate()
                {
                    region.assign_fixed(|| "tag", self.tag, offset, || tag)?;
                    region.assign_advice(|| "value", self.value, offset, || value)?;
                }
                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for PiTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![self.tag.into(), self.value.into()]
    }

    fn annotations(&self) -> Vec<String> {
        vec![String::from("tag"), String::from("value")]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_fixed(self.tag, Rotation::cur()),
            meta.query_advice(self.value, Rotation::cur()),
        ]
    }
}

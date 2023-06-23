use super::*;

/// byte table stores the value from 0 to 255 which is used to check whether the input is a byte
#[derive(Clone, Debug)]
pub struct ByteTable {
    range256: Column<Fixed>,
}

impl ByteTable {
    /// construct the table
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let range256 = meta.fixed_column();
        Self { range256 }
    }

    /// load table
    pub fn load<F: Field>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "is_byte table",
            |mut region| {
                for i in 0..(1 << 8) {
                    region.assign_fixed(
                        || format!("row_{}", i),
                        self.range256,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for ByteTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![self.range256.into()]
    }

    fn annotations(&self) -> Vec<String> {
        vec![String::from("range256")]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![meta.query_fixed(self.range256, Rotation::cur())]
    }
}

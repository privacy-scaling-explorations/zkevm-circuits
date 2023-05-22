use super::*;

/// Lookup table for max n bits range check
#[derive(Clone, Copy, Debug)]
pub struct UXTable<const N_BITS: usize> {
    col: Column<Fixed>,
}

impl<const N_BITS: usize> UXTable<N_BITS> {
    /// Construct the Exponentiation table.
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            col: meta.fixed_column(),
        }
    }

    /// Load the `UXTable` for range check
    pub fn load<F: Field>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || format!("assign u{} fixed column", 8),
            |mut region| {
                for i in 0..(1 << N_BITS) {
                    region.assign_fixed(
                        || format!("assign {} in u{} fixed column", i, N_BITS),
                        self.col,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

impl<F: Field, const N_BITS: usize> LookupTable<F> for UXTable<N_BITS> {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![self.col.into()]
    }

    fn annotations(&self) -> Vec<String> {
        vec![format!("u{}_col", N_BITS)]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![meta.query_fixed(self.col, Rotation::cur())]
    }
}

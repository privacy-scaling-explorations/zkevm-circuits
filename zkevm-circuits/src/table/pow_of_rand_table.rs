use super::*;
use crate::evm_circuit::util::constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon};
use bus_mapping::circuit_input_builder::{N_BYTES_PER_PAIR, N_PAIRING_PER_OP};

/// Lookup table for powers of keccak randomness up to exponent in [0, 128)
#[derive(Clone, Copy, Debug)]
pub struct PowOfRandTable {
    /// Whether the row is enabled.
    pub q_enable: Column<Fixed>,
    /// Whether the row is the first enabled row.
    pub is_first: Column<Fixed>,
    /// exponent = [0, 1, 2, ..., 126, 127] for enabled rows.
    /// exponent = 0 for all other rows (disabled).
    pub exponent: Column<Fixed>,
    /// power of keccak randomness.
    pub pow_of_rand: Column<Advice>,
}

impl PowOfRandTable {
    /// Construct the powers of randomness table.
    pub fn construct<F: Field>(
        meta: &mut ConstraintSystem<F>,
        challenges: &Challenges<Expression<F>>,
    ) -> Self {
        let table = Self {
            q_enable: meta.fixed_column(),
            is_first: meta.fixed_column(),
            exponent: meta.fixed_column(),
            pow_of_rand: meta.advice_column_in(SecondPhase),
        };

        meta.create_gate("pow_of_rand_table: first row", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            cb.require_equal(
                "first row: rand ^ 0 == 1",
                meta.query_advice(table.pow_of_rand, Rotation::cur()),
                1.expr(),
            );
            cb.gate(and::expr([
                meta.query_fixed(table.q_enable, Rotation::cur()),
                meta.query_fixed(table.is_first, Rotation::cur()),
            ]))
        });

        meta.create_gate("pow_of_rand_table: all other enabled rows", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            cb.require_equal(
                "pow_of_rand::cur == pow_of_rand::prev * rand",
                meta.query_advice(table.pow_of_rand, Rotation::cur()),
                meta.query_advice(table.pow_of_rand, Rotation::prev()) * challenges.keccak_input(),
            );
            cb.gate(and::expr([
                meta.query_fixed(table.q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(table.is_first, Rotation::cur())),
            ]))
        });

        table
    }

    /// Assign values to the table.
    pub fn assign<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let r = challenges.keccak_input();
        layouter.assign_region(
            || "power of randomness table",
            |mut region| {
                let pows_of_rand =
                    std::iter::successors(Some(Value::known(F::ONE)), |&v| Some(v * r))
                        .take(N_PAIRING_PER_OP * N_BYTES_PER_PAIR);

                for (idx, pow_of_rand) in pows_of_rand.enumerate() {
                    region.assign_fixed(
                        || format!("q_enable at offset = {idx}"),
                        self.q_enable,
                        idx,
                        || Value::known(F::ONE),
                    )?;
                    region.assign_fixed(
                        || format!("is_first at offset = {idx}"),
                        self.is_first,
                        idx,
                        || Value::known(if idx == 0 { F::ONE } else { F::ZERO }),
                    )?;
                    region.assign_fixed(
                        || format!("exponent at offset = {idx}"),
                        self.exponent,
                        idx,
                        || Value::known(F::from(idx as u64)),
                    )?;
                    region.assign_advice(
                        || format!("pow_of_rand at offset = {idx}"),
                        self.pow_of_rand,
                        idx,
                        || pow_of_rand,
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for PowOfRandTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.q_enable.into(),
            self.is_first.into(),
            self.exponent.into(),
            self.pow_of_rand.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("q_enable"),
            String::from("is_first"),
            String::from("exponent"),
            String::from("pow_of_rand"),
        ]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_fixed(self.q_enable, Rotation::cur()),
            meta.query_fixed(self.exponent, Rotation::cur()),
            meta.query_advice(self.pow_of_rand, Rotation::cur()),
        ]
    }
}

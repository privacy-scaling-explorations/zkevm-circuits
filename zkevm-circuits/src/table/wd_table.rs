use bus_mapping::circuit_input_builder::Withdrawal;

use super::*;

/// Table that contains the fields of all Withdrawals in a block
#[derive(Clone, Debug)]
pub struct WdTable {
    /// withdrawal id
    pub id: Column<Advice>,
    /// validator id
    pub validator_id: Column<Advice>,
    /// withdrawal address
    pub address: Word<Column<Advice>>,
    /// validator withdrawal amount in Gwei
    pub amount: Column<Advice>,
}

impl WdTable {
    /// Construct a new WdTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            id: meta.advice_column(),
            validator_id: meta.advice_column(),
            address: Word::new([meta.advice_column(), meta.advice_column()]),
            amount: meta.advice_column(),
        }
    }

    /// Assign the `WdTable` from a list of block `withdrawal`s
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        withdrawals: &[Withdrawal],
        max_withdrawals: usize,
    ) -> Result<(), Error> {
        assert!(
            withdrawals.len() <= max_withdrawals,
            "withdrawals.len() <= max_withdrawals: withdrawals.len()={}, max_withdrawals={}",
            withdrawals.len(),
            max_withdrawals
        );

        fn assign_row<F: Field>(
            region: &mut Region<'_, F>,
            offset: usize,
            advice_columns: &[Column<Advice>],
            row: &[Value<F>; 5],
            msg: &str,
        ) -> Result<(), Error> {
            for (index, column) in advice_columns.iter().enumerate() {
                region.assign_advice(
                    || format!("wd table {} row {}", msg, offset),
                    *column,
                    offset,
                    || row[if index > 0 { index + 1 } else { index }],
                )?;
            }
            Ok(())
        }

        layouter.assign_region(
            || "wd table",
            |mut region| {
                let advice_columns = [
                    self.id,
                    self.validator_id,
                    self.address.lo(),
                    self.address.hi(),
                    self.amount,
                ];

                // Assign withdrawal data
                let padding_withdrawals: Vec<_> = (withdrawals.len()..max_withdrawals)
                    .map(|i| Withdrawal::padding_withdrawal(i + 1))
                    .collect();
                for (offset, wd) in withdrawals
                    .iter()
                    .chain(padding_withdrawals.iter())
                    .enumerate()
                {
                    let address_word = Word::from(wd.address);
                    let row = [
                        Value::known(F::from(wd.id)),
                        Value::known(F::from(wd.validator_id)),
                        Value::known(address_word.lo()),
                        Value::known(address_word.hi()),
                        Value::known(F::from(wd.amount)),
                    ];
                    assign_row(
                        &mut region,
                        offset,
                        &advice_columns,
                        &row,
                        "assign wd table",
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for WdTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.id.into(),
            self.validator_id.into(),
            self.address.lo().into(),
            self.address.hi().into(),
            self.amount.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("id"),
            String::from("validator_id"),
            String::from("address_lo"),
            String::from("address_hi"),
            String::from("amount"),
        ]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.id, Rotation::cur()),
            meta.query_advice(self.validator_id, Rotation::cur()),
            meta.query_advice(self.address.lo(), Rotation::cur()),
            meta.query_advice(self.address.hi(), Rotation::cur()),
            meta.query_advice(self.amount, Rotation::cur()),
        ]
    }
}

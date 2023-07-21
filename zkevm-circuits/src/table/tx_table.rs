use super::*;

/// Tag used to identify each field in the transaction in a row of the
/// transaction table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TxFieldTag {
    /// Unused tag
    Null = 0,
    /// Nonce
    Nonce,
    /// Gas
    Gas,
    /// GasPrice
    GasPrice,
    /// CallerAddress
    CallerAddress,
    /// CalleeAddress
    CalleeAddress,
    /// IsCreate
    IsCreate,
    /// Value
    Value,
    /// CallDataLength
    CallDataLength,
    /// Gas cost for transaction call data (4 for byte == 0, 16 otherwise)
    CallDataGasCost,
    /// TxSignHash: Hash of the transaction without the signature, used for
    /// signing.
    TxSignHash,
    /// CallData
    CallData,
    /// Invalid tx
    TxInvalid,
    /// AccessListGasCost
    AccessListGasCost,
}
impl_expr!(TxFieldTag);

/// Tag for a TxLogField in RwTable
#[derive(Clone, Copy, Debug, PartialEq, Eq, EnumIter)]
pub enum TxLogFieldTag {
    /// Address field
    Address = 1,
    /// Topic field
    Topic,
    /// Data field
    Data,
}
impl_expr!(TxLogFieldTag);

/// Tag for a TxReceiptField in RwTable
#[derive(Clone, Copy, Debug, PartialEq, Eq, EnumIter, EnumCount)]
pub enum TxReceiptFieldTag {
    /// Tx result
    PostStateOrStatus = 1,
    /// CumulativeGasUsed in the tx
    CumulativeGasUsed,
    /// Number of logs in the tx
    LogLength,
}
impl_expr!(TxReceiptFieldTag);

/// Alias for TxFieldTag used by EVM Circuit
pub type TxContextFieldTag = TxFieldTag;

/// Table that contains the fields of all Transactions in a block
#[derive(Clone, Debug)]
pub struct TxTable {
    /// Tx ID
    pub tx_id: Column<Advice>,
    /// Tag (TxContextFieldTag)
    pub tag: Column<Fixed>,
    /// Index for Tag = CallData
    pub index: Column<Advice>,
    /// Value
    pub value: word::Word<Column<Advice>>,
}

impl TxTable {
    /// Construct a new TxTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tx_id: meta.advice_column(),
            tag: meta.fixed_column(),
            index: meta.advice_column(),
            value: word::Word::new([meta.advice_column(), meta.advice_column()]),
        }
    }

    /// Assign the `TxTable` from a list of block `Transaction`s, followig the
    /// same layout that the Tx Circuit uses.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        txs: &[Transaction],
        max_txs: usize,
        max_calldata: usize,
    ) -> Result<(), Error> {
        assert!(
            txs.len() <= max_txs,
            "txs.len() <= max_txs: txs.len()={}, max_txs={}",
            txs.len(),
            max_txs
        );
        let sum_txs_calldata = txs.iter().map(|tx| tx.call_data.len()).sum();
        assert!(
            sum_txs_calldata <= max_calldata,
            "sum_txs_calldata <= max_calldata: sum_txs_calldata={}, max_calldata={}",
            sum_txs_calldata,
            max_calldata,
        );

        fn assign_row<F: Field>(
            region: &mut Region<'_, F>,
            offset: usize,
            advice_columns: &[Column<Advice>],
            tag: &Column<Fixed>,
            row: &[Value<F>; 5],
            msg: &str,
        ) -> Result<(), Error> {
            for (index, column) in advice_columns.iter().enumerate() {
                region.assign_advice(
                    || format!("tx table {} row {}", msg, offset),
                    *column,
                    offset,
                    || row[if index > 0 { index + 1 } else { index }],
                )?;
            }
            region.assign_fixed(
                || format!("tx table {} row {}", msg, offset),
                *tag,
                offset,
                || row[1],
            )?;
            Ok(())
        }

        layouter.assign_region(
            || "tx table",
            |mut region| {
                let mut offset = 0;
                let advice_columns = [self.tx_id, self.index, self.value.lo(), self.value.hi()];
                assign_row(
                    &mut region,
                    offset,
                    &advice_columns,
                    &self.tag,
                    &[(); 5].map(|_| Value::known(F::ZERO)),
                    "all-zero",
                )?;
                offset += 1;

                // Tx Table contains an initial region that has a size parametrized by max_txs
                // with all the tx data except for calldata, and then a second
                // region that has a size parametrized by max_calldata with all
                // the tx calldata.  This is required to achieve a constant fixed column tag
                // regardless of the number of input txs or the calldata size of each tx.
                let mut calldata_assignments: Vec<[Value<F>; 5]> = Vec::new();
                // Assign Tx data (all tx fields except for calldata)
                let padding_txs: Vec<_> = (txs.len()..max_txs)
                    .map(|i| Transaction::padding_tx(i + 1))
                    .collect();
                for tx in txs.iter().chain(padding_txs.iter()) {
                    let tx_id = Value::known(F::from(tx.id));
                    let tx_data = vec![
                        (
                            TxContextFieldTag::Nonce,
                            word::Word::from(tx.nonce.as_u64()),
                        ),
                        (TxContextFieldTag::Gas, word::Word::from(tx.gas())),
                        (TxContextFieldTag::GasPrice, word::Word::from(tx.gas_price)),
                        (TxContextFieldTag::CallerAddress, word::Word::from(tx.from)),
                        (
                            TxContextFieldTag::CalleeAddress,
                            word::Word::from(tx.to_or_contract_addr()),
                        ),
                        (
                            TxContextFieldTag::IsCreate,
                            word::Word::from(tx.is_create()),
                        ),
                        (TxContextFieldTag::Value, word::Word::from(tx.value)),
                        (
                            TxContextFieldTag::CallDataLength,
                            word::Word::from(tx.call_data.len() as u64),
                        ),
                        (
                            TxContextFieldTag::CallDataGasCost,
                            word::Word::from(tx.call_data_gas_cost()),
                        ),
                        (
                            TxContextFieldTag::TxInvalid,
                            word::Word::from(tx.invalid_tx),
                        ),
                        (
                            TxContextFieldTag::AccessListGasCost,
                            word::Word::from(tx.access_list_gas_cost),
                        )
                    ]
                    .iter()
                    .map(|&(tag, word)| {
                        [
                            tx_id,
                            Value::known(F::from(tag as u64)),
                            Value::known(F::ZERO),
                            Value::known(word.lo()),
                            Value::known(word.hi()),
                        ]
                    })
                    .collect_vec();
                    let tx_calldata = tx
                        .call_data
                        .iter()
                        .enumerate()
                        .map(|(idx, byte)| {
                            [
                                tx_id,
                                Value::known(F::from(TxContextFieldTag::CallData as u64)),
                                Value::known(F::from(idx as u64)),
                                Value::known(F::from(*byte as u64)),
                                Value::known(F::ZERO),
                            ]
                        })
                        .collect_vec();
                    for row in tx_data {
                        assign_row(&mut region, offset, &advice_columns, &self.tag, &row, "")?;
                        offset += 1;
                    }
                    calldata_assignments.extend(tx_calldata.iter());
                }
                // Assign Tx calldata
                let padding_calldata = (sum_txs_calldata..max_calldata).map(|_| {
                    [
                        Value::known(F::ZERO),
                        Value::known(F::from(TxContextFieldTag::CallData as u64)),
                        Value::known(F::ZERO),
                        Value::known(F::ZERO),
                        Value::known(F::ZERO),
                    ]
                });
                for row in calldata_assignments.into_iter().chain(padding_calldata) {
                    assign_row(&mut region, offset, &advice_columns, &self.tag, &row, "")?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for TxTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.tx_id.into(),
            self.tag.into(),
            self.index.into(),
            self.value.lo().into(),
            self.value.hi().into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("tx_id"),
            String::from("tag"),
            String::from("index"),
            String::from("value_lo"),
            String::from("value_hi"),
        ]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.tx_id, Rotation::cur()),
            meta.query_fixed(self.tag, Rotation::cur()),
            meta.query_advice(self.index, Rotation::cur()),
            meta.query_advice(self.value.lo(), Rotation::cur()),
            meta.query_advice(self.value.hi(), Rotation::cur()),
        ]
    }
}

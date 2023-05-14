//! The transaction circuit implementation.

// Naming notes:
// - *_be: Big-Endian bytes
// - *_le: Little-Endian bytes

pub mod sign_verify;

#[cfg(any(feature = "test", test, feature = "test-circuits"))]
mod dev;
#[cfg(any(feature = "test", test))]
mod test;
#[cfg(any(feature = "test", test, feature = "test-circuits"))]
pub use dev::TxCircuit as TestTxCircuit;

use crate::{
    table::{KeccakTable, TxFieldTag, TxTable},
    util::{random_linear_combine_word as rlc, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use eth_types::{geth_types::Transaction, sign_types::SignData, Field, ToLittleEndian, ToScalar};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed},
};
use itertools::Itertools;
use log::error;
use sign_verify::{AssignedSignatureVerify, SignVerifyChip, SignVerifyConfig};
use std::marker::PhantomData;

/// Number of static fields per tx: [nonce, gas, gas_price,
/// caller_address, callee_address, is_create, value, call_data_length,
/// call_data_gas_cost, tx_sign_hash].
/// Note that call data bytes are layed out in the TxTable after all the static
/// fields arranged by txs.
pub(crate) const TX_LEN: usize = 10;

/// Config for TxCircuit
#[derive(Clone, Debug)]
pub struct TxCircuitConfig<F: Field> {
    tx_id: Column<Advice>,
    tag: Column<Fixed>,
    index: Column<Advice>,
    value: Column<Advice>,
    sign_verify: SignVerifyConfig,
    _marker: PhantomData<F>,
    // External tables
    keccak_table: KeccakTable,
}

/// Circuit configuration arguments
pub struct TxCircuitConfigArgs<F: Field> {
    /// TxTable
    pub tx_table: TxTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for TxCircuitConfig<F> {
    type ConfigArgs = TxCircuitConfigArgs<F>;

    /// Return a new TxCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            tx_table,
            keccak_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        let tx_id = tx_table.tx_id;
        let tag = tx_table.tag;
        let index = tx_table.index;
        let value = tx_table.value;
        meta.enable_equality(value);

        let sign_verify = SignVerifyConfig::new(meta, keccak_table.clone(), challenges);

        Self {
            tx_id,
            tag,
            index,
            value,
            sign_verify,
            keccak_table,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> TxCircuitConfig<F> {
    /// Load ECDSA RangeChip table.
    pub fn load_aux_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.sign_verify.load_range(layouter)
    }

    /// Assigns a tx circuit row and returns the assigned cell of the value in
    /// the row.
    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: usize,
        tag: TxFieldTag,
        index: usize,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.assign_advice(
            || "tx_id",
            self.tx_id,
            offset,
            || Value::known(F::from(tx_id as u64)),
        )?;
        region.assign_fixed(
            || "tag",
            self.tag,
            offset,
            || Value::known(F::from(tag as u64)),
        )?;
        region.assign_advice(
            || "index",
            self.index,
            offset,
            || Value::known(F::from(index as u64)),
        )?;
        region.assign_advice(|| "value", self.value, offset, || value)
    }

    /// Get number of rows required.
    pub fn get_num_rows_required(num_tx: usize) -> usize {
        let num_rows_range_table = 1 << 18;
        // Number of rows required to verify a transaction.
        let num_rows_per_tx = 140436;
        (num_tx * num_rows_per_tx).max(num_rows_range_table)
    }
}

/// Tx Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct TxCircuit<F: Field> {
    /// Max number of supported transactions
    pub max_txs: usize,
    /// Max number of supported calldata bytes
    pub max_calldata: usize,
    /// SignVerify chip
    pub sign_verify: SignVerifyChip<F>,
    /// List of Transactions
    pub txs: Vec<Transaction>,
    /// Chain ID
    pub chain_id: u64,
}

impl<F: Field> TxCircuit<F> {
    /// Return a new TxCircuit
    pub fn new(max_txs: usize, max_calldata: usize, chain_id: u64, txs: Vec<Transaction>) -> Self {
        TxCircuit::<F> {
            max_txs,
            max_calldata,
            sign_verify: SignVerifyChip::new(max_txs),
            txs,
            chain_id,
        }
    }

    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub fn min_num_rows(txs_len: usize, call_data_len: usize) -> usize {
        let tx_table_len = txs_len * TX_LEN + call_data_len;
        std::cmp::max(tx_table_len, SignVerifyChip::<F>::min_num_rows(txs_len))
    }

    fn assign_tx_table(
        &self,
        config: &TxCircuitConfig<F>,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
        assigned_sig_verifs: Vec<AssignedSignatureVerify<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "tx table",
            |mut region| {
                let mut offset = 0;
                // Empty entry
                config.assign_row(
                    &mut region,
                    offset,
                    0,
                    TxFieldTag::Null,
                    0,
                    Value::known(F::ZERO),
                )?;
                offset += 1;
                // Assign al Tx fields except for call data
                let tx_default = Transaction::default();
                for (i, assigned_sig_verif) in assigned_sig_verifs.iter().enumerate() {
                    let tx = if i < self.txs.len() {
                        &self.txs[i]
                    } else {
                        &tx_default
                    };

                    for (tag, value) in [
                        (TxFieldTag::Nonce, Value::known(F::from(tx.nonce))),
                        (
                            TxFieldTag::Gas,
                            Value::known(F::from(tx.gas_limit.as_u64())),
                        ),
                        (
                            TxFieldTag::GasPrice,
                            challenges
                                .evm_word()
                                .map(|challenge| rlc(tx.gas_price.to_le_bytes(), challenge)),
                        ),
                        (
                            TxFieldTag::CallerAddress,
                            Value::known(tx.from.to_scalar().expect("tx.from too big")),
                        ),
                        (
                            TxFieldTag::CalleeAddress,
                            Value::known(tx.to_or_zero().to_scalar().expect("tx.to too big")),
                        ),
                        (
                            TxFieldTag::IsCreate,
                            Value::known(F::from(tx.is_create() as u64)),
                        ),
                        (
                            TxFieldTag::Value,
                            challenges
                                .evm_word()
                                .map(|challenge| rlc(tx.value.to_le_bytes(), challenge)),
                        ),
                        (
                            TxFieldTag::CallDataLength,
                            Value::known(F::from(tx.call_data.0.len() as u64)),
                        ),
                        (
                            TxFieldTag::CallDataGasCost,
                            Value::known(F::from(tx.call_data_gas_cost())),
                        ),
                        (
                            TxFieldTag::TxSignHash,
                            assigned_sig_verif.msg_hash_rlc.value().copied(),
                        ),
                    ] {
                        let assigned_cell =
                            config.assign_row(&mut region, offset, i + 1, tag, 0, value)?;
                        offset += 1;

                        // Ref. spec 0. Copy constraints using fixed offsets between the tx rows and
                        // the SignVerifyChip
                        match tag {
                            TxFieldTag::CallerAddress => region.constrain_equal(
                                assigned_cell.cell(),
                                assigned_sig_verif.address.cell(),
                            )?,
                            TxFieldTag::TxSignHash => region.constrain_equal(
                                assigned_cell.cell(),
                                assigned_sig_verif.msg_hash_rlc.cell(),
                            )?,
                            _ => (),
                        }
                    }
                }

                // Assign call data
                let mut calldata_count = 0;
                for (i, tx) in self.txs.iter().enumerate() {
                    for (index, byte) in tx.call_data.0.iter().enumerate() {
                        assert!(calldata_count < self.max_calldata);
                        config.assign_row(
                            &mut region,
                            offset,
                            i + 1, // tx_id
                            TxFieldTag::CallData,
                            index,
                            Value::known(F::from(*byte as u64)),
                        )?;
                        offset += 1;
                        calldata_count += 1;
                    }
                }
                for _ in calldata_count..self.max_calldata {
                    config.assign_row(
                        &mut region,
                        offset,
                        0, // tx_id
                        TxFieldTag::CallData,
                        0,
                        Value::known(F::ZERO),
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}

impl<F: Field> SubCircuit<F> for TxCircuit<F> {
    type Config = TxCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn new_from_block(block: &witness::Block<F>) -> Self {
        Self::new(
            block.circuits_params.max_txs,
            block.circuits_params.max_calldata,
            block.context.chain_id.as_u64(),
            block
                .eth_block
                .transactions
                .iter()
                .map(|tx| tx.into())
                .collect(),
        )
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            Self::min_num_rows(
                block.txs.len(),
                block.txs.iter().map(|tx| tx.call_data.len()).sum(),
            ),
            Self::min_num_rows(
                block.circuits_params.max_txs,
                block.circuits_params.max_calldata,
            ),
        )
    }

    /// Make the assignments to the TxCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        assert!(self.txs.len() <= self.max_txs);
        let sign_datas: Vec<SignData> = self
            .txs
            .iter()
            .map(|tx| {
                tx.sign_data(self.chain_id).map_err(|e| {
                    error!("tx_to_sign_data error for tx {:?}", e);
                    Error::Synthesis
                })
            })
            .try_collect()?;

        config.load_aux_tables(layouter)?;
        let assigned_sig_verifs =
            self.sign_verify
                .assign(&config.sign_verify, layouter, &sign_datas, challenges)?;
        self.assign_tx_table(config, challenges, layouter, assigned_sig_verifs)?;
        Ok(())
    }

    fn instance(&self) -> Vec<Vec<F>> {
        // The maingate expects an instance column, but we don't use it, so we return an
        // "empty" instance column
        vec![vec![]]
    }
}

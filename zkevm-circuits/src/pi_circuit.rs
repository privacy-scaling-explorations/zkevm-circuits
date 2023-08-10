//! Public Input Circuit implementation
mod param;

#[cfg(any(test, feature = "test-circuits"))]
mod dev;
#[cfg(test)]
mod test;
use std::{cmp::min, iter, marker::PhantomData};

#[cfg(feature = "test-circuits")]
pub use PiCircuit as TestPiCircuit;

use eth_types::{self, Field, ToLittleEndian};
use halo2_proofs::plonk::{Expression, Instance, SecondPhase};
use itertools::Itertools;
use param::*;

use crate::{
    evm_circuit::{
        param::{
            N_BYTES_BLOCK, N_BYTES_EXTRA_VALUE, N_BYTES_HALF_WORD, N_BYTES_TX, N_BYTES_U64,
            N_BYTES_WORD,
        },
        util::{
            constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon},
            from_bytes,
        },
    },
    instance::{
        public_data_convert, BlockValues, ExtraValues, PublicData, TxValues, NONZERO_BYTE_GAS_COST,
        ZERO_BYTE_GAS_COST,
    },
    table::{BlockTable, KeccakTable, LookupTable, TxFieldTag, TxTable},
    tx_circuit::TX_LEN,
    util::{word::Word, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use gadgets::{
    is_zero::IsZeroChip,
    util::{not, or, Expr},
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};

/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct PiCircuitConfig<F: Field> {
    /// Max number of supported transactions
    max_txs: usize,
    /// Max number of supported calldata bytes
    max_calldata: usize,

    // q_digest_last: will be 1 on last byte of keccak digest, others are 0
    q_digest_last: Selector,
    // q_bytes_last: will be 1 on last byte of raw public input last byte, others are 0
    q_bytes_last: Selector,
    // q_tx_table: 1 on the rows where tx_table is activated, others are 0
    q_tx_table: Selector,
    // q_tx_calldata: 1 on the rows where tx_table calldata is activated, others are 0
    q_tx_calldata: Selector,
    // q_calldata_start: 1 on the starting row of calldata in tx_table, others are 0
    q_calldata_start: Selector,
    // q_rpi_keccak_lookup: enable keccak lookup
    q_rpi_keccak_lookup: Selector,
    // q_rpi_value_start: assure rpi_bytes sync with rpi_value_lc when cross boundary.
    // because we layout rpi bytes vertically, which is concated from multiple original values.
    // The value can be one byte or multiple bytes. The order of values is pre-defined and
    // hardcode. can't use selector here because we need rotation
    q_rpi_value_start: Column<Fixed>,
    // q_digest_value_start: mark starting of hi and low. can't use selector here because we need
    // rotation
    q_digest_value_start: Column<Fixed>,

    tx_id_inv: Column<Advice>,
    // Do not need tx_value_hi_inv, because tx_value_inv only
    // refer in tx_calldata constrains, and only need tx_value.lo() part
    tx_value_lo_inv: Column<Advice>,
    tx_id_diff_inv: Column<Advice>,
    fixed_u16: Column<Fixed>,
    calldata_gas_cost: Column<Advice>,
    is_final: Column<Advice>,

    // rpi_bytes: raw public input bytes laid verticlly
    rpi_bytes: Column<Advice>,
    // rpi_bytes_keccakrlc: rpi_bytes rlc by keccak challenge. This is for Keccak lookup input
    // rlc
    rpi_bytes_keccakrlc: Column<Advice>,
    // rpi_value_lc: This is similar with rpi_bytes_keccakrlc, while the key differences is
    // it's linear combination with base 256.
    rpi_value_lc: Column<Advice>,
    // rpi_digest_bytes: Keccak digest raw bytes laid verticlly in this column
    rpi_digest_bytes: Column<Advice>,
    // rpi_digest_bytes_limbs: hi, lo limbs of digest
    rpi_digest_bytes_limbs: Column<Advice>,

    q_rpi_byte_enable: Selector,

    pi_instance: Column<Instance>, // keccak_digest_hi, keccak_digest_lo

    _marker: PhantomData<F>,
    // External tables
    block_table: BlockTable,
    tx_table: TxTable,
    keccak_table: KeccakTable,
}

/// Circuit configuration arguments
pub struct PiCircuitConfigArgs<F: Field> {
    /// Max number of supported transactions
    pub max_txs: usize,
    /// Max number of supported calldata bytes
    pub max_calldata: usize,
    /// TxTable
    pub tx_table: TxTable,
    /// BlockTable
    pub block_table: BlockTable,
    /// Keccak Table
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for PiCircuitConfig<F> {
    type ConfigArgs = PiCircuitConfigArgs<F>;

    /// Return a new PiCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            max_txs,
            max_calldata,
            block_table,
            tx_table,
            keccak_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        let q_tx_table = meta.complex_selector();
        let q_tx_calldata = meta.complex_selector();
        let q_calldata_start = meta.complex_selector();
        let q_rpi_keccak_lookup = meta.complex_selector();
        // Tx Table
        let tx_id = tx_table.tx_id;
        let tx_value = tx_table.value;
        let tag = tx_table.tag;
        let index = tx_table.index;
        let tx_id_inv = meta.advice_column();
        let tx_value_lo_inv = meta.advice_column();
        let tx_id_diff_inv = meta.advice_column();
        // The difference of tx_id of adjacent rows in calldata part of tx table
        // lies in the interval [0, 2^16] if their tx_id both do not equal to zero.
        // We do not use 2^8 for the reason that a large block may have more than
        // 2^8 transfer transactions which have 21000*2^8 (~ 5.376M) gas.
        let fixed_u16 = meta.fixed_column();
        let calldata_gas_cost = meta.advice_column_in(SecondPhase);
        let is_final = meta.advice_column();

        let q_digest_last = meta.complex_selector();
        let q_bytes_last = meta.complex_selector();
        let q_rpi_byte_enable = meta.complex_selector();
        let q_rpi_value_start = meta.fixed_column();
        let q_digest_value_start = meta.fixed_column();

        let rpi_bytes = meta.advice_column();
        let rpi_bytes_keccakrlc = meta.advice_column_in(SecondPhase);
        let rpi_value_lc = meta.advice_column();
        let rpi_digest_bytes = meta.advice_column();
        let rpi_digest_bytes_limbs = meta.advice_column();

        let pi_instance = meta.instance_column();

        // Annotate table columns
        tx_table.annotate_columns(meta);
        block_table.annotate_columns(meta);

        meta.enable_equality(block_table.value.lo());
        meta.enable_equality(block_table.value.hi());
        meta.enable_equality(tx_table.tx_id);
        meta.enable_equality(tx_table.index);
        meta.enable_equality(tx_table.value.lo());
        meta.enable_equality(tx_table.value.hi());

        meta.enable_equality(rpi_value_lc);
        meta.enable_equality(rpi_bytes_keccakrlc);

        meta.enable_equality(rpi_digest_bytes_limbs);

        meta.enable_equality(pi_instance);

        // gate 1 and gate 2 are compensation branch
        // 1: rpi_bytes_keccakrlc[last] = rpi_bytes[last]
        meta.create_gate("rpi_bytes_keccakrlc[last] = rpi_bytes[last]", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "rpi_bytes_keccakrlc[last] = rpi_bytes[last]",
                meta.query_advice(rpi_bytes_keccakrlc, Rotation::cur()),
                meta.query_advice(rpi_bytes, Rotation::cur()),
            );

            cb.gate(meta.query_selector(q_bytes_last) * meta.query_selector(q_rpi_byte_enable))
        });

        // 2: rpi_bytes_keccakrlc[i] = keccak_rand * rpi_bytes_keccakrlc[i+1] + rpi_bytes[i]"
        meta.create_gate(
            "rpi_bytes_keccakrlc[i] = keccak_rand * rpi_bytes_keccakrlc[i+1] + rpi_bytes[i]",
            |meta| {
                let mut cb = BaseConstraintBuilder::default();

                let rpi_bytes_keccakrlc_cur =
                    meta.query_advice(rpi_bytes_keccakrlc, Rotation::cur());
                let rpi_bytes_keccakrlc_next =
                    meta.query_advice(rpi_bytes_keccakrlc, Rotation::next());
                let rpi_bytes_cur = meta.query_advice(rpi_bytes, Rotation::cur());

                let keccak_rand = challenges.keccak_input();
                cb.require_equal(
                    "rpi_bytes_keccakrlc[i] = keccak_rand * rpi_bytes_keccakrlc[i+1] + rpi_bytes[i]",
                    rpi_bytes_keccakrlc_cur,
                    rpi_bytes_keccakrlc_next * keccak_rand + rpi_bytes_cur,
                );

                cb.gate(
                    not::expr(meta.query_selector(q_bytes_last)) *
                    meta.query_selector(q_rpi_byte_enable)
                )
            },
        );

        // gate 3 and gate 4 are compensation branch
        // 3: rpi_value_lc[i] = rpi_value_lc[i+1] * byte_pow_base
        // + rpi_bytes[i]
        meta.create_gate(
            "rpi_value_lc[i] = rpi_value_lc[i-1] * byte_pow_base + rpi_bytes[i]",
            |meta| {
                let mut cb = BaseConstraintBuilder::default();
                let q_rpi_value_start_cur = meta.query_fixed(q_rpi_value_start, Rotation::cur());
                let rpi_value_lc_next = meta.query_advice(rpi_value_lc, Rotation::next());
                let rpi_value_lc_cur = meta.query_advice(rpi_value_lc, Rotation::cur());
                let rpi_bytes_cur = meta.query_advice(rpi_bytes, Rotation::cur());

                cb.require_equal(
                    "rpi_value_lc[i] = rpi_value_lc[i+1] * r + rpi_bytes[i]",
                    rpi_value_lc_cur,
                    rpi_value_lc_next * BYTE_POW_BASE.expr() + rpi_bytes_cur,
                );

                cb.gate(not::expr(q_rpi_value_start_cur) * meta.query_selector(q_rpi_byte_enable))
            },
        );

        // 4. rpi_value_lc[i] = rpi_bytes[i]
        meta.create_gate("rpi_value_lc[i] = rpi_bytes[i]", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            let q_rpi_value_start_cur = meta.query_fixed(q_rpi_value_start, Rotation::cur());

            cb.require_equal(
                "rpi_value_lc[i] = rpi_bytes[i]",
                meta.query_advice(rpi_bytes, Rotation::cur()),
                meta.query_advice(rpi_value_lc, Rotation::cur()),
            );

            cb.gate(q_rpi_value_start_cur * meta.query_selector(q_rpi_byte_enable))
        });

        // 5. lookup rpi_bytes_keccakrlc against rpi_digest_bytes_limbs
        meta.lookup_any(
            "lookup rpi_bytes_keccakrlc against rpi_digest_bytes_limbs",
            |meta| {
                let circuit_len =
                    PiCircuitConfig::<F>::circuit_len_by_txs_calldata(max_txs, max_calldata).expr();
                let is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                let input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                let input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                let output_lo = meta.query_advice(keccak_table.output.lo(), Rotation::cur());
                let output_hi = meta.query_advice(keccak_table.output.hi(), Rotation::cur());

                // is_enabled
                let q_rpi_keccak_lookup = meta.query_selector(q_rpi_keccak_lookup);
                // input_rlc
                let rpi_bytes_keccakrlc_cur =
                    meta.query_advice(rpi_bytes_keccakrlc, Rotation::cur());
                // output
                let rpi_digest_lo = meta.query_advice(rpi_digest_bytes_limbs, Rotation::cur());
                let rpi_digest_hi = meta.query_advice(rpi_digest_bytes_limbs, Rotation::next());

                vec![
                    (q_rpi_keccak_lookup.expr() * 1.expr(), is_enabled),
                    (
                        q_rpi_keccak_lookup.expr() * rpi_bytes_keccakrlc_cur,
                        input_rlc,
                    ),
                    (q_rpi_keccak_lookup.expr() * circuit_len, input_len),
                    (q_rpi_keccak_lookup.expr() * rpi_digest_lo, output_lo),
                    (q_rpi_keccak_lookup * rpi_digest_hi, output_hi),
                ]
            },
        );

        let tx_id_is_zero_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_tx_calldata),
            |meta| meta.query_advice(tx_table.tx_id, Rotation::cur()),
            tx_id_inv,
        );

        let tx_value_is_zero_lo_config = IsZeroChip::configure(
            meta,
            |meta| {
                or::expr([
                    meta.query_selector(q_tx_table),
                    meta.query_selector(q_tx_calldata),
                ])
            },
            |meta| meta.query_advice(tx_value.lo(), Rotation::cur()),
            tx_value_lo_inv,
        );
        let tx_value_is_zero_config = tx_value_is_zero_lo_config.expr();
        let _tx_id_diff_is_zero_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_tx_calldata),
            |meta| {
                meta.query_advice(tx_table.tx_id, Rotation::next())
                    - meta.query_advice(tx_table.tx_id, Rotation::cur())
            },
            tx_id_diff_inv,
        );

        meta.lookup_any("tx_id_diff", |meta| {
            let tx_id_next = meta.query_advice(tx_id, Rotation::next());
            let tx_id = meta.query_advice(tx_id, Rotation::cur());
            let tx_id_inv_next = meta.query_advice(tx_id_inv, Rotation::next());
            let tx_id_diff_inv = meta.query_advice(tx_id_diff_inv, Rotation::cur());
            let fixed_u16_table = meta.query_fixed(fixed_u16, Rotation::cur());

            let tx_id_next_nonzero = tx_id_next.expr() * tx_id_inv_next;
            let tx_id_not_equal_to_next = (tx_id_next.expr() - tx_id.expr()) * tx_id_diff_inv;
            let tx_id_diff_minus_one = tx_id_next - tx_id - 1.expr();

            vec![(
                tx_id_diff_minus_one * tx_id_next_nonzero * tx_id_not_equal_to_next,
                fixed_u16_table,
            )]
        });

        meta.create_gate("calldata constraints", |meta| {
            let q_is_calldata = meta.query_selector(q_tx_calldata);
            let q_calldata_start = meta.query_selector(q_calldata_start);
            let tx_idx = meta.query_advice(tx_id, Rotation::cur());
            let tx_idx_next = meta.query_advice(tx_id, Rotation::next());
            let tx_idx_inv_next = meta.query_advice(tx_id_inv, Rotation::next());
            let tx_idx_diff_inv = meta.query_advice(tx_id_diff_inv, Rotation::cur());
            let idx = meta.query_advice(index, Rotation::cur());
            let idx_next = meta.query_advice(index, Rotation::next());
            let value_next_lo = meta.query_advice(tx_value.lo(), Rotation::next());
            let value_inv_next_lo = meta.query_advice(tx_value_lo_inv, Rotation::next());

            let gas_cost = meta.query_advice(calldata_gas_cost, Rotation::cur());
            let gas_cost_next = meta.query_advice(calldata_gas_cost, Rotation::next());
            let is_final = meta.query_advice(is_final, Rotation::cur());

            let is_tx_id_nonzero = not::expr(tx_id_is_zero_config.expr());
            let is_tx_id_next_nonzero = tx_idx_next.expr() * tx_idx_inv_next.expr();

            let is_value_zero = tx_value_is_zero_config.expr();
            let is_value_nonzero = not::expr(tx_value_is_zero_config.expr());

            let is_value_next_nonzero = value_next_lo.expr() * value_inv_next_lo.expr();
            let is_value_next_zero = not::expr(is_value_next_nonzero.expr());

            // gas = value == 0 ? 4 : 16
            let gas = ZERO_BYTE_GAS_COST.expr() * is_value_zero.expr()
                + NONZERO_BYTE_GAS_COST.expr() * is_value_nonzero.expr();
            let gas_next = ZERO_BYTE_GAS_COST.expr() * is_value_next_zero
                + NONZERO_BYTE_GAS_COST.expr() * is_value_next_nonzero;

            // if tx_id == 0 then idx == 0, tx_id_next == 0
            let default_calldata_row_constraint1 = tx_id_is_zero_config.expr() * idx.expr();
            let default_calldata_row_constraint2 = tx_id_is_zero_config.expr() * tx_idx_next.expr();
            let default_calldata_row_constraint3 = tx_id_is_zero_config.expr() * is_final.expr();
            let default_calldata_row_constraint4 = tx_id_is_zero_config.expr() * gas_cost.expr();

            // if tx_id != 0 then
            //    1. tx_id_next == tx_id: idx_next == idx + 1, gas_cost_next == gas_cost +
            //       gas_next, is_final == false;
            //    2. tx_id_next == tx_id + 1 + x (where x is in [0, 2^16)): idx_next == 0,
            //       gas_cost_next == gas_next, is_final == true;
            //    3. tx_id_next == 0: is_final == true, idx_next == 0, gas_cost_next == 0;
            // either case 1, case 2 or case 3 holds.

            let tx_id_equal_to_next =
                1.expr() - (tx_idx_next.expr() - tx_idx.expr()) * tx_idx_diff_inv.expr();
            let idx_of_same_tx_constraint =
                tx_id_equal_to_next.clone() * (idx_next.expr() - idx.expr() - 1.expr());
            let idx_of_next_tx_constraint = (tx_idx_next.expr() - tx_idx.expr()) * idx_next.expr();

            let gas_cost_of_same_tx_constraint = tx_id_equal_to_next.clone()
                * (gas_cost_next.expr() - gas_cost.expr() - gas_next.expr());
            let gas_cost_of_next_tx_constraint = is_tx_id_next_nonzero.expr()
                * (tx_idx_next.expr() - tx_idx.expr())
                * (gas_cost_next.expr() - gas_next.expr());

            let is_final_of_same_tx_constraint = tx_id_equal_to_next * is_final.expr();
            let is_final_of_next_tx_constraint =
                (tx_idx_next.expr() - tx_idx.expr()) * (is_final.expr() - 1.expr());

            // if tx_id != 0 then
            //    1. q_calldata_start * (index - 0) == 0 and
            //    2. q_calldata_start * (gas_cost - gas) == 0.

            vec![
                q_is_calldata.expr() * default_calldata_row_constraint1,
                q_is_calldata.expr() * default_calldata_row_constraint2,
                q_is_calldata.expr() * default_calldata_row_constraint3,
                q_is_calldata.expr() * default_calldata_row_constraint4,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * idx_of_same_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * idx_of_next_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * gas_cost_of_same_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * gas_cost_of_next_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * is_final_of_same_tx_constraint,
                q_is_calldata.expr() * is_tx_id_nonzero.expr() * is_final_of_next_tx_constraint,
                q_calldata_start.expr() * is_tx_id_nonzero.expr() * (idx - 0.expr()),
                q_calldata_start.expr() * is_tx_id_nonzero.expr() * (gas_cost - gas),
            ]
        });

        // Test if tx tag equals to CallDataLength
        let tx_tag_is_cdl_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_tx_table),
            |meta| meta.query_fixed(tag, Rotation::cur()) - TxFieldTag::CallDataLength.expr(),
            tx_id_inv,
        );

        meta.create_gate(
            "call_data_gas_cost should be zero if call_data_length is zero",
            |meta| {
                let q_tx_table = meta.query_selector(q_tx_table);

                let is_calldata_length_zero = tx_value_is_zero_config.expr();
                let is_calldata_length_row = tx_tag_is_cdl_config.expr();
                let calldata_cost = meta.query_advice(tx_value.lo(), Rotation::next());

                vec![q_tx_table * is_calldata_length_row * is_calldata_length_zero * calldata_cost]
            },
        );

        meta.lookup_any("gas_cost in tx table", |meta| {
            let q_tx_table = meta.query_selector(q_tx_table);
            let is_final = meta.query_advice(is_final, Rotation::cur());

            let tx_id = meta.query_advice(tx_id, Rotation::cur());

            // calldata gas cost assigned in the tx table
            // CallDataGasCost is on the next row of CallDataLength
            let calldata_cost_assigned = meta.query_advice(tx_value.lo(), Rotation::next());
            // calldata gas cost calculated in call data
            let calldata_cost_calc = meta.query_advice(calldata_gas_cost, Rotation::cur());

            let is_calldata_length_row = tx_tag_is_cdl_config.expr();
            let is_calldata_length_nonzero = not::expr(tx_value_is_zero_config.expr());

            // lookup (tx_id, true, is_calldata_length_nonzero * is_calldata_cost *
            // gas_cost) in the table (tx_id, is_final, gas_cost)
            // if q_tx_table is true
            let condition = q_tx_table * is_calldata_length_nonzero * is_calldata_length_row;

            vec![
                (condition.expr() * tx_id.expr(), tx_id),
                (condition.expr() * 1.expr(), is_final),
                (
                    condition.expr() * calldata_cost_assigned,
                    calldata_cost_calc,
                ),
            ]
        });

        Self {
            max_txs,
            max_calldata,
            block_table,
            q_digest_last,
            q_bytes_last,
            q_tx_calldata,
            q_calldata_start,
            q_rpi_keccak_lookup,
            q_rpi_value_start,
            q_tx_table,
            q_digest_value_start,
            tx_table,
            keccak_table,
            tx_id_inv,
            tx_value_lo_inv,
            tx_id_diff_inv,
            fixed_u16,
            calldata_gas_cost,
            is_final,
            rpi_bytes,
            rpi_bytes_keccakrlc,
            rpi_value_lc,
            rpi_digest_bytes,
            rpi_digest_bytes_limbs,
            q_rpi_byte_enable,
            pi_instance,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> PiCircuitConfig<F> {
    /// Return the number of rows in the circuit
    #[inline]
    fn circuit_len(&self) -> usize {
        Self::circuit_len_by_txs_calldata(self.max_txs, self.max_calldata)
    }

    /// Return the number of rows for txs and calldata
    #[inline]
    fn circuit_len_by_txs_calldata(txs: usize, calldata: usize) -> usize {
        N_BYTES_ONE
            + N_BYTES_BLOCK
            + N_BYTES_EXTRA_VALUE
            + Self::circuit_len_tx_id(txs)
            + Self::circuit_len_tx_index(txs)
            + Self::circuit_len_tx_values(txs)
            + calldata
    }

    #[inline]
    fn circuit_len_tx_values(txs: usize) -> usize {
        N_BYTES_TX * (txs) + N_BYTES_ONE
    }

    #[inline]
    fn circuit_len_tx_id(txs: usize) -> usize {
        N_BYTES_U64 * TX_LEN * txs + N_BYTES_U64 // empty row
    }

    #[inline]
    fn circuit_len_tx_index(txs: usize) -> usize {
        N_BYTES_U64 * TX_LEN * txs + N_BYTES_U64 // empty row
    }

    fn assign_empty_txtable_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "tx_id_inv",
            self.tx_id_inv,
            offset,
            || Value::known(F::ZERO),
        )?;
        region.assign_advice(
            || "tx_value_lo_inv",
            self.tx_value_lo_inv,
            offset,
            || Value::known(F::ZERO),
        )?;
        region.assign_advice(
            || "is_final",
            self.is_final,
            offset,
            || Value::known(F::ZERO),
        )?;
        region.assign_advice(
            || "gas_cost",
            self.calldata_gas_cost,
            offset,
            || Value::known(F::ZERO),
        )?;
        region.assign_advice(
            || "tx_id",
            self.tx_table.tx_id,
            offset,
            || Value::known(F::ZERO),
        )?;
        region.assign_fixed(
            || "tag",
            self.tx_table.tag,
            offset,
            || Value::known(F::from(TxFieldTag::Null as u64)),
        )?;
        region.assign_advice(
            || "index",
            self.tx_table.index,
            offset,
            || Value::known(F::ZERO),
        )?;
        Word::default().into_value().assign_advice(
            region,
            || "tx_value",
            self.tx_table.value,
            offset,
        )?;
        Ok(())
    }

    fn reset_rpi_digest_row(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        region.assign_advice(
            || "rpi_digest_bytes_limbs",
            self.rpi_digest_bytes_limbs,
            offset,
            || Value::known(F::ZERO),
        )?;

        Ok(())
    }

    fn reset_rpi_bytes_row(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        // assign q_rpi_value_start
        region.assign_fixed(
            || "q_rpi_value_start",
            self.q_rpi_value_start,
            offset,
            || Value::known(F::ZERO),
        )?;

        // assign rpi bytes
        region.assign_advice(
            || "rpi_bytes",
            self.rpi_bytes,
            offset,
            || Value::known(F::ZERO),
        )?;

        // assign rpi_bytes_keccakrlc
        region.assign_advice(
            || "rpi_bytes_keccakrlc",
            self.rpi_bytes_keccakrlc,
            offset,
            || Value::known(F::ZERO),
        )?;

        // assign rpi_value_lc
        region.assign_advice(
            || "rpi_value_lc",
            self.rpi_value_lc,
            offset,
            || Value::known(F::ZERO),
        )?;

        Ok(())
    }

    /// Assigns a tx_table row and stores the values in a vec for the
    /// raw_public_inputs column
    #[allow(clippy::too_many_arguments)]
    fn assign_tx_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: u64,
        tag: TxFieldTag,
        index: u64,
        tx_value_bytes_le: &[u8],
        rpi_bytes_keccakrlc: &mut Value<F>,
        challenges: &Challenges<Value<F>>,
        current_offset: &mut usize,
        rpi_bytes: &mut [u8],
        zero_cell: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        // tx_id_inv = (tag - CallDataLength)^(-1)
        let tx_id_inv = if tag != TxFieldTag::CallDataLength {
            let x = F::from(tag as u64) - F::from(TxFieldTag::CallDataLength as u64);
            x.invert().unwrap_or(F::ZERO)
        } else {
            F::ZERO
        };
        let tag = F::from(tag as u64);
        let tx_value = Word::new([
            from_bytes::value(
                &tx_value_bytes_le[..min(N_BYTES_HALF_WORD, tx_value_bytes_le.len())],
            ),
            if tx_value_bytes_le.len() > N_BYTES_HALF_WORD {
                from_bytes::value(&tx_value_bytes_le[N_BYTES_HALF_WORD..])
            } else {
                F::ZERO
            },
        ])
        .into_value();
        let tx_value_inv = tx_value.map(|t| t.map(|x| x.invert().unwrap_or(F::ZERO)));

        self.q_tx_table.enable(region, offset)?;

        // Assign vals to Tx_table
        let tx_id_assignedcell = region.assign_advice(
            || "tx_id",
            self.tx_table.tx_id,
            offset,
            || Value::known(F::from(tx_id)),
        )?;
        region.assign_fixed(|| "tag", self.tx_table.tag, offset, || Value::known(tag))?;

        let tx_index_assignedcell = region.assign_advice(
            || "index",
            self.tx_table.index,
            offset,
            || Value::known(F::from(index)),
        )?;

        let tx_value_assignedcell =
            tx_value.assign_advice(region, || "tx_value", self.tx_table.value, offset)?;

        // tx_id
        let (_, raw_tx_id) = self.assign_raw_bytes(
            region,
            &tx_id.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        region.constrain_equal(tx_id_assignedcell.cell(), raw_tx_id.lo().cell())?;

        // index
        let (_, raw_tx_index) = self.assign_raw_bytes(
            region,
            &index.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        region.constrain_equal(tx_index_assignedcell.cell(), raw_tx_index.lo().cell())?;

        // tx value
        let (_, raw_tx_value) = self.assign_raw_bytes(
            region,
            tx_value_bytes_le,
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell,
        )?;
        region.constrain_equal(tx_value_assignedcell.lo().cell(), raw_tx_value.lo().cell())?;
        region.constrain_equal(tx_value_assignedcell.hi().cell(), raw_tx_value.hi().cell())?;

        // derived inverse not belong to TxTable so do not need copy constraints
        region.assign_advice(
            || "tx_id_inv",
            self.tx_id_inv,
            offset,
            || Value::known(tx_id_inv),
        )?;
        // tx_value_lo_inv have no use in tx table non-calldata row
        region.assign_advice(
            || "tx_value_lo_inv",
            self.tx_value_lo_inv,
            offset,
            || tx_value_inv.lo(),
        )?;

        Ok(())
    }

    /// Assigns one calldata row
    #[allow(clippy::too_many_arguments)]
    fn assign_tx_calldata_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: usize,
        tx_id_next: usize,
        index: usize,
        tx_value_byte: u8,
        rpi_bytes_keccakrlc: &mut Value<F>,
        challenges: &Challenges<Value<F>>,
        current_offset: &mut usize,
        rpi_bytes: &mut [u8],
        is_final: bool,
        gas_cost: F,
        zero_cell: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let tx_id = F::from(tx_id as u64);
        let tx_id_inv = tx_id.invert().unwrap_or(F::ZERO);
        let tx_id_diff = F::from(tx_id_next as u64) - tx_id;
        let tx_id_diff_inv = tx_id_diff.invert().unwrap_or(F::ZERO);
        let tag = F::from(TxFieldTag::CallData as u64);
        let index = F::from(index as u64);
        let tx_value: Word<Value<F>> = Word::from(tx_value_byte).into_value();
        let tx_value_inv = tx_value.map(|t| t.map(|x| x.invert().unwrap_or(F::ZERO)));
        let is_final = if is_final { F::ONE } else { F::ZERO };

        self.q_tx_calldata.enable(region, offset)?;

        // Assign vals to Tx_table
        region.assign_advice(
            || "tx_id",
            self.tx_table.tx_id,
            offset,
            || Value::known(tx_id),
        )?;
        region.assign_advice(
            || "tx_id_inv",
            self.tx_id_inv,
            offset,
            || Value::known(tx_id_inv),
        )?;
        region.assign_fixed(|| "tag", self.tx_table.tag, offset, || Value::known(tag))?;
        region.assign_advice(
            || "index",
            self.tx_table.index,
            offset,
            || Value::known(index),
        )?;

        let tx_value_cell =
            tx_value.assign_advice(region, || "tx_value", self.tx_table.value, offset)?;

        region.assign_advice(
            || "tx_value_lo_inv",
            self.tx_value_lo_inv,
            offset,
            || tx_value_inv.lo(),
        )?;
        region.assign_advice(
            || "tx_id_diff_inv",
            self.tx_id_diff_inv,
            offset,
            || Value::known(tx_id_diff_inv),
        )?;
        region.assign_advice(
            || "is_final",
            self.is_final,
            offset,
            || Value::known(is_final),
        )?;
        region.assign_advice(
            || "gas_cost",
            self.calldata_gas_cost,
            offset,
            || Value::known(gas_cost),
        )?;

        let (rpi_bytes_keccakrlc_cell, rpi_value_lc_cell) = self.assign_raw_bytes(
            region,
            &[tx_value_byte],
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell,
        )?;

        // constrain `value` field in calldata match with public input lc cell
        // tx_id and index constrains will be on tx circuit
        region.constrain_equal(rpi_value_lc_cell.lo().cell(), tx_value_cell.lo().cell())?;
        region.constrain_equal(rpi_value_lc_cell.hi().cell(), tx_value_cell.hi().cell())?;

        Ok(rpi_bytes_keccakrlc_cell)
    }

    /// assign raw bytes
    #[allow(clippy::too_many_arguments)]
    fn assign_raw_bytes(
        &self,
        region: &mut Region<'_, F>,
        value_bytes_le: &[u8],
        rpi_bytes_keccakrlc: &mut Value<F>,
        rpi_bytes: &mut [u8],
        current_offset: &mut usize,
        challenges: &Challenges<Value<F>>,
        zero_cell: AssignedCell<F, F>,
    ) -> Result<AssignedByteCells<F>, Error> {
        assert!(!value_bytes_le.is_empty());
        assert!(value_bytes_le.len() <= N_BYTES_WORD);

        let keccak_rand = challenges.keccak_input();

        let mut rpi_value_lc_cells: Vec<AssignedCell<F, F>> = vec![];
        let mut rpi_bytes_keccakrlc_cells: Vec<AssignedCell<F, F>> = vec![];
        let start_offset = *current_offset;

        let value_bytes_be: Vec<u8> = value_bytes_le.iter().rev().copied().collect_vec();
        let value_bytes_chunk: Vec<Vec<u8>> = value_bytes_be
            .rchunks(N_BYTES_HALF_WORD)
            // chunks will go from right to left first, here we reverse the order to assure left to
            // right
            .rev()
            .map(|x| x.to_vec())
            .collect();

        *current_offset = value_bytes_chunk.iter().try_fold(
            // after rchunk
            start_offset,
            |mut offset, bytes| -> Result<usize, Error> {
                bytes.iter().enumerate().try_fold(
                    Value::known(F::ZERO),
                    |rpi_value_lc, (i, byte)| -> Result<Value<F>, Error> {
                        // assign q_rpi_value_start when index match beginning of chunk size
                        region.assign_fixed(
                            || "q_rpi_value_start",
                            self.q_rpi_value_start,
                            offset,
                            || Value::known(if i == 0 { F::ONE } else { F::ZERO }),
                        )?;

                        let rpi_value_lc = if i == 0 {
                            Value::known(F::ZERO)
                        } else {
                            rpi_value_lc
                        }
                        .zip(Value::known(F::from(BYTE_POW_BASE)))
                        .and_then(|(acc, rand)| Value::known(acc * rand + F::from(*byte as u64)));

                        // assign rpi_value_lc
                        let rpi_value_lc_cell = region.assign_advice(
                            || "rpi_value_lc",
                            self.rpi_value_lc,
                            offset,
                            || rpi_value_lc,
                        )?;

                        // for rpi_value_lc_cell, it accumulated per N_BYTES_HALF_WORD chunk size,
                        // and the remains
                        if i == bytes.len() - 1 {
                            rpi_value_lc_cells.push(rpi_value_lc_cell);
                        }

                        rpi_bytes[offset] = *byte;

                        // this is mutable for accumulated across value
                        *rpi_bytes_keccakrlc =
                            rpi_bytes_keccakrlc
                                .zip(keccak_rand)
                                .and_then(|(acc, rand)| {
                                    Value::known(acc * rand + F::from(*byte as u64))
                                });

                        // enable
                        self.q_rpi_byte_enable.enable(region, offset)?;

                        // assign rpi bytes
                        region.assign_advice(
                            || "rpi_bytes",
                            self.rpi_bytes,
                            offset,
                            || Value::known(F::from(*byte as u64)),
                        )?;

                        // assign rpi_bytes_keccakrlc
                        let rpi_bytes_keccakrlc_cell = region.assign_advice(
                            || "rpi_bytes_keccakrlc",
                            self.rpi_bytes_keccakrlc,
                            offset,
                            || *rpi_bytes_keccakrlc,
                        )?;

                        if start_offset - offset == value_bytes_le.len() - 1 {
                            rpi_bytes_keccakrlc_cells.push(rpi_bytes_keccakrlc_cell);
                        }

                        offset = offset.saturating_sub(1);

                        Ok(rpi_value_lc)
                    },
                )?;
                Ok(offset)
            },
        )?;

        assert!(rpi_value_lc_cells.len() <= 2); // at most hi, lo 2 cells
        rpi_value_lc_cells.reverse(); // reverse to lo, hi order
        assert!(rpi_bytes_keccakrlc_cells.len() == 1); // keccak rlc only 1 cell

        Ok((
            rpi_bytes_keccakrlc_cells[0].clone(),
            Word::new(
                (0..2) // padding rpi_value_lc_cells to 2 limbs if less then 2
                    .map(|i| rpi_value_lc_cells.get(i).unwrap_or(&zero_cell).clone())
                    .collect_vec()
                    .try_into()
                    .unwrap(),
            ),
        ))
    }

    /// Assigns the values for block table in the block_table column
    /// and rpi_bytes columns. Copy constraints will be enable
    /// to assure block_table value cell equal with respective rpi_byte_rlc cell
    #[allow(clippy::too_many_arguments)]
    fn assign_block_table(
        &self,
        region: &mut Region<'_, F>,
        block_table_offset: &mut usize,
        block_values: BlockValues,
        rpi_bytes_keccakrlc: &mut Value<F>,
        challenges: &Challenges<Value<F>>,
        current_offset: &mut usize,
        rpi_bytes: &mut [u8],
        zero_cell: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        let mut block_copy_cells = vec![];

        // coinbase
        let block_value = Word::from(block_values.coinbase)
            .into_value()
            .assign_advice(
                region,
                || "coinbase",
                self.block_table.value,
                *block_table_offset,
            )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values
                .coinbase
                .to_fixed_bytes()
                .iter()
                .rev()
                .copied()
                .collect_vec(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        // gas_limit
        let block_value = Word::from(block_values.gas_limit)
            .into_value()
            .assign_advice(
                region,
                || "gas_limit",
                self.block_table.value,
                *block_table_offset,
            )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values.gas_limit.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        // number
        let block_value = Word::from(block_values.number).into_value().assign_advice(
            region,
            || "number",
            self.block_table.value,
            *block_table_offset,
        )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values.number.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        // timestamp
        let block_value = Word::from(block_values.timestamp)
            .into_value()
            .assign_advice(
                region,
                || "timestamp",
                self.block_table.value,
                *block_table_offset,
            )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values.timestamp.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        // difficulty
        let block_value = Word::from(block_values.difficulty)
            .into_value()
            .assign_advice(
                region,
                || "difficulty",
                self.block_table.value,
                *block_table_offset,
            )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values.difficulty.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        // base_fee
        let block_value = Word::from(block_values.base_fee)
            .into_value()
            .assign_advice(
                region,
                || "base_fee",
                self.block_table.value,
                *block_table_offset,
            )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values.base_fee.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        // chain_id
        let block_value = Word::from(block_values.chain_id)
            .into_value()
            .assign_advice(
                region,
                || "chain_id",
                self.block_table.value,
                *block_table_offset,
            )?;
        let (_, word) = self.assign_raw_bytes(
            region,
            &block_values.chain_id.to_le_bytes(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;
        block_copy_cells.push((block_value, word));
        *block_table_offset += 1;

        for prev_hash in block_values.history_hashes {
            let block_value = Word::from(prev_hash).into_value().assign_advice(
                region,
                || "prev_hash",
                self.block_table.value,
                *block_table_offset,
            )?;
            let (_, word) = self.assign_raw_bytes(
                region,
                &prev_hash
                    .to_fixed_bytes()
                    .iter()
                    .rev()
                    .copied()
                    .collect_vec(),
                rpi_bytes_keccakrlc,
                rpi_bytes,
                current_offset,
                challenges,
                zero_cell.clone(),
            )?;
            block_copy_cells.push((block_value, word));
            *block_table_offset += 1;
        }

        block_copy_cells.iter().try_for_each(|(left, right)| {
            region.constrain_equal(left.lo().cell(), right.lo().cell())?;
            region.constrain_equal(left.hi().cell(), right.hi().cell())?;
            Ok::<(), Error>(())
        })?;

        Ok(())
    }

    /// Assigns the extra fields (not in block or tx tables):
    ///   - block hash
    ///   - state root
    ///   - previous block state root
    /// to the rpi_byte column
    #[allow(clippy::too_many_arguments)]
    fn assign_extra_fields(
        &self,
        region: &mut Region<'_, F>,
        extra: ExtraValues,
        rpi_bytes_keccakrlc: &mut Value<F>,
        challenges: &Challenges<Value<F>>,
        current_offset: &mut usize,
        rpi_bytes: &mut [u8],
        zero_cell: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        // block hash
        self.assign_raw_bytes(
            region,
            &extra
                .block_hash
                .to_fixed_bytes()
                .iter()
                .copied()
                .rev()
                .collect_vec(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;

        // block state root
        self.assign_raw_bytes(
            region,
            &extra
                .state_root
                .to_fixed_bytes()
                .iter()
                .copied()
                .rev()
                .collect_vec(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell.clone(),
        )?;

        // previous block state root
        self.assign_raw_bytes(
            region,
            &extra
                .prev_state_root
                .to_fixed_bytes()
                .iter()
                .copied()
                .rev()
                .collect_vec(),
            rpi_bytes_keccakrlc,
            rpi_bytes,
            current_offset,
            challenges,
            zero_cell,
        )?;

        Ok(())
    }

    /// Assign digest word
    fn assign_rpi_digest_word(
        &self,
        region: &mut Region<'_, F>,
        digest_word: Word<F>,
    ) -> Result<Word<AssignedCell<F, F>>, Error> {
        let lo_assigned_cell = region.assign_advice(
            || "rpi_digest_bytes_limbs_lo",
            self.rpi_digest_bytes_limbs,
            0,
            || digest_word.into_value().lo(),
        )?;
        let hi_assigned_cell = region.assign_advice(
            || "rpi_digest_bytes_limbs_hi",
            self.rpi_digest_bytes_limbs,
            1,
            || digest_word.into_value().hi(),
        )?;
        Ok(Word::new([lo_assigned_cell, hi_assigned_cell]))
    }
}

/// Public Inputs Circuit
#[derive(Clone, Default, Debug)]
pub struct PiCircuit<F: Field> {
    max_txs: usize,
    max_calldata: usize,
    /// PublicInputs data known by the verifier
    pub public_data: PublicData,
    _marker: PhantomData<F>,
}

impl<F: Field> PiCircuit<F> {
    /// Creates a new PiCircuit
    pub fn new(max_txs: usize, max_calldata: usize, public_data: PublicData) -> Self {
        Self {
            max_txs,
            max_calldata,
            public_data,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> SubCircuit<F> for PiCircuit<F> {
    type Config = PiCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn new_from_block(block: &witness::Block<F>) -> Self {
        let public_data = public_data_convert(block);
        PiCircuit::new(
            block.circuits_params.max_txs,
            block.circuits_params.max_calldata,
            public_data,
        )
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        let calldata_len = block.txs.iter().map(|tx| tx.call_data.len()).sum();
        (
            Self::Config::circuit_len_by_txs_calldata(block.txs.len(), calldata_len),
            Self::Config::circuit_len_by_txs_calldata(
                block.circuits_params.max_txs,
                block.circuits_params.max_calldata,
            ),
        )
    }

    /// Compute the public inputs for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        let rpi_digest_byte_field = self
            .public_data
            .get_rpi_digest_word(self.max_txs, self.max_calldata);

        vec![vec![rpi_digest_byte_field.lo(), rpi_digest_byte_field.hi()]]
    }

    /// Make the assignments to the PiCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed u16 table",
            |mut region| {
                for i in 0..(1 << 16) {
                    region.assign_fixed(
                        || format!("row_{}", i),
                        config.fixed_u16,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }

                Ok(())
            },
        )?;
        let digest_word_assigned = layouter.assign_region(
            || "region 0",
            |mut region| {
                // Annotate columns

                config.tx_table.annotate_columns_in_region(&mut region);
                config.block_table.annotate_columns_in_region(&mut region);
                config.keccak_table.annotate_columns_in_region(&mut region);

                region.name_column(|| "q_rpi_value_start", config.q_rpi_value_start);
                region.name_column(|| "rpi_bytes", config.rpi_bytes);
                region.name_column(|| "rpi_bytes_keccakrlc", config.rpi_bytes_keccakrlc);
                region.name_column(|| "rpi_value_lc", config.rpi_value_lc);
                region.name_column(|| "q_digest_value_start", config.q_digest_value_start);
                region.name_column(|| "rpi_digest_bytes", config.rpi_digest_bytes);
                region.name_column(|| "rpi_digest_bytes_lc", config.rpi_digest_bytes_limbs);
                region.name_column(|| "tx_id_inv", config.tx_id_inv);
                region.name_column(|| "tx_value_lo_inv", config.tx_value_lo_inv);
                region.name_column(|| "tx_id_diff_inv", config.tx_id_diff_inv);

                region.name_column(|| "fixed_u16", config.fixed_u16);
                region.name_column(|| "calldata_gas_cost", config.calldata_gas_cost);
                region.name_column(|| "is_final", config.is_final);

                region.name_column(|| "Public_Inputs", config.pi_instance);

                let circuit_len = config.circuit_len();
                let mut rpi_bytes = vec![0u8; circuit_len];

                let mut rpi_bytes_keccakrlc = Value::known(F::ZERO);

                // traverse reversely of the region
                let mut current_offset: usize = circuit_len - 1;
                let start_offset = current_offset;

                config.q_digest_last.enable(&mut region, N_BYTES_WORD - 1)?; // digest is 32 bytes
                config.q_bytes_last.enable(&mut region, start_offset)?;

                // assign last + 1 to 0 to as wordaround to skip CellNotAssigned Error from
                // Mock_prover
                config.reset_rpi_bytes_row(&mut region, start_offset + 1)?;
                config.reset_rpi_digest_row(&mut region, N_BYTES_WORD)?;

                // Assign block table
                let block_values = self.public_data.get_block_table_values();
                let mut block_table_offset = 0;

                // assign empty row in block table
                let zero_word = Word::default().into_value().assign_advice(
                    &mut region,
                    || "zero",
                    config.block_table.value,
                    block_table_offset,
                )?;
                let zero_cell = zero_word.hi();
                let (_, _) = config.assign_raw_bytes(
                    &mut region,
                    &0u8.to_le_bytes(),
                    &mut rpi_bytes_keccakrlc,
                    &mut rpi_bytes,
                    &mut current_offset,
                    challenges,
                    zero_cell.clone(),
                )?;
                block_table_offset += 1;
                config.assign_block_table(
                    &mut region,
                    &mut block_table_offset,
                    block_values,
                    &mut rpi_bytes_keccakrlc,
                    challenges,
                    &mut current_offset,
                    &mut rpi_bytes,
                    zero_cell.clone(),
                )?;
                assert_eq!(start_offset - current_offset, N_BYTES_ONE + N_BYTES_BLOCK);

                // Assign extra fields
                let extra_vals = self.public_data.get_extra_values();
                config.assign_extra_fields(
                    &mut region,
                    extra_vals,
                    &mut rpi_bytes_keccakrlc,
                    challenges,
                    &mut current_offset,
                    &mut rpi_bytes,
                    zero_cell,
                )?;
                assert_eq!(
                    start_offset - current_offset,
                    N_BYTES_ONE + N_BYTES_BLOCK + N_BYTES_EXTRA_VALUE
                );

                let mut tx_table_offset = 0;
                // Assign Tx table
                let txs = self.public_data.get_tx_table_values();
                assert!(txs.len() <= config.max_txs);
                let tx_default = TxValues::default();

                // Add empty row
                // assign first tx_value empty row, and to obtain zero cell via hi() part.
                // we use hi() part to copy-constrains other tx_table value `hi` cells.
                let zero_cell = Word::default()
                    .into_value()
                    .assign_advice(&mut region, || "tx_value", config.tx_table.value, 0)?
                    .hi();
                config.assign_tx_row(
                    &mut region,
                    tx_table_offset,
                    0u64,
                    TxFieldTag::Null,
                    0u64,
                    &[0u8; 1],
                    &mut rpi_bytes_keccakrlc,
                    challenges,
                    &mut current_offset,
                    &mut rpi_bytes,
                    zero_cell.clone(),
                )?;
                tx_table_offset += 1;

                iter::empty()
                    .chain(&txs)
                    .chain((0..(config.max_txs - txs.len())).map(|_| &tx_default))
                    .enumerate()
                    .try_for_each(|(i, tx)| -> Result<(), Error> {
                        for (tag, value_bytes) in &[
                            (TxFieldTag::Nonce, tx.nonce.to_le_bytes().to_vec()),
                            (TxFieldTag::Gas, tx.gas_limit.to_le_bytes().to_vec()),
                            (TxFieldTag::GasPrice, tx.gas_price.to_le_bytes().to_vec()),
                            (
                                TxFieldTag::CallerAddress,
                                tx.from_addr
                                    .as_fixed_bytes()
                                    .iter()
                                    .copied()
                                    .rev()
                                    .collect_vec(),
                            ),
                            (
                                TxFieldTag::CalleeAddress,
                                tx.to_addr
                                    .as_fixed_bytes()
                                    .iter()
                                    .copied()
                                    .rev()
                                    .collect_vec(),
                            ),
                            (TxFieldTag::IsCreate, tx.is_create.to_le_bytes().to_vec()),
                            (TxFieldTag::TxInvalid, tx.invalid_tx.to_le_bytes().to_vec()),
                            (
                                TxFieldTag::AccessListGasCost,
                                tx.access_list_gas_cost.to_le_bytes().to_vec(),
                            ),
                            (TxFieldTag::Value, tx.value.to_le_bytes().to_vec()),
                            (
                                TxFieldTag::CallDataLength,
                                tx.call_data_len.to_le_bytes().to_vec(),
                            ),
                            (
                                TxFieldTag::CallDataGasCost,
                                tx.call_data_gas_cost.to_le_bytes().to_vec(),
                            ),
                            // TODO witness tx.tx_sign_hash
                            (TxFieldTag::TxSignHash, tx.tx_sign_hash.to_vec()),
                        ] {
                            let i: u64 = i.try_into().unwrap();
                            // assign tx field
                            config.assign_tx_row(
                                &mut region,
                                tx_table_offset,
                                i + 1,
                                *tag,
                                0,
                                value_bytes,
                                &mut rpi_bytes_keccakrlc,
                                challenges,
                                &mut current_offset,
                                &mut rpi_bytes,
                                zero_cell.clone(),
                            )?;
                            tx_table_offset += 1;
                        }
                        Ok(())
                    })?;
                assert_eq!(
                    start_offset - current_offset,
                    N_BYTES_ONE
                        + N_BYTES_BLOCK
                        + N_BYTES_EXTRA_VALUE
                        + Self::Config::circuit_len_tx_id(config.max_txs)
                        + Self::Config::circuit_len_tx_index(config.max_txs)
                        + Self::Config::circuit_len_tx_values(config.max_txs)
                );

                // Tx Table CallData
                let mut calldata_count = 0;
                config
                    .q_calldata_start
                    .enable(&mut region, tx_table_offset)?;

                let mut call_data_offset = TX_LEN * self.max_txs + EMPTY_TX_ROW_COUNT;

                let txs = self.public_data.transactions.clone();
                for (i, tx) in self.public_data.transactions.iter().enumerate() {
                    let call_data_length = tx.call_data.0.len();
                    let mut gas_cost = F::ZERO;
                    for (index, byte) in tx.call_data.0.iter().enumerate() {
                        assert!(calldata_count < config.max_calldata);
                        let is_final = index == call_data_length - 1;
                        gas_cost += if *byte == 0 {
                            F::from(ZERO_BYTE_GAS_COST)
                        } else {
                            F::from(NONZERO_BYTE_GAS_COST)
                        };
                        let tx_id_next = if is_final {
                            let mut j = i + 1;
                            while j < txs.len() && txs[j].call_data.0.is_empty() {
                                j += 1;
                            }
                            if j >= txs.len() {
                                0
                            } else {
                                j + 1
                            }
                        } else {
                            i + 1
                        };

                        config.assign_tx_calldata_row(
                            &mut region,
                            call_data_offset,
                            i + 1,
                            tx_id_next,
                            index,
                            *byte,
                            &mut rpi_bytes_keccakrlc,
                            challenges,
                            &mut current_offset,
                            &mut rpi_bytes,
                            is_final,
                            gas_cost,
                            zero_cell.clone(),
                        )?;
                        call_data_offset += 1;
                        calldata_count += 1;
                    }
                }

                for _ in calldata_count..config.max_calldata {
                    config.assign_tx_calldata_row(
                        &mut region,
                        call_data_offset,
                        0, // tx_id
                        0,
                        0,
                        0u8,
                        &mut rpi_bytes_keccakrlc,
                        challenges,
                        &mut current_offset,
                        &mut rpi_bytes,
                        false,
                        F::ZERO,
                        zero_cell.clone(),
                    )?;
                    call_data_offset += 1;
                }
                assert_eq!(current_offset, 0);

                // assign keccak digest
                let digest_word = self
                    .public_data
                    .get_rpi_digest_word::<F>(config.max_txs, config.max_calldata);

                let digest_word_assigned =
                    config.assign_rpi_digest_word(&mut region, digest_word)?;

                // lookup assignment
                // also assign empty to last of TxTable
                config.assign_empty_txtable_row(&mut region, call_data_offset)?;

                // keccak lookup occur on offset 0
                config.q_rpi_keccak_lookup.enable(&mut region, 0)?;

                Ok(digest_word_assigned)
            },
        )?;

        // Constrain raw_public_input cells to public inputs

        layouter.constrain_instance(digest_word_assigned.lo().cell(), config.pi_instance, 0)?;
        layouter.constrain_instance(digest_word_assigned.hi().cell(), config.pi_instance, 1)?;

        Ok(())
    }
}

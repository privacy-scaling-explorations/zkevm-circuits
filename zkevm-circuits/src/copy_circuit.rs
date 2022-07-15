//! The Copy circuit implements constraints and lookups for read-write steps for
//! copied bytes while execution opcodes such as CALLDATACOPY, CODECOPY, LOGS,
//! etc.

use bus_mapping::circuit_input_builder::{CopyDataType, CopyEvent, CopyStep, NumberOrHash};
use eth_types::{Field, ToAddress, ToScalar, U256};
use gadgets::{
    binary_number::{BinaryNumberChip, BinaryNumberConfig},
    less_than::{LtChip, LtConfig, LtInstruction},
    util::{and, not, or, Expr},
};
use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};

use crate::evm_circuit::{
    table::{BytecodeFieldTag, LookupTable, RwTableTag, TxContextFieldTag, TxLogFieldTag},
    util::{constraint_builder::BaseConstraintBuilder, RandomLinearCombination},
    witness::Block,
};

/// The rw table shared between evm circuit and state circuit
#[derive(Clone, Copy, Debug)]
pub struct CopyCircuit<F> {
    /// Whether the row is enabled or not.
    pub q_enable: Column<Fixed>,
    /// Whether this row denotes a step. A read row is a step and a write row is
    /// not.
    pub q_step: Selector,
    /// Whether the row is the first read-write pair for a copy event.
    pub is_first: Column<Advice>,
    /// Whether the row is the last read-write pair for a copy event.
    pub is_last: Column<Advice>,
    /// The relevant ID for the read-write row, represented as a random linear
    /// combination. The ID may be one of the below:
    /// 1. Call ID/Caller ID for CopyDataType::Memory
    /// 2. RLC encoding of bytecode hash for CopyDataType::Bytecode
    /// 3. Transaction ID for CopyDataType::TxCalldata, CopyDataType::TxLog
    pub id: Column<Advice>,
    /// The source/destination address for this copy step.
    pub addr: Column<Advice>,
    /// The end of the source buffer for the copy event.
    pub src_addr_end: Column<Advice>,
    /// The number of bytes left to be copied.
    pub bytes_left: Column<Advice>,
    /// The value copied in this copy step.
    pub value: Column<Advice>,
    /// In case of a bytecode tag, this denotes whether or not the copied byte
    /// is an opcode or push data byte.
    pub is_code: Column<Advice>,
    /// Whether the row is padding.
    pub is_pad: Column<Advice>,
    /// The associated read-write counter for this row.
    pub rw_counter: Column<Advice>,
    /// Decrementing counter denoting reverse read-write counter.
    pub rwc_inc_left: Column<Advice>,
    /// Binary chip to constrain the copy table conditionally depending on the
    /// current row's tag, whether it is Bytecode, Memory, TxCalldata or
    /// TxLog.
    pub tag: BinaryNumberConfig<CopyDataType, 3>,
    /// Lt chip to check: src_addr < src_addr_end.
    /// Since `src_addr` and `src_addr_end` are u64, 8 bytes are sufficient for
    /// the Lt chip.
    pub addr_lt_addr_end: LtConfig<F, 8>,
}

impl<F: Field> LookupTable<F> for CopyCircuit<F> {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.is_first, Rotation::cur()),
            meta.query_advice(self.id, Rotation::cur()), // src_id
            self.tag.value(Rotation::cur())(meta),       // src_tag
            meta.query_advice(self.id, Rotation::next()), // dst_id
            self.tag.value(Rotation::next())(meta),      // dst_tag
            meta.query_advice(self.addr, Rotation::cur()), // src_addr
            meta.query_advice(self.src_addr_end, Rotation::cur()), // src_addr_end
            meta.query_advice(self.addr, Rotation::next()), // dst_addr
            meta.query_advice(self.bytes_left, Rotation::cur()), // length
            meta.query_advice(self.rw_counter, Rotation::cur()), // rw_counter
            meta.query_advice(self.rwc_inc_left, Rotation::cur()), // rwc_inc_left
        ]
    }
}

impl<F: Field> CopyCircuit<F> {
    /// Configure the Copy Circuit constraining read-write steps and doing
    /// appropriate lookups to the Tx Table, RW Table and Bytecode Table.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        tx_table: &dyn LookupTable<F>,
        rw_table: &dyn LookupTable<F>,
        bytecode_table: &dyn LookupTable<F>,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_step = meta.complex_selector();
        let is_first = meta.advice_column();
        let is_last = meta.advice_column();
        let id = meta.advice_column();
        let addr = meta.advice_column();
        let src_addr_end = meta.advice_column();
        let bytes_left = meta.advice_column();
        let value = meta.advice_column();
        let is_code = meta.advice_column();
        let is_pad = meta.advice_column();
        let rw_counter = meta.advice_column();
        let rwc_inc_left = meta.advice_column();

        let tag = BinaryNumberChip::configure(meta, q_enable);

        let addr_lt_addr_end = LtChip::configure(
            meta,
            |meta| meta.query_selector(q_step),
            |meta| meta.query_advice(addr, Rotation::cur()),
            |meta| meta.query_advice(src_addr_end, Rotation::cur()),
        );

        meta.create_gate("verify row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean(
                "is_first is boolean",
                meta.query_advice(is_first, Rotation::cur()),
            );
            cb.require_boolean(
                "is_last is boolean",
                meta.query_advice(is_last, Rotation::cur()),
            );
            cb.require_zero(
                "is_first == 0 when q_step == 0",
                and::expr([
                    not::expr(meta.query_selector(q_step)),
                    meta.query_advice(is_first, Rotation::cur()),
                ]),
            );
            cb.require_zero(
                "is_last == 0 when q_step == 1",
                and::expr([
                    meta.query_advice(is_last, Rotation::cur()),
                    meta.query_selector(q_step),
                ]),
            );

            let not_last_two_rows = 1.expr()
                - meta.query_advice(is_last, Rotation::cur())
                - meta.query_advice(is_last, Rotation::next());
            cb.condition(not_last_two_rows, |cb| {
                cb.require_equal(
                    "rows[0].id == rows[2].id",
                    meta.query_advice(id, Rotation::cur()),
                    meta.query_advice(id, Rotation(2)),
                );
                cb.require_equal(
                    "rows[0].tag == rows[2].tag",
                    tag.value(Rotation::cur())(meta),
                    tag.value(Rotation(2))(meta),
                );
                cb.require_equal(
                    "rows[0].addr + 1 == rows[2].addr",
                    meta.query_advice(addr, Rotation::cur()) + 1.expr(),
                    meta.query_advice(addr, Rotation(2)),
                );
                cb.require_equal(
                    "rows[0].src_addr_end == rows[2].src_addr_end for non-last step",
                    meta.query_advice(src_addr_end, Rotation::cur()),
                    meta.query_advice(src_addr_end, Rotation(2)),
                );
            });

            let rw_diff = and::expr([
                or::expr([
                    tag.value_equals(CopyDataType::Memory, Rotation::cur())(meta),
                    tag.value_equals(CopyDataType::TxLog, Rotation::cur())(meta),
                ]),
                not::expr(meta.query_advice(is_pad, Rotation::cur())),
            ]);
            cb.condition(
                not::expr(meta.query_advice(is_last, Rotation::cur())),
                |cb| {
                    cb.require_equal(
                        "rows[0].rw_counter + rw_diff == rows[1].rw_counter",
                        meta.query_advice(rw_counter, Rotation::cur()) + rw_diff.clone(),
                        meta.query_advice(rw_counter, Rotation::next()),
                    );
                    cb.require_equal(
                        "rows[0].rwc_inc_left - rw_diff == rows[1].rwc_inc_left",
                        meta.query_advice(rwc_inc_left, Rotation::cur()) - rw_diff.clone(),
                        meta.query_advice(rwc_inc_left, Rotation::next()),
                    );
                },
            );
            cb.condition(meta.query_advice(is_last, Rotation::cur()), |cb| {
                cb.require_equal(
                    "rwc_inc_left == rw_diff for last row in the copy slot",
                    meta.query_advice(rwc_inc_left, Rotation::cur()),
                    rw_diff,
                );
            });

            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("verify step", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "bytes_left == 1 for last step",
                and::expr([
                    meta.query_advice(is_last, Rotation::next()),
                    1.expr() - meta.query_advice(bytes_left, Rotation::cur()),
                ]),
            );
            cb.condition(
                not::expr(meta.query_advice(is_last, Rotation::next())),
                |cb| {
                    cb.require_equal(
                        "bytes_left == bytes_left_next + 1 for non-last step",
                        meta.query_advice(bytes_left, Rotation::cur()),
                        meta.query_advice(bytes_left, Rotation(2)) + 1.expr(),
                    );
                },
            );
            cb.require_equal(
                "write value == read value",
                meta.query_advice(value, Rotation::cur()),
                meta.query_advice(value, Rotation::next()),
            );
            cb.require_zero(
                "value == 0 when is_pad == 1 for read",
                and::expr([
                    meta.query_advice(is_pad, Rotation::cur()),
                    meta.query_advice(value, Rotation::cur()),
                ]),
            );
            cb.require_equal(
                "is_pad == 1 - (src_addr < src_addr_end) for read row",
                1.expr() - addr_lt_addr_end.is_lt(meta, None),
                meta.query_advice(is_pad, Rotation::cur()),
            );
            cb.require_zero(
                "is_pad == 0 for write row",
                meta.query_advice(is_pad, Rotation::next()),
            );

            cb.gate(meta.query_selector(q_step))
        });

        meta.lookup_any("Memory lookup", |meta| {
            let cond = meta.query_fixed(q_enable, Rotation::cur())
                * tag.value_equals(CopyDataType::Memory, Rotation::cur())(meta)
                * not::expr(meta.query_advice(is_pad, Rotation::cur()));
            vec![
                meta.query_advice(rw_counter, Rotation::cur()),
                not::expr(meta.query_selector(q_step)),
                RwTableTag::Memory.expr(),
                meta.query_advice(id, Rotation::cur()), // call_id
                meta.query_advice(addr, Rotation::cur()), // memory address
                0.expr(),
                0.expr(),
                meta.query_advice(value, Rotation::cur()),
                0.expr(),
                0.expr(),
                0.expr(),
            ]
            .into_iter()
            .zip(rw_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (cond.clone() * arg, table))
            .collect()
        });

        meta.lookup_any("TxLog lookup", |meta| {
            let cond = meta.query_fixed(q_enable, Rotation::cur())
                * tag.value_equals(CopyDataType::TxLog, Rotation::cur())(meta);
            vec![
                meta.query_advice(rw_counter, Rotation::cur()),
                1.expr(),
                RwTableTag::TxLog.expr(),
                meta.query_advice(id, Rotation::cur()), // tx_id
                meta.query_advice(addr, Rotation::cur()), // byte_index || field_tag || log_id
                0.expr(),
                0.expr(),
                meta.query_advice(value, Rotation::cur()),
                0.expr(),
                0.expr(),
                0.expr(),
            ]
            .into_iter()
            .zip(rw_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (cond.clone() * arg, table))
            .collect()
        });

        meta.lookup_any("Bytecode lookup", |meta| {
            let cond = meta.query_fixed(q_enable, Rotation::cur())
                * tag.value_equals(CopyDataType::Bytecode, Rotation::cur())(meta)
                * not::expr(meta.query_advice(is_pad, Rotation::cur()));
            vec![
                meta.query_advice(id, Rotation::cur()),
                BytecodeFieldTag::Byte.expr(),
                meta.query_advice(addr, Rotation::cur()),
                meta.query_advice(is_code, Rotation::cur()),
                meta.query_advice(value, Rotation::cur()),
            ]
            .into_iter()
            .zip(bytecode_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (cond.clone() * arg, table))
            .collect()
        });

        meta.lookup_any("Tx calldata lookup", |meta| {
            let cond = meta.query_fixed(q_enable, Rotation::cur())
                * tag.value_equals(CopyDataType::TxCalldata, Rotation::cur())(meta)
                * not::expr(meta.query_advice(is_pad, Rotation::cur()));
            vec![
                meta.query_advice(id, Rotation::cur()),
                TxContextFieldTag::CallData.expr(),
                meta.query_advice(addr, Rotation::cur()),
                meta.query_advice(value, Rotation::cur()),
            ]
            .into_iter()
            .zip(tx_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (cond.clone() * arg, table))
            .collect()
        });

        Self {
            q_enable,
            q_step,
            is_first,
            is_last,
            id,
            addr,
            src_addr_end,
            bytes_left,
            value,
            is_code,
            is_pad,
            rw_counter,
            rwc_inc_left,
            tag,
            addr_lt_addr_end,
        }
    }

    /// Assign a witness block to the Copy Circuit.
    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        let tag_chip = BinaryNumberChip::construct(self.tag);
        let lt_chip = LtChip::construct(self.addr_lt_addr_end);

        layouter.assign_region(
            || "assign copy table",
            |mut region| {
                let mut offset = 0;
                for copy_event in block.copy_events.values() {
                    for (step_idx, copy_step) in copy_event.steps.iter().enumerate() {
                        self.assign_step(
                            &mut region,
                            offset,
                            block.randomness,
                            copy_event,
                            step_idx,
                            copy_step,
                            &tag_chip,
                            &lt_chip,
                        )?;
                        offset += 1;
                    }
                }
                // pad two rows in the end to satisfy Halo2 cell assignment check
                for _ in 0..2 {
                    self.assign_padding_row(&mut region, offset, &tag_chip)?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_step(
        &self,
        region: &mut Region<F>,
        offset: usize,
        randomness: F,
        copy_event: &CopyEvent,
        step_idx: usize,
        copy_step: &CopyStep,
        tag_chip: &BinaryNumberChip<F, CopyDataType, 3>,
        lt_chip: &LtChip<F, 8>,
    ) -> Result<(), Error> {
        // q_enable
        region.assign_fixed(|| "q_enable", self.q_enable, offset, || Ok(F::one()))?;
        // enable q_step on the Read step
        if copy_step.rw.is_read() {
            self.q_step.enable(region, offset)?;
        }

        let id = if copy_step.rw.is_read() {
            &copy_event.src_id
        } else {
            &copy_event.dst_id
        };
        let bytes_left = copy_event.length - step_idx as u64 / 2;

        // is_first
        region.assign_advice(
            || format!("assign is_first {}", offset),
            self.is_first,
            offset,
            || Ok(if step_idx == 0 { F::one() } else { F::zero() }),
        )?;
        // is_last
        region.assign_advice(
            || format!("assign is_last {}", offset),
            self.is_last,
            offset,
            || {
                Ok(if step_idx == copy_event.steps.len() - 1 {
                    F::one()
                } else {
                    F::zero()
                })
            },
        )?;
        // id
        region.assign_advice(
            || format!("assign id {}", offset),
            self.id,
            offset,
            || {
                Ok(match id {
                    NumberOrHash::Number(n) => F::from(*n as u64),
                    NumberOrHash::Hash(h) => {
                        // since code hash in the bytecode table is represented in
                        // the little-endian form, we reverse the big-endian bytes
                        // of H256.
                        let le_bytes = {
                            let mut b = h.to_fixed_bytes();
                            b.reverse();
                            b
                        };
                        RandomLinearCombination::random_linear_combine(le_bytes, randomness)
                    }
                })
            },
        )?;
        // addr
        region.assign_advice(
            || format!("assign addr {}", offset),
            self.addr,
            offset,
            || {
                Ok(match copy_step.tag {
                    CopyDataType::TxLog => {
                        let addr = (U256::from(copy_step.addr)
                            + (U256::from(TxLogFieldTag::Data as u64) << 32)
                            + (U256::from(copy_event.log_id.unwrap()) << 48))
                            .to_address();
                        addr.to_scalar().unwrap()
                    }
                    _ => F::from(copy_step.addr),
                })
            },
        )?;
        // value
        region.assign_advice(
            || format!("assign value {}", offset),
            self.value,
            offset,
            || Ok(F::from(copy_step.value as u64)),
        )?;
        // is_code
        region.assign_advice(
            || format!("assign is_code {}", offset),
            self.is_code,
            offset,
            || Ok(copy_step.is_code.map_or(F::zero(), |v| F::from(v))),
        )?;
        // is_pad
        region.assign_advice(
            || format!("assign is_pad {}", offset),
            self.is_pad,
            offset,
            || Ok(F::from(copy_step.is_pad)),
        )?;
        // rw_counter
        region.assign_advice(
            || format!("assign rw_counter {}", offset),
            self.rw_counter,
            offset,
            || Ok(F::from(copy_step.rwc.0 as u64)),
        )?;
        // rwc_inc_left
        region.assign_advice(
            || format!("assign rwc_inc_left {}", offset),
            self.rwc_inc_left,
            offset,
            || Ok(F::from(copy_step.rwc_inc_left)),
        )?;
        // tag binary number chip
        tag_chip.assign(region, offset, &copy_step.tag)?;
        // assignment for read steps
        if copy_step.rw.is_read() {
            // src_addr_end
            region.assign_advice(
                || format!("assign src_addr_end {}", offset),
                self.src_addr_end,
                offset,
                || Ok(F::from(copy_event.src_addr_end)),
            )?;
            // bytes_left
            region.assign_advice(
                || format!("assign bytes_left {}", offset),
                self.bytes_left,
                offset,
                || Ok(F::from(bytes_left)),
            )?;
            // lt chip
            lt_chip.assign(
                region,
                offset,
                F::from(copy_step.addr),
                F::from(copy_event.src_addr_end),
            )?;
        }
        Ok(())
    }

    fn assign_padding_row(
        &self,
        region: &mut Region<F>,
        offset: usize,
        tag_chip: &BinaryNumberChip<F, CopyDataType, 3>,
    ) -> Result<(), Error> {
        // q_enable
        region.assign_fixed(|| "q_enable", self.q_enable, offset, || Ok(F::zero()))?;
        // is_first
        region.assign_advice(
            || format!("assign is_first {}", offset),
            self.is_first,
            offset,
            || Ok(F::zero()),
        )?;
        // is_last
        region.assign_advice(
            || format!("assign is_last {}", offset),
            self.is_last,
            offset,
            || Ok(F::zero()),
        )?;
        // id
        region.assign_advice(
            || format!("assign id {}", offset),
            self.id,
            offset,
            || Ok(F::zero()),
        )?;
        // addr
        region.assign_advice(
            || format!("assign addr {}", offset),
            self.addr,
            offset,
            || Ok(F::zero()),
        )?;
        // src_addr_end
        region.assign_advice(
            || format!("assign src_addr_end {}", offset),
            self.src_addr_end,
            offset,
            || Ok(F::zero()),
        )?;
        // bytes_left
        region.assign_advice(
            || format!("assign bytes_left {}", offset),
            self.bytes_left,
            offset,
            || Ok(F::zero()),
        )?;
        // value
        region.assign_advice(
            || format!("assign value {}", offset),
            self.value,
            offset,
            || Ok(F::zero()),
        )?;
        // is_code
        region.assign_advice(
            || format!("assign is_code {}", offset),
            self.is_code,
            offset,
            || Ok(F::zero()),
        )?;
        // is_pad
        region.assign_advice(
            || format!("assign is_pad {}", offset),
            self.is_pad,
            offset,
            || Ok(F::zero()),
        )?;
        // rw_counter
        region.assign_advice(
            || format!("assign rw_counter {}", offset),
            self.rw_counter,
            offset,
            || Ok(F::zero()),
        )?;
        // rwc_inc_left
        region.assign_advice(
            || format!("assign rwc_inc_left {}", offset),
            self.rwc_inc_left,
            offset,
            || Ok(F::zero()),
        )?;
        // tag
        tag_chip.assign(region, offset, &CopyDataType::default())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use bus_mapping::{
        circuit_input_builder::{CircuitInputBuilder, CopyDataType},
        mock::BlockData,
    };
    use eth_types::{bytecode, geth_types::GethData, Field, Word};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use itertools::Itertools;
    use mock::TestContext;
    use rand::{prelude::SliceRandom, Rng};

    use crate::{
        evm_circuit::witness::{block_convert, Block, Bytecode, RwMap, Transaction},
        rw_table::RwTable,
    };

    use super::CopyCircuit;

    #[derive(Clone)]
    struct MyConfig<F> {
        tx_table: [Column<Advice>; 4],
        rw_table: RwTable,
        bytecode_table: [Column<Advice>; 5],
        copy_table: CopyCircuit<F>,
    }

    impl<F: Field> MyConfig<F> {
        fn load_txs(
            &self,
            layouter: &mut impl Layouter<F>,
            txs: &[Transaction],
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "tx table",
                |mut region| {
                    let mut offset = 0;
                    for column in self.tx_table {
                        region.assign_advice(
                            || "tx table all-zero row",
                            column,
                            offset,
                            || Ok(F::zero()),
                        )?;
                    }
                    offset += 1;

                    for tx in txs.iter() {
                        for row in tx.table_assignments(randomness) {
                            for (column, value) in self.tx_table.iter().zip_eq(row) {
                                region.assign_advice(
                                    || format!("tx table row {}", offset),
                                    *column,
                                    offset,
                                    || Ok(value),
                                )?;
                            }
                            offset += 1;
                        }
                    }
                    Ok(())
                },
            )
        }

        fn load_rws(
            &self,
            layouter: &mut impl Layouter<F>,
            rws: &RwMap,
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "rw table",
                |mut region| {
                    let mut offset = 0;
                    self.rw_table
                        .assign(&mut region, offset, &Default::default())?;
                    offset += 1;

                    let mut rows = rws
                        .0
                        .values()
                        .flat_map(|rws| rws.iter())
                        .collect::<Vec<_>>();

                    rows.sort_by_key(|a| a.rw_counter());
                    let mut expected_rw_counter = 1;
                    for rw in rows {
                        assert!(rw.rw_counter() == expected_rw_counter);
                        expected_rw_counter += 1;

                        self.rw_table.assign(
                            &mut region,
                            offset,
                            &rw.table_assignment(randomness),
                        )?;
                        offset += 1;
                    }
                    Ok(())
                },
            )
        }

        fn load_bytecodes<'a>(
            &self,
            layouter: &mut impl Layouter<F>,
            bytecodes: impl IntoIterator<Item = &'a Bytecode> + Clone,
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "bytecode table",
                |mut region| {
                    let mut offset = 0;
                    for column in self.bytecode_table {
                        region.assign_advice(
                            || "bytecode table all-zero row",
                            column,
                            offset,
                            || Ok(F::zero()),
                        )?;
                    }
                    offset += 1;

                    for bytecode in bytecodes.clone() {
                        for row in bytecode.table_assignments(randomness) {
                            for (column, value) in self.bytecode_table.iter().zip_eq(row) {
                                region.assign_advice(
                                    || format!("bytecode table row {}", offset),
                                    *column,
                                    offset,
                                    || Ok(value),
                                )?;
                            }
                            offset += 1;
                        }
                    }
                    Ok(())
                },
            )
        }
    }

    #[derive(Default)]
    struct MyCircuit<F> {
        block: Block<F>,
    }

    impl<F> MyCircuit<F> {
        pub fn new(block: Block<F>) -> Self {
            Self { block }
        }
    }

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let tx_table = [(); 4].map(|_| meta.advice_column());
            let rw_table = RwTable::construct(meta);
            let bytecode_table = [(); 5].map(|_| meta.advice_column());
            let copy_table = CopyCircuit::configure(meta, &tx_table, &rw_table, &bytecode_table);

            MyConfig {
                tx_table,
                rw_table,
                bytecode_table,
                copy_table,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            config.load_txs(&mut layouter, &self.block.txs, self.block.randomness)?;
            config.load_rws(&mut layouter, &self.block.rws, self.block.randomness)?;
            config.load_bytecodes(
                &mut layouter,
                self.block.bytecodes.values(),
                self.block.randomness,
            )?;
            config.copy_table.assign_block(&mut layouter, &self.block)
        }
    }

    fn run_circuit<F: Field>(k: u32, block: Block<F>) -> Result<(), Vec<VerifyFailure>> {
        let circuit = MyCircuit::<F>::new(block);
        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        prover.verify()
    }

    fn gen_calldatacopy_data() -> CircuitInputBuilder {
        let code = bytecode! {
            PUSH32(Word::from(0x20))
            PUSH32(Word::from(0x00))
            PUSH32(Word::from(0x00))
            CALLDATACOPY
            STOP
        };
        let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
        let block: GethData = test_ctx.into();
        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        builder
    }

    fn gen_codecopy_data() -> CircuitInputBuilder {
        let code = bytecode! {
            PUSH32(Word::from(0x20))
            PUSH32(Word::from(0x00))
            PUSH32(Word::from(0x00))
            CODECOPY
            STOP
        };
        let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
        let block: GethData = test_ctx.into();
        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        builder
    }

    #[test]
    fn copy_circuit_valid_calldatacopy() {
        let builder = gen_calldatacopy_data();
        let block = block_convert(&builder.block, &builder.code_db);
        assert!(run_circuit(10, block).is_ok());
    }

    #[test]
    fn copy_circuit_valid_codecopy() {
        let builder = gen_codecopy_data();
        let block = block_convert(&builder.block, &builder.code_db);
        assert!(run_circuit(10, block).is_ok());
    }

    fn perturb_bytecode(block: &mut bus_mapping::circuit_input_builder::Block) {
        debug_assert!(!block.copy_events.is_empty());
        debug_assert!(!block.copy_events[0].steps.is_empty());

        let mut rng = rand::thread_rng();
        let idxs = block.copy_events[0]
            .steps
            .iter()
            .enumerate()
            .filter(|(_i, step)| step.tag == CopyDataType::Bytecode)
            .map(|(i, _step)| i)
            .collect::<Vec<usize>>();
        let rand_idx = idxs.choose(&mut rng).unwrap();
        block.copy_events[0].steps[*rand_idx].value = rng.gen();
    }

    fn perturb_memory(block: &mut bus_mapping::circuit_input_builder::Block) {
        debug_assert!(!block.copy_events.is_empty());
        debug_assert!(!block.copy_events[0].steps.is_empty());

        let mut rng = rand::thread_rng();
        let idxs = block.copy_events[0]
            .steps
            .iter()
            .enumerate()
            .filter(|(_i, step)| step.tag == CopyDataType::Memory)
            .map(|(i, _step)| i)
            .collect::<Vec<usize>>();
        let rand_idx = idxs.choose(&mut rng).unwrap();
        block.copy_events[0].steps[*rand_idx].value = rng.gen();
    }

    fn perturb_txcalldata(block: &mut bus_mapping::circuit_input_builder::Block) {
        debug_assert!(!block.copy_events.is_empty());
        debug_assert!(!block.copy_events[0].steps.is_empty());

        let mut rng = rand::thread_rng();
        let idxs = block.copy_events[0]
            .steps
            .iter()
            .enumerate()
            .filter(|(_i, step)| step.tag == CopyDataType::TxCalldata)
            .map(|(i, _step)| i)
            .collect::<Vec<usize>>();
        let rand_idx = idxs.choose(&mut rng).unwrap();
        block.copy_events[0].steps[*rand_idx].value = rng.gen();
    }

    #[test]
    fn copy_circuit_invalid_calldatacopy() {
        let mut builder = gen_calldatacopy_data();
        match rand::thread_rng().gen_bool(0.5) {
            true => perturb_memory(&mut builder.block),
            false => perturb_txcalldata(&mut builder.block),
        }
        let block = block_convert(&builder.block, &builder.code_db);
        assert!(run_circuit(10, block).is_err());
    }

    #[test]
    fn copy_circuit_invalid_codecopy() {
        let mut builder = gen_codecopy_data();
        match rand::thread_rng().gen_bool(0.5) {
            true => perturb_memory(&mut builder.block),
            false => perturb_bytecode(&mut builder.block),
        }
        let block = block_convert(&builder.block, &builder.code_db);
        assert!(run_circuit(10, block).is_err());
    }
}

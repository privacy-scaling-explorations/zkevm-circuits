#![allow(missing_docs)]
use bus_mapping::{circuit_input_builder::CopyDataType, operation::RW};
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    less_than::{LtChip, LtConfig},
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};

use crate::{
    evm_circuit::{
        table::LookupTable,
        util::{and, constraint_builder::BaseConstraintBuilder, not, or, RandomLinearCombination},
        witness::Block,
    },
    util::{self, Expr},
};

impl<F: FieldExt> util::Expr<F> for CopyDataType {
    fn expr(&self) -> Expression<F> {
        Expression::Constant(F::from(*self as u64))
    }
}

/// The rw table shared between evm circuit and state circuit
#[derive(Clone, Debug)]
pub struct CopyTableConfig<F> {
    /// Whether this row denotes a step. A read row is a step and a write row is
    /// not.
    pub q_step: Selector,
    /// Whether the row is the first read-write pair for a copy event.
    pub q_first: Column<Advice>,
    /// Whether the row is the last read-write pair for a copy event.
    pub q_last: Column<Advice>,
    /// The relevant ID for the read-write row, represented as a random linear
    /// combination. The ID may be one of the below: 1. Call ID/Caller ID
    /// for CopyDataType::Memory 2. Bytecode hash for CopyDataType::Bytecode
    /// 3. Transaction ID for CopyDataType::TxCalldata
    /// 4. Log ID for CopyDataType::TxLog
    pub id: Column<Advice>,
    /// Log ID in case the row denotes a log write operation.
    pub log_id: Column<Advice>,
    /// The tag of the row, denoting the copy data type.
    pub tag: Column<Advice>,
    /// The source/destination address for this copy step.
    pub addr: Column<Advice>,
    /// The end of the source buffer for the copy event.
    pub addr_end: Column<Advice>,
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
    /// Helper field for checking whether the row is tagged
    /// CopyDataType::Bytecode.
    pub is_bytecode_inv: Column<Advice>,
    /// IsZeroConfig for checking if the row is tagged CopyDataType::Bytecode.
    pub is_bytecode: IsZeroConfig<F>,
    /// Helper field for checking whether the row is tagged
    /// CopyDataType::Memory.
    pub is_memory_inv: Column<Advice>,
    /// IsZeroConfig for checking if the row is tagged CopyDataType::Memory.
    pub is_memory: IsZeroConfig<F>,
    /// Helper field for checking whether the row is tagged
    /// CopyDataType::TxCalldata.
    pub is_tx_calldata_inv: Column<Advice>,
    /// IsZeroConfig for checking if the row is tagged CopyDataType::TxCalldata.
    pub is_tx_calldata: IsZeroConfig<F>,
    /// Helper field for checking whether the row is tagged CopyDataType::TxLog.
    pub is_tx_log_inv: Column<Advice>,
    /// IsZeroConfig for checking if the row is tagged CopyDataType::TxLog.
    pub is_tx_log: IsZeroConfig<F>,
    /// Lt chip to check: src_addr < src_addr_end.
    /// Since `src_addr` and `src_addr_end` are u64, 8 bytes are sufficient for
    /// the Lt chip.
    pub addr_lt_addr_end: LtConfig<F, 8>,
}

impl<F: FieldExt> LookupTable<F> for CopyTableConfig<F> {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.q_first, Rotation::cur()),
            meta.query_advice(self.id, Rotation::cur()),
            meta.query_advice(self.tag, Rotation::cur()),
            meta.query_advice(self.id, Rotation::next()),
            meta.query_advice(self.tag, Rotation::next()),
            meta.query_advice(self.addr, Rotation::cur()),
            meta.query_advice(self.addr_end, Rotation::cur()),
            meta.query_advice(self.addr, Rotation::next()),
            meta.query_advice(self.bytes_left, Rotation::cur()),
            meta.query_advice(self.rw_counter, Rotation::cur()),
            meta.query_advice(self.rwc_inc_left, Rotation::cur()),
            meta.query_advice(self.log_id, Rotation::next()),
        ]
    }
}

impl<F: FieldExt> CopyTableConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, fixed_table: &dyn LookupTable<F>) -> Self {
        let q_step = meta.complex_selector();
        let q_first = meta.advice_column();
        let q_last = meta.advice_column();
        let id = meta.advice_column();
        let log_id = meta.advice_column();
        let tag = meta.advice_column();
        let addr = meta.advice_column();
        let addr_end = meta.advice_column();
        let bytes_left = meta.advice_column();
        let value = meta.advice_column();
        let is_code = meta.advice_column();
        let is_pad = meta.advice_column();
        let rw_counter = meta.advice_column();
        let rwc_inc_left = meta.advice_column();

        let is_bytecode_inv = meta.advice_column();
        let is_memory_inv = meta.advice_column();
        let is_tx_calldata_inv = meta.advice_column();
        let is_tx_log_inv = meta.advice_column();

        let is_bytecode = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - CopyDataType::Bytecode.expr(),
            is_memory_inv,
        );
        let is_memory = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - CopyDataType::Memory.expr(),
            is_memory_inv,
        );
        let is_tx_calldata = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - CopyDataType::TxCalldata.expr(),
            is_memory_inv,
        );
        let is_tx_log = IsZeroChip::configure(
            meta,
            |_| 1.expr(),
            |meta| meta.query_advice(tag, Rotation::cur()) - CopyDataType::TxLog.expr(),
            is_memory_inv,
        );

        let addr_lt_addr_end = LtChip::configure(
            meta,
            |_meta| 1.expr(),
            |meta| meta.query_advice(addr, Rotation::cur()),
            |meta| meta.query_advice(addr_end, Rotation::cur()),
        );

        meta.create_gate("verify row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean("q_step == 0 || q_step == 1", meta.query_selector(q_step));
            cb.require_boolean(
                "q_first == 0 || q_first == 1",
                meta.query_advice(q_first, Rotation::cur()),
            );
            cb.require_boolean(
                "q_last == 0 || q_last == 1",
                meta.query_advice(q_last, Rotation::cur()),
            );
            cb.require_zero(
                "q_first == 0 when q_step == 0",
                and::expr([
                    1.expr() - meta.query_selector(q_step),
                    meta.query_advice(q_first, Rotation::cur()),
                ]),
            );
            cb.require_zero(
                "q_last == 0 when q_step == 1",
                and::expr([
                    meta.query_advice(q_last, Rotation::cur()),
                    meta.query_selector(q_step),
                ]),
            );

            cb.condition(
                not::expr(or::expr([
                    meta.query_advice(q_last, Rotation::cur()),
                    meta.query_advice(q_last, Rotation::next()),
                ])),
                |cb| {
                    cb.require_equal(
                        "rows[0].id == rows[2].id",
                        meta.query_advice(id, Rotation::cur()),
                        meta.query_advice(id, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].log_id == rows[2].log_id",
                        meta.query_advice(log_id, Rotation::cur()),
                        meta.query_advice(log_id, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].tag == rows[2].tag",
                        meta.query_advice(tag, Rotation::cur()),
                        meta.query_advice(tag, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].addr + 1 == rows[2].addr",
                        meta.query_advice(addr, Rotation::cur()) + 1.expr(),
                        meta.query_advice(addr, Rotation(2)),
                    );
                    cb.require_equal(
                        "rows[0].addr_end == rows[2].addr_end",
                        meta.query_advice(addr_end, Rotation::cur()),
                        meta.query_advice(addr_end, Rotation(2)),
                    );
                },
            );

            let rw_diff = and::expr([
                not::expr(meta.query_advice(is_pad, Rotation::cur())),
                not::expr(is_memory.is_zero_expression.clone())
                    + not::expr(is_tx_log.is_zero_expression.clone()),
            ]);
            cb.condition(
                not::expr(meta.query_advice(q_last, Rotation::cur())),
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
            cb.condition(meta.query_advice(q_last, Rotation::cur()), |cb| {
                cb.require_equal(
                    "rwc_inc_left == 1 for last row in the copy slot",
                    meta.query_advice(rwc_inc_left, Rotation::cur()),
                    rw_diff,
                );
            });

            cb.gate(not::expr(meta.query_advice(is_pad, Rotation::cur())))
        });

        meta.create_gate("verify step", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "bytes_left == 1 for last step",
                and::expr([
                    meta.query_advice(q_last, Rotation::next()),
                    1.expr() - meta.query_advice(bytes_left, Rotation::cur()),
                ]),
            );
            cb.require_zero(
                "bytes_left == bytes_left_next + 1 for non-last step",
                and::expr([
                    1.expr() - meta.query_advice(q_last, Rotation::next()),
                    meta.query_advice(bytes_left, Rotation::cur())
                        - meta.query_advice(bytes_left, Rotation(2))
                        - 1.expr(),
                ]),
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

        // TODO(rohit): fixed lookup to copy pairs.

        Self {
            q_step,
            q_first,
            q_last,
            id,
            log_id,
            tag,
            addr,
            addr_end,
            bytes_left,
            value,
            is_code,
            is_pad,
            rw_counter,
            rwc_inc_left,

            is_memory_inv,
            is_bytecode_inv,
            is_tx_calldata_inv,
            is_tx_log_inv,

            is_memory,
            is_bytecode,
            is_tx_calldata,
            is_tx_log,

            addr_lt_addr_end,
        }
    }

    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        let is_bytecode_chip = IsZeroChip::construct(self.is_bytecode.clone());
        let is_memory_chip = IsZeroChip::construct(self.is_memory.clone());
        let is_tx_calldata_chip = IsZeroChip::construct(self.is_tx_calldata.clone());
        let is_tx_log_chip = IsZeroChip::construct(self.is_tx_log.clone());

        layouter.assign_region(
            || "assign copy table",
            |mut region| {
                let mut offset = 0;
                for copy_event in block.copy_events.iter() {
                    for (step_count, copy_rw_pair) in copy_event.steps.chunks(2).enumerate() {
                        debug_assert_eq!(
                            copy_rw_pair.len(),
                            2,
                            "copy read-write pair of len: {}",
                            copy_rw_pair.len()
                        );

                        // Read row
                        let read_row = copy_rw_pair.get(0).cloned().unwrap();
                        debug_assert_eq!(
                            read_row.rw,
                            RW::READ,
                            "expected read row to be RW::READ",
                        );
                        // q_step enabled.
                        self.q_step.enable(&mut region, 2 * offset)?;
                        // q_first
                        region.assign_advice(
                            || format!("assign q_first {}", offset),
                            self.q_first,
                            offset,
                            || Ok(if step_count == 0 { F::one() } else { F::zero() }),
                        )?;
                        // q_last
                        region.assign_advice(
                            || format!("assign q_last {}", offset),
                            self.q_last,
                            offset,
                            || Ok(F::zero()),
                        )?;
                        // id
                        region.assign_advice(
                            || format!("assign id {}", offset),
                            self.id,
                            offset,
                            || {
                                Ok(RandomLinearCombination::random_linear_combine(
                                    copy_event.src_id.bytes(),
                                    block.randomness,
                                ))
                            },
                        )?;
                        // log_id
                        region.assign_advice(
                            || format!("assign log_id {}", offset),
                            self.log_id,
                            offset,
                            // read row does not have a log ID since TxLog can only be on the write
                            // side.
                            || Ok(F::zero()),
                        )?;
                        // tag
                        region.assign_advice(
                            || format!("assign tag {}", offset),
                            self.tag,
                            offset,
                            || Ok(F::from(read_row.tag as u64)),
                        )?;
                        // addr
                        region.assign_advice(
                            || format!("assign addr {}", offset),
                            self.addr,
                            offset,
                            || Ok(F::from(read_row.addr)),
                        )?;
                        // addr_end
                        region.assign_advice(
                            || format!("assign addr_end {}", offset),
                            self.addr_end,
                            offset,
                            || Ok(read_row.addr_end.map_or(F::zero(), |v| F::from(v))),
                        )?;
                        // bytes_left
                        region.assign_advice(
                            || format!("assign bytes_left {}", offset),
                            self.bytes_left,
                            offset,
                            || Ok(F::from(copy_event.length - step_count as u64)),
                        )?;
                        // value
                        region.assign_advice(
                            || format!("assign value {}", offset),
                            self.value,
                            offset,
                            || Ok(F::from(read_row.value as u64)),
                        )?;
                        // is_code
                        region.assign_advice(
                            || format!("assign is_code {}", offset),
                            self.is_code,
                            offset,
                            || Ok(read_row.is_code.map_or(F::zero(), |v| F::from(v))),
                        )?;
                        // is_pad
                        region.assign_advice(
                            || format!("assign is_pad {}", offset),
                            self.is_pad,
                            offset,
                            || Ok(F::from(read_row.is_pad)),
                        )?;
                        // rw_counter
                        region.assign_advice(
                            || format!("assign rw_counter {}", offset),
                            self.rw_counter,
                            offset,
                            || Ok(read_row.rwc.map_or(F::zero(), |v| F::from(v.0 as u64))),
                        )?;
                        // rwc_inc_left
                        region.assign_advice(
                            || format!("assign rwc_inc_left {}", offset),
                            self.rwc_inc_left,
                            offset,
                            || Ok(F::zero()), // TODO(rohit): fix this
                        )?;
                        is_bytecode_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.src_type == CopyDataType::Bytecode {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;
                        is_memory_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.src_type == CopyDataType::Memory {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;
                        is_tx_calldata_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.src_type == CopyDataType::TxCalldata {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;
                        is_tx_log_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.src_type == CopyDataType::TxLog {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;

                        offset += 1;

                        // Write row
                        let write_row = copy_rw_pair.get(1).cloned().unwrap();
                        debug_assert_eq!(
                            write_row.rw,
                            RW::WRITE,
                            "expected write row to be RW::WRITE",
                        );
                        // q_step not enabled.
                        // q_first
                        region.assign_advice(
                            || format!("assign q_first {}", offset),
                            self.q_first,
                            offset,
                            || Ok(F::zero()),
                        )?;
                        // q_last
                        region.assign_advice(
                            || format!("assign q_last {}", offset),
                            self.q_last,
                            offset,
                            || {
                                Ok(if step_count == copy_event.steps.len() - 1 {
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
                                Ok(RandomLinearCombination::random_linear_combine(
                                    copy_event.dst_id.bytes(),
                                    block.randomness,
                                ))
                            },
                        )?;
                        // log_id
                        region.assign_advice(
                            || format!("assign log_id {}", offset),
                            self.log_id,
                            offset,
                            || Ok(copy_event.log_id.map_or(F::zero(), |v| F::from(v))),
                        )?;
                        // tag
                        region.assign_advice(
                            || format!("assign tag {}", offset),
                            self.tag,
                            offset,
                            || Ok(F::from(write_row.tag as u64)),
                        )?;
                        // addr
                        region.assign_advice(
                            || format!("assign addr {}", offset),
                            self.addr,
                            offset,
                            || Ok(F::from(write_row.addr)),
                        )?;
                        // addr_end
                        region.assign_advice(
                            || format!("assign addr_end {}", offset),
                            self.addr_end,
                            offset,
                            || Ok(write_row.addr_end.map_or(F::zero(), |v| F::from(v))),
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
                            || Ok(F::from(write_row.value as u64)),
                        )?;
                        // is_code
                        region.assign_advice(
                            || format!("assign is_code {}", offset),
                            self.is_code,
                            offset,
                            || Ok(write_row.is_code.map_or(F::zero(), |v| F::from(v))),
                        )?;
                        // is_pad
                        region.assign_advice(
                            || format!("assign is_pad {}", offset),
                            self.is_pad,
                            offset,
                            || Ok(F::from(write_row.is_pad)),
                        )?;
                        // rw_counter
                        region.assign_advice(
                            || format!("assign rw_counter {}", offset),
                            self.rw_counter,
                            offset,
                            || Ok(write_row.rwc.map_or(F::zero(), |v| F::from(v.0 as u64))),
                        )?;
                        // rwc_inc_left
                        region.assign_advice(
                            || format!("assign rwc_inc_left {}", offset),
                            self.rwc_inc_left,
                            offset,
                            || Ok(F::zero()), // TODO(rohit): fix this
                        )?;
                        is_bytecode_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.dst_type == CopyDataType::Bytecode {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;
                        is_memory_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.dst_type == CopyDataType::Memory {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;
                        is_tx_calldata_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.dst_type == CopyDataType::TxCalldata {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;
                        is_tx_log_chip.assign(
                            &mut region,
                            offset,
                            Some(if copy_event.dst_type == CopyDataType::TxLog {
                                F::zero()
                            } else {
                                F::one()
                            }),
                        )?;

                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

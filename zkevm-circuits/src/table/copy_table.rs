use super::*;

type CopyTableRow<F> = [(Value<F>, &'static str); 9];
type CopyCircuitRow<F> = [(Value<F>, &'static str); 5];

/// Copy Table, used to verify copies of byte chunks between Memory, Bytecode,
/// TxLogs and TxCallData.
#[derive(Clone, Copy, Debug)]
pub struct CopyTable {
    /// Whether the row is the first read-write pair for a copy event.
    pub is_first: Column<Advice>,
    /// The relevant ID for the read-write row, represented as a random linear
    /// combination. The ID may be one of the below:
    /// 1. Call ID/Caller ID for CopyDataType::Memory
    /// 2. The hi/lo limbs of bytecode hash for CopyDataType::Bytecode
    /// 3. Transaction ID for CopyDataType::TxCalldata, CopyDataType::TxLog
    pub id: word::Word<Column<Advice>>,
    /// The source/destination address for this copy step.  Can be memory
    /// address, byte index in the bytecode, tx call data, and tx log data.
    pub addr: Column<Advice>,
    /// The end of the source buffer for the copy event.  Any data read from an
    /// address greater than or equal to this value will be 0.
    pub src_addr_end: Column<Advice>,
    /// The number of bytes left to be copied.
    pub bytes_left: Column<Advice>,
    /// An accumulator value in the RLC representation. This is used for
    /// specific purposes, for instance, when `tag == CopyDataType::RlcAcc`.
    /// Having an additional column for the `rlc_acc` simplifies the lookup
    /// to copy table.
    pub rlc_acc: Column<Advice>,
    /// The associated read-write counter for this row.
    pub rw_counter: Column<Advice>,
    /// Decrementing counter denoting reverse read-write counter.
    pub rwc_inc_left: Column<Advice>,
    /// Binary chip to constrain the copy table conditionally depending on the
    /// current row's tag, whether it is Bytecode, Memory, TxCalldata or
    /// TxLog.
    pub tag: BinaryNumberConfig<CopyDataType, 3>,
}

impl CopyTable {
    /// Construct a new CopyTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>, q_enable: Column<Fixed>) -> Self {
        Self {
            is_first: meta.advice_column(),
            id: word::Word::new([meta.advice_column(), meta.advice_column()]),
            tag: BinaryNumberChip::configure(meta, q_enable, None),
            addr: meta.advice_column(),
            src_addr_end: meta.advice_column(),
            bytes_left: meta.advice_column(),
            rlc_acc: meta.advice_column_in(SecondPhase),
            rw_counter: meta.advice_column(),
            rwc_inc_left: meta.advice_column(),
        }
    }

    /// Generate the copy table and copy circuit assignments from a copy event.
    pub fn assignments<F: Field>(
        copy_event: &CopyEvent,
        challenges: Challenges<Value<F>>,
    ) -> Vec<(CopyDataType, CopyTableRow<F>, CopyCircuitRow<F>)> {
        let mut assignments = Vec::new();
        // rlc_acc
        let rlc_acc = {
            let values = copy_event
                .bytes
                .iter()
                .map(|(value, _)| *value)
                .collect::<Vec<u8>>();
            challenges
                .keccak_input()
                .map(|keccak_input| rlc::value(values.iter().rev(), keccak_input))
        };
        let mut value_acc = Value::known(F::ZERO);
        for (step_idx, (is_read_step, copy_step)) in copy_event
            .bytes
            .iter()
            .flat_map(|(value, is_code)| {
                let read_step = CopyStep {
                    value: *value,
                    is_code: if copy_event.src_type == CopyDataType::Bytecode {
                        Some(*is_code)
                    } else {
                        None
                    },
                };
                let write_step = CopyStep {
                    value: *value,
                    is_code: if copy_event.dst_type == CopyDataType::Bytecode {
                        Some(*is_code)
                    } else {
                        None
                    },
                };
                once((true, read_step)).chain(once((false, write_step)))
            })
            .enumerate()
        {
            // is_first
            let is_first = Value::known(if step_idx == 0 { F::ONE } else { F::ZERO });
            // is last
            let is_last = if step_idx == copy_event.bytes.len() * 2 - 1 {
                Value::known(F::ONE)
            } else {
                Value::known(F::ZERO)
            };

            // id
            let id = if is_read_step {
                number_or_hash_to_word(&copy_event.src_id)
            } else {
                number_or_hash_to_word(&copy_event.dst_id)
            };

            // tag binary bumber chip
            let tag = if is_read_step {
                copy_event.src_type
            } else {
                copy_event.dst_type
            };

            // addr
            let copy_step_addr: u64 =
                if is_read_step {
                    copy_event.src_addr
                } else {
                    copy_event.dst_addr
                } + (u64::try_from(step_idx).unwrap() - if is_read_step { 0 } else { 1 }) / 2u64;

            let addr = if tag == CopyDataType::TxLog {
                Value::known(
                    build_tx_log_address(
                        copy_step_addr,
                        TxLogFieldTag::Data,
                        copy_event.log_id.unwrap(),
                    )
                    .to_scalar()
                    .unwrap(),
                )
            } else {
                Value::known(F::from(copy_step_addr))
            };

            // bytes_left
            let bytes_left = u64::try_from(copy_event.bytes.len() * 2 - step_idx).unwrap() / 2;
            // value
            let value = Value::known(F::from(copy_step.value as u64));
            // value_acc
            if is_read_step {
                value_acc = value_acc * challenges.keccak_input() + value;
            }
            // is_pad
            let is_pad = Value::known(F::from(
                (is_read_step && copy_step_addr >= copy_event.src_addr_end) as u64,
            ));

            // is_code
            let is_code = Value::known(copy_step.is_code.map_or(F::ZERO, |v| F::from(v as u64)));

            assignments.push((
                tag,
                [
                    (is_first, "is_first"),
                    (id.lo(), "id_lo"),
                    (id.hi(), "id_hi"),
                    (addr, "addr"),
                    (
                        Value::known(F::from(copy_event.src_addr_end)),
                        "src_addr_end",
                    ),
                    (Value::known(F::from(bytes_left)), "bytes_left"),
                    (
                        match (copy_event.src_type, copy_event.dst_type) {
                            (CopyDataType::Memory, CopyDataType::Bytecode) => rlc_acc,
                            (_, CopyDataType::RlcAcc) => rlc_acc,
                            _ => Value::known(F::ZERO),
                        },
                        "rlc_acc",
                    ),
                    (
                        Value::known(F::from(copy_event.rw_counter(step_idx))),
                        "rw_counter",
                    ),
                    (
                        Value::known(F::from(copy_event.rw_counter_increase_left(step_idx))),
                        "rwc_inc_left",
                    ),
                ],
                [
                    (is_last, "is_last"),
                    (value, "value"),
                    (value_acc, "value_acc"),
                    (is_pad, "is_pad"),
                    (is_code, "is_code"),
                ],
            ));
        }
        assignments
    }

    /// Assign the `CopyTable` from a `Block`.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "copy table",
            |mut region| {
                let mut offset = 0;
                for column in <CopyTable as LookupTable<F>>::advice_columns(self) {
                    region.assign_advice(
                        || "copy table all-zero row",
                        column,
                        offset,
                        || Value::known(F::ZERO),
                    )?;
                }
                offset += 1;

                let tag_chip = BinaryNumberChip::construct(self.tag);
                let copy_table_columns = <CopyTable as LookupTable<F>>::advice_columns(self);
                for copy_event in block.copy_events.iter() {
                    for (tag, row, _) in Self::assignments(copy_event, *challenges) {
                        for (&column, (value, label)) in copy_table_columns.iter().zip_eq(row) {
                            region.assign_advice(
                                || format!("{} at row: {}", label, offset),
                                column,
                                offset,
                                || value,
                            )?;
                        }
                        tag_chip.assign(&mut region, offset, &tag)?;
                        offset += 1;
                    }
                }

                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for CopyTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.is_first.into(),
            self.id.lo().into(),
            self.id.hi().into(),
            self.addr.into(),
            self.src_addr_end.into(),
            self.bytes_left.into(),
            self.rlc_acc.into(),
            self.rw_counter.into(),
            self.rwc_inc_left.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("is_first"),
            String::from("id_lo"),
            String::from("id_hi"),
            String::from("addr"),
            String::from("src_addr_end"),
            String::from("bytes_left"),
            String::from("rlc_acc"),
            String::from("rw_counter"),
            String::from("rwc_inc_left"),
        ]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_advice(self.is_first, Rotation::cur()),
            meta.query_advice(self.id.lo(), Rotation::cur()), // src_id
            meta.query_advice(self.id.hi(), Rotation::cur()), // src_id
            self.tag.value(Rotation::cur())(meta),            // src_tag
            meta.query_advice(self.id.lo(), Rotation::next()), // dst_id
            meta.query_advice(self.id.hi(), Rotation::next()), // dst_id
            self.tag.value(Rotation::next())(meta),           // dst_tag
            meta.query_advice(self.addr, Rotation::cur()),    // src_addr
            meta.query_advice(self.src_addr_end, Rotation::cur()), // src_addr_end
            meta.query_advice(self.addr, Rotation::next()),   // dst_addr
            meta.query_advice(self.bytes_left, Rotation::cur()), // length
            meta.query_advice(self.rlc_acc, Rotation::cur()), // rlc_acc
            meta.query_advice(self.rw_counter, Rotation::cur()), // rw_counter
            meta.query_advice(self.rwc_inc_left, Rotation::cur()), // rwc_inc_left
        ]
    }
}

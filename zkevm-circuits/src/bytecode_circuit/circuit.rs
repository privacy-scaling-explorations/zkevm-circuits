use crate::{
    evm_circuit::util::{
        and,
        constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon},
        not, or, select,
    },
    table::{BytecodeFieldTag, BytecodeTable, KeccakTable, LookupTable},
    util::{
        get_push_size,
        word::{empty_code_hash_word_value, Word, Word32, WordExpr},
        Challenges, Expr, SubCircuit, SubCircuitConfig,
    },
    witness,
};
use bus_mapping::state_db::EMPTY_CODE_HASH_LE;
use eth_types::Field;
use gadgets::is_zero::{IsZeroChip, IsZeroInstruction};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase, VirtualCells,
    },
    poly::Rotation,
};
use log::trace;
use std::vec;

use super::{
    bytecode_unroller::{unroll, UnrolledBytecode},
    param::PUSH_TABLE_WIDTH,
};

#[derive(Debug, Clone, Default)]
/// Row for assignment
pub struct BytecodeCircuitRow<F: Field> {
    offset: usize,
    last_row_offset: usize,
    code_hash: Word<Value<F>>,
    tag: F,
    index: F,
    is_code: F,
    value: F,
    push_data_left: u64,
    value_rlc: Value<F>,
    length: F,
    push_data_size: F,
}
impl<F: Field> BytecodeCircuitRow<F> {
    /// enable selector if we are within the range of table size.
    pub fn enable(&self) -> bool {
        self.offset <= self.last_row_offset
    }

    /// Determine if we are at last row of the bytecode table.
    pub fn last(&self) -> bool {
        self.offset == self.last_row_offset
    }

    /// Get offset
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Witness to IsZero chip to determine if we are at the last row of a bytecode instance
    pub fn diff(&self) -> F {
        self.index + F::ONE - self.length
    }
}

#[derive(Clone, Debug)]
/// Bytecode circuit configuration
pub struct BytecodeCircuitConfig<F> {
    minimum_rows: usize,
    q_enable: Column<Fixed>,
    q_first: Column<Fixed>,
    q_last: Column<Fixed>,
    bytecode_table: BytecodeTable,
    push_data_left: Column<Advice>,
    value_rlc: Column<Advice>,
    length: Column<Advice>,
    push_data_size: Column<Advice>,
    push_data_left_is_zero: IsZeroChip<F>,
    index_length_diff_is_zero: IsZeroChip<F>,
    push_table: [Column<Fixed>; PUSH_TABLE_WIDTH],
    // External tables
    pub(crate) keccak_table: KeccakTable,
}

/// Circuit configuration arguments
pub struct BytecodeCircuitConfigArgs<F: Field> {
    /// BytecodeTable
    pub bytecode_table: BytecodeTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for BytecodeCircuitConfig<F> {
    type ConfigArgs = BytecodeCircuitConfigArgs<F>;

    /// Return a new BytecodeCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            bytecode_table,
            keccak_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();
        let value = bytecode_table.value;
        let push_data_left = meta.advice_column();
        let value_rlc = meta.advice_column_in(SecondPhase);
        let length = meta.advice_column();
        let push_data_size = meta.advice_column();
        let push_data_left_inv = meta.advice_column();
        let index_length_diff_inv = meta.advice_column();
        let push_table = array_init::array_init(|_| meta.fixed_column());

        // annotate columns
        bytecode_table.annotate_columns(meta);
        keccak_table.annotate_columns(meta);
        push_table.iter().enumerate().for_each(|(idx, &col)| {
            meta.annotate_lookup_any_column(col, || format!("push_table_{}", idx))
        });

        let is_header_to_header = |meta: &mut VirtualCells<F>| {
            and::expr(vec![
                not::expr(meta.query_advice(bytecode_table.tag, Rotation::cur())),
                not::expr(meta.query_advice(bytecode_table.tag, Rotation::next())),
            ])
        };

        let is_header_to_byte = |meta: &mut VirtualCells<F>| {
            and::expr(vec![
                not::expr(meta.query_advice(bytecode_table.tag, Rotation::cur())),
                meta.query_advice(bytecode_table.tag, Rotation::next()),
            ])
        };

        let is_byte_to_header = |meta: &mut VirtualCells<F>| {
            and::expr(vec![
                meta.query_advice(bytecode_table.tag, Rotation::cur()),
                not::expr(meta.query_advice(bytecode_table.tag, Rotation::next())),
            ])
        };

        let is_byte_to_byte = |meta: &mut VirtualCells<F>| {
            and::expr(vec![
                meta.query_advice(bytecode_table.tag, Rotation::cur()),
                meta.query_advice(bytecode_table.tag, Rotation::next()),
            ])
        };

        let is_header = |meta: &mut VirtualCells<F>| {
            not::expr(meta.query_advice(bytecode_table.tag, Rotation::cur()))
        };

        let is_byte =
            |meta: &mut VirtualCells<F>| meta.query_advice(bytecode_table.tag, Rotation::cur());

        // A byte is an opcode when `push_data_left == 0` on the current row,
        // else it's push data.
        let push_data_left_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_fixed(q_enable, Rotation::cur()),
            |meta| meta.query_advice(push_data_left, Rotation::cur()),
            push_data_left_inv,
        );

        let index_length_diff_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_fixed(q_enable, Rotation::cur()),
            |meta| {
                meta.query_advice(bytecode_table.index, Rotation::cur()) + 1.expr()
                    - meta.query_advice(length, Rotation::cur())
            },
            index_length_diff_inv,
        );

        // When q_first || q_last ->
        // assert cur.tag == Header
        meta.create_gate("first and last row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "cur.tag == Header",
                meta.query_advice(bytecode_table.tag, Rotation::cur()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                or::expr(vec![
                    meta.query_fixed(q_first, Rotation::cur()),
                    meta.query_fixed(q_last, Rotation::cur()),
                ]),
            ]))
        });

        // When is_header ->
        // assert cur.index == 0
        // assert cur.value == cur.length
        meta.create_gate("Header row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "cur.index == 0",
                meta.query_advice(bytecode_table.index, Rotation::cur()),
            );

            cb.require_equal(
                "cur.value == cur.length",
                meta.query_advice(bytecode_table.value, Rotation::cur()),
                meta.query_advice(length, Rotation::cur()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_last, Rotation::cur())),
                is_header(meta),
            ]))
        });

        // When is_byte ->
        // assert push_data_size_table_lookup(cur.value, cur.push_data_size)
        // assert cur.is_code == (cur.push_data_left == 0)
        meta.create_gate("Byte row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "cur.is_code == (cur.push_data_left == 0)",
                meta.query_advice(bytecode_table.is_code, Rotation::cur()),
                push_data_left_is_zero.clone().is_zero_expression,
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_last, Rotation::cur())),
                is_byte(meta),
            ]))
        });
        meta.lookup_any(
            "push_data_size_table_lookup(cur.value, cur.push_data_size)",
            |meta| {
                let enable = and::expr(vec![
                    meta.query_fixed(q_enable, Rotation::cur()),
                    not::expr(meta.query_fixed(q_last, Rotation::cur())),
                    is_byte(meta),
                ]);

                let lookup_columns = vec![value, push_data_size];

                let mut constraints = vec![];

                for i in 0..PUSH_TABLE_WIDTH {
                    constraints.push((
                        enable.clone() * meta.query_advice(lookup_columns[i], Rotation::cur()),
                        meta.query_fixed(push_table[i], Rotation::cur()),
                    ))
                }
                constraints
            },
        );

        // When is_header_to_header or q_last ->
        // assert cur.length == 0
        // assert cur.hash == EMPTY_HASH
        meta.create_gate("Header to header row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "cur.length == 0",
                meta.query_advice(length, Rotation::cur()),
            );

            let empty_hash_word: Word<Expression<F>> =
                Word32::new(EMPTY_CODE_HASH_LE.map(|v| Expression::Constant(F::from(v as u64))))
                    .to_word();

            cb.require_equal_word(
                "assert cur.hash == EMPTY_HASH",
                Word::new([
                    meta.query_advice(bytecode_table.code_hash.lo(), Rotation::cur()),
                    meta.query_advice(bytecode_table.code_hash.hi(), Rotation::cur()),
                ]),
                empty_hash_word,
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                or::expr(vec![
                    is_header_to_header(meta),
                    meta.query_fixed(q_last, Rotation::cur()),
                ]),
            ]))
        });

        // When is_header_to_byte ->
        // assert next.length == cur.length
        // assert next.index == 0
        // assert next.is_code == 1
        // assert next.hash == cur.hash
        // assert next.value_rlc == next.value
        meta.create_gate("Header to byte row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "next.length == cur.length",
                meta.query_advice(length, Rotation::next()),
                meta.query_advice(length, Rotation::cur()),
            );

            cb.require_zero(
                "next.index == 0",
                meta.query_advice(bytecode_table.index, Rotation::next()),
            );

            cb.require_equal(
                "next.is_code == 1",
                meta.query_advice(bytecode_table.is_code, Rotation::next()),
                1.expr(),
            );

            cb.require_equal_word(
                "next.hash == cur.hash",
                Word::new([
                    meta.query_advice(bytecode_table.code_hash.lo(), Rotation::next()),
                    meta.query_advice(bytecode_table.code_hash.hi(), Rotation::next()),
                ]),
                Word::new([
                    meta.query_advice(bytecode_table.code_hash.lo(), Rotation::cur()),
                    meta.query_advice(bytecode_table.code_hash.hi(), Rotation::cur()),
                ]),
            );

            cb.require_equal(
                "next.value_rlc == next.value",
                meta.query_advice(value_rlc, Rotation::next()),
                meta.query_advice(bytecode_table.value, Rotation::next()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_last, Rotation::cur())),
                is_header_to_byte(meta),
            ]))
        });

        // When is_byte_to_byte ->
        // assert next.length == cur.length
        // assert next.index == cur.index + 1
        // assert next.hash == cur.hash
        // assert next.value_rlc == cur.value_rlc * randomness + next.value
        // if cur.is_code:
        //     assert next.push_data_left == cur.push_data_size
        // else:
        //     assert next.push_data_left == cur.push_data_left - 1
        meta.create_gate("Byte to Byte row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "next.length == cur.length",
                meta.query_advice(length, Rotation::next()),
                meta.query_advice(length, Rotation::cur()),
            );

            cb.require_equal(
                "next.index == cur.index + 1",
                meta.query_advice(bytecode_table.index, Rotation::next()),
                meta.query_advice(bytecode_table.index, Rotation::cur()) + 1.expr(),
            );

            cb.require_equal_word(
                "next.hash == cur.hash",
                Word::new([
                    meta.query_advice(bytecode_table.code_hash.lo(), Rotation::next()),
                    meta.query_advice(bytecode_table.code_hash.hi(), Rotation::next()),
                ]),
                Word::new([
                    meta.query_advice(bytecode_table.code_hash.lo(), Rotation::cur()),
                    meta.query_advice(bytecode_table.code_hash.hi(), Rotation::cur()),
                ]),
            );

            cb.require_equal(
                "next.value_rlc == cur.value_rlc * randomness + next.value",
                meta.query_advice(value_rlc, Rotation::next()),
                meta.query_advice(value_rlc, Rotation::cur()) * challenges.keccak_input()
                    + meta.query_advice(value, Rotation::next()),
            );

            cb.require_equal(
                "next.push_data_left == cur.is_code ? cur.push_data_size : cur.push_data_left - 1",
                meta.query_advice(push_data_left, Rotation::next()),
                select::expr(
                    meta.query_advice(bytecode_table.is_code, Rotation::cur()),
                    meta.query_advice(push_data_size, Rotation::cur()),
                    meta.query_advice(push_data_left, Rotation::cur()) - 1.expr(),
                ),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_last, Rotation::cur())),
                is_byte_to_byte(meta),
            ]))
        });

        // When cur.tag == Byte and cur.index + 1 == cur.length ->
        // assert next.tag == Header
        meta.create_gate("cur.tag == Byte and cur.index + 1 == cur.length", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_zero(
                "next.tag == Header",
                meta.query_advice(bytecode_table.tag, Rotation::next()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                meta.query_advice(bytecode_table.tag, Rotation::cur()),
                index_length_diff_is_zero.clone().is_zero_expression,
            ]))
        });

        // When is_byte_to_header ->
        // assert cur.index + 1 == cur.length
        // assert keccak256_table_lookup(cur.hash, cur.length, cur.value_rlc)
        meta.create_gate("Byte to Header row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "cur.index + 1 == cur.length",
                meta.query_advice(bytecode_table.index, Rotation::cur()) + 1.expr(),
                meta.query_advice(length, Rotation::cur()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_last, Rotation::cur())),
                is_byte_to_header(meta),
            ]))
        });
        meta.lookup_any(
            "keccak256_table_lookup(cur.value_rlc, cur.length, cur.hash_word)",
            |meta| {
                let enable = and::expr(vec![
                    meta.query_fixed(q_enable, Rotation::cur()),
                    not::expr(meta.query_fixed(q_last, Rotation::cur())),
                    is_byte_to_header(meta),
                ]);

                let mut constraints = vec![(
                    enable.clone(),
                    meta.query_advice(keccak_table.is_enabled, Rotation::cur()),
                )];

                for (circuit_column, table_column) in
                    keccak_table.match_columns(value_rlc, length, bytecode_table.code_hash)
                {
                    constraints.push((
                        enable.clone() * meta.query_advice(circuit_column, Rotation::cur()),
                        meta.query_advice(table_column, Rotation::cur()),
                    ))
                }

                constraints
            },
        );

        let push_data_left_is_zero = IsZeroChip::construct(push_data_left_is_zero);
        let index_length_diff_is_zero = IsZeroChip::construct(index_length_diff_is_zero);

        BytecodeCircuitConfig {
            minimum_rows: meta.minimum_rows(),
            q_enable,
            q_first,
            q_last,
            bytecode_table,
            push_data_left,
            value_rlc,
            length,
            push_data_size,
            push_data_left_is_zero,
            index_length_diff_is_zero,
            push_table,
            keccak_table,
        }
    }
}

impl<F: Field> BytecodeCircuitConfig<F> {
    pub(crate) fn assign_internal(
        &self,
        layouter: &mut impl Layouter<F>,
        size: usize,
        witness: &[UnrolledBytecode<F>],
        overwrite: &UnrolledBytecode<F>,
        challenges: &Challenges<Value<F>>,
        fail_fast: bool,
    ) -> Result<(), Error> {
        // Subtract the unusable rows from the size
        assert!(size > self.minimum_rows);
        let last_row_offset = size - self.minimum_rows + 1;

        trace!(
            "size: {}, minimum_rows: {}, last_row_offset:{}",
            size,
            self.minimum_rows,
            last_row_offset
        );

        layouter.assign_region(
            || "assign bytecode",
            |mut region| {
                // annotate columns
                self.annotate_circuit(&mut region);

                let mut offset = 0;
                for bytecode in witness.iter() {
                    self.assign_bytecode(
                        &mut region,
                        bytecode,
                        challenges,
                        &mut offset,
                        last_row_offset,
                        fail_fast,
                    )?;
                }

                // Padding
                for idx in offset..=last_row_offset {
                    self.set_padding_row(&mut region, idx, last_row_offset)?;
                }

                // Overwrite the witness assignment by using the values in the `overwrite`
                // parameter.  This is used to explicitly set intermediate witness values for
                // negative tests.
                let mut value_rlc = challenges.keccak_input().map(|_| F::ZERO);
                for (offset, row) in overwrite.rows.iter().enumerate() {
                    for (name, column, value) in [
                        ("tag", self.bytecode_table.tag, row.tag),
                        ("index", self.bytecode_table.index, row.index),
                        ("is_code", self.bytecode_table.is_code, row.is_code),
                        ("value", self.bytecode_table.value, row.value),
                        ("length", self.length, F::from(overwrite.bytes.len() as u64)),
                    ] {
                        region.assign_advice(
                            || format!("assign {} {}", name, offset),
                            column,
                            offset,
                            || Value::known(value),
                        )?;
                    }

                    if row.tag == F::ONE {
                        value_rlc.as_mut().zip(challenges.keccak_input()).map(
                            |(value_rlc, challenge)| {
                                *value_rlc = *value_rlc * challenge + row.value
                            },
                        );
                    } else {
                        value_rlc = challenges.keccak_input().map(|_| F::ZERO);
                    }

                    for (name, column, value) in [("value_rlc", self.value_rlc, value_rlc)] {
                        region.assign_advice(
                            || format!("assign {} {}", name, offset),
                            column,
                            offset,
                            || value,
                        )?;
                    }
                }
                Ok(())
            },
        )
    }

    fn assign_bytecode(
        &self,
        region: &mut Region<'_, F>,
        bytecode: &UnrolledBytecode<F>,
        challenges: &Challenges<Value<F>>,
        offset: &mut usize,
        last_row_offset: usize,
        fail_fast: bool,
    ) -> Result<(), Error> {
        // Run over all the bytes
        let mut push_data_left = 0;
        let mut next_push_data_left = 0;
        let mut push_data_size = 0;
        let mut value_rlc = challenges.keccak_input().map(|_| F::ZERO);
        let length = F::from(bytecode.bytes.len() as u64);

        let code_hash = Word::from(bytecode.rows[0].code_hash).into_value();

        for (idx, row) in bytecode.rows.iter().enumerate() {
            if fail_fast && *offset > last_row_offset {
                log::error!(
                    "Bytecode Circuit: offset={} > last_row_offset={}",
                    offset,
                    last_row_offset
                );
                return Err(Error::Synthesis);
            }

            // Track which byte is an opcode and which is push
            // data
            if idx > 0 {
                let is_code = push_data_left == 0;

                push_data_size = get_push_size(row.value.get_lower_128() as u8);

                next_push_data_left = if is_code {
                    push_data_size
                } else {
                    push_data_left - 1
                };

                value_rlc
                    .as_mut()
                    .zip(challenges.keccak_input())
                    .map(|(value_rlc, challenge)| *value_rlc = *value_rlc * challenge + row.value);
            }

            // Set the data for this row
            if *offset < last_row_offset {
                let row = BytecodeCircuitRow {
                    offset: *offset,
                    last_row_offset,
                    code_hash,
                    tag: row.tag,
                    index: row.index,
                    is_code: row.is_code,
                    value: row.value,
                    push_data_left,
                    value_rlc,
                    length,
                    push_data_size: F::from(push_data_size),
                };
                self.set_row(region, row.clone())?;

                trace!("bytecode.set_row({:?})", row);

                *offset += 1;
                push_data_left = next_push_data_left
            }
            if *offset == last_row_offset {
                self.set_padding_row(region, *offset, last_row_offset)?;
            }
        }

        Ok(())
    }

    fn set_padding_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        last_row_offset: usize,
    ) -> Result<(), Error> {
        self.set_row(
            region,
            BytecodeCircuitRow {
                offset,
                last_row_offset,
                code_hash: empty_code_hash_word_value(),
                tag: F::from(BytecodeFieldTag::Header as u64),
                value_rlc: Value::known(F::ZERO),
                ..Default::default()
            },
        )
    }

    fn set_row(&self, region: &mut Region<'_, F>, row: BytecodeCircuitRow<F>) -> Result<(), Error> {
        let offset = row.offset;
        // q_enable
        region.assign_fixed(
            || format!("assign q_enable {}", offset),
            self.q_enable,
            offset,
            || Value::known(F::from(row.enable().into())),
        )?;

        // q_first
        region.assign_fixed(
            || format!("assign q_first {}", offset),
            self.q_first,
            offset,
            || Value::known(F::from((offset == 0).into())),
        )?;

        // q_last
        region.assign_fixed(
            || format!("assign q_last {}", offset),
            self.q_last,
            offset,
            || Value::known(F::from(row.last().into())),
        )?;

        // Advices
        for (name, column, value) in [
            ("tag", self.bytecode_table.tag, row.tag),
            ("index", self.bytecode_table.index, row.index),
            ("is_code", self.bytecode_table.is_code, row.is_code),
            ("value", self.bytecode_table.value, row.value),
            (
                "push_data_left",
                self.push_data_left,
                F::from(row.push_data_left),
            ),
            ("length", self.length, row.length),
            ("push_data_size", self.push_data_size, row.push_data_size),
        ] {
            region.assign_advice(
                || format!("assign {} {}", name, offset),
                column,
                offset,
                || Value::known(value),
            )?;
        }
        for (name, column, value) in [("value_rlc", self.value_rlc, row.value_rlc)] {
            region.assign_advice(
                || format!("assign {} {}", name, offset),
                column,
                offset,
                || value,
            )?;
        }

        row.code_hash.assign_advice(
            region,
            || format!("assign code_hash {}", offset),
            self.bytecode_table.code_hash,
            offset,
        )?;

        self.push_data_left_is_zero.assign(
            region,
            offset,
            Value::known(F::from(row.push_data_left)),
        )?;

        self.index_length_diff_is_zero
            .assign(region, offset, Value::known(row.diff()))?;

        Ok(())
    }

    fn annotate_circuit(&self, region: &mut Region<F>) {
        self.bytecode_table.annotate_columns_in_region(region);
        self.keccak_table.annotate_columns_in_region(region);

        self.push_data_left_is_zero
            .annotate_columns_in_region(region, "BYTECODE");
        self.index_length_diff_is_zero
            .annotate_columns_in_region(region, "BYTECODE");
        region.name_column(|| "BYTECODE_q_enable", self.q_enable);
        region.name_column(|| "BYTECODE_q_first", self.q_first);
        region.name_column(|| "BYTECODE_q_last", self.q_last);
        region.name_column(|| "BYTECODE_length", self.length);
        region.name_column(|| "BYTECODE_push_data_left", self.push_data_left);
        region.name_column(|| "BYTECODE_push_data_size", self.push_data_size);
        region.name_column(|| "BYTECODE_value_rlc", self.value_rlc);
    }

    /// load fixed tables
    pub(crate) fn load_aux_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        // push table: BYTE -> NUM_PUSHED:
        // [0, OpcodeId::PUSH1] -> 0
        // [OpcodeId::PUSH1, OpcodeId::PUSH32] -> [1..32]
        // [OpcodeId::PUSH32, 256] -> 0
        layouter.assign_region(
            || "push table",
            |mut region| {
                for byte in 0usize..256 {
                    let push_size = get_push_size(byte as u8);
                    for (name, column, value) in &[
                        ("byte", self.push_table[0], byte as u64),
                        ("push_size", self.push_table[1], push_size),
                    ] {
                        region.assign_fixed(
                            || format!("Push table assign {} {}", name, byte),
                            *column,
                            byte,
                            || Value::known(F::from(*value)),
                        )?;
                    }
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

/// BytecodeCircuit
#[derive(Clone, Default, Debug)]
pub struct BytecodeCircuit<F: Field> {
    /// Unrolled bytecodes
    pub bytecodes: Vec<UnrolledBytecode<F>>,
    /// Circuit size
    pub size: usize,
    /// Overwrite
    pub overwrite: UnrolledBytecode<F>,
}

impl<F: Field> BytecodeCircuit<F> {
    /// new BytecodeCircuitTester
    pub fn new(bytecodes: Vec<UnrolledBytecode<F>>, size: usize) -> Self {
        BytecodeCircuit {
            bytecodes,
            size,
            overwrite: Default::default(),
        }
    }

    /// Creates bytecode circuit from block and bytecode_size.
    pub fn new_from_block_sized(block: &witness::Block<F>, bytecode_size: usize) -> Self {
        let bytecodes: Vec<UnrolledBytecode<F>> = block
            .bytecodes
            .values()
            .map(|b| unroll(b.bytes.clone()))
            .collect();
        Self::new(bytecodes, bytecode_size)
    }
}

impl<F: Field> SubCircuit<F> for BytecodeCircuit<F> {
    type Config = BytecodeCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn new_from_block(block: &witness::Block<F>) -> Self {
        let bytecode_size = block.circuits_params.max_bytecode;
        Self::new_from_block_sized(block, bytecode_size)
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            block
                .bytecodes
                .values()
                .map(|bytecode| bytecode.bytes.len() + 1)
                .sum(),
            block.circuits_params.max_bytecode,
        )
    }

    /// Make the assignments to the TxCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load_aux_tables(layouter)?;
        config.assign_internal(
            layouter,
            self.size,
            &self.bytecodes,
            &self.overwrite,
            challenges,
            false,
        )
    }
}

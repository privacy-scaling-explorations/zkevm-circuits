//! Fixed lookup tables and dynamic lookup tables for the EVM circuit

use crate::{
    evm_circuit::step::{ExecutionState, ResponsibleOp},
    impl_expr,
    util::word::Word,
};
use bus_mapping::{evm::OpcodeId, precompile::PrecompileCalls};
use eth_types::Field;
use gadgets::util::Expr;
use halo2_proofs::plonk::Expression;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

#[derive(Clone, Copy, Debug, EnumIter)]
/// Tags for different fixed tables
pub enum FixedTableTag {
    /// x == 0
    Zero = 0,
    /// 0 <= x < 5
    Range5,
    /// 0 <= x < 16
    Range16,
    /// 0 <= x < 32
    Range32,
    /// 0 <= x < 64
    Range64,
    /// 0 <= x < 128
    Range128,
    /// 0 <= x < 256
    Range256,
    /// 0 <= x < 512
    Range512,
    /// 0 <= x < 1024
    Range1024,
    /// -128 <= x < 128
    SignByte,
    /// bitwise AND
    BitwiseAnd,
    /// bitwise OR
    BitwiseOr,
    /// bitwise XOR
    BitwiseXor,
    /// lookup for corresponding opcode
    ResponsibleOpcode,
    /// power of 2
    Pow2,
    /// Lookup constant gas cost for opcodes
    ConstantGasCost,
    PrecompileInfo,
}
impl_expr!(FixedTableTag);

impl FixedTableTag {
    /// build up the fixed table row values
    pub(crate) fn build<F: Field>(&self) -> Box<dyn Iterator<Item = [F; 4]>> {
        let tag = F::from(*self as u64);
        match self {
            Self::Zero => Box::new((0..1).map(move |_| [tag, F::ZERO, F::ZERO, F::ZERO])),
            Self::Range5 => {
                Box::new((0..5).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range16 => {
                Box::new((0..16).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range32 => {
                Box::new((0..32).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range64 => {
                Box::new((0..64).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range128 => {
                Box::new((0..128).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range256 => {
                Box::new((0..256).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range512 => {
                Box::new((0..512).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::Range1024 => {
                Box::new((0..1024).map(move |value| [tag, F::from(value), F::ZERO, F::ZERO]))
            }
            Self::SignByte => Box::new((0..256).map(move |value| {
                [
                    tag,
                    F::from(value),
                    F::from((value >> 7) * 0xFFu64),
                    F::ZERO,
                ]
            })),
            Self::BitwiseAnd => Box::new((0..256).flat_map(move |lhs| {
                (0..256).map(move |rhs| [tag, F::from(lhs), F::from(rhs), F::from(lhs & rhs)])
            })),
            Self::BitwiseOr => Box::new((0..256).flat_map(move |lhs| {
                (0..256).map(move |rhs| [tag, F::from(lhs), F::from(rhs), F::from(lhs | rhs)])
            })),
            Self::BitwiseXor => Box::new((0..256).flat_map(move |lhs| {
                (0..256).map(move |rhs| [tag, F::from(lhs), F::from(rhs), F::from(lhs ^ rhs)])
            })),
            Self::ResponsibleOpcode => {
                Box::new(ExecutionState::iter().flat_map(move |execution_state| {
                    execution_state.responsible_opcodes().into_iter().map(
                        move |responsible_opcode| {
                            let (op, aux) = match responsible_opcode {
                                ResponsibleOp::Op(op) => (op, F::ZERO),
                                ResponsibleOp::InvalidStackPtr(op, stack_ptr) => {
                                    (op, F::from(u64::from(stack_ptr)))
                                }
                            };
                            [
                                tag,
                                F::from(execution_state.as_u64()),
                                F::from(op.as_u64()),
                                aux,
                            ]
                        },
                    )
                }))
            }
            Self::Pow2 => Box::new((0..256).map(move |value| {
                let (pow_lo, pow_hi) = if value < 128 {
                    (F::from_u128(1_u128 << value), F::from(0))
                } else {
                    (F::from(0), F::from_u128(1 << (value - 128)))
                };
                [tag, F::from(value), pow_lo, pow_hi]
            })),
            Self::ConstantGasCost => Box::new(
                OpcodeId::iter()
                    .filter(move |opcode| opcode.constant_gas_cost() > 0)
                    .map(move |opcode| {
                        [
                            tag,
                            F::from(opcode.as_u64()),
                            F::from(opcode.constant_gas_cost()),
                            F::ZERO,
                        ]
                    }),
            ),
            Self::PrecompileInfo => Box::new(PrecompileCalls::iter().map(move |precompile| {
                [
                    tag,
                    F::from({
                        let state: ExecutionState = precompile.into();
                        state.as_u64()
                    }),
                    F::from(u64::from(precompile)),
                    F::from(precompile.base_gas_cost().0),
                ]
            })),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter)]
/// Each item represents the lookup table to query
pub enum Table {
    /// The range check table for u8
    U8,
    /// The range check table for u16
    U16,
    /// The rest of the fixed table. See [`FixedTableTag`]
    Fixed,
    /// Lookup for transactions
    Tx,
    /// Lookup for read write operations
    Rw,
    /// Lookup for bytecode table
    Bytecode,
    /// Lookup for block constants
    Block,
    /// Lookup for copy table
    Copy,
    /// Lookup for keccak table
    Keccak,
    /// Lookup for exp table
    Exp,
}

#[derive(Clone, Debug)]
/// Read-Write Table fields
pub(crate) struct RwValues<F> {
    /// The unique identifier for the Read or Write. Depending on context, this field could be used
    /// for Transaction ID or call ID
    id: Expression<F>,
    /// The position to Stack, Memory, or account, where the read or write takes place, depending
    /// on the cell value of the [`bus_mapping::operation::Target`].
    address: Expression<F>,
    /// Could be [`crate::table::CallContextFieldTag`], [`crate::table::AccountFieldTag`],
    /// [`crate::table::TxLogFieldTag`], or [`crate::table::TxReceiptFieldTag`] depending on
    /// the cell value of the [`bus_mapping::operation::Target`]
    field_tag: Expression<F>,
    /// Storage key of two limbs
    storage_key: Word<Expression<F>>,
    /// The current storage value
    value: Word<Expression<F>>,
    /// The previous storage value
    value_prev: Word<Expression<F>>,
    /// The initial storage value before the current transaction
    init_val: Word<Expression<F>>,
}

impl<F: Field> RwValues<F> {
    /// Constructor for RwValues
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        id: Expression<F>,
        address: Expression<F>,
        field_tag: Expression<F>,
        storage_key: Word<Expression<F>>,
        value: Word<Expression<F>>,
        value_prev: Word<Expression<F>>,
        init_val: Word<Expression<F>>,
    ) -> Self {
        Self {
            id,
            address,
            field_tag,
            storage_key,
            value,
            value_prev,
            init_val,
        }
    }

    pub(crate) fn revert_value(&self) -> Self {
        let new_self = self.clone();
        Self {
            value_prev: new_self.value,
            value: new_self.value_prev,
            ..new_self
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum Lookup<F> {
    /// Lookup to fixed table, which contains serveral pre-built tables such as
    /// range tables or bitwise tables.
    Fixed {
        /// Tag to specify which table to lookup.
        tag: Expression<F>,
        /// Values that must satisfy the pre-built relationship.
        values: [Expression<F>; 3],
    },
    /// Lookup to tx table, which contains transactions of this block.
    Tx {
        /// Id of transaction, the first transaction has id = 1.
        id: Expression<F>,
        /// Tag to specify which field to read.
        field_tag: Expression<F>,
        /// Index to specify which byte of calldata, which is only used when
        /// field_tag is Calldata, otherwise should be set to 0.
        index: Expression<F>,
        /// Value of the field.
        value: Word<Expression<F>>,
    },
    /// Lookup to read-write table, which contains read-write access records of
    /// time-aware data.
    Rw {
        /// Counter for how much read-write have been done, which stands for
        /// the sequential timestamp.
        counter: Expression<F>,
        /// A boolean value to specify if the access record is a read or write.
        is_write: Expression<F>,
        /// Tag to specify which read-write data to access, see RwTableTag for
        /// all tags.
        tag: Expression<F>,
        /// Values corresponding to the tag.
        values: RwValues<F>,
    },
    /// Lookup to bytecode table, which contains all used creation code and
    /// contract code.
    Bytecode {
        /// Hash to specify which code to read.
        hash: Word<Expression<F>>,
        /// Tag to specify whether its the bytecode length or byte value in the
        /// bytecode.
        tag: Expression<F>,
        /// Index to specify which byte of bytecode.
        index: Expression<F>,
        /// A boolean value to specify if the value is executable opcode or the
        /// data portion of PUSH* operations.
        is_code: Expression<F>,
        /// Value corresponding to the tag.
        value: Expression<F>,
    },
    /// Lookup to block table, which contains constants of this block.
    Block {
        /// Tag to specify which field to read.
        field_tag: Expression<F>,
        /// Stores the block number only when field_tag is BlockHash, otherwise
        /// should be set to 0.
        number: Expression<F>,
        /// Value of the field.
        value: Word<Expression<F>>,
    },
    /// Lookup to copy table.
    CopyTable {
        /// Whether the row is the first row of the copy event.
        is_first: Expression<F>,
        /// The source ID for the copy event.
        src_id: Word<Expression<F>>,
        /// The source tag for the copy event.
        src_tag: Expression<F>,
        /// The destination ID for the copy event.
        dst_id: Word<Expression<F>>,
        /// The destination tag for the copy event.
        dst_tag: Expression<F>,
        /// The source address where bytes are copied from.
        src_addr: Expression<F>,
        /// The source address where all source-side bytes have been copied.
        /// This does not necessarily mean there no more bytes to be copied, but
        /// any bytes following this address will indicating padding.
        src_addr_end: Expression<F>,
        /// The destination address at which bytes are copied.
        dst_addr: Expression<F>,
        /// The number of bytes to be copied in this copy event.
        length: Expression<F>,
        /// The RLC accumulator value, which is used for SHA3 opcode.
        rlc_acc: Expression<F>,
        /// The RW counter at the start of the copy event.
        rw_counter: Expression<F>,
        /// The RW counter that is incremented by the time all bytes have been
        /// copied specific to this copy event.
        rwc_inc: Expression<F>,
    },
    /// Lookup to keccak table.
    KeccakTable {
        /// Accumulator to the input.
        input_rlc: Expression<F>,
        /// Length of input that is being hashed.
        input_len: Expression<F>,
        /// Output (hash) until this state. hash will be split into multiple expression in little
        /// endian.
        output: Word<Expression<F>>,
    },
    /// Lookup to exponentiation table.
    ExpTable {
        identifier: Expression<F>,
        is_last: Expression<F>,
        base_limbs: [Expression<F>; 4],
        exponent_lo_hi: [Expression<F>; 2],
        exponentiation_lo_hi: [Expression<F>; 2],
    },
    /// Conditional lookup enabled by the first element.
    Conditional(Expression<F>, Box<Lookup<F>>),
}

impl<F: Field> Lookup<F> {
    pub(crate) fn conditional(self, condition: Expression<F>) -> Self {
        Self::Conditional(condition, self.into())
    }

    pub(crate) fn table(&self) -> Table {
        match self {
            Self::Fixed { .. } => Table::Fixed,
            Self::Tx { .. } => Table::Tx,
            Self::Rw { .. } => Table::Rw,
            Self::Bytecode { .. } => Table::Bytecode,
            Self::Block { .. } => Table::Block,
            Self::CopyTable { .. } => Table::Copy,
            Self::KeccakTable { .. } => Table::Keccak,
            Self::ExpTable { .. } => Table::Exp,
            Self::Conditional(_, lookup) => lookup.table(),
        }
    }

    pub(crate) fn input_exprs(&self) -> Vec<Expression<F>> {
        match self {
            Self::Fixed { tag, values } => [vec![tag.clone()], values.to_vec()].concat(),
            Self::Tx {
                id,
                field_tag,
                index,
                value,
            } => vec![
                id.clone(),
                field_tag.clone(),
                index.clone(),
                value.lo(),
                value.hi(),
            ],
            Self::Rw {
                counter,
                is_write,
                tag,
                values,
            } => vec![
                counter.clone(),
                is_write.clone(),
                tag.clone(),
                values.id.clone(),
                values.address.clone(),
                values.field_tag.clone(),
                values.storage_key.lo(),
                values.storage_key.hi(),
                values.value.lo(),
                values.value.hi(),
                values.value_prev.lo(),
                values.value_prev.hi(),
                values.init_val.lo(),
                values.init_val.hi(),
            ],
            Self::Bytecode {
                hash,
                tag,
                index,
                is_code,
                value,
            } => vec![
                hash.lo(),
                hash.hi(),
                tag.clone(),
                index.clone(),
                is_code.clone(),
                value.clone(),
            ],
            Self::Block {
                field_tag,
                number,
                value,
            } => vec![field_tag.clone(), number.clone(), value.lo(), value.hi()],
            Self::CopyTable {
                is_first,
                src_id,
                src_tag,
                dst_id,
                dst_tag,
                src_addr,
                src_addr_end,
                dst_addr,
                length,
                rlc_acc,
                rw_counter,
                rwc_inc,
            } => vec![
                is_first.clone(),
                src_id.lo(),
                src_id.hi(),
                src_tag.clone(),
                dst_id.lo(),
                dst_id.hi(),
                dst_tag.clone(),
                src_addr.clone(),
                src_addr_end.clone(),
                dst_addr.clone(),
                length.clone(),
                rlc_acc.clone(),
                rw_counter.clone(),
                rwc_inc.clone(),
            ],
            Self::KeccakTable {
                input_rlc,
                input_len,
                output,
            } => vec![
                1.expr(), // is_enabled
                input_rlc.clone(),
                input_len.clone(),
                output.lo(),
                output.hi(),
            ],
            Self::ExpTable {
                identifier,
                is_last,
                base_limbs,
                exponent_lo_hi,
                exponentiation_lo_hi,
            } => vec![
                1.expr(), // is_step
                identifier.clone(),
                is_last.clone(),
                base_limbs[0].clone(),
                base_limbs[1].clone(),
                base_limbs[2].clone(),
                base_limbs[3].clone(),
                exponent_lo_hi[0].clone(),
                exponent_lo_hi[1].clone(),
                exponentiation_lo_hi[0].clone(),
                exponentiation_lo_hi[1].clone(),
            ],
            Self::Conditional(condition, lookup) => lookup
                .input_exprs()
                .into_iter()
                .map(|expr| condition.clone() * expr)
                .collect(),
        }
    }
}

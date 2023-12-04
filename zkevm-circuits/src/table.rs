//! Table definitions used cross-circuits

use crate::{
    impl_expr,
    util::{
        keccak, rlc,
        word::{self, Word},
        Challenges,
    },
    witness::{MptUpdateRow, MptUpdates},
};

#[cfg(not(feature = "js"))]
use crate::{
    util::{
        build_tx_log_address,
    }
};

#[cfg(not(feature = "js"))]
use crate::{
    copy_circuit::util::number_or_hash_to_word,
    witness::{Block, BlockContext, Rw, RwMap, RwRow, Transaction},
};

#[cfg(not(feature = "js"))]
use bus_mapping::circuit_input_builder::{CopyDataType, CopyEvent, CopyStep};
use core::iter::once;
use eth_types::{Field, ToScalar, U256};

#[cfg(not(feature = "js"))]
use gadgets::{
    binary_number::{BinaryNumberChip, BinaryNumberConfig},
    util::{split_u256, split_u256_limb64},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, *},
    poly::Rotation,
};
use itertools::Itertools;
use std::array;
use strum_macros::{EnumCount, EnumIter};

/// block table
#[cfg(not(feature = "js"))]
pub(crate) mod block_table;

/// bytecode table
#[cfg(not(feature = "js"))]
pub(crate) mod bytecode_table;

/// copy Table
#[cfg(not(feature = "js"))]
pub(crate) mod copy_table;

/// exp(exponentiation) table
#[cfg(not(feature = "js"))]
pub(crate) mod exp_table;

/// keccak table
pub(crate) mod keccak_table;

/// mpt table
pub mod mpt_table;

/// rw table
#[cfg(not(feature = "js"))]
pub(crate) mod rw_table;

/// tx table
#[cfg(not(feature = "js"))]
pub(crate) mod tx_table;

/// ux table
#[cfg(not(feature = "js"))]
pub(crate) mod ux_table;

/// withdrawal table
#[cfg(not(feature = "js"))]
pub(crate) mod wd_table;

#[cfg(not(feature = "js"))]
pub(crate) use block_table::{BlockContextFieldTag, BlockTable};

#[cfg(not(feature = "js"))]
pub(crate) use bytecode_table::{BytecodeFieldTag, BytecodeTable};

#[cfg(not(feature = "js"))]
pub(crate) use copy_table::CopyTable;

#[cfg(not(feature = "js"))]
pub(crate) use exp_table::ExpTable;

pub use keccak_table::KeccakTable;

#[cfg(not(feature = "js"))]
pub(crate) use ux_table::UXTable;

pub use mpt_table::{MPTProofType, MptTable};

#[cfg(not(feature = "js"))]
pub(crate) use rw_table::RwTable;

#[cfg(not(feature = "js"))]
pub(crate) use tx_table::{
    TxContextFieldTag, TxFieldTag, TxLogFieldTag, TxReceiptFieldTag, TxTable,
};

#[cfg(not(feature = "js"))]
pub(crate) use wd_table::WdTable;

/// Trait used to define lookup tables
pub trait LookupTable<F: Field> {
    /// Returns the list of ALL the table columns following the table order.
    fn columns(&self) -> Vec<Column<Any>>;

    /// Returns the list of ALL the table advice columns following the table
    /// order.
    fn advice_columns(&self) -> Vec<Column<Advice>> {
        self.columns()
            .iter()
            .map(|&col| col.try_into())
            .filter_map(|res| res.ok())
            .collect()
    }

    /// Returns the String annotations associated to each column of the table.
    fn annotations(&self) -> Vec<String>;

    /// Return the list of expressions used to define the lookup table.
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.columns()
            .iter()
            .map(|&column| meta.query_any(column, Rotation::cur()))
            .collect()
    }

    /// Annotates a lookup table by passing annotations for each of it's
    /// columns.
    fn annotate_columns(&self, cs: &mut ConstraintSystem<F>) {
        self.columns()
            .iter()
            .zip(self.annotations().iter())
            .for_each(|(&col, ann)| cs.annotate_lookup_any_column(col, || ann))
    }

    /// Annotates columns of a table embedded within a circuit region.
    fn annotate_columns_in_region(&self, region: &mut Region<F>) {
        self.columns()
            .iter()
            .zip(self.annotations().iter())
            .for_each(|(&col, ann)| region.name_column(|| ann, col))
    }
}

impl<F: Field, C: Into<Column<Any>> + Copy, const W: usize> LookupTable<F> for [C; W] {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.iter()
            .map(|column| meta.query_any(*column, Rotation::cur()))
            .collect()
    }

    fn columns(&self) -> Vec<Column<Any>> {
        self.iter().map(|&col| col.into()).collect()
    }

    fn annotations(&self) -> Vec<String> {
        vec![]
    }
}

/// Tag for an AccountField in RwTable
#[derive(Clone, Copy, Debug, EnumIter, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AccountFieldTag {
    /// Nonce field
    Nonce = 1,
    /// Balance field
    Balance,
    /// CodeHash field
    CodeHash,
    /// NonExisting field
    NonExisting,
}
impl_expr!(AccountFieldTag);

/// Tag for a CallContextField in RwTable
#[derive(Clone, Copy, Debug, PartialEq, Eq, EnumIter)]
pub enum CallContextFieldTag {
    /// RwCounterEndOfReversion
    RwCounterEndOfReversion = 1,
    /// CallerId
    CallerId,
    /// TxId
    TxId,
    /// Depth
    Depth,
    /// CallerAddress
    CallerAddress,
    /// CalleeAddress
    CalleeAddress,
    /// CallDataOffset
    CallDataOffset,
    /// CallDataLength
    CallDataLength,
    /// ReturnDataOffset
    ReturnDataOffset,
    /// ReturnDataLength
    ReturnDataLength,
    /// Value
    Value,
    /// IsSuccess
    IsSuccess,
    /// IsPersistent
    IsPersistent,
    /// IsStatic
    IsStatic,

    /// LastCalleeId
    LastCalleeId,
    /// LastCalleeReturnDataOffset
    LastCalleeReturnDataOffset,
    /// LastCalleeReturnDataLength
    LastCalleeReturnDataLength,

    /// IsRoot
    IsRoot,
    /// IsCreate
    IsCreate,
    /// CodeHash
    CodeHash,
    /// ProgramCounter
    ProgramCounter,
    /// StackPointer
    StackPointer,
    /// GasLeft
    GasLeft,
    /// MemorySize
    MemorySize,
    /// ReversibleWriteCounter
    ReversibleWriteCounter,
}
impl_expr!(CallContextFieldTag);

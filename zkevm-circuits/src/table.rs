//! Table definitions used cross-circuits

// CHANGELOG: Move table definitions from evm_circuit/table.rs and rw_table.rs
// to here

use crate::evm_circuit::witness::RwRow;
use crate::evm_circuit::{
    util::{rlc, RandomLinearCombination},
    witness::{BlockContext, Bytecode, RwMap, Transaction},
};
use crate::impl_expr;
use eth_types::{Field, ToLittleEndian, Word};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use halo2_proofs::{circuit::Layouter, plonk::*, poly::Rotation};
use itertools::Itertools;
use keccak256::plain::Keccak;
use strum_macros::{EnumCount, EnumIter};

// /// Trait used for dynamic tables.
// pub trait TableColumns<C: ColumnType> {
//     /// Returns the list of columns following the table order.  This trait
//     /// requires all the columns to be of the same type.
//     fn columns(&self) -> Vec<Column<C>>;
// }

/// Trait used to define lookup tables
pub trait LookupTable {
    /// Returns the list of advice columns following the table order.
    fn columns(&self) -> Vec<Column<Advice>> {
        Vec::new()
    }

    /// Return the list of expressions used to define the lookup table.
    fn table_exprs<F: Field>(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.columns()
            .iter()
            .map(|column| meta.query_advice(*column, Rotation::cur()))
            .collect()
    }
}

// impl<F: Field, T: TableColumns<Advice>> LookupTable<F> for T {
//     fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
//         self.columns()
//             .iter()
//             .map(|column| meta.query_advice(*column, Rotation::cur()))
//             .collect()
//     }
// }

impl<F: Field, C: Into<Column<Any>> + Clone, const W: usize> LookupTable<F> for [C; W] {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.iter()
            .map(|column| meta.query_any(column.clone(), Rotation::cur()))
            .collect()
    }
}

/// Tag used to identify each field in the transaction in a row of the
/// transaction table.
#[derive(Clone, Copy, Debug)]
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
}
impl_expr!(TxFieldTag);

/// Alias for TxFieldTag used by EVM Circuit
pub type TxContextFieldTag = TxFieldTag;

/// Table that contains the fields of all Transactions in a block
#[derive(Clone, Debug)]
pub struct TxTable {
    /// Tx ID
    pub tx_id: Column<Advice>,
    /// Tag (TxContextFieldTag)
    pub tag: Column<Advice>,
    /// Index for Tag = CallData
    pub index: Column<Advice>,
    /// Value
    pub value: Column<Advice>,
}

impl TxTable {
    /// Construct a new TxTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tx_id: meta.advice_column(),
            tag: meta.advice_column(),
            index: meta.advice_column(),
            value: meta.advice_column(),
        }
    }
}

impl<F: Field> LookupTable<F> for TxTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![self.tx_id, self.tag, self.index, self.value]
    }
}

/// Assign the `TxTable` from a list of block `Transaction`s, followig the same
/// layout that the Tx Circuit uses.
pub fn load_txs<F: Field>(
    tx_table: &TxTable,
    layouter: &mut impl Layouter<F>,
    txs: &[Transaction],
    randomness: F,
) -> Result<(), Error> {
    layouter.assign_region(
        || "tx table",
        |mut region| {
            let mut offset = 0;
            for column in tx_table.columns() {
                region.assign_advice(
                    || "tx table all-zero row",
                    column,
                    offset,
                    || Ok(F::zero()),
                )?;
            }
            offset += 1;

            // println!("DBG load_txs");
            let tx_table_columns = tx_table.columns();
            for tx in txs.iter() {
                for row in tx.table_assignments(randomness) {
                    // print!("{:02} ", offset);
                    for (column, value) in tx_table_columns.iter().zip_eq(row) {
                        // print!("{:?} ", value);
                        region.assign_advice(
                            || format!("tx table row {}", offset),
                            *column,
                            offset,
                            || Ok(value),
                        )?;
                    }
                    offset += 1;
                    // println!("");
                }
            }
            Ok(())
        },
    )
}

/// Tag to identify the operation type in a RwTable row
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, EnumIter)]
pub enum RwTableTag {
    /// Start (used for padding)
    Start = 1,
    /// Stack operation
    Stack,
    /// Memory operation
    Memory,
    /// Account Storage operation
    AccountStorage,
    /// Tx Access List Account operation
    TxAccessListAccount,
    /// Tx Access List Account Storage operation
    TxAccessListAccountStorage,
    /// Tx Refund operation
    TxRefund,
    /// Account operation
    Account,
    /// Account Destructed operation
    AccountDestructed,
    /// Call Context operation
    CallContext,
    /// Tx Log operation
    TxLog,
    /// Tx Receipt operation
    TxReceipt,
}
impl_expr!(RwTableTag);

impl RwTableTag {
    /// Returns true if the RwTable operation is reversible
    pub fn is_reversible(self) -> bool {
        return matches!(
            self,
            RwTableTag::TxAccessListAccount
                | RwTableTag::TxAccessListAccountStorage
                | RwTableTag::TxRefund
                | RwTableTag::Account
                | RwTableTag::AccountStorage
                | RwTableTag::AccountDestructed
        );
    }
}

impl From<RwTableTag> for usize {
    fn from(t: RwTableTag) -> Self {
        t as usize
    }
}

/// Tag for an AccountField in RwTable
#[derive(Clone, Copy, Debug, EnumIter)]
pub enum AccountFieldTag {
    /// Nonce field
    Nonce = 1,
    /// Balance field
    Balance,
    /// CodeHash field
    CodeHash,
}
impl_expr!(AccountFieldTag);

/// Tag for a TxLogField in RwTable
#[derive(Clone, Copy, Debug, PartialEq, EnumIter)]
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
#[derive(Clone, Copy, Debug, PartialEq, EnumIter, EnumCount)]
pub enum TxReceiptFieldTag {
    /// Tx result
    PostStateOrStatus = 1,
    /// CumulativeGasUsed in the tx
    CumulativeGasUsed,
    /// Number of logs in the tx
    LogLength,
}
impl_expr!(TxReceiptFieldTag);

/// Tag for a CallContextField in RwTable
#[derive(Clone, Copy, Debug, PartialEq, EnumIter)]
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

/// The RwTable shared between EVM Circuit and State Circuit, which contains
/// traces of the EVM state operations.
#[derive(Clone, Copy)]
pub struct RwTable {
    /// Read Write Counter
    pub rw_counter: Column<Advice>,
    /// Is Write
    pub is_write: Column<Advice>,
    /// Tag
    pub tag: Column<Advice>,
    /// Key1 (Id)
    pub key1: Column<Advice>,
    /// Key2 (Address)
    pub key2: Column<Advice>,
    /// Key3 (FieldTag)
    pub key3: Column<Advice>,
    /// Key3 (StorageKey)
    pub key4: Column<Advice>,
    /// Value
    pub value: Column<Advice>,
    /// Value Previous
    pub value_prev: Column<Advice>,
    /// Aux1 (Committed Value)
    pub aux1: Column<Advice>,
    /// Aux2
    pub aux2: Column<Advice>,
}

impl<F: Field> LookupTable<F> for RwTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![
            self.rw_counter,
            self.is_write,
            self.tag,
            self.key1,
            self.key2,
            self.key3,
            self.key4,
            self.value,
            self.value_prev,
            self.aux1,
            self.aux2,
        ]
    }
}
impl RwTable {
    /// Construct a new RwTable
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            rw_counter: meta.advice_column(),
            is_write: meta.advice_column(),
            tag: meta.advice_column(),
            key1: meta.advice_column(),
            key2: meta.advice_column(),
            key3: meta.advice_column(),
            key4: meta.advice_column(),
            value: meta.advice_column(),
            value_prev: meta.advice_column(),
            aux1: meta.advice_column(),
            aux2: meta.advice_column(),
        }
    }
    /// Assign a `RwRow` at offset into the `RwTable`
    pub fn assign<F: FieldExt>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &RwRow<F>,
    ) -> Result<(), Error> {
        for (column, value) in [
            (self.rw_counter, row.rw_counter),
            (self.is_write, row.is_write),
            (self.tag, row.tag),
            (self.key1, row.key1),
            (self.key2, row.key2),
            (self.key3, row.key3),
            (self.key4, row.key4),
            (self.value, row.value),
            (self.value_prev, row.value_prev),
            (self.aux1, row.aux1),
            (self.aux2, row.aux2),
        ] {
            region.assign_advice(|| "assign rw row on rw table", column, offset, || Ok(value))?;
        }
        Ok(())
    }
}

/// Assign the `RwTable` from a `RwMap`, followig the same
/// table layout that the State Circuit uses.
pub fn load_rws<F: Field>(
    rw_table: &RwTable,
    layouter: &mut impl Layouter<F>,
    rws: &RwMap,
    randomness: F,
) -> Result<(), Error> {
    layouter.assign_region(
        || "rw table",
        |mut region| {
            let mut offset = 0;
            rw_table.assign(&mut region, offset, &Default::default())?;
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

                rw_table.assign(&mut region, offset, &rw.table_assignment(randomness))?;
                offset += 1;
            }
            Ok(())
        },
    )
}

/// Tag to identify the field in a Bytecode Table row
#[derive(Clone, Copy, Debug)]
pub enum BytecodeFieldTag {
    /// Length field
    Length,
    /// Byte field
    Byte,
    /// Padding field
    Padding,
}
impl_expr!(BytecodeFieldTag);

// CHANGELOG: Added BytecodeTable to help reusing the table config with other
// circuits
/// Table with Bytecode indexed by its Code Hash
#[derive(Clone, Debug)]
pub struct BytecodeTable {
    /// Code Hash
    pub code_hash: Column<Advice>, // CHANGELOG: Renamed from hash
    /// Tag
    pub tag: Column<Advice>,
    /// Index
    pub index: Column<Advice>,
    /// Is Code is true when the byte is not an argument to a PUSH* instruction.
    pub is_code: Column<Advice>,
    /// Value
    pub value: Column<Advice>,
}

impl BytecodeTable {
    /// Construct a new BytecodeTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            code_hash: meta.advice_column(),
            tag: meta.advice_column(),
            index: meta.advice_column(),
            is_code: meta.advice_column(),
            value: meta.advice_column(),
        }
    }
}

impl<F: Field> LookupTable<F> for BytecodeTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![
            self.code_hash,
            self.tag,
            self.index,
            self.is_code,
            self.value,
        ]
    }
}

// use crate::util::TableShow;

/// Assign the `BytecodeTable` from a list of bytecodes, followig the same
/// table layout that the Bytecode Circuit uses.
pub fn load_bytecodes<'a, F: Field>(
    bytecode_table: &BytecodeTable,
    layouter: &mut impl Layouter<F>,
    bytecodes: impl IntoIterator<Item = &'a Bytecode> + Clone,
    randomness: F,
) -> Result<(), Error> {
    // println!("> load_bytecodes");
    // let mut table = TableShow::<F>::new(vec!["codeHash", "tag", "index",
    // "isCode", "value"]);
    layouter.assign_region(
        || "bytecode table",
        |mut region| {
            let mut offset = 0;
            for column in bytecode_table.columns() {
                region.assign_advice(
                    || "bytecode table all-zero row",
                    column,
                    offset,
                    || Ok(F::zero()),
                )?;
            }
            offset += 1;

            let bytecode_table_columns = bytecode_table.columns();
            for bytecode in bytecodes.clone() {
                for row in bytecode.table_assignments(randomness) {
                    // let mut column_index = 0;
                    for (column, value) in bytecode_table_columns.iter().zip_eq(row) {
                        region.assign_advice(
                            || format!("bytecode table row {}", offset),
                            *column,
                            offset,
                            || Ok(value),
                        )?;
                        // table.push(column_index, value);
                        // column_index += 1;
                    }
                    offset += 1;
                }
            }
            // table.print();
            Ok(())
        },
    )
}

/// Tag to identify the field in a Block Table row
// Keep the sequence consistent with OpcodeId for scalar
#[derive(Clone, Copy, Debug)]
pub enum BlockContextFieldTag {
    /// Coinbase field
    Coinbase = 1,
    /// Timestamp field
    Timestamp,
    /// Number field
    Number,
    /// Difficulty field
    Difficulty,
    /// Gas Limit field
    GasLimit,
    /// Base Fee field
    BaseFee = 8,
    /// Block Hash field
    BlockHash,
    /// Chain ID field.  Although this is not a field in the block header, we
    /// add it here for convenience.
    ChainId,
}
impl_expr!(BlockContextFieldTag);

/// Table with Block header fields
#[derive(Clone, Debug)]
pub struct BlockTable {
    /// Tag
    pub tag: Column<Advice>,
    /// Index
    pub index: Column<Advice>,
    /// Value
    pub value: Column<Advice>,
}

impl BlockTable {
    /// Construct a new BlockTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.advice_column(),
            index: meta.advice_column(),
            value: meta.advice_column(),
        }
    }
}

impl<F: Field> LookupTable<F> for BlockTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![self.tag, self.index, self.value]
    }
}

/// Assign the `BlockTable` from a `BlockContext`.
pub fn load_block<F: Field>(
    block_table: &BlockTable,
    layouter: &mut impl Layouter<F>,
    block: &BlockContext,
    randomness: F,
) -> Result<(), Error> {
    layouter.assign_region(
        || "block table",
        |mut region| {
            let mut offset = 0;
            for column in block_table.columns() {
                region.assign_advice(
                    || "block table all-zero row",
                    column,
                    offset,
                    || Ok(F::zero()),
                )?;
            }
            offset += 1;

            let block_table_columns = block_table.columns();
            for row in block.table_assignments(randomness) {
                for (column, value) in block_table_columns.iter().zip_eq(row) {
                    region.assign_advice(
                        || format!("block table row {}", offset),
                        *column,
                        offset,
                        || Ok(value),
                    )?;
                }
                offset += 1;
            }

            Ok(())
        },
    )
}

/// Keccak Table, used to verify keccak hashing from RLC'ed input.
#[derive(Clone, Debug)]
pub struct KeccakTable {
    /// True when the row is enabled
    pub is_enabled: Column<Advice>,
    /// Byte array input as `RLC(reversed(input))`
    pub input_rlc: Column<Advice>, // RLC of input bytes
    /// Byte array input length
    pub input_len: Column<Advice>,
    /// RLC of the hash result
    pub output_rlc: Column<Advice>, // RLC of hash of input bytes
}

impl KeccakTable {
    /// Construct a new KeccakTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_enabled: meta.advice_column(),
            input_rlc: meta.advice_column(),
            input_len: meta.advice_column(),
            output_rlc: meta.advice_column(),
        }
    }
}

impl<F: Field> LookupTable<F> for KeccakTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![
            self.is_enabled,
            self.input_rlc,
            self.input_len,
            self.output_rlc,
        ]
    }
}

/// Generate the keccak table assignments from a byte array input.
pub fn keccak_table_assignments<F: Field>(input: &[u8], randomness: F) -> Vec<[F; 4]> {
    // CHANGELOG: Using `RLC(reversed(input))`
    let input_rlc: F = rlc::value(input.iter().rev(), randomness);
    let input_len = F::from(input.len() as u64);
    let mut keccak = Keccak::default();
    keccak.update(input);
    let output = keccak.digest();
    let output_rlc = RandomLinearCombination::<F, 32>::random_linear_combine(
        Word::from_big_endian(output.as_slice()).to_le_bytes(),
        randomness,
    );

    vec![[F::one(), input_rlc, input_len, output_rlc]]
}

// NOTE: For now, the input_rlc of the keccak is defined as
// `RLC(reversed(input))` for convenience of the circuits that do the lookups.
// This allows calculating the `input_rlc` after all the inputs bytes have been
// layed out via the pattern `acc[i] = acc[i-1] * r + value[i]`.
/// Assign the `KeccakTable` from a list hashing inputs, followig the same
/// table layout that the Keccak Circuit uses.
pub fn load_keccaks<'a, F: Field>(
    keccak_table: &KeccakTable,
    layouter: &mut impl Layouter<F>,
    inputs: impl IntoIterator<Item = &'a [u8]> + Clone,
    randomness: F,
) -> Result<(), Error> {
    // println!("> super_circuit.load_keccaks");
    // let mut table = TableShow::<F>::new(vec!["is_enabled", "input_rlc",
    // "input_len", "output_rlc"]);
    layouter.assign_region(
        || "keccak table",
        |mut region| {
            let mut offset = 0;
            for column in keccak_table.columns() {
                region.assign_advice(
                    || "keccak table all-zero row",
                    column,
                    offset,
                    || Ok(F::zero()),
                )?;
            }
            offset += 1;

            let keccak_table_columns = keccak_table.columns();
            for input in inputs.clone() {
                // println!("+ {:?}", input);
                for row in keccak_table_assignments(input, randomness) {
                    // let mut column_index = 0;
                    for (column, value) in keccak_table_columns.iter().zip_eq(row) {
                        region.assign_advice(
                            || format!("keccak table row {}", offset),
                            *column,
                            offset,
                            || Ok(value),
                        )?;
                        // table.push(column_index, value);
                        // column_index += 1;
                    }
                    offset += 1;
                }
            }
            // table.print();
            Ok(())
        },
    )
}

/// Copy Table, used to verify copies of byte chunks between Memory, Bytecode,
/// TxLogs and TxCallData.
#[derive(Clone, Debug)]
pub struct CopyTable {
    /// Boolean value to indicate the first row in a copy event.
    pub is_first: Column<Advice>,
    /// Can be $txID, $callID, $codeHash (RLC encoded).
    pub id: Column<Advice>,
    /// Type of data source/destination, including Memory, Bytecode, TxCalldata,
    /// TxLog.
    pub tag: Column<Advice>,
    /// Address in the source data.  Can be memory address, byte index in the
    /// bytecode, tx call data, and tx log data.
    pub addr: Column<Advice>,
    /// Address boundary of the source data. Any data read from address greater
    /// than or equal to this value will be 0.
    pub src_addr_end: Column<Advice>,
    /// Number of bytes to be copied.
    pub bytes_left: Column<Advice>,
    /// Current RW counter at the beginning of the copy
    pub rw_counter: Column<Advice>,
    /// How much the RW counter will increase in a copy event.
    pub rwc_inc_left: Column<Advice>,
}

/*
impl CopyTable {
    /// Construct a new KeccakTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_first: meta.advice_column(),
            id: meta.advice_column(),
            tag: meta.advice_column(),
            addr: meta.advice_column(),
            src_addr_end: meta.advice_column(),
            bytes_left: meta.advice_column(),
            rw_counter: meta.advice_column(),
            rwc_inc_left: meta.advice_column(),
        }
    }
}

impl TableColumns<Advice> for CopyTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![
            self.is_first,
            self.id,
            self.tag,
            self.addr,
            self.src_addr_end,
            self.bytes_left,
            self.rw_counter,
            self.rwc_inc_left,
        ]
    }
}

impl<F: Field> LookupTable<F> for CopyTable {
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
*/

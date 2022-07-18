//! Table definitions used cross-circuits

use crate::evm_circuit::{witness::RwRow};
use crate::evm_circuit::{
    util::{rlc, RandomLinearCombination},
    witness::{BlockContext, Bytecode, RwMap, Transaction},
};
use itertools::Itertools;
use crate::impl_expr;
use eth_types::{Field, ToLittleEndian, Word};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use halo2_proofs::{circuit::Layouter, plonk::*};
use keccak256::plain::Keccak;
use strum_macros::{EnumCount, EnumIter};

pub trait TableColumns<C: ColumnType> {
    fn columns(&self) -> Vec<Column<C>>;
}

// TODO: Deduplicate with
// `zkevm-circuits/src/evm_circuit/table.rs::TxContextFieldTag`.
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
pub type TxContextFieldTag = TxFieldTag; 

/// TxTable columns
#[derive(Clone, Debug)]
pub struct TxTable {
    pub tx_id: Column<Advice>,
    pub tag: Column<Advice>,
    pub index: Column<Advice>,
    pub value: Column<Advice>,
}

impl TxTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tx_id: meta.advice_column(),
            tag: meta.advice_column(),
            index: meta.advice_column(),
            value: meta.advice_column(),
        }
    }
}

impl TableColumns<Advice> for TxTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![self.tx_id, self.tag, self.index, self.value]
    }
}

// TODO: Move to src/tables.rs
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, EnumIter)]
pub enum RwTableTag {
    Start = 1,
    Stack,
    Memory,
    AccountStorage,
    TxAccessListAccount,
    TxAccessListAccountStorage,
    TxRefund,
    Account,
    AccountDestructed,
    CallContext,
    TxLog,
    TxReceipt,
}
impl_expr!(RwTableTag);

impl RwTableTag {
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

#[derive(Clone, Copy, Debug, EnumIter)]
pub enum AccountFieldTag {
    Nonce = 1,
    Balance,
    CodeHash,
}
impl_expr!(AccountFieldTag);

#[derive(Clone, Copy, Debug, PartialEq, EnumIter)]
pub enum TxLogFieldTag {
    Address = 1,
    Topic,
    Data,
}
impl_expr!(TxLogFieldTag);

#[derive(Clone, Copy, Debug, PartialEq, EnumIter, EnumCount)]
pub enum TxReceiptFieldTag {
    PostStateOrStatus = 1,
    CumulativeGasUsed,
    LogLength,
}
impl_expr!(TxReceiptFieldTag);

#[derive(Clone, Copy, Debug, PartialEq, EnumIter)]
pub enum CallContextFieldTag {
    RwCounterEndOfReversion = 1,
    CallerId,
    TxId,
    Depth,
    CallerAddress,
    CalleeAddress,
    CallDataOffset,
    CallDataLength,
    ReturnDataOffset,
    ReturnDataLength,
    Value,
    IsSuccess,
    IsPersistent,
    IsStatic,

    LastCalleeId,
    LastCalleeReturnDataOffset,
    LastCalleeReturnDataLength,

    IsRoot,
    IsCreate,
    CodeHash,
    ProgramCounter,
    StackPointer,
    GasLeft,
    MemorySize,
    ReversibleWriteCounter,
}
impl_expr!(CallContextFieldTag);

/// The rw table shared between evm circuit and state circuit
#[derive(Clone, Copy)]
pub struct RwTable {
    pub rw_counter: Column<Advice>,
    pub is_write: Column<Advice>,
    pub tag: Column<Advice>,
    pub key1: Column<Advice>,
    pub key2: Column<Advice>,
    pub key3: Column<Advice>,
    pub key4: Column<Advice>,
    pub value: Column<Advice>,
    pub value_prev: Column<Advice>,
    pub aux1: Column<Advice>,
    pub aux2: Column<Advice>,
}

impl TableColumns<Advice> for RwTable {
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

// TODO: Move to src/tables.rs
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

#[derive(Clone, Copy, Debug)]
pub enum BytecodeFieldTag {
    Length,
    Byte,
    Padding,
}
impl_expr!(BytecodeFieldTag);

// CHANGELOG: Added BytecodeTable to help reusing the table config with other
// circuits
#[derive(Clone, Debug)]
pub struct BytecodeTable {
    pub code_hash: Column<Advice>, // CHANGELOG: Renamed from hash
    pub tag: Column<Advice>,
    pub index: Column<Advice>,
    pub is_code: Column<Advice>,
    pub value: Column<Advice>,
}

impl BytecodeTable {
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

impl TableColumns<Advice> for BytecodeTable {
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

// TODO: Move to src/tables.rs
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

// Keep the sequence consistent with OpcodeId for scalar
#[derive(Clone, Copy, Debug)]
pub enum BlockContextFieldTag {
    Coinbase = 1,
    Timestamp,
    Number,
    Difficulty,
    GasLimit,
    BaseFee = 8,
    BlockHash,
    ChainId,
}
impl_expr!(BlockContextFieldTag);

// TODO: Move to src/tables.rs
#[derive(Clone, Debug)]
pub struct BlockTable {
    pub tag: Column<Advice>,
    pub index: Column<Advice>,
    pub value: Column<Advice>,
}

impl BlockTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.advice_column(),
            index: meta.advice_column(),
            value: meta.advice_column(),
        }
    }
}

impl TableColumns<Advice> for BlockTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![self.tag, self.index, self.value]
    }
}

// TODO: Move to src/tables.rs
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

// TODO: Move to src/tables.rs
#[derive(Clone, Debug)]
pub struct KeccakTable {
    pub is_enabled: Column<Advice>,
    pub input_rlc: Column<Advice>, // RLC of input bytes
    pub input_len: Column<Advice>,
    pub output_rlc: Column<Advice>, // RLC of hash of input bytes
}

impl KeccakTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_enabled: meta.advice_column(),
            input_rlc: meta.advice_column(),
            input_len: meta.advice_column(),
            output_rlc: meta.advice_column(),
        }
    }
}

impl TableColumns<Advice> for KeccakTable {
    fn columns(&self) -> Vec<Column<Advice>> {
        vec![
            self.is_enabled,
            self.input_rlc,
            self.input_len,
            self.output_rlc,
        ]
    }
}

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

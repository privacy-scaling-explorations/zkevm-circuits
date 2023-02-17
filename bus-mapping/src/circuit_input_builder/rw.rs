use eth_types::{Address, Field, ToAddress, ToLittleEndian, ToScalar, Word, U256};
use gadgets::impl_expr;
use halo2_proofs::{circuit::Value, plonk::Expression};
use itertools::Itertools;
use strum::{EnumCount, EnumIter};

fn rlc<'a, I, F: Field>(values: I, randomness: F) -> F
where
    I: IntoIterator<Item = &'a u8>,
    <I as IntoIterator>::IntoIter: DoubleEndedIterator,
{
    let mut values = values.into_iter().rev().map(|byte| F::from(*byte as u64));
    let init = values.next().expect("values should not be empty");

    values.fold(init, |acc, value| acc * randomness + value)
}

pub fn build_tx_log_address(index: u64, field_tag: TxLogFieldTag, log_id: u64) -> Address {
    (U256::from(index) + (U256::from(field_tag as u64) << 32) + (U256::from(log_id) << 48))
        .to_address()
}

/// Marker that defines whether an Operation performs a `READ` or a `WRITE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RW {
    /// Marks op as READ.
    READ,
    /// Marks op as WRITE.
    WRITE,
}

impl RW {
    /// Returns true if the RW corresponds internally to a [`READ`](RW::READ).
    pub const fn is_read(&self) -> bool {
        matches!(self, RW::READ)
    }

    /// Returns true if the RW corresponds internally to a [`WRITE`](RW::WRITE).
    pub const fn is_write(&self) -> bool {
        matches!(self, RW::WRITE)
    }
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
        matches!(
            self,
            RwTableTag::TxAccessListAccount
                | RwTableTag::TxAccessListAccountStorage
                | RwTableTag::TxRefund
                | RwTableTag::Account
                | RwTableTag::AccountStorage
        )
    }
}

impl From<RwTableTag> for usize {
    fn from(t: RwTableTag) -> Self {
        t as usize
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

/// Tag for a TxLogField in RwTable
#[derive(Clone, Copy, Debug, PartialEq, Eq, EnumIter)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, EnumIter, EnumCount)]
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

/// Rw constainer for a witness block
#[derive(Debug, Default, Clone)]
pub struct RwMap(pub Vec<Rw>);

impl std::ops::Index<usize> for RwMap {
    type Output = Rw;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.0[idx]
    }
}

impl RwMap {
    /// TODO:
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// TODO:
    pub fn push(&mut self, rw: Rw) -> usize {
        let idx = self.0.len();
        self.0.push(rw);
        idx
    }

    /// Calculates the number of Rw::Start rows needed.
    /// `target_len` is allowed to be 0 as an "auto" mode,
    /// then only 1 Rw::Start row will be prepadded.
    /// TODO:
    pub fn padding_len(rows_len: usize, target_len: usize) -> usize {
        if target_len > rows_len {
            target_len - rows_len
        } else {
            if target_len != 0 {
                log::error!(
                    "RwMap::padding_len overflow, target_len: {}, rows_len: {}",
                    target_len,
                    rows_len
                );
            }
            1
        }
    }

    /// TODO:
    pub fn check_rw_counter_sanity(&self) {
        for (idx, rw_counter) in self
            .0
            .iter()
            .filter(|rw| !matches!(rw.tag(), RwTableTag::Start))
            .map(|r| r.rw_counter())
            .sorted()
            .enumerate()
        {
            debug_assert_eq!(idx, rw_counter - 1);
        }
    }

    /// Prepad Rw::Start rows to target length
    pub fn table_assignments_prepad(rows: &[Rw], target_len: usize) -> (Vec<Rw>, usize) {
        // Remove Start rows as we will add them from scratch.
        let rows: Vec<Rw> = rows
            .iter()
            .skip_while(|rw| matches!(rw, Rw::Start { .. }))
            .cloned()
            .collect();
        let padding_length = Self::padding_len(rows.len(), target_len);
        let padding = (1..=padding_length).map(|rw_counter| Rw::Start { rw_counter });
        (padding.chain(rows.into_iter()).collect(), padding_length)
    }

    /// Build Rws for assignment
    pub fn table_assignments(&self) -> Vec<Rw> {
        self.0
            .iter()
            .cloned()
            .sorted_by_key(|row| {
                (
                    row.tag() as u64,
                    row.id().unwrap_or_default(),
                    row.address().unwrap_or_default(),
                    row.field_tag().unwrap_or_default(),
                    row.storage_key().unwrap_or_default(),
                    row.rw_counter(),
                )
            })
            .collect()
    }
}

/// Read-write records in execution. Rws are used for connecting evm circuit and
/// state circuits.
#[derive(Clone, Copy, Debug)]
pub enum Rw {
    /// Start
    Start {
        /// TODO:
        rw_counter: usize,
    },
    /// TxAccessListAccount
    TxAccessListAccount {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        tx_id: usize,
        /// TODO:
        account_address: Address,
        /// TODO:
        is_warm: bool,
        /// TODO:
        is_warm_prev: bool,
    },
    /// TxAccessListAccountStorage
    TxAccessListAccountStorage {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        tx_id: usize,
        /// TODO:
        account_address: Address,
        /// TODO:
        storage_key: Word,
        /// TODO:
        is_warm: bool,
        /// TODO:
        is_warm_prev: bool,
    },
    /// TxRefund
    TxRefund {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        tx_id: usize,
        /// TODO:
        value: u64,
        /// TODO:
        value_prev: u64,
    },
    /// Account
    Account {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        account_address: Address,
        /// TODO:
        field_tag: AccountFieldTag,
        /// TODO:
        value: Word,
        /// TODO:
        value_prev: Word,
    },
    /// AccountStorage
    AccountStorage {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        account_address: Address,
        /// TODO:
        storage_key: Word,
        /// TODO:
        value: Word,
        /// TODO:
        value_prev: Word,
        /// TODO:
        tx_id: usize,
        /// TODO:
        committed_value: Word,
    },
    /// CallContext
    CallContext {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        call_id: usize,
        /// TODO:
        field_tag: CallContextFieldTag,
        /// TODO:
        value: Word,
    },
    /// Stack
    Stack {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        call_id: usize,
        /// TODO:
        stack_pointer: usize,
        /// TODO:
        value: Word,
    },
    /// Memory
    Memory {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        call_id: usize,
        /// TODO:
        memory_address: u64,
        /// TODO:
        byte: u8,
    },
    /// TxLog
    TxLog {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        tx_id: usize,
        /// TODO:
        log_id: u64, // pack this can index together into address?
        /// TODO:
        field_tag: TxLogFieldTag,
        /// topic index (0..4) if field_tag is TxLogFieldTag:Topic
        /// byte index if field_tag is TxLogFieldTag:Data
        /// 0 for other field tags
        index: usize,
        /// when it is topic field, value can be word type
        value: Word,
    },
    /// TxReceipt
    TxReceipt {
        /// TODO:
        rw_counter: usize,
        /// TODO:
        is_write: bool,
        /// TODO:
        tx_id: usize,
        /// TODO:
        field_tag: TxReceiptFieldTag,
        /// TODO:
        value: u64,
    },
}

/// Rw table row assignment
#[derive(Default, Clone, Copy, Debug)]
pub struct RwRow<F> {
    /// TODO:
    pub rw_counter: F,
    /// TODO:
    pub is_write: F,
    /// TODO:
    pub tag: F,
    /// TODO:
    pub id: F,
    /// TODO:
    pub address: F,
    /// TODO:
    pub field_tag: F,
    /// TODO:
    pub storage_key: F,
    /// TODO:
    pub value: F,
    /// TODO:
    pub value_prev: F,
    /// TODO:
    pub aux1: F,
    /// TODO:
    pub aux2: F,
}

impl<F: Field> RwRow<F> {
    /// TODO:
    pub fn values(&self) -> [F; 11] {
        [
            self.rw_counter,
            self.is_write,
            self.tag,
            self.id,
            self.address,
            self.field_tag,
            self.storage_key,
            self.value,
            self.value_prev,
            self.aux1,
            self.aux2,
        ]
    }
    /// TODO:
    pub fn rlc(&self, randomness: F) -> F {
        let values = self.values();
        values
            .iter()
            .rev()
            .fold(F::zero(), |acc, value| acc * randomness + value)
    }

    /// TODO:
    pub fn rlc_value(&self, randomness: Value<F>) -> Value<F> {
        randomness.map(|randomness| self.rlc(randomness))
    }
}

impl Rw {
    /// TODO:
    pub fn tx_access_list_value_pair(&self) -> (bool, bool) {
        match self {
            Self::TxAccessListAccount {
                is_warm,
                is_warm_prev,
                ..
            } => (*is_warm, *is_warm_prev),
            Self::TxAccessListAccountStorage {
                is_warm,
                is_warm_prev,
                ..
            } => (*is_warm, *is_warm_prev),
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn tx_refund_value_pair(&self) -> (u64, u64) {
        match self {
            Self::TxRefund {
                value, value_prev, ..
            } => (*value, *value_prev),
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn account_value_pair(&self) -> (Word, Word) {
        match self {
            Self::Account {
                value, value_prev, ..
            } => (*value, *value_prev),
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn aux_pair(&self) -> (usize, Word) {
        match self {
            Self::AccountStorage {
                tx_id,
                committed_value,
                ..
            } => (*tx_id, *committed_value),
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn storage_value_aux(&self) -> (Word, Word, usize, Word) {
        match self {
            Self::AccountStorage {
                value,
                value_prev,
                tx_id,
                committed_value,
                ..
            } => (*value, *value_prev, *tx_id, *committed_value),
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn call_context_value(&self) -> Word {
        match self {
            Self::CallContext { value, .. } => *value,
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn stack_value(&self) -> Word {
        match self {
            Self::Stack { value, .. } => *value,
            _ => {
                dbg!(self);
                unreachable!();
            }
        }
    }

    /// TODO:
    pub fn log_value(&self) -> Word {
        match self {
            Self::TxLog { value, .. } => *value,
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn receipt_value(&self) -> u64 {
        match self {
            Self::TxReceipt { value, .. } => *value,
            _ => unreachable!(),
        }
    }

    /// TODO:
    pub fn memory_value(&self) -> u8 {
        match self {
            Self::Memory { byte, .. } => *byte,
            _ => unreachable!(),
        }
    }

    // At this moment is a helper for the EVM circuit until EVM challange API is
    // applied
    /// TODO:
    pub fn table_assignment_aux<F: Field>(&self, randomness: F) -> RwRow<F> {
        RwRow {
            rw_counter: F::from(self.rw_counter() as u64),
            is_write: F::from(self.is_write() as u64),
            tag: F::from(self.tag() as u64),
            id: F::from(self.id().unwrap_or_default() as u64),
            address: self.address().unwrap_or_default().to_scalar().unwrap(),
            field_tag: F::from(self.field_tag().unwrap_or_default() as u64),
            storage_key: rlc(
                &self.storage_key().unwrap_or_default().to_le_bytes(),
                randomness,
            ),
            value: self.value_assignment(randomness),
            value_prev: self.value_prev_assignment(randomness).unwrap_or_default(),
            aux1: F::zero(), // only used for AccountStorage::tx_id, which moved to key1.
            aux2: self
                .committed_value_assignment(randomness)
                .unwrap_or_default(),
        }
    }

    /// TODO:
    pub fn table_assignment<F: Field>(&self, randomness: Value<F>) -> RwRow<Value<F>> {
        RwRow {
            rw_counter: Value::known(F::from(self.rw_counter() as u64)),
            is_write: Value::known(F::from(self.is_write() as u64)),
            tag: Value::known(F::from(self.tag() as u64)),
            id: Value::known(F::from(self.id().unwrap_or_default() as u64)),
            address: Value::known(self.address().unwrap_or_default().to_scalar().unwrap()),
            field_tag: Value::known(F::from(self.field_tag().unwrap_or_default() as u64)),
            storage_key: randomness.map(|randomness| {
                rlc(
                    &self.storage_key().unwrap_or_default().to_le_bytes(),
                    randomness,
                )
            }),
            value: randomness.map(|randomness| self.value_assignment(randomness)),
            value_prev: randomness
                .map(|randomness| self.value_prev_assignment(randomness).unwrap_or_default()),
            aux1: Value::known(F::zero()), /* only used for AccountStorage::tx_id, which moved to
                                            * key1. */
            aux2: randomness.map(|randomness| {
                self.committed_value_assignment(randomness)
                    .unwrap_or_default()
            }),
        }
    }

    /// TODO:
    pub fn rw_counter(&self) -> usize {
        match self {
            Self::Start { rw_counter }
            | Self::Memory { rw_counter, .. }
            | Self::Stack { rw_counter, .. }
            | Self::AccountStorage { rw_counter, .. }
            | Self::TxAccessListAccount { rw_counter, .. }
            | Self::TxAccessListAccountStorage { rw_counter, .. }
            | Self::TxRefund { rw_counter, .. }
            | Self::Account { rw_counter, .. }
            | Self::CallContext { rw_counter, .. }
            | Self::TxLog { rw_counter, .. }
            | Self::TxReceipt { rw_counter, .. } => *rw_counter,
        }
    }

    /// TODO:
    pub fn is_write(&self) -> bool {
        match self {
            Self::Start { .. } => false,
            Self::Memory { is_write, .. }
            | Self::Stack { is_write, .. }
            | Self::AccountStorage { is_write, .. }
            | Self::TxAccessListAccount { is_write, .. }
            | Self::TxAccessListAccountStorage { is_write, .. }
            | Self::TxRefund { is_write, .. }
            | Self::Account { is_write, .. }
            | Self::CallContext { is_write, .. }
            | Self::TxLog { is_write, .. }
            | Self::TxReceipt { is_write, .. } => *is_write,
        }
    }

    /// TODO:
    pub fn tag(&self) -> RwTableTag {
        match self {
            Self::Start { .. } => RwTableTag::Start,
            Self::Memory { .. } => RwTableTag::Memory,
            Self::Stack { .. } => RwTableTag::Stack,
            Self::AccountStorage { .. } => RwTableTag::AccountStorage,
            Self::TxAccessListAccount { .. } => RwTableTag::TxAccessListAccount,
            Self::TxAccessListAccountStorage { .. } => RwTableTag::TxAccessListAccountStorage,
            Self::TxRefund { .. } => RwTableTag::TxRefund,
            Self::Account { .. } => RwTableTag::Account,
            Self::CallContext { .. } => RwTableTag::CallContext,
            Self::TxLog { .. } => RwTableTag::TxLog,
            Self::TxReceipt { .. } => RwTableTag::TxReceipt,
        }
    }

    /// TODO:
    pub fn id(&self) -> Option<usize> {
        match self {
            Self::AccountStorage { tx_id, .. }
            | Self::TxAccessListAccount { tx_id, .. }
            | Self::TxAccessListAccountStorage { tx_id, .. }
            | Self::TxRefund { tx_id, .. }
            | Self::TxLog { tx_id, .. }
            | Self::TxReceipt { tx_id, .. } => Some(*tx_id),
            Self::CallContext { call_id, .. }
            | Self::Stack { call_id, .. }
            | Self::Memory { call_id, .. } => Some(*call_id),
            Self::Start { .. } | Self::Account { .. } => None,
        }
    }

    /// TODO:
    pub fn address(&self) -> Option<Address> {
        match self {
            Self::TxAccessListAccount {
                account_address, ..
            }
            | Self::TxAccessListAccountStorage {
                account_address, ..
            }
            | Self::Account {
                account_address, ..
            }
            | Self::AccountStorage {
                account_address, ..
            } => Some(*account_address),
            Self::Memory { memory_address, .. } => Some(U256::from(*memory_address).to_address()),
            Self::Stack { stack_pointer, .. } => {
                Some(U256::from(*stack_pointer as u64).to_address())
            }
            Self::TxLog {
                log_id,
                field_tag,
                index,
                ..
            } => {
                // make field_tag fit into one limb (16 bits)
                Some(build_tx_log_address(*index as u64, *field_tag, *log_id))
            }
            Self::Start { .. }
            | Self::CallContext { .. }
            | Self::TxRefund { .. }
            | Self::TxReceipt { .. } => None,
        }
    }

    /// TODO:
    pub fn field_tag(&self) -> Option<u64> {
        match self {
            Self::Account { field_tag, .. } => Some(*field_tag as u64),
            Self::CallContext { field_tag, .. } => Some(*field_tag as u64),
            Self::TxReceipt { field_tag, .. } => Some(*field_tag as u64),
            Self::Start { .. }
            | Self::Memory { .. }
            | Self::Stack { .. }
            | Self::AccountStorage { .. }
            | Self::TxAccessListAccount { .. }
            | Self::TxAccessListAccountStorage { .. }
            | Self::TxRefund { .. }
            | Self::TxLog { .. } => None,
        }
    }

    /// TODO:
    pub fn storage_key(&self) -> Option<Word> {
        match self {
            Self::AccountStorage { storage_key, .. }
            | Self::TxAccessListAccountStorage { storage_key, .. } => Some(*storage_key),
            Self::Start { .. }
            | Self::CallContext { .. }
            | Self::Stack { .. }
            | Self::Memory { .. }
            | Self::TxRefund { .. }
            | Self::Account { .. }
            | Self::TxAccessListAccount { .. }
            | Self::TxLog { .. }
            | Self::TxReceipt { .. } => None,
        }
    }

    /// TODO:
    pub fn value_assignment<F: Field>(&self, randomness: F) -> F {
        match self {
            Self::Start { .. } => F::zero(),
            Self::CallContext {
                field_tag, value, ..
            } => {
                match field_tag {
                    // Only these two tags have values that may not fit into a scalar, so we need to
                    // RLC.
                    CallContextFieldTag::CodeHash | CallContextFieldTag::Value => {
                        rlc(&value.to_le_bytes(), randomness)
                    }
                    _ => value.to_scalar().unwrap(),
                }
            }
            Self::Account {
                value, field_tag, ..
            } => match field_tag {
                AccountFieldTag::CodeHash | AccountFieldTag::Balance => {
                    rlc(&value.to_le_bytes(), randomness)
                }
                AccountFieldTag::Nonce | AccountFieldTag::NonExisting => value.to_scalar().unwrap(),
            },
            Self::AccountStorage { value, .. } | Self::Stack { value, .. } => {
                rlc(&value.to_le_bytes(), randomness)
            }

            Self::TxLog {
                field_tag, value, ..
            } => match field_tag {
                TxLogFieldTag::Topic => rlc(&value.to_le_bytes(), randomness),
                _ => value.to_scalar().unwrap(),
            },

            Self::TxAccessListAccount { is_warm, .. }
            | Self::TxAccessListAccountStorage { is_warm, .. } => F::from(*is_warm as u64),
            Self::Memory { byte, .. } => F::from(u64::from(*byte)),
            Self::TxRefund { value, .. } | Self::TxReceipt { value, .. } => F::from(*value),
        }
    }

    /// TODO:
    pub fn value_prev_assignment<F: Field>(&self, randomness: F) -> Option<F> {
        match self {
            Self::Account {
                value_prev,
                field_tag,
                ..
            } => Some(match field_tag {
                AccountFieldTag::CodeHash | AccountFieldTag::Balance => {
                    rlc(&value_prev.to_le_bytes(), randomness)
                }
                AccountFieldTag::Nonce | AccountFieldTag::NonExisting => {
                    value_prev.to_scalar().unwrap()
                }
            }),
            Self::AccountStorage { value_prev, .. } => {
                Some(rlc(&value_prev.to_le_bytes(), randomness))
            }
            Self::TxAccessListAccount { is_warm_prev, .. }
            | Self::TxAccessListAccountStorage { is_warm_prev, .. } => {
                Some(F::from(*is_warm_prev as u64))
            }
            Self::TxRefund { value_prev, .. } => Some(F::from(*value_prev)),
            Self::Start { .. }
            | Self::Stack { .. }
            | Self::Memory { .. }
            | Self::CallContext { .. }
            | Self::TxLog { .. }
            | Self::TxReceipt { .. } => None,
        }
    }

    fn committed_value_assignment<F: Field>(&self, randomness: F) -> Option<F> {
        match self {
            Self::AccountStorage {
                committed_value, ..
            } => Some(rlc(&committed_value.to_le_bytes(), randomness)),
            _ => None,
        }
    }
}

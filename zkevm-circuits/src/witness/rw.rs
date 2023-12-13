//! The Read-Write table related structs
use std::{collections::HashMap, iter};

use bus_mapping::{
    exec_trace::OperationRef,
    operation::{
        self, AccountField, CallContextField, StepStateField, Target, TxLogField, TxReceiptField,
    },
};
use eth_types::{Address, Field, ToAddress, ToScalar, Word, U256};
use halo2_proofs::circuit::Value;
use itertools::Itertools;

use crate::{
    table::{
        AccountFieldTag, CallContextFieldTag, StepStateFieldTag, TxLogFieldTag, TxReceiptFieldTag,
    },
    util::{build_tx_log_address, unwrap_value, word},
};

use super::MptUpdates;

const U64_BYTES: usize = u64::BITS as usize / 8usize;

/// Rw constainer for a witness block
#[derive(Debug, Default, Clone)]
pub struct RwMap(pub HashMap<Target, Vec<Rw>>);

impl std::ops::Index<(Target, usize)> for RwMap {
    type Output = Rw;

    fn index(&self, (tag, idx): (Target, usize)) -> &Self::Output {
        &self.0.get(&tag).unwrap()[idx]
    }
}

impl std::ops::Index<OperationRef> for RwMap {
    type Output = Rw;

    fn index(&self, OperationRef(tag, idx): OperationRef) -> &Self::Output {
        &self.0.get(&tag).unwrap()[idx]
    }
}

impl RwMap {
    /// Check rw_counter is continuous
    pub fn check_rw_counter_sanity(&self) {
        for (rw_counter_prev, rw_counter_cur) in self
            .0
            .iter()
            .filter(|(tag, _rs)| !matches!(tag, Target::Padding) && !matches!(tag, Target::Start))
            .flat_map(|(_tag, rs)| rs)
            .map(|r| r.rw_counter())
            .sorted()
            .tuple_windows()
        {
            debug_assert_eq!(rw_counter_cur - rw_counter_prev, 1);
        }
    }
    /// Check value in the same way like StateCircuit
    pub fn check_value(&self) {
        let err_msg_first = "first access reads don't change value";
        let err_msg_non_first = "non-first access reads don't change value";
        let rows = self.table_assignments(false);
        let updates = MptUpdates::mock_from(&rows);
        let mut errs = Vec::new();
        for idx in 1..rows.len() {
            let row = &rows[idx];
            let prev_row = &rows[idx - 1];
            let is_first = {
                let key = |row: &Rw| {
                    (
                        row.tag() as u64,
                        row.id().unwrap_or_default(),
                        row.address().unwrap_or_default(),
                        row.field_tag().unwrap_or_default(),
                        row.storage_key().unwrap_or_default(),
                    )
                };
                key(prev_row) != key(row)
            };
            if !row.is_write() {
                let value = row.value_assignment();
                if is_first {
                    // value == init_value
                    let init_value = updates
                        .get(row)
                        .map(|u| u.value_assignments().1)
                        .unwrap_or_default();
                    if value != init_value {
                        errs.push((idx, err_msg_first, *row, *prev_row));
                    }
                } else {
                    // value == prev_value
                    let prev_value = prev_row.value_assignment();

                    if value != prev_value {
                        errs.push((idx, err_msg_non_first, *row, *prev_row));
                    }
                }
            }
        }
        if !errs.is_empty() {
            log::error!("after rw value check, err num: {}", errs.len());
            for (idx, err_msg, row, prev_row) in errs {
                log::error!(
                    "err: rw idx: {}, reason: \"{}\", row: {:?}, prev_row: {:?}",
                    idx,
                    err_msg,
                    row,
                    prev_row
                );
            }
        }
    }
    /// Calculates the number of Rw::Padding rows needed.
    /// `target_len` is allowed to be 0 as an "auto" mode,
    pub(crate) fn padding_len(rows_len: usize, target_len: usize) -> usize {
        if target_len > rows_len {
            target_len - rows_len
        } else {
            if target_len != 0 {
                panic!(
                    "RwMap::padding_len overflow, target_len: {}, rows_len: {}",
                    target_len, rows_len
                );
            }
            0
        }
    }
    /// padding Rw::Start/Rw::Padding accordingly
    pub fn table_assignments_padding(
        rows: &[Rw],
        target_len: usize,
        is_first_row_padding: bool,
    ) -> (Vec<Rw>, usize) {
        // Remove Start/Padding rows as we will add them from scratch.
        let rows_trimmed: Vec<Rw> = rows
            .iter()
            .filter(|rw| !matches!(rw, Rw::Start { .. } | Rw::Padding { .. }))
            .cloned()
            .collect();
        let padding_length = {
            let length = Self::padding_len(rows_trimmed.len(), target_len);
            if is_first_row_padding {
                length.saturating_sub(1)
            } else {
                length
            }
        };

        // option 1: need to provide padding starting rw_counter at function parameters
        // option 2: just padding after local max rw_counter + 1
        // We adapt option 2 for now
        // the side effect is it introduce malleable proof when append `Rw::Padding` rw_counter,
        // because `Rw::Padding` is not global unique
        let start_padding_rw_counter = rows_trimmed
            .iter()
            .map(|rw| rw.rw_counter())
            .max()
            .unwrap_or(1)
            + 1;
        let padding = (start_padding_rw_counter..start_padding_rw_counter + padding_length)
            .map(|rw_counter| Rw::Padding { rw_counter });
        (
            iter::empty()
                .chain(is_first_row_padding.then_some(Rw::Start { rw_counter: 1 }))
                .chain(rows_trimmed.into_iter())
                .chain(padding.into_iter())
                .collect(),
            padding_length,
        )
    }
    /// Build Rws for assignment
    pub fn table_assignments(&self, keep_chronological_order: bool) -> Vec<Rw> {
        let mut rows: Vec<Rw> = self.0.values().flatten().cloned().collect();
        if keep_chronological_order {
            rows.sort_by_key(|row| (row.rw_counter(), row.tag() as u64));
        } else {
            rows.sort_by_key(|row| {
                (
                    row.tag() as u64,
                    row.id().unwrap_or_default(),
                    row.address().unwrap_or_default(),
                    row.field_tag().unwrap_or_default(),
                    row.storage_key().unwrap_or_default(),
                    row.rw_counter(),
                )
            });
        }

        rows
    }

    /// Get RwMap for a chunk specified by start and end
    pub fn from_chunked(
        container: &operation::OperationContainer,
        start: usize,
        end: usize,
    ) -> Self {
        let mut rws: Self = container.into();
        for rw in rws.0.values_mut() {
            rw.retain(|r| r.rw_counter() >= start && r.rw_counter() < end)
        }
        rws
    }

}

#[allow(
    missing_docs,
    reason = "Some of the docs are tedious and can be found at https://github.com/privacy-scaling-explorations/zkevm-specs/blob/master/specs/tables.md"
)]
/// Read-write records in execution. Rws are used for connecting evm circuit and
/// state circuits.
#[derive(Clone, Copy, Debug)]
pub enum Rw {
    /// Start
    Start { rw_counter: usize },
    /// TxAccessListAccount
    TxAccessListAccount {
        rw_counter: usize,
        is_write: bool,
        tx_id: usize,
        account_address: Address,
        is_warm: bool,
        is_warm_prev: bool,
    },
    /// TxAccessListAccountStorage
    TxAccessListAccountStorage {
        rw_counter: usize,
        is_write: bool,
        tx_id: usize,
        account_address: Address,
        storage_key: Word,
        is_warm: bool,
        is_warm_prev: bool,
    },
    /// TxRefund
    TxRefund {
        rw_counter: usize,
        is_write: bool,
        tx_id: usize,
        value: u64,
        value_prev: u64,
    },
    /// Account
    Account {
        rw_counter: usize,
        is_write: bool,
        account_address: Address,
        field_tag: AccountFieldTag,
        value: Word,
        value_prev: Word,
    },
    /// AccountStorage
    AccountStorage {
        rw_counter: usize,
        is_write: bool,
        account_address: Address,
        storage_key: Word,
        value: Word,
        value_prev: Word,
        tx_id: usize,
        committed_value: Word,
    },
    /// CallContext
    CallContext {
        rw_counter: usize,
        is_write: bool,
        call_id: usize,
        field_tag: CallContextFieldTag,
        value: Word,
    },
    /// Stack
    Stack {
        rw_counter: usize,
        is_write: bool,
        call_id: usize,
        stack_pointer: usize,
        value: Word,
    },
    /// Memory
    Memory {
        rw_counter: usize,
        is_write: bool,
        call_id: usize,
        memory_address: u64,
        byte: u8,
    },
    /// TxLog
    TxLog {
        rw_counter: usize,
        is_write: bool,
        tx_id: usize,
        log_id: u64, // pack this can index together into address?
        field_tag: TxLogFieldTag,
        /// index has 3 usages depends on `crate::table::TxLogFieldTag`
        /// - topic index (0..4) if field_tag is TxLogFieldTag::Topic
        /// - byte index if field_tag is TxLogFieldTag:Data
        /// - 0 for other field tags
        index: usize,
        /// when it is topic field, value can be word type
        value: Word,
    },
    /// TxReceipt
    TxReceipt {
        rw_counter: usize,
        is_write: bool,
        tx_id: usize,
        field_tag: TxReceiptFieldTag,
        value: u64,
    },

    /// StepState
    StepState {
        rw_counter: usize,
        is_write: bool,
        field_tag: StepStateFieldTag,
        value: Word,
    },

    /// ...

    /// Padding, must be the largest enum
    Padding { rw_counter: usize },
}

/// general to vector
pub trait ToVec<T> {
    /// to 2d vec
    fn to2dvec(&self) -> Vec<Vec<T>>;
}

impl<F: Field> ToVec<Value<F>> for Vec<Rw> {
    fn to2dvec(&self) -> Vec<Vec<Value<F>>> {
        self.iter()
            .map(|row| {
                row.table_assignment::<F>()
                    .unwrap()
                    .values()
                    .iter()
                    .map(|f| Value::known(*f))
                    .collect::<Vec<Value<F>>>()
            })
            .collect::<Vec<Vec<Value<F>>>>()
    }
}

/// Rw table row assignment
#[derive(Default, Clone, Copy, Debug)]
pub struct RwRow<F> {
    pub(crate) rw_counter: F,
    pub(crate) is_write: F,
    pub(crate) tag: F,
    pub(crate) id: F,
    pub(crate) address: F,
    pub(crate) field_tag: F,
    pub(crate) storage_key: word::Word<F>,
    pub(crate) value: word::Word<F>,
    pub(crate) value_prev: word::Word<F>,
    pub(crate) init_val: word::Word<F>,
}

impl<F: Field> RwRow<F> {
    pub(crate) fn values(&self) -> [F; 14] {
        [
            self.rw_counter,
            self.is_write,
            self.tag,
            self.id,
            self.address,
            self.field_tag,
            self.storage_key.lo(),
            self.storage_key.hi(),
            self.value.lo(),
            self.value.hi(),
            self.value_prev.lo(),
            self.value_prev.hi(),
            self.init_val.lo(),
            self.init_val.hi(),
        ]
    }

    pub(crate) fn rlc(&self, randomness: F) -> F {
        let values = self.values();
        values
            .iter()
            .rev()
            .fold(F::ZERO, |acc, value| acc * randomness + value)
    }
}

impl<F: Field> RwRow<Value<F>> {
    pub(crate) fn unwrap(self) -> RwRow<F> {
        let unwrap_f = |f: Value<F>| {
            let mut inner = None;
            _ = f.map(|v| {
                inner = Some(v);
            });
            inner.unwrap_or_default()
        };
        let unwrap_w = |f: word::Word<Value<F>>| {
            let (lo, hi) = f.into_lo_hi();
            word::Word::new([unwrap_f(lo), unwrap_f(hi)])
        };

        RwRow {
            rw_counter: unwrap_f(self.rw_counter),
            is_write: unwrap_f(self.is_write),
            tag: unwrap_f(self.tag),
            id: unwrap_f(self.id),
            address: unwrap_f(self.address),
            field_tag: unwrap_f(self.field_tag),
            storage_key: unwrap_w(self.storage_key),
            value: unwrap_w(self.value),
            value_prev: unwrap_w(self.value_prev),
            init_val: unwrap_w(self.init_val),
        }
    }

    /// padding Rw::Start/Rw::Padding accordingly
    pub fn padding(
        rows: &[RwRow<Value<F>>],
        target_len: usize,
        is_first_row_padding: bool,
    ) -> (Vec<RwRow<Value<F>>>, usize) {
        // Remove Start/Padding rows as we will add them from scratch.
        let rows_trimmed = rows
            .iter()
            .filter(|rw| {
                let tag = unwrap_value(rw.tag);
                !(tag == F::from(Target::Start as u64) || tag == F::from(Target::Padding as u64))
                    && tag != F::ZERO // 0 is invalid tag
            })
            .cloned()
            .collect::<Vec<RwRow<Value<F>>>>();
        let padding_length = {
            let length = RwMap::padding_len(rows_trimmed.len(), target_len);
            if is_first_row_padding {
                length.saturating_sub(1)
            } else {
                length
            }
        };
        let start_padding_rw_counter = {
            let start_padding_rw_counter = rows_trimmed
                .iter()
                .map(|rw| unwrap_value(rw.rw_counter))
                .max()
                .unwrap_or(F::from(1u64))
                + F::ONE;
            // Assume root of unity < 2**64
            assert!(
                start_padding_rw_counter.to_repr()[U64_BYTES..]
                    .iter()
                    .cloned()
                    .sum::<u8>()
                    == 0,
                "rw counter > 2 ^ 64"
            );
            u64::from_le_bytes(
                start_padding_rw_counter.to_repr()[..U64_BYTES]
                    .try_into()
                    .unwrap(),
            )
        } as usize;

        let padding = (start_padding_rw_counter..start_padding_rw_counter + padding_length).map(
            |rw_counter| RwRow {
                rw_counter: Value::known(F::from(rw_counter as u64)),
                tag: Value::known(F::from(Target::Padding as u64)),
                ..Default::default()
            },
        );
        (
            iter::once(RwRow {
                rw_counter: Value::known(F::ONE),
                tag: Value::known(F::from(Target::Start as u64)),
                ..Default::default()
            })
            .take(if is_first_row_padding { 1 } else { 0 })
            .chain(rows_trimmed.into_iter())
            .chain(padding.into_iter())
            .collect(),
            padding_length,
        )
    }
}

impl<F: Field> ToVec<Value<F>> for Vec<RwRow<Value<F>>> {
    fn to2dvec(&self) -> Vec<Vec<Value<F>>> {
        self.iter()
            .map(|row| {
                row.unwrap()
                    .values()
                    .iter()
                    .map(|f| Value::known(*f))
                    .collect::<Vec<Value<F>>>()
            })
            .collect::<Vec<Vec<Value<F>>>>()
    }
}

impl Rw {
    pub(crate) fn tx_access_list_value_pair(&self) -> (bool, bool) {
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

    pub(crate) fn tx_refund_value_pair(&self) -> (u64, u64) {
        match self {
            Self::TxRefund {
                value, value_prev, ..
            } => (*value, *value_prev),
            _ => unreachable!(),
        }
    }

    pub(crate) fn account_balance_pair(&self) -> (Word, Word) {
        match self {
            Self::Account {
                value,
                value_prev,
                field_tag,
                ..
            } => {
                debug_assert_eq!(field_tag, &AccountFieldTag::Balance);
                (*value, *value_prev)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn account_nonce_pair(&self) -> (Word, Word) {
        match self {
            Self::Account {
                value,
                value_prev,
                field_tag,
                ..
            } => {
                debug_assert_eq!(field_tag, &AccountFieldTag::Nonce);
                (*value, *value_prev)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn account_codehash_pair(&self) -> (Word, Word) {
        match self {
            Self::Account {
                value,
                value_prev,
                field_tag,
                ..
            } => {
                debug_assert_eq!(field_tag, &AccountFieldTag::CodeHash);
                (*value, *value_prev)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn aux_pair(&self) -> (usize, Word) {
        match self {
            Self::AccountStorage {
                tx_id,
                committed_value,
                ..
            } => (*tx_id, *committed_value),
            _ => unreachable!(),
        }
    }

    pub(crate) fn storage_value_aux(&self) -> (Word, Word, usize, Word) {
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

    pub(crate) fn call_context_value(&self) -> Word {
        match self {
            Self::CallContext { value, .. } => *value,
            _ => unreachable!(),
        }
    }

    pub(crate) fn stack_value(&self) -> Word {
        match self {
            Self::Stack { value, .. } => *value,
            _ => unreachable!(),
        }
    }

    pub(crate) fn receipt_value(&self) -> u64 {
        match self {
            Self::TxReceipt { value, .. } => *value,
            _ => unreachable!(),
        }
    }

    pub(crate) fn memory_value(&self) -> u8 {
        match self {
            Self::Memory { byte, .. } => *byte,
            _ => unreachable!(),
        }
    }

    pub(crate) fn table_assignment<F: Field>(&self) -> RwRow<Value<F>> {
        RwRow {
            rw_counter: Value::known(F::from(self.rw_counter() as u64)),
            is_write: Value::known(F::from(self.is_write() as u64)),
            tag: Value::known(F::from(self.tag() as u64)),
            id: Value::known(F::from(self.id().unwrap_or_default() as u64)),
            address: Value::known(self.address().unwrap_or_default().to_scalar().unwrap()),
            field_tag: Value::known(F::from(self.field_tag().unwrap_or_default())),
            storage_key: word::Word::from(self.storage_key().unwrap_or_default()).into_value(),
            value: word::Word::from(self.value_assignment()).into_value(),
            value_prev: word::Word::from(self.value_prev_assignment().unwrap_or_default())
                .into_value(),
            init_val: word::Word::from(self.committed_value_assignment().unwrap_or_default())
                .into_value(),
        }
    }

    pub(crate) fn rw_counter(&self) -> usize {
        match self {
            Self::Start { rw_counter }
            | Self::Padding { rw_counter }
            | Self::Memory { rw_counter, .. }
            | Self::Stack { rw_counter, .. }
            | Self::AccountStorage { rw_counter, .. }
            | Self::TxAccessListAccount { rw_counter, .. }
            | Self::TxAccessListAccountStorage { rw_counter, .. }
            | Self::TxRefund { rw_counter, .. }
            | Self::Account { rw_counter, .. }
            | Self::CallContext { rw_counter, .. }
            | Self::StepState { rw_counter, .. }
            | Self::TxLog { rw_counter, .. }
            | Self::TxReceipt { rw_counter, .. } => *rw_counter,
        }
    }

    pub(crate) fn is_write(&self) -> bool {
        match self {
            Self::Padding { .. } | Self::Start { .. } => false,
            Self::Memory { is_write, .. }
            | Self::Stack { is_write, .. }
            | Self::AccountStorage { is_write, .. }
            | Self::TxAccessListAccount { is_write, .. }
            | Self::TxAccessListAccountStorage { is_write, .. }
            | Self::TxRefund { is_write, .. }
            | Self::Account { is_write, .. }
            | Self::CallContext { is_write, .. }
            | Self::StepState { is_write, .. }
            | Self::TxLog { is_write, .. }
            | Self::TxReceipt { is_write, .. } => *is_write,
        }
    }

    pub(crate) fn tag(&self) -> Target {
        match self {
            Self::Padding { .. } => Target::Padding,
            Self::Start { .. } => Target::Start,
            Self::Memory { .. } => Target::Memory,
            Self::Stack { .. } => Target::Stack,
            Self::AccountStorage { .. } => Target::Storage,
            Self::TxAccessListAccount { .. } => Target::TxAccessListAccount,
            Self::TxAccessListAccountStorage { .. } => Target::TxAccessListAccountStorage,
            Self::TxRefund { .. } => Target::TxRefund,
            Self::Account { .. } => Target::Account,
            Self::CallContext { .. } => Target::CallContext,
            Self::TxLog { .. } => Target::TxLog,
            Self::TxReceipt { .. } => Target::TxReceipt,
            Self::StepState { .. } => Target::StepState,
        }
    }

    pub(crate) fn id(&self) -> Option<usize> {
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
            Self::Padding { .. }
            | Self::Start { .. }
            | Self::Account { .. }
            | Self::StepState { .. } => None,
        }
    }

    pub(crate) fn address(&self) -> Option<Address> {
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
            Self::Padding { .. }
            | Self::Start { .. }
            | Self::CallContext { .. }
            | Self::StepState { .. }
            | Self::TxRefund { .. }
            | Self::TxReceipt { .. } => None,
        }
    }

    pub(crate) fn field_tag(&self) -> Option<u64> {
        match self {
            Self::Account { field_tag, .. } => Some(*field_tag as u64),
            Self::CallContext { field_tag, .. } => Some(*field_tag as u64),
            Self::StepState { field_tag, .. } => Some(*field_tag as u64),
            Self::TxReceipt { field_tag, .. } => Some(*field_tag as u64),
            Self::Padding { .. }
            | Self::Start { .. }
            | Self::Memory { .. }
            | Self::Stack { .. }
            | Self::AccountStorage { .. }
            | Self::TxAccessListAccount { .. }
            | Self::TxAccessListAccountStorage { .. }
            | Self::TxRefund { .. }
            | Self::TxLog { .. } => None,
        }
    }

    pub(crate) fn storage_key(&self) -> Option<Word> {
        match self {
            Self::AccountStorage { storage_key, .. }
            | Self::TxAccessListAccountStorage { storage_key, .. } => Some(*storage_key),
            Self::Padding { .. }
            | Self::Start { .. }
            | Self::CallContext { .. }
            | Self::StepState { .. }
            | Self::Stack { .. }
            | Self::Memory { .. }
            | Self::TxRefund { .. }
            | Self::Account { .. }
            | Self::TxAccessListAccount { .. }
            | Self::TxLog { .. }
            | Self::TxReceipt { .. } => None,
        }
    }

    pub(crate) fn value_assignment(&self) -> Word {
        match self {
            Self::Padding { .. } | Self::Start { .. } => U256::zero(),
            Self::CallContext { value, .. }
            | Self::StepState { value, .. }
            | Self::Account { value, .. }
            | Self::AccountStorage { value, .. }
            | Self::Stack { value, .. }
            | Self::TxLog { value, .. } => *value,
            Self::TxAccessListAccount { is_warm, .. }
            | Self::TxAccessListAccountStorage { is_warm, .. } => U256::from(*is_warm as u64),
            Self::Memory { byte, .. } => U256::from(u64::from(*byte)),
            Self::TxRefund { value, .. } | Self::TxReceipt { value, .. } => U256::from(*value),
        }
    }

    pub(crate) fn value_prev_assignment(&self) -> Option<Word> {
        match self {
            Self::Account { value_prev, .. } | Self::AccountStorage { value_prev, .. } => {
                Some(*value_prev)
            }
            Self::TxAccessListAccount { is_warm_prev, .. }
            | Self::TxAccessListAccountStorage { is_warm_prev, .. } => {
                Some(U256::from(*is_warm_prev as u64))
            }
            Self::TxRefund { value_prev, .. } => Some(U256::from(*value_prev)),
            Self::Padding { .. }
            | Self::Start { .. }
            | Self::Stack { .. }
            | Self::Memory { .. }
            | Self::CallContext { .. }
            | Self::StepState { .. }
            | Self::TxLog { .. }
            | Self::TxReceipt { .. } => None,
        }
    }

    fn committed_value_assignment(&self) -> Option<Word> {
        match self {
            Self::AccountStorage {
                committed_value, ..
            } => Some(*committed_value),
            _ => None,
        }
    }
}

impl From<&operation::OperationContainer> for RwMap {
    fn from(container: &operation::OperationContainer) -> Self {
        // Get rws raning all indices from the whole container
        {
            let mut rws = HashMap::<Target, Vec<Rw>>::default();
    
            rws.insert(
                Target::Padding,
                container
                    .padding
                    .iter()
                    .map(|op| Rw::Padding {
                        rw_counter: op.rwc().into(),
                    })
                    .collect(),
            );
            rws.insert(
                Target::Start,
                container
                    .start
                    .iter()
                    .map(|op| Rw::Start {
                        rw_counter: op.rwc().into(),
                    })
                    .collect(),
            );
            rws.insert(
                Target::TxAccessListAccount,
                container
                    .tx_access_list_account
                    .iter()
                    .map(|op| Rw::TxAccessListAccount {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        tx_id: op.op().tx_id,
                        account_address: op.op().address,
                        is_warm: op.op().is_warm,
                        is_warm_prev: op.op().is_warm_prev,
                    })
                    .collect(),
            );
            rws.insert(
                Target::TxAccessListAccountStorage,
                container
                    .tx_access_list_account_storage
                    .iter()
                    .map(|op| Rw::TxAccessListAccountStorage {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        tx_id: op.op().tx_id,
                        account_address: op.op().address,
                        storage_key: op.op().key,
                        is_warm: op.op().is_warm,
                        is_warm_prev: op.op().is_warm_prev,
                    })
                    .collect(),
            );
            rws.insert(
                Target::TxRefund,
                container
                    .tx_refund
                    .iter()
                    .map(|op| Rw::TxRefund {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        tx_id: op.op().tx_id,
                        value: op.op().value,
                        value_prev: op.op().value_prev,
                    })
                    .collect(),
            );
            rws.insert(
                Target::Account,
                container
                    .account
                    .iter()
                    .map(|op| Rw::Account {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        account_address: op.op().address,
                        field_tag: match op.op().field {
                            AccountField::Nonce => AccountFieldTag::Nonce,
                            AccountField::Balance => AccountFieldTag::Balance,
                            AccountField::CodeHash => AccountFieldTag::CodeHash,
                        },
                        value: op.op().value,
                        value_prev: op.op().value_prev,
                    })
                    .collect(),
            );
            rws.insert(
                Target::Storage,
                container
                    .storage
                    .iter()
                    .map(|op| Rw::AccountStorage {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        account_address: op.op().address,
                        storage_key: op.op().key,
                        value: op.op().value,
                        value_prev: op.op().value_prev,
                        tx_id: op.op().tx_id,
                        committed_value: op.op().committed_value,
                    })
                    .collect(),
            );
            rws.insert(
                Target::CallContext,
                container
                    .call_context
                    .iter()
                    .map(|op| Rw::CallContext {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        call_id: op.op().call_id,
                        field_tag: match op.op().field {
                            CallContextField::RwCounterEndOfReversion => {
                                CallContextFieldTag::RwCounterEndOfReversion
                            }
                            CallContextField::CallerId => CallContextFieldTag::CallerId,
                            CallContextField::TxId => CallContextFieldTag::TxId,
                            CallContextField::Depth => CallContextFieldTag::Depth,
                            CallContextField::CallerAddress => CallContextFieldTag::CallerAddress,
                            CallContextField::CalleeAddress => CallContextFieldTag::CalleeAddress,
                            CallContextField::CallDataOffset => CallContextFieldTag::CallDataOffset,
                            CallContextField::CallDataLength => CallContextFieldTag::CallDataLength,
                            CallContextField::ReturnDataOffset => CallContextFieldTag::ReturnDataOffset,
                            CallContextField::ReturnDataLength => CallContextFieldTag::ReturnDataLength,
                            CallContextField::Value => CallContextFieldTag::Value,
                            CallContextField::IsSuccess => CallContextFieldTag::IsSuccess,
                            CallContextField::IsPersistent => CallContextFieldTag::IsPersistent,
                            CallContextField::IsStatic => CallContextFieldTag::IsStatic,
                            CallContextField::LastCalleeId => CallContextFieldTag::LastCalleeId,
                            CallContextField::LastCalleeReturnDataOffset => {
                                CallContextFieldTag::LastCalleeReturnDataOffset
                            }
                            CallContextField::LastCalleeReturnDataLength => {
                                CallContextFieldTag::LastCalleeReturnDataLength
                            }
                            CallContextField::IsRoot => CallContextFieldTag::IsRoot,
                            CallContextField::IsCreate => CallContextFieldTag::IsCreate,
                            CallContextField::CodeHash => CallContextFieldTag::CodeHash,
                            CallContextField::ProgramCounter => CallContextFieldTag::ProgramCounter,
                            CallContextField::StackPointer => CallContextFieldTag::StackPointer,
                            CallContextField::GasLeft => CallContextFieldTag::GasLeft,
                            CallContextField::MemorySize => CallContextFieldTag::MemorySize,
                            CallContextField::ReversibleWriteCounter => {
                                CallContextFieldTag::ReversibleWriteCounter
                            }
                        },
                        value: op.op().value,
                    })
                    .collect(),
            );
            rws.insert(
                Target::Stack,
                container
                    .stack
                    .iter()
                    .map(|op| Rw::Stack {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        call_id: op.op().call_id(),
                        stack_pointer: usize::from(*op.op().address()),
                        value: *op.op().value(),
                    })
                    .collect(),
            );
            rws.insert(
                Target::Memory,
                container
                    .memory
                    .iter()
                    .map(|op| Rw::Memory {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        call_id: op.op().call_id(),
                        memory_address: u64::from_le_bytes(
                            op.op().address().to_le_bytes()[..U64_BYTES]
                                .try_into()
                                .unwrap(),
                        ),
                        byte: op.op().value(),
                    })
                    .collect(),
            );
            rws.insert(
                Target::TxLog,
                container
                    .tx_log
                    .iter()
                    .map(|op| Rw::TxLog {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        tx_id: op.op().tx_id,
                        log_id: op.op().log_id as u64,
                        field_tag: match op.op().field {
                            TxLogField::Address => TxLogFieldTag::Address,
                            TxLogField::Topic => TxLogFieldTag::Topic,
                            TxLogField::Data => TxLogFieldTag::Data,
                        },
                        index: op.op().index,
                        value: op.op().value,
                    })
                    .collect(),
            );
            rws.insert(
                Target::TxReceipt,
                container
                    .tx_receipt
                    .iter()
                    .map(|op| Rw::TxReceipt {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        tx_id: op.op().tx_id,
                        field_tag: match op.op().field {
                            TxReceiptField::PostStateOrStatus => TxReceiptFieldTag::PostStateOrStatus,
                            TxReceiptField::LogLength => TxReceiptFieldTag::LogLength,
                            TxReceiptField::CumulativeGasUsed => TxReceiptFieldTag::CumulativeGasUsed,
                        },
                        value: op.op().value,
                    })
                    .collect(),
            );
            rws.insert(
                Target::StepState,
                container
                    .step_state
                    .iter()
                    .map(|op| Rw::StepState {
                        rw_counter: op.rwc().into(),
                        is_write: op.rw().is_write(),
                        field_tag: match op.op().field {
                            StepStateField::CallID => StepStateFieldTag::CallID,
                            StepStateField::IsRoot => StepStateFieldTag::IsRoot,
                            StepStateField::IsCreate => StepStateFieldTag::IsCreate,
                            StepStateField::CodeHash => StepStateFieldTag::CodeHash,
                            StepStateField::ProgramCounter => StepStateFieldTag::ProgramCounter,
                            StepStateField::StackPointer => StepStateFieldTag::StackPointer,
                            StepStateField::GasLeft => StepStateFieldTag::GasLeft,
                            StepStateField::MemoryWordSize => StepStateFieldTag::MemoryWordSize,
                            StepStateField::ReversibleWriteCounter => {
                                StepStateFieldTag::ReversibleWriteCounter
                            }
                            StepStateField::LogID => StepStateFieldTag::LogID,
                        },
                        value: op.op().value,
                    })
                    .collect(),
            );
            Self(rws)
        }
    }
}

/// RwFingerprints
#[derive(Debug, Default, Clone)]
pub struct RwFingerprints<F> {
    /// acc_prev_fingerprints
    pub acc_prev_fingerprints: F,
    /// acc_next_fingerprints
    pub acc_next_fingerprints: F,
    /// row_pre_fingerprints
    pub row_pre_fingerprints: F,
    /// row_next_fingerprints
    pub row_next_fingerprints: F,
}

impl<F: Field> RwFingerprints<F> {
    /// new by value
    pub fn new(row_prev: F, row_next: F, acc_pref: F, acc_next: F) -> Self {
        Self {
            acc_prev_fingerprints: acc_pref,
            acc_next_fingerprints: acc_next,
            row_pre_fingerprints: row_prev,
            row_next_fingerprints: row_next,
        }
    }
}

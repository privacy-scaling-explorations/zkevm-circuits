//! This module contains the logic for parsing and interacting with EVM
//! execution traces.
use crate::operation::RwTableTag;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq)]
/// The target and index of an `Operation` in the context of an
/// `ExecutionTrace`.
pub struct OperationRef(pub RwTableTag, pub usize);

impl fmt::Debug for OperationRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "OperationRef{{ {}, {} }}",
            match self.0 {
                RwTableTag::Start => "Start",
                RwTableTag::Memory => "Memory",
                RwTableTag::Stack => "Stack",
                RwTableTag::AccountStorage => "Storage",
                RwTableTag::TxAccessListAccount => "TxAccessListAccount",
                RwTableTag::TxAccessListAccountStorage => "TxAccessListAccountStorage",
                RwTableTag::TxRefund => "TxRefund",
                RwTableTag::Account => "Account",
                RwTableTag::CallContext => "CallContext",
                RwTableTag::TxReceipt => "TxReceipt",
                RwTableTag::TxLog => "TxLog",
            },
            self.1
        ))
    }
}

impl From<(RwTableTag, usize)> for OperationRef {
    fn from(op_ref_data: (RwTableTag, usize)) -> Self {
        Self(op_ref_data.0, op_ref_data.1)
    }
}

impl OperationRef {
    /// Return the `OperationRef` as a `usize`.
    pub const fn as_usize(&self) -> usize {
        self.1
    }

    /// Return the [`RwTableTag`] op type of the `OperationRef`.
    pub const fn target(&self) -> RwTableTag {
        self.0
    }
}


use strum_macros::EnumIter;
use crate::circuit_tools::cell_manager::CustomTable;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter)]
pub enum Table {
    Fixed,
    Tx,
    Rw,
    Bytecode,
    Block,
    Copy,
    Keccak,
    Exp,
}

impl CustomTable for Table {
    fn matches_to(&self, other: &Self) -> bool {
        self == other
    }
}
use crate::{
    circuit_tools::{cached_region::ChallengeSet, cell_manager::EvmCellType, table::LookupTable},
    evm_circuit::table::Table,
    table::KeccakTable,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::Value,
    plonk::{Any, Column},
};

impl<F: Field> LookupTable<F> for KeccakTable {
    type TableCellType = EvmCellType;

    fn get_type(&self) -> EvmCellType {
        EvmCellType::Lookup(Table::Keccak)
    }

    fn phase(&self) -> u8 {
        0
    }

    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.is_enabled.into(),
            self.input_rlc.into(),
            self.input_len.into(),
            self.output_rlc.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("is_enabled"),
            String::from("input_rlc"),
            String::from("input_len"),
            String::from("output_rlc"),
        ]
    }
}

impl<F: Field> ChallengeSet<F> for crate::util::Challenges<Value<F>> {
    fn indexed(&self) -> Vec<&Value<F>> {
        vec![&self.evm_word, &self.keccak_input, &self.lookup_input]
    }
}

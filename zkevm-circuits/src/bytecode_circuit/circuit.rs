use std::cell::RefCell;

use chiquito::backend::halo2::{chiquito2Halo2, ChiquitoHalo2};

use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, Expression},
};

use crate::{
    bytecode_circuit::bytecode_chiquito::bytecode_circuit,
    table::{BytecodeTable, KeccakTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness,
};

use super::{
    bytecode_unroller::{unroll, UnrolledBytecode},
    push_data_chiquito::push_data_table_circuit,
    wit_gen::BytecodeWitnessGen,
};

/// WitnessInput
pub type WitnessInput<F> = (Vec<UnrolledBytecode<F>>, Challenges<Value<F>>, usize, usize);

/// BytecodeCircuitConfig
#[derive(Clone, Debug)]
pub struct BytecodeCircuitConfig<F: Field> {
    compiled: ChiquitoHalo2<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>>,
    push_data_table: ChiquitoHalo2<F, (), ()>,
    pub(crate) keccak_table: KeccakTable,

    minimum_rows: usize,
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
    fn new(meta: &mut ConstraintSystem<F>, config: Self::ConfigArgs) -> Self {
        let push_data_value = meta.fixed_column();
        let push_data_size = meta.fixed_column();

        let mut push_data_table =
            chiquito2Halo2(push_data_table_circuit(push_data_value, push_data_size));

        push_data_table.configure(meta);

        let mut circuit =
            chiquito2Halo2(bytecode_circuit(&config, push_data_value, push_data_size));

        circuit.configure(meta);

        Self {
            compiled: circuit,
            push_data_table,
            keccak_table: config.keccak_table,
            minimum_rows: meta.minimum_rows(),
        }
    }
}

#[derive(Default, Debug, Clone)]
/// BytecodeCircuit
pub struct BytecodeCircuit<F: Field> {
    /// Unrolled bytecodes
    pub bytecodes: Vec<UnrolledBytecode<F>>,
    /// Circuit size
    pub size: usize,
    /// Overwrite
    pub overwrite_len: usize,
}

impl<F: Field> BytecodeCircuit<F> {
    /// new BytecodeCircuitTester
    pub fn new(bytecodes: Vec<UnrolledBytecode<F>>, size: usize) -> Self {
        BytecodeCircuit {
            bytecodes,
            size,
            overwrite_len: 0,
        }
    }

    /// new BytecodeCircuitTester overwritting the length
    pub fn new_overwrite_len(
        bytecodes: Vec<UnrolledBytecode<F>>,
        size: usize,
        overwrite_len: usize,
    ) -> Self {
        BytecodeCircuit {
            bytecodes,
            size,
            overwrite_len,
        }
    }

    /// Creates bytecode circuit from block and bytecode_size.
    pub fn new_from_block_sized(block: &witness::Block<F>, bytecode_size: usize) -> Self {
        let bytecodes: Vec<UnrolledBytecode<F>> = block
            .bytecodes
            .iter()
            .map(|(_, b)| unroll(b.bytes.clone()))
            .collect();
        Self::new(bytecodes, bytecode_size)
    }
}

impl<F: Field> SubCircuit<F> for BytecodeCircuit<F> {
    type Config = BytecodeCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        // TODO: Find a nicer way to add the extra `128`.  Is this to account for
        // unusable rows? Then it could be calculated like this:
        // fn unusable_rows<F: Field, C: Circuit<F>>() -> usize {
        //     let mut cs = ConstraintSystem::default();
        //     C::configure(&mut cs);
        //     cs.blinding_factors()
        // }
        let bytecode_size = block.circuits_params.max_bytecode + 128;
        Self::new_from_block_sized(block, bytecode_size)
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.push_data_table.synthesize(layouter, ());
        config.compiled.synthesize(
            layouter,
            (
                self.bytecodes.clone(),
                *challenges,
                self.size - (config.minimum_rows + 1),
                self.overwrite_len,
            ),
        );

        Ok(())
    }

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
}

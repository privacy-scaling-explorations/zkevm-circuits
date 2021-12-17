use crate::{
    evm_circuit::{
        execution::{
            bus_mapping_tmp::{Block, Call, ExecStep, Transaction},
            ExecutionGadget,
        },
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition::Delta,
            },
            from_bytes, RandomLinearCombination,
        },
    },
    util::Expr,
};
use array_init::array_init;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct MsizeGadget<F> {
    same_context: SameContextGadget<F>,
    value: RandomLinearCombination<F, 8>,
}

impl<F: FieldExt> ExecutionGadget<F> for MsizeGadget<F> {
    const NAME: &'static str = "MSIZE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::MSIZE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // memory_size is limited to 64 bits so we only consider 8 bytes
        let bytes = array_init(|_| cb.query_cell());
        cb.require_equal(
            "Constrain memory_size equal to stack value",
            from_bytes::expr(&bytes),
            cb.curr.state.memory_size.expr(),
        );

        // Push the value on the stack
        let value = RandomLinearCombination::new(bytes, cb.randomness());
        cb.stack_push(value.expr());

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            ..Default::default()
        };
        let opcode = cb.query_cell();
        let same_context = SameContextGadget::construct(
            cb,
            opcode,
            step_state_transition,
            None,
        );

        Self {
            same_context,
            value,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        _: &Block<F>,
        _: &Transaction<F>,
        _: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        self.value.assign(
            region,
            offset,
            Some((step.memory_size).to_le_bytes()),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        execution::bus_mapping_tmp::{
            Block, Bytecode, Call, ExecStep, Rw, Transaction,
        },
        step::ExecutionState,
        test::run_test_circuit_incomplete_fixed_table,
        util::RandomLinearCombination,
    };
    use bus_mapping::{
        eth_types::{ToBigEndian, ToLittleEndian, Word},
        evm::OpcodeId,
    };
    use halo2::arithmetic::BaseExt;
    use pairing::bn256::Fr as Fp;

    #[test]
    fn test_ok() {
        let opcode = OpcodeId::MSIZE;
        let address = Word::from(0x12FFFF);
        let value = Word::from_big_endian(&(1..33).collect::<Vec<_>>());
        let memory_size = 38913;
        let gas_cost = 2;

        let randomness = Fp::rand();
        let bytecode = Bytecode::new(
            [
                vec![OpcodeId::PUSH32.as_u8()],
                value.to_be_bytes().to_vec(),
                vec![OpcodeId::PUSH32.as_u8()],
                address.to_be_bytes().to_vec(),
                vec![opcode.as_u8(), OpcodeId::STOP.as_u8()],
            ]
            .concat(),
        );
        let block = Block {
            randomness,
            txs: vec![Transaction {
                calls: vec![Call {
                    id: 1,
                    is_root: false,
                    is_create: false,
                    opcode_source:
                        RandomLinearCombination::random_linear_combine(
                            bytecode.hash.to_le_bytes(),
                            randomness,
                        ),
                }],
                steps: vec![
                    ExecStep {
                        rw_indices: vec![0],
                        execution_state: ExecutionState::MSIZE,
                        rw_counter: 1,
                        program_counter: 66,
                        stack_pointer: 1023,
                        gas_left: gas_cost,
                        gas_cost,
                        memory_size,
                        opcode: Some(opcode),
                        ..Default::default()
                    },
                    ExecStep {
                        execution_state: ExecutionState::STOP,
                        rw_counter: 2,
                        program_counter: 67,
                        stack_pointer: 1023 - 1,
                        gas_left: 0,
                        memory_size,
                        opcode: Some(OpcodeId::STOP),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            }],
            rws: vec![Rw::Stack {
                rw_counter: 1,
                is_write: true,
                call_id: 1,
                stack_pointer: 1023 - 1,
                value: Word::from(memory_size),
            }],
            bytecodes: vec![bytecode],
        };
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }
}

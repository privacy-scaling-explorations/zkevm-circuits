use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_U64},
        step::ExecutionState,
        table::BlockContextFieldTag,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            from_bytes, RandomLinearCombination, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use eth_types::ToLittleEndian;
use halo2_proofs::{circuit::Region, plonk::Error};
use std::convert::{TryFrom, TryInto};

#[derive(Clone, Debug)]
pub(crate) struct BlockCtxU64Gadget<F> {
    same_context: SameContextGadget<F>,
    value_u64: RandomLinearCombination<F, N_BYTES_U64>,
}

impl<F: Field> ExecutionGadget<F> for BlockCtxU64Gadget<F> {
    const NAME: &'static str = "BlockCTXU64";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BLOCKCTXU64;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let value_u64 = cb.query_rlc();

        // Push the u64 value to the stack
        cb.stack_push(value_u64.expr());

        // Get op's FieldTag
        let opcode = cb.query_cell();
        let blockctx_tag = BlockContextFieldTag::Coinbase.expr()
            + (opcode.expr() - OpcodeId::COINBASE.as_u64().expr());

        // Lookup block table with TIMESTAMP/NUMBER/GASLIMIT
        cb.block_lookup(blockctx_tag, None, from_bytes::expr(&value_u64.cells));

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::TIMESTAMP.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            value_u64,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let value = block.rws[step.rw_indices[0]].stack_value();

        self.value_u64.assign(
            region,
            offset,
            Some(u64::try_from(value).unwrap().to_le_bytes()),
        )?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BlockCtxU160Gadget<F> {
    same_context: SameContextGadget<F>,
    value_u160: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
}

impl<F: Field> ExecutionGadget<F> for BlockCtxU160Gadget<F> {
    const NAME: &'static str = "BlockCTXU160";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BLOCKCTXU160;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let value_u160 = cb.query_rlc();

        // Push the u64 value to the stack
        cb.stack_push(value_u160.expr());

        // Get op's FieldTag
        let opcode = cb.query_cell();
        let blockctx_tag = BlockContextFieldTag::Coinbase.expr()
            + (opcode.expr() - OpcodeId::COINBASE.as_u64().expr());

        // Lookup block table with COINBASE
        cb.block_lookup(blockctx_tag, None, from_bytes::expr(&value_u160.cells));

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::COINBASE.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            value_u160,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let value = block.rws[step.rw_indices[0]].stack_value();

        self.value_u160.assign(
            region,
            offset,
            Some(
                value.to_le_bytes()[..N_BYTES_ACCOUNT_ADDRESS]
                    .try_into()
                    .unwrap(),
            ),
        )?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BlockCtxU256Gadget<F> {
    same_context: SameContextGadget<F>,
    value_u256: Word<F>,
}

impl<F: Field> ExecutionGadget<F> for BlockCtxU256Gadget<F> {
    const NAME: &'static str = "BLOCKCTXU256";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BLOCKCTXU256;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let value_u256 = cb.query_rlc();

        // Push the u64 value to the stack
        cb.stack_push(value_u256.expr());

        // Get op's FieldTag
        let opcode = cb.query_cell();
        let blockctx_tag = BlockContextFieldTag::Coinbase.expr()
            + (opcode.expr() - OpcodeId::COINBASE.as_u64().expr());

        // Lookup block table with DIFFICULTY/BASEFEE RLC value
        cb.block_lookup(blockctx_tag, None, value_u256.expr());

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::TIMESTAMP.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            value_u256,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let value = block.rws[step.rw_indices[0]].stack_value();

        self.value_u256
            .assign(region, offset, Some(value.to_le_bytes()))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::bytecode;
    use mock::TestContext;

    fn test_ok(bytecode: bytecode::Bytecode) {
        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }

    #[test]
    fn blockcxt_u64_gadget_test() {
        let bytecode = bytecode! {
            TIMESTAMP
            STOP
            NUMBER
            STOP
            GASLIMIT
            STOP
        };
        test_ok(bytecode);
    }
    #[test]
    fn blockcxt_u160_gadget_test() {
        let bytecode = bytecode! {
            COINBASE
            STOP
        };
        test_ok(bytecode);
    }

    #[test]
    fn blockcxt_u256_gadget_test() {
        let bytecode = bytecode! {
            DIFFICULTY
            STOP
            BASEFEE
            STOP
        };
        test_ok(bytecode);
    }
}

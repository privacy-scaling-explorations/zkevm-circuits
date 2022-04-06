use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_WORD,
        step::ExecutionState,
        table::BlockContextFieldTag,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::{circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ChainIdGadget<F> {
    same_context: SameContextGadget<F>,
    chain_id: RandomLinearCombination<F, N_BYTES_WORD>,
}

impl<F: Field> ExecutionGadget<F> for ChainIdGadget<F> {
    const NAME: &'static str = "CHAINID";

    const EXECUTION_STATE: ExecutionState = ExecutionState::CHAINID;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let chain_id = cb.query_rlc();

        // Push the value to the stack
        cb.stack_push(chain_id.expr());

        // Lookup block table with chain_id
        cb.block_lookup(BlockContextFieldTag::ChainId.expr(), None, chain_id.expr());

        // State transition
        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::CHAINID.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            chain_id,
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
        let chain_id = block.rws[step.rw_indices[0]].stack_value();
        self.chain_id
            .assign(region, offset, Some(chain_id.to_le_bytes()))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::bytecode;
    use eth_types::evm_types::{GasCost, OpcodeId};
    use mock::test_ctx::{helpers::*, TestContext};

    #[test]
    fn chainid_gadget_test() {
        let bytecode = bytecode! {
            #[start]
            CHAINID
            STOP
        };
        let gas = GasCost::TX.as_u64() + OpcodeId::CHAINID.as_u64();
        let ctx = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(bytecode),
            |mut txs, accs| {
                txs[0]
                    .to(accs[0].address)
                    .from(accs[1].address)
                    .gas(gas.into());
            },
            |block, _tx| block,
        )
        .unwrap();

        assert_eq!(run_test_circuits(ctx, None), Ok(()));
    }
}

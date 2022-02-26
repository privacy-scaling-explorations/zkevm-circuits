use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_ACCOUNT_ADDRESS,
        step::ExecutionState,
        table::{AccountFieldTag, CallContextFieldTag},
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            from_bytes, Cell, RandomLinearCombination, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::{evm_types::GasCost, Field, ToAddress, ToLittleEndian, ToScalar, U256};
use halo2_proofs::{circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ExtcodehashGadget<F> {
    same_context: SameContextGadget<F>,
    external_address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
    tx_id: Cell<F>,
    previously_accessed: Cell<F>,
    external_code_hash: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for ExtcodehashGadget<F> {
    const NAME: &'static str = "EXTCODEHASH";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXTCODEHASH;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let external_address = cb.query_rlc();
        cb.stack_pop(external_address.expr());

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);

        let previously_accessed = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            from_bytes::expr(&external_address.cells),
            1.expr(),
            previously_accessed.expr(),
        );

        let external_code_hash = cb.query_cell();
        cb.account_read(
            from_bytes::expr(&external_address.cells),
            AccountFieldTag::CodeHash,
            external_code_hash.expr(),
        );

        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(5.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(0.expr()),
            ..Default::default()
        };
        let dynamic_gas_cost = (1.expr() - previously_accessed.expr())
            * (GasCost::COLD_ACCOUNT_ACCESS_COST.as_u64()
                - GasCost::WARM_STORAGE_READ_COST.as_u64())
            .expr();
        let same_context =
            SameContextGadget::construct(cb, opcode, step_state_transition, Some(dynamic_gas_cost));

        Self {
            same_context,
            external_address,
            tx_id,
            previously_accessed,
            external_code_hash,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let external_address = block.rws[step.rw_indices[0]].stack_value().to_address();
        let mut le_bytes = external_address.0;
        le_bytes.reverse();
        self.external_address
            .assign(region, offset, Some(le_bytes))?;

        self.tx_id
            .assign(region, offset, U256::from(tx.id).to_scalar())?;

        let previously_accessed = match GasCost::from(step.gas_cost) {
            GasCost::COLD_ACCOUNT_ACCESS_COST => 0,
            GasCost::WARM_STORAGE_READ_COST => 1,
            _ => unreachable!(),
        };
        self.previously_accessed
            .assign(region, offset, Some(F::from(previously_accessed)))?;

        let external_code_hash = block.rws[step.rw_indices[4]].stack_value();
        self.external_code_hash.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                external_code_hash.to_le_bytes(),
                block.randomness,
            )),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::{address, bytecode, ToWord, H160};

    fn test_ok(address: H160) {
        let code = bytecode! {
            PUSH20(address.to_word())
            #[start]
            EXTCODEHASH
            STOP
        };
        assert_eq!(run_test_circuits(code), Ok(()));
    }

    #[test]
    fn extcodehash_gadget_warm_account() {
        // The default address is already in the address access set because
        // `run_test_circuits` works by executing bytecode deployed at the
        // default address.
        test_ok(H160::default());
    }

    #[test]
    fn extcodehash_gadget_cold_account() {
        // This address isn't otherwise accessed, so calling EXTCODEHASH on it will
        // incur a higher gas cost.
        test_ok(address!("0xaabbccddee000000000000000000000000000011"));
    }
}

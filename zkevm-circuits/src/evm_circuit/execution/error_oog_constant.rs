use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_GAS, N_BYTES_MEMORY_WORD_SIZE},
        step::ExecutionState,
        util::{
            constraint_builder::ConstraintBuilder,
            math_gadget::{IsEqualGadget, IsZeroGadget, RangeCheckGadget},
            memory_gadget::{address_high, address_low, MemoryExpansionGadget},
            CachedRegion, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::{evm_types::OpcodeId, Field, ToLittleEndian};
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGConstantGadget<F> {
    opcode: Cell<F>,
    // constrain gas left is less than required
    gas_required: Cell<F>,
    insufficient_gas: RangeCheckGadget<F, N_BYTES_GAS>,
}

impl<F: Field> ExecutionGadget<F> for ErrorOOGConstantGadget<F> {
    const NAME: &'static str = "ErrorOutOfGasConstant";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorOutOfGasConstant;

    // Support other OOG due to pure memory including CREATE, RETURN and REVERT
    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let gas_required = cb.query_cell();

        // Check if the amount of gas available is less than the amount of gas
        // required
        let insufficient_gas =  RangeCheckGadget::construct(
                cb,
                gas_required.expr() - cb.curr.state.gas_left.expr(),
            );

        // TODO: Use ContextSwitchGadget to switch call context to caller's and
        // consume all gas_left.

        Self {
            opcode,
            gas_required,
            insufficient_gas,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        _call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();

        // Inputs/Outputs
        self.gas_required.assign(region, offset, Some(F::from(step.gas_cost)))?;
        // Gas insufficient check
        // Get `gas_available` variable here once it's available
        self.insufficient_gas
            .assign(region, offset, F::from(step.gas_cost - step.gas_left))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_bytes, test_util::run_test_circuits};
    use eth_types::bytecode;
    use eth_types::evm_types::OpcodeId;
    use mock::TestContext;

    fn test_ok(opcode: OpcodeId, bytes: &[u8]) {
        assert!(bytes.len() as u8 == opcode.as_u8() - OpcodeId::PUSH1.as_u8() + 1,);

        let mut bytecode = bytecode! {
            .write_op(opcode)
        };
        for b in bytes {
            bytecode.write(*b);
        }
        bytecode.write_op(OpcodeId::STOP);

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }

    #[test]
    fn push_gadget_simple() {
        test_ok(OpcodeId::PUSH1, &[1]);
        // test_ok(OpcodeId::PUSH2, &[1, 2]);
        // test_ok(
        //     OpcodeId::PUSH31,
        //     &[
        //         1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
        //         24, 25, 26, 27, 28, 29, 30, 31,
        //     ],
        // );
        // test_ok(
        //     OpcodeId::PUSH32,
        //     &[
        //         1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
        //         24, 25, 26, 27, 28, 29, 30, 31, 32,
        //     ],
        // );
    }

}

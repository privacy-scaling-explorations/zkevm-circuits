use crate::evm_circuit::{
    execution::ExecutionGadget,
    param::N_BYTES_GAS,
    step::ExecutionState,
    util::{
        constraint_builder::ConstraintBuilder, math_gadget::RangeCheckGadget, CachedRegion, Cell,
    },
    witness::{Block, Call, ExecStep, Transaction},
};
use crate::util::Expr;
use eth_types::Field;
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGConstantGadget<F> {
    opcode: Cell<F>,
    // constrain gas left is less than required
    gas_required: Cell<F>,
    insufficient_gas: RangeCheckGadget<F, N_BYTES_GAS>,
    // restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorOOGConstantGadget<F> {
    const NAME: &'static str = "ErrorOutOfGasConstant";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorOutOfGasConstant;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let gas_required = cb.query_cell();

        // Check if the amount of gas available is less than the amount of gas
        // required
        let insufficient_gas =
            RangeCheckGadget::construct(cb, gas_required.expr() - cb.curr.state.gas_left.expr());

        // TODO: Handle root & internal call constraints and use ContextSwitchGadget to
        // switch call context to caller's and consume all gas_left

        Self {
            opcode,
            gas_required,
            insufficient_gas,
            // restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        _block: &Block<F>,
        _tx: &Transaction,
        _call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let _opcode = step.opcode.unwrap();

        // Inputs/Outputs
        self.gas_required
            .assign(region, offset, Value::known(F::from(step.gas_cost)))?;
        // Gas insufficient check
        // Get `gas_available` variable here once it's available
        self.insufficient_gas
            .assign(region, offset, F::from(step.gas_cost - step.gas_left))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::run_test_circuit_geth_data_default;
    use bus_mapping::evm::OpcodeId;
    use eth_types::{self, bytecode, evm_types::GasCost, geth_types::GethData, Word};
    use halo2_proofs::halo2curves::bn256::Fr;
    use mock::{
        eth, gwei, test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS,
    };

    fn gas(call_data: &[u8]) -> Word {
        Word::from(
            GasCost::TX.as_u64()
                + 2 * OpcodeId::PUSH32.constant_gas_cost().as_u64()
                + call_data
                    .iter()
                    .map(|&x| if x == 0 { 4 } else { 16 })
                    .sum::<u64>(),
        )
    }

    fn test_oog_constant(tx: eth_types::Transaction, is_success: bool) {
        let code = if is_success {
            bytecode! {
                PUSH1(0)
                PUSH1(0)
                RETURN
            }
        } else {
            bytecode! {
                PUSH1(0)
                PUSH1(0)
            }
        };

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            |mut txs, _accs| {
                txs[0]
                    .to(tx.to.unwrap())
                    .from(tx.from)
                    .gas_price(tx.gas_price.unwrap())
                    .gas(tx.gas - 1)
                    .input(tx.input)
                    .value(tx.value);
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    fn mock_tx(value: Word, gas_price: Word, calldata: Vec<u8>) -> eth_types::Transaction {
        let from = MOCK_ACCOUNTS[1];
        let to = MOCK_ACCOUNTS[0];
        eth_types::Transaction {
            from,
            to: Some(to),
            value,
            gas: gas(&calldata),
            gas_price: Some(gas_price),
            input: calldata.into(),
            ..Default::default()
        }
    }

    #[test]
    fn oog_constant_gadget_simple() {
        // Transfer 1 ether, successfully
        // in root call
        test_oog_constant(mock_tx(eth(1), gwei(2), vec![]), false);
        // TODO: add internal call test
    }
}

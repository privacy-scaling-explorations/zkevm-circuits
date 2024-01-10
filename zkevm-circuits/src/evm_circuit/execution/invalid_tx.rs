use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_GAS,
        step::ExecutionState,
        util::{
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            math_gadget::{IsEqualGadget, LtGadget, LtWordGadget},
            tx::{BeginTxHelperGadget, EndTxHelperGadget, TxDataGadget},
            CachedRegion, Cell, StepRws, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::AccountFieldTag,
    util::word::{Word32Cell, WordExpr},
};
use eth_types::{Field, ToScalar};
use gadgets::util::{not, or, Expr, Scalar};
use halo2_proofs::{circuit::Value, plonk::Error};

/// Gadget for invalid Tx
#[derive(Clone, Debug)]
pub(crate) struct InvalidTxGadget<F> {
    begin_tx: BeginTxHelperGadget<F>,
    tx: TxDataGadget<F>,
    account_nonce: Cell<F>,
    is_nonce_match: IsEqualGadget<F>,
    insufficient_gas_limit: LtGadget<F, N_BYTES_GAS>,
    balance: Word32Cell<F>,
    insufficient_balance: LtWordGadget<F>,
    end_tx: EndTxHelperGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for InvalidTxGadget<F> {
    const NAME: &'static str = "ErrorInvalidTx";

    const EXECUTION_STATE: ExecutionState = ExecutionState::InvalidTx;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let begin_tx = BeginTxHelperGadget::configure(cb);
        let tx = TxDataGadget::configure(cb, begin_tx.tx_id.expr(), true);

        // Check if the nonce is invalid
        let account_nonce = cb.query_cell_phase2();
        cb.account_read(
            tx.caller_address.to_word(),
            AccountFieldTag::Nonce,
            Word::from_lo_unchecked(account_nonce.expr()),
        );
        let is_nonce_match = IsEqualGadget::construct(cb, account_nonce.expr(), tx.nonce.expr());

        // Check if the gas limit is larger or equal to the intrinsic gas cost
        let insufficient_gas_limit =
            LtGadget::<F, N_BYTES_GAS>::construct(cb, tx.gas.expr(), tx.intrinsic_gas());

        // Check if the balance is sufficient to pay for the total tx cost (intrinsic gas + value)
        let balance = cb.query_word32();
        cb.account_read(
            tx.caller_address.to_word(),
            AccountFieldTag::Balance,
            balance.to_word(),
        );
        let insufficient_balance =
            LtWordGadget::construct(cb, &balance.to_word(), &tx.total_cost().to_word());

        // At least one of the invalid conditions needs to be true
        let invalid_tx = or::expr([
            not::expr(is_nonce_match.expr()),
            insufficient_gas_limit.expr(),
            insufficient_balance.expr(),
        ]);
        cb.require_equal("Tx needs to be invalid", invalid_tx.expr(), 1.expr());

        let end_tx = EndTxHelperGadget::construct(
            cb,
            begin_tx.tx_id.expr(),
            false.expr(),
            0.expr(),
            8.expr(),
        );

        Self {
            begin_tx,
            tx,
            account_nonce,
            is_nonce_match,
            insufficient_gas_limit,
            balance,
            insufficient_balance,
            end_tx,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        _call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let mut rws = StepRws::new(block, step);
        rws.offset_add(1);

        let account_nonce = rws
            .next()
            .account_nonce_pair()
            .0
            .to_scalar()
            .expect("unexpected U256 -> Scalar conversion failure");
        let balance = rws.next().account_balance_pair().0;
        self.begin_tx.assign(region, offset, tx)?;
        self.tx.assign(region, offset, tx)?;
        self.account_nonce
            .assign(region, offset, Value::known(account_nonce))?;
        self.is_nonce_match
            .assign(region, offset, account_nonce, tx.nonce.as_u64().scalar())?;
        self.insufficient_gas_limit.assign(
            region,
            offset,
            tx.gas().scalar(),
            tx.intrinsic_gas_cost().scalar(),
        )?;
        self.balance.assign_u256(region, offset, balance)?;
        self.insufficient_balance.assign(
            region,
            offset,
            balance,
            tx.gas_price * tx.gas() + tx.value,
        )?;
        self.end_tx.assign(region, offset, block, tx)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{self, bytecode, Word};

    use mock::{eth, gwei, TestContext, MOCK_ACCOUNTS};

    #[test]
    fn invalid_tx_invalid_nonce() {
        // The nonce used in the tx is not correct.
        // Use a higher nonce and a lower nonce.
        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];
        let code = bytecode! {
            STOP
        };
        let ctx = TestContext::<2, 2>::new(
            None,
            |accs| {
                accs[0].address(to).balance(eth(1)).code(code.clone());
                accs[1].address(from).balance(eth(1)).nonce(1);
            },
            |mut txs, _| {
                txs[0].to(to).from(from).invalid().set_nonce(5);
                txs[1].to(to).from(from).invalid().set_nonce(0);
            },
            |block, _| block,
        )
        .unwrap();
        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn invalid_tx_insufficient_gas() {
        // Invalid if gas_limit < intrinsic gas
        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];
        let ctx = TestContext::<2, 2>::new(
            None,
            |accs| {
                accs[0].address(to).balance(eth(1));
                accs[1].address(from).balance(eth(1));
            },
            |mut txs, _| {
                txs[0]
                    .to(to)
                    .from(from)
                    .gas_price(gwei(1))
                    .gas(Word::from(100))
                    .invalid();
                txs[1]
                    .to(to)
                    .from(from)
                    .gas_price(gwei(1))
                    .gas(Word::from(300000));
            },
            |block, _| block,
        )
        .unwrap();
        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn invalid_tx_insufficient_balance() {
        // Invalid if the balance < intrinsic gas cost + value
        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];
        let ctx = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(to).balance(eth(1));
                accs[1].address(from).balance(gwei(50000)).nonce(1);
            },
            |mut txs, _| {
                txs[0]
                    .to(to)
                    .from(from)
                    .gas_price(gwei(1))
                    .gas(Word::from(30000))
                    .value(gwei(30000))
                    .invalid();
            },
            |block, _| block,
        )
        .unwrap();
        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn invalid_tx_state_transitions() {
        fn test_ok<const NTX: usize>(tx_states: [bool; NTX]) {
            let to = MOCK_ACCOUNTS[0];
            let from = MOCK_ACCOUNTS[1];
            let code = bytecode! {
                STOP
            };
            let ctx = TestContext::<2, NTX>::new(
                None,
                |accs| {
                    accs[0].address(to).balance(eth(1)).code(code.clone());
                    accs[1].address(from).balance(eth(1)).nonce(1);
                },
                |mut txs, _| {
                    for i in 0..NTX {
                        txs[i].to(to).from(from);
                        // For invalid txs, just set the nonce to a wrong value
                        if !tx_states[i] {
                            txs[i].invalid().set_nonce(99);
                        }
                    }
                },
                |block, _| block,
            )
            .unwrap();
            CircuitTestBuilder::new_from_test_ctx(ctx).run();
        }

        // Check different permutations to make sure all transitions work correctly
        test_ok([false]);
        test_ok([true]);
        test_ok([false, false]);
        test_ok([true, false]);
        test_ok([false, true]);
        test_ok([true, true]);
        test_ok([false, false, false]);
        test_ok([true, false, false]);
        test_ok([false, true, false]);
        test_ok([false, false, true]);
    }
}

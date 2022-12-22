use crate::evm_circuit::execution::ExecutionGadget;
use crate::evm_circuit::param::N_BYTES_ACCOUNT_ADDRESS;
use crate::evm_circuit::step::ExecutionState;
use crate::evm_circuit::util::common_gadget::SameContextGadget;
use crate::evm_circuit::util::constraint_builder::Transition::Delta;
use crate::evm_circuit::util::constraint_builder::{
    ConstraintBuilder, ReversionInfo, StepStateTransition,
};
use crate::evm_circuit::util::{from_bytes, select, CachedRegion, Cell, RandomLinearCombination};
use crate::evm_circuit::witness::{Block, Call, ExecStep, Rw, Transaction};
use crate::table::{AccountFieldTag, CallContextFieldTag};
use crate::util::Expr;
use eth_types::evm_types::GasCost;
use eth_types::{Field, ToAddress, ToLittleEndian};
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct ExtcodesizeGadget<F> {
    same_context: SameContextGadget<F>,
    address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
    reversion_info: ReversionInfo<F>,
    tx_id: Cell<F>,
    is_warm: Cell<F>,
    code_hash: Cell<F>,
    code_size: Cell<F>,
    exists: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for ExtcodesizeGadget<F> {
    const NAME: &'static str = "EXTCODESIZE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXTCODESIZE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let address = cb.query_rlc();
        cb.stack_pop(address.expr());

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);
        let is_warm = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            from_bytes::expr(&address.cells),
            1.expr(),
            is_warm.expr(),
            Some(&mut reversion_info),
        );

        let code_hash = cb.query_cell();
        let code_size = cb.query_cell();
        let exists = cb.query_bool();
        cb.condition(exists.expr(), |cb| {
            cb.account_read(
                from_bytes::expr(&address.cells),
                AccountFieldTag::CodeHash,
                code_hash.expr(),
            );
            let bytecode_length_lookup = cb.bytecode_length(code_hash.expr());
            cb.require_equal(
                "code_size == bytecode_length_lookup if account exists",
                code_size.expr(),
                bytecode_length_lookup.expr(),
            );
        });
        cb.condition(1.expr() - exists.expr(), |cb| {
            cb.account_read(
                from_bytes::expr(&address.cells),
                AccountFieldTag::NonExisting,
                0.expr(),
            );
            cb.require_zero(
                "code_size == 0 if account is non-existing",
                code_size.expr(),
            );
        });

        cb.stack_push(select::expr(exists.expr(), code_size.expr(), 0.expr()));

        let gas_cost = select::expr(
            is_warm.expr(),
            GasCost::WARM_ACCESS.expr(),
            GasCost::COLD_ACCOUNT_ACCESS.expr(),
        );

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(7.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(0.expr()),
            gas_left: Delta(-gas_cost),
            reversible_write_counter: Delta(1.expr()),
            ..Default::default()
        };

        let opcode = cb.query_cell();
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            address,
            tx_id,
            reversion_info,
            is_warm,
            code_hash,
            code_size,
            exists,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let address = block.rws[step.rw_indices[0]].stack_value().to_address();
        let mut address_bytes = address.0;
        address_bytes.reverse();
        self.address.assign(region, offset, Some(address_bytes))?;

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id as u64)))?;

        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        let (_, is_warm) = block.rws[step.rw_indices[4]].tx_access_list_value_pair();
        self.is_warm
            .assign(region, offset, Value::known(F::from(is_warm)))?;

        let (code_hash, exists) = match block.rws[step.rw_indices[5]] {
            Rw::Account {
                field_tag: AccountFieldTag::CodeHash,
                value,
                ..
            } => (
                RandomLinearCombination::random_linear_combine(
                    value.to_le_bytes(),
                    block.randomness,
                ),
                true,
            ),
            Rw::Account {
                field_tag: AccountFieldTag::NonExisting,
                ..
            } => (F::zero(), false),
            _ => unreachable!(),
        };

        let code_size = block.rws[step.rw_indices[6]].stack_value().as_u64();

        self.code_hash
            .assign(region, offset, Value::known(code_hash))?;
        self.code_size
            .assign(region, offset, Value::known(F::from(code_size)))?;
        self.exists
            .assign(region, offset, Value::known(F::from(exists)))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::rand_bytes;
    use crate::test_util::run_test_circuits;
    use eth_types::geth_types::Account;
    use eth_types::{address, bytecode, Address, Bytecode, ToWord, Word, U256};
    use lazy_static::lazy_static;
    use mock::TestContext;

    lazy_static! {
        static ref TEST_ADDRESS: Address = address!("0xaabbccddee000000000000000000000000000000");
    }

    // TODO:
    fn test_ok(external_account: Option<Account>, is_warm: bool) {
        let external_address = external_account
            .as_ref()
            .map(|a| a.address)
            .unwrap_or(*EXTERNAL_ADDRESS);

        // Make the external account warm, if needed, by first getting its external code
        // hash.
        let mut code = Bytecode::default();
        if is_warm {
            code.append(&bytecode! {
                PUSH20(external_address.to_word())
                EXTCODEHASH // TODO: Change this to BALANCE once is implemented
                POP
            });
        }
        code.append(&bytecode! {
            PUSH20(external_address.to_word())
            #[start]
            EXTCODEHASH
            STOP
        });

        // Execute the bytecode and get trace
        let block: GethData = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(Word::from(1u64 << 20))
                    .code(code);

                accs[1].address(external_address);
                if let Some(external_account) = external_account {
                    accs[1]
                        .balance(external_account.balance)
                        .nonce(external_account.nonce)
                        .code(external_account.code);
                }
                accs[2]
                    .address(address!("0x0000000000000000000000000000000000000010"))
                    .balance(Word::from(1u64 << 20));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[2].address);
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        test_circuits_block_geth_data_default(block).unwrap();
    }

    #[test]
    fn extcodehash_warm_empty_account() {
        test_ok(None, true);
    }

    #[test]
    fn extcodehash_cold_empty_account() {
        test_ok(None, false);
    }

    #[test]
    fn extcodehash_warm_existing_account() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                nonce: U256::from(259),
                code: Bytes::from([3]),
                ..Default::default()
            }),
            true,
        );
    }

    #[test]
    fn extcodehash_cold_existing_account() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                balance: U256::from(900),
                code: Bytes::from([32, 59]),
                ..Default::default()
            }),
            false,
        );
    }

    #[test]
    fn extcodehash_nonempty_account_edge_cases() {
        // EIP-158 defines empty accounts to be those with balance = 0, nonce = 0, and
        // code = [].
        let nonce_only_account = Account {
            address: *EXTERNAL_ADDRESS,
            nonce: U256::from(200),
            ..Default::default()
        };
        // This account state is possible if another account sends ETH to a previously
        // empty account.
        let balance_only_account = Account {
            address: *EXTERNAL_ADDRESS,
            balance: U256::from(200),
            ..Default::default()
        };
        // This account state should no longer be possible because contract nonces start
        // at 1, per EIP-161. However, the requirement that the code be emtpy is still
        // in the yellow paper and our constraints, so we test this case
        // anyways.
        let contract_only_account = Account {
            address: *EXTERNAL_ADDRESS,
            code: Bytes::from([32, 59]),
            ..Default::default()
        };

        for account in [
            nonce_only_account,
            balance_only_account,
            contract_only_account,
        ] {
            test_ok(Some(account), false);
        }
    }
}

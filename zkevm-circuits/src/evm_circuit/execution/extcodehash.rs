use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_ACCOUNT_ADDRESS,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                EVMConstraintBuilder, ReversionInfo, StepStateTransition, Transition::Delta,
            },
            select, AccountAddress, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::{
        word::{Word32Cell, WordCell, WordExpr},
        Expr,
    },
};
use eth_types::{evm_types::GasCost, Field};
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ExtcodehashGadget<F> {
    same_context: SameContextGadget<F>,
    address_word: Word32Cell<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    is_warm: Cell<F>,
    code_hash: WordCell<F>,
}

impl<F: Field> ExecutionGadget<F> for ExtcodehashGadget<F> {
    const NAME: &'static str = "EXTCODEHASH";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXTCODEHASH;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let address_word = cb.query_word32();
        // let address = cb.query_account_address();
        let address = AccountAddress::new(
            address_word.limbs[..N_BYTES_ACCOUNT_ADDRESS]
                .to_vec()
                .try_into()
                .unwrap(),
            256.expr(),
        );

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);

        let is_warm = cb.query_bool();
        cb.account_access_list_write_unchecked(
            tx_id.expr(),
            address.to_word(),
            1.expr(),
            is_warm.expr(),
            Some(&mut reversion_info),
        );

        // range check will be cover by account code_hash lookup
        let code_hash = cb.query_word_unchecked();
        // For non-existing accounts the code_hash must be 0 in the rw_table.
        cb.account_read_word(
            address.to_word(),
            AccountFieldTag::CodeHash,
            code_hash.to_word(),
        );
        cb.stack_push_word(code_hash.to_word());

        let gas_cost = select::expr(
            is_warm.expr(),
            GasCost::WARM_ACCESS.expr(),
            GasCost::COLD_ACCOUNT_ACCESS.expr(),
        );
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(cb.rw_counter_offset()),
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
            address_word,
            tx_id,
            reversion_info,
            is_warm,
            code_hash,
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

        let address = block.get_rws(step, 0).stack_value();
        self.address_word.assign_u256(region, offset, address)?;

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id as u64)))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        let (_, is_warm) = block.get_rws(step, 4).tx_access_list_value_pair();
        self.is_warm
            .assign(region, offset, Value::known(F::from(is_warm as u64)))?;

        let code_hash = block.get_rws(step, 5).account_value_pair().0;
        self.code_hash.assign_u256(region, offset, code_hash)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{
        address, bytecode, geth_types::Account, Address, Bytecode, Bytes, ToWord, Word, U256, U64,
    };
    use lazy_static::lazy_static;
    use mock::TestContext;

    lazy_static! {
        static ref EXTERNAL_ADDRESS: Address =
            address!("0xaabbccddee000000000000000000000000000000");
    }

    fn test_ok(external_account: Option<Account>, is_warm: bool) {
        let external_address = external_account
            .clone()
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
        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(Word::from(1u64 << 20))
                    .code(code);

                accs[1].address(external_address);
                if let Some(external_account) = external_account {
                    accs[1].account(&external_account);
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
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
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
                nonce: U64::from(259),
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
            nonce: U64::from(200),
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
        // at 1, per EIP-161. However, the requirement that the code be empty is still
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

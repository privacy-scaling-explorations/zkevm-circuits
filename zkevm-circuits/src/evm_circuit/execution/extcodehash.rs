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
use eth_types::ToLittleEndian;
use eth_types::{evm_types::GasCost, Field, ToAddress, ToScalar, H256, U256};
use ethers_core::utils::keccak256;
use halo2_proofs::{circuit::Region, plonk::Error};
use lazy_static::lazy_static;

lazy_static! {
    static ref EMPTY_CODE_HASH_LE_BYTES: [u8; 32] = U256::from(keccak256(&[])).to_le_bytes();
}

#[derive(Clone, Debug)]
pub(crate) struct ExtcodehashGadget<F> {
    same_context: SameContextGadget<F>,
    external_address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
    tx_id: Cell<F>,
    is_warm: Cell<F>,
    nonce: Cell<F>,
    balance: Cell<F>,
    code_hash: Cell<F>,
    is_empty: Cell<F>, // I think this can be combined with nonzero_witness?
    nonzero_witness: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for ExtcodehashGadget<F> {
    const NAME: &'static str = "EXTCODEHASH";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXTCODEHASH;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let external_address = cb.query_rlc();
        cb.stack_pop(external_address.expr());

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);

        let is_warm = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            from_bytes::expr(&external_address.cells),
            1.expr(),
            is_warm.expr(),
        );

        let nonce = cb.query_cell();
        cb.account_read(
            from_bytes::expr(&external_address.cells),
            AccountFieldTag::Nonce,
            nonce.expr(),
        );
        let balance = cb.query_cell();
        cb.account_read(
            from_bytes::expr(&external_address.cells),
            AccountFieldTag::Balance,
            balance.expr(),
        );
        let code_hash = cb.query_cell();
        cb.account_read(
            from_bytes::expr(&external_address.cells),
            AccountFieldTag::CodeHash,
            code_hash.expr(),
        );

        let is_empty = cb.query_bool();
        cb.require_zero(
            "is_empty is 0 when nonce is non-zero",
            is_empty.expr() * nonce.expr(),
        );
        // Note that balance is RLC encoded, but RLC(x) = 0 iff x = 0, so we don't need
        // go to the work of writing out the RLC expression
        cb.require_zero(
            "is_empty is 0 when balance is non-zero",
            is_empty.expr() * balance.expr(),
        );
        let empty_code_hash_rlc = Word::random_linear_combine_expr(
            EMPTY_CODE_HASH_LE_BYTES.map(|x| x.expr()),
            cb.power_of_randomness(),
        );
        cb.require_zero(
            "is_empty is 0 when code_hash is non-zero",
            is_empty.expr() * (code_hash.expr() - empty_code_hash_rlc.clone()),
        );

        let nonzero_witness = cb.query_cell();
        cb.require_zero(
            "is_empty is 1 when none of nonce, balance, or (code_hash - empty_code_hash_rlc) are invertible",
            (1.expr() - is_empty.expr()) *
            (1.expr() - nonce.expr() * nonzero_witness.expr()) *
            (1.expr() - balance.expr() * nonzero_witness.expr()) *
            (1.expr() - (code_hash.expr() - empty_code_hash_rlc) * nonzero_witness.expr()),
        );

        cb.stack_push((1.expr() - is_empty.expr()) * code_hash.expr());

        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(7.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(0.expr()),
            ..Default::default()
        };
        let dynamic_gas_cost = (1.expr() - is_warm.expr())
            * (GasCost::COLD_ACCOUNT_ACCESS_COST.expr() - GasCost::WARM_STORAGE_READ_COST.expr());
        let same_context =
            SameContextGadget::construct(cb, opcode, step_state_transition, Some(dynamic_gas_cost));

        Self {
            same_context,
            external_address,
            tx_id,
            is_warm,
            nonce,
            balance,
            code_hash,
            is_empty,
            nonzero_witness,
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

        let is_warm = match GasCost::from(step.gas_cost) {
            GasCost::COLD_ACCOUNT_ACCESS_COST => 0,
            GasCost::WARM_STORAGE_READ_COST => 1,
            _ => unreachable!(),
        };
        self.is_warm
            .assign(region, offset, Some(F::from(is_warm)))?;

        let [nonce, balance, code_hash, external_code_hash] = [3, 4, 5, 6].map(|i| {
            block.rws[step.rw_indices[i]]
                .table_assignment(block.randomness)
                .value
        });
        self.nonce.assign(region, offset, Some(nonce))?;
        self.balance.assign(region, offset, Some(balance))?;
        self.code_hash.assign(region, offset, Some(code_hash))?;

        dbg!(code_hash);
        dbg!(external_code_hash);

        let empty_code_hash_rlc =
            Word::random_linear_combine(*EMPTY_CODE_HASH_LE_BYTES, block.randomness);

        dbg!(empty_code_hash_rlc);

        if let Some(inverse) = nonce.invert().into() {
            self.nonzero_witness.assign(region, offset, Some(inverse))?;
        } else if let Some(inverse) = balance.invert().into() {
            self.nonzero_witness.assign(region, offset, Some(inverse))?;
        } else if let Some(inverse) = (code_hash - empty_code_hash_rlc).invert().into() {
            self.nonzero_witness.assign(region, offset, Some(inverse))?;
        } else {
            self.is_empty.assign(region, offset, Some(F::one()))?;
        }
        // dbg!(is_empty);

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

use crate::{
    evm_circuit::{
        param::N_BYTES_U64,
        step::ExecutionState,
        util::{
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, StepStateTransition, Transition::*,
            },
            math_gadget::{
                AddWordsGadget, ConstantDivisionGadget, IsEqualGadget, MulWordByU64Gadget,
            },
            CachedRegion, Cell, Word,
        },
        witness::{Block, Transaction},
    },
    table::{CallContextFieldTag, TxContextFieldTag, TxReceiptFieldTag},
    util::word::{Word32Cell, WordCell},
};
use bus_mapping::operation::Target;
use eth_types::{evm_types::GasCost, Field};
use gadgets::util::{select, Expr, Scalar};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};
use strum::EnumCount;

/// Gadget for beginning a tx
#[derive(Clone, Debug)]
pub(crate) struct BeginTxHelperGadget<F> {
    // tx_id is query in current scope. The range should be determined here
    pub(crate) tx_id: Cell<F>,
}

impl<F: Field> BeginTxHelperGadget<F> {
    pub(crate) fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        // Use rw_counter of the step which triggers next call as its call_id.
        let call_id: Cell<F> = cb.curr.state.rw_counter.clone();

        let tx_id = cb.query_cell(); // already constrain `if step_first && tx_id = 1` and `tx_id += 1` at EndTx
        cb.debug_expression("tx_id", tx_id.expr());
        cb.call_context_lookup_write(
            Some(call_id.expr()),
            CallContextFieldTag::TxId,
            Word::from_lo_unchecked(tx_id.expr()),
        ); // rwc_delta += 1

        // Add first BeginTx step constraint to have id == 1
        cb.step_first(|cb| {
            cb.require_equal("tx_id is initialized to be 1", tx_id.expr(), 1.expr());
        });

        Self { tx_id }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        tx: &Transaction,
    ) -> Result<(), Error> {
        self.tx_id
            .assign(region, offset, Value::known(tx.id.scalar()))?;

        Ok(())
    }
}

/// Gadget for ending a tx
#[derive(Clone, Debug)]
pub(crate) struct EndTxHelperGadget<F> {
    current_cumulative_gas_used: Cell<F>,
    is_first_tx: IsEqualGadget<F>,
}

impl<F: Field> EndTxHelperGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        tx_id: Expression<F>,
        is_persistent: Expression<F>,
        gas_used: Expression<F>,
        num_rw: Expression<F>,
    ) -> Self {
        let is_first_tx = IsEqualGadget::construct(cb, tx_id.expr(), 1.expr());

        // Constrain tx receipt fields
        cb.tx_receipt_lookup(
            1.expr(),
            tx_id.expr(),
            TxReceiptFieldTag::PostStateOrStatus,
            is_persistent.expr(),
        );
        cb.tx_receipt_lookup(
            1.expr(),
            tx_id.expr(),
            TxReceiptFieldTag::LogLength,
            cb.curr.state.log_id.expr(),
        );
        let current_cumulative_gas_used = cb.query_cell();
        cb.condition(is_first_tx.expr(), |cb| {
            cb.require_zero(
                "current_cumulative_gas_used is zero when tx is first tx",
                current_cumulative_gas_used.expr(),
            );
        });
        cb.condition(1.expr() - is_first_tx.expr(), |cb| {
            cb.tx_receipt_lookup(
                0.expr(),
                tx_id.expr() - 1.expr(),
                TxReceiptFieldTag::CumulativeGasUsed,
                current_cumulative_gas_used.expr(),
            );
        });
        cb.tx_receipt_lookup(
            1.expr(),
            tx_id.expr(),
            TxReceiptFieldTag::CumulativeGasUsed,
            gas_used + current_cumulative_gas_used.expr(),
        );

        // Transition
        let rw_counter = num_rw.expr() - is_first_tx.expr();
        cb.condition(
            cb.next
                .execution_state_selector([ExecutionState::BeginTx, ExecutionState::InvalidTx]),
            |cb| {
                cb.call_context_lookup_write(
                    Some(cb.next.state.rw_counter.expr()),
                    CallContextFieldTag::TxId,
                    Word::from_lo_unchecked(tx_id.expr() + 1.expr()),
                );
                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(rw_counter.clone()),
                    ..StepStateTransition::any()
                });
            },
        );
        cb.condition(
            cb.next.execution_state_selector([ExecutionState::EndBlock]),
            |cb| {
                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(rw_counter.expr() - 1.expr()),
                    // We propagate call_id so that EndBlock can get the last tx_id
                    // in order to count processed txs.
                    call_id: Same,
                    ..StepStateTransition::any()
                });
            },
        );

        Self {
            is_first_tx,
            current_cumulative_gas_used,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
    ) -> Result<(), Error> {
        self.is_first_tx
            .assign(region, offset, F::from(tx.id), F::ONE)?;

        let current_cumulative_gas_used: u64 = if tx.id == 1 {
            0
        } else {
            // first transaction needs TxReceiptFieldTag::COUNT(3) lookups to tx receipt,
            // while later transactions need 4 (with one extra cumulative gas read) lookups
            let rw = &block.rws[(
                Target::TxReceipt,
                (tx.id as usize - 2) * (TxReceiptFieldTag::COUNT + 1) + 2,
            )];
            rw.receipt_value()
        };
        self.current_cumulative_gas_used.assign(
            region,
            offset,
            Value::known(F::from(current_cumulative_gas_used)),
        )?;

        Ok(())
    }
}

/// Gadget for reading the tx data
#[derive(Clone, Debug)]
pub(crate) struct TxDataGadget<F> {
    pub(crate) nonce: Cell<F>,
    pub(crate) caller_address: WordCell<F>,
    pub(crate) callee_address: WordCell<F>,
    pub(crate) is_create: Cell<F>,
    pub(crate) gas: Cell<F>,
    pub(crate) call_data_length: Cell<F>,
    pub(crate) call_data_gas_cost: Cell<F>,
    pub(crate) gas_price: Word32Cell<F>,
    pub(crate) value: Word32Cell<F>,

    pub(crate) mul_gas_fee_by_gas: MulWordByU64Gadget<F>,
    pub(crate) call_data_word_length: ConstantDivisionGadget<F, N_BYTES_U64>,

    pub(crate) gas_mul_gas_price_plus_value: Option<AddWordsGadget<F, 2, false>>,
    pub(crate) cost_sum: Option<Word32Cell<F>>,
}

impl<F: Field> TxDataGadget<F> {
    pub(crate) fn configure(
        cb: &mut EVMConstraintBuilder<F>,
        tx_id: Expression<F>,
        calculate_total_cost: bool,
    ) -> Self {
        let [nonce, gas, is_create, call_data_length, call_data_gas_cost] = [
            TxContextFieldTag::Nonce,
            TxContextFieldTag::Gas,
            TxContextFieldTag::IsCreate,
            TxContextFieldTag::CallDataLength,
            TxContextFieldTag::CallDataGasCost,
        ]
        .map(|field_tag| cb.tx_context(tx_id.expr(), field_tag, None));
        let [gas_price, value] = [TxContextFieldTag::GasPrice, TxContextFieldTag::Value]
            .map(|field_tag| cb.tx_context_as_word32(tx_id.expr(), field_tag, None));

        let [caller_address, callee_address] = [
            TxContextFieldTag::CallerAddress,
            TxContextFieldTag::CalleeAddress,
        ]
        .map(|field_tag| cb.tx_context_as_word(tx_id.expr(), field_tag, None));

        // TODO: Implement EIP 1559 (currently it only supports legacy
        // transaction format)
        // Calculate transaction gas fee
        let mul_gas_fee_by_gas = MulWordByU64Gadget::construct(cb, gas_price.clone(), gas.expr());

        let call_data_word_length =
            ConstantDivisionGadget::construct(cb, call_data_length.expr() + 31.expr(), 32);

        let (cost_sum, gas_mul_gas_price_plus_value) = if calculate_total_cost {
            let cost_sum = cb.query_word32();
            let gas_mul_gas_price_plus_value = AddWordsGadget::construct(
                cb,
                [mul_gas_fee_by_gas.product().clone(), value.clone()],
                cost_sum.clone(),
            );
            (Some(cost_sum), Some(gas_mul_gas_price_plus_value))
        } else {
            (None, None)
        };

        Self {
            nonce,
            is_create,
            gas,
            call_data_length,
            call_data_gas_cost,
            gas_price,
            value,
            mul_gas_fee_by_gas,
            call_data_word_length,
            caller_address,
            callee_address,
            gas_mul_gas_price_plus_value,
            cost_sum,
        }
    }

    pub(crate) fn intrinsic_gas(&self) -> Expression<F> {
        // Calculate gas cost of init code for EIP-3860.
        let init_code_gas_cost = select::expr(
            self.is_create.expr(),
            self.call_data_word_length.quotient().expr()
                * eth_types::evm_types::INIT_CODE_WORD_GAS.expr(),
            0.expr(),
        );

        select::expr(
            self.is_create.expr(),
            GasCost::CREATION_TX.expr(),
            GasCost::TX.expr(),
        ) + self.call_data_gas_cost.expr()
            + init_code_gas_cost.expr()
    }

    pub(crate) fn total_cost(&self) -> Word32Cell<F> {
        self.gas_mul_gas_price_plus_value
            .clone()
            .unwrap()
            .sum()
            .clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        tx: &Transaction,
    ) -> Result<(), Error> {
        let gas_fee = tx.gas_price * tx.gas();

        self.nonce
            .assign(region, offset, Value::known(tx.nonce.as_u64().scalar()))?;
        self.is_create
            .assign(region, offset, Value::known(tx.is_create().scalar()))?;
        self.gas
            .assign(region, offset, Value::known(tx.gas().scalar()))?;
        self.call_data_length.assign(
            region,
            offset,
            Value::known(F::from(tx.call_data.len() as u64)),
        )?;
        self.call_data_gas_cost.assign(
            region,
            offset,
            Value::known(tx.call_data_gas_cost().scalar()),
        )?;
        self.call_data_word_length
            .assign(region, offset, tx.call_data.len() as u128 + 31)?;
        self.gas_price.assign_u256(region, offset, tx.gas_price)?;
        self.value.assign_u256(region, offset, tx.value)?;
        self.callee_address
            .assign_h160(region, offset, tx.to_or_contract_addr())?;
        self.caller_address.assign_h160(region, offset, tx.from)?;
        self.mul_gas_fee_by_gas
            .assign(region, offset, tx.gas_price, tx.gas(), gas_fee)?;
        let sum = gas_fee + tx.value;

        if self.cost_sum.is_some() && self.gas_mul_gas_price_plus_value.is_some() {
            self.cost_sum
                .as_ref()
                .unwrap()
                .assign_u256(region, offset, sum)?;
            self.gas_mul_gas_price_plus_value.as_ref().unwrap().assign(
                region,
                offset,
                [gas_fee, tx.value],
                sum,
            )?;
        }

        Ok(())
    }
}

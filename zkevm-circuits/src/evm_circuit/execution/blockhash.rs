use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_U64, N_BYTES_WORD},
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            from_bytes,
            math_gadget::{IsEqualGadget, LtGadget},
            CachedRegion, Cell, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::BlockContextFieldTag,
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian, ToScalar};
use gadgets::util::not;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct BlockHashGadget<F> {
    same_context: SameContextGadget<F>,
    block_number: RandomLinearCombination<F, N_BYTES_U64>,
    current_block_number: Cell<F>,
    block_hash: RandomLinearCombination<F, N_BYTES_WORD>,
    block_lt: LtGadget<F, N_BYTES_U64>,
    diff_lt: LtGadget<F, 2>,
    is_valid: IsEqualGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for BlockHashGadget<F> {
    const NAME: &'static str = "BLOCKHASH";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BLOCKHASH;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let block_number = cb.query_rlc();
        cb.stack_pop(block_number.expr());

        let current_block_number = cb.query_cell();
        cb.block_lookup(
            BlockContextFieldTag::Number.expr(),
            None,
            current_block_number.expr(),
        );

        let block_lt = LtGadget::construct(
            cb,
            from_bytes::expr(&block_number.cells),
            current_block_number.expr(),
        );

        let diff_lt = LtGadget::construct(
            cb,
            current_block_number.expr(),
            256.expr() + from_bytes::expr(&block_number.cells),
        );

        let is_valid = IsEqualGadget::construct(cb, 1.expr(), block_lt.expr() * diff_lt.expr());

        let block_hash = cb.query_rlc();
        cb.condition(is_valid.expr(), |cb| {
            cb.block_lookup(
                BlockContextFieldTag::BlockHash.expr(),
                Some(from_bytes::expr(&block_number.cells)),
                block_hash.expr(),
            );
        });
        cb.condition(not::expr(is_valid.expr()), |cb| {
            cb.require_zero("invalid range", block_hash.expr());
        });

        cb.stack_push(block_hash.expr());

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(2.expr()),
            program_counter: Delta(1.expr()),
            gas_left: Delta(-OpcodeId::BLOCKHASH.constant_gas_cost().expr()),
            ..Default::default()
        };

        let opcode = cb.query_cell();
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);
        Self {
            same_context,
            block_number,
            current_block_number,
            block_hash,
            block_lt,
            diff_lt,
            is_valid,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let block_number = block.rws[step.rw_indices[0]].stack_value();
        self.block_number.assign(
            region,
            offset,
            Some(
                block_number.to_le_bytes()[..N_BYTES_U64].try_into().unwrap()
            ),
        )?;
        let block_number: F = block_number.to_scalar().unwrap();

        let current_block_number = block.context.number;
        self.current_block_number
            .assign(region, offset, current_block_number.to_scalar())?;

        self.block_hash.assign(
            region,
            offset,
            Some(block.rws[step.rw_indices[1]].stack_value().to_le_bytes()),
        )?;

        let (block_lt, _) = self.block_lt.assign(
            region,
            offset,
            block_number,
            current_block_number.to_scalar().unwrap(),
        )?;

        let (diff_lt, _) = self.diff_lt.assign(
            region,
            offset,
            current_block_number.to_scalar().unwrap(),
            block_number + F::from(256),
        )?;

        self.is_valid
            .assign(region, offset, F::one(), block_lt * diff_lt)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        evm_circuit::witness::block_convert,
        test_util::{test_circuits_using_witness_block, BytecodeTestConfig},
    };
    use bus_mapping::mock::BlockData;
    use eth_types::{bytecode, geth_types::GethData, Bytecode, U256};
    use mock::test_ctx::{helpers::*, TestContext};

    fn test_ok(block_number: u64, current_block_number: u64) {
        let mut code = Bytecode::default();

        code.append(&bytecode! {
            PUSH8(block_number)
            BLOCKHASH
            STOP
        });
        let mut history_hashes = Vec::new();
        if current_block_number < 256 {
            for number in 0..current_block_number {
                history_hashes.push(U256::from(number));
            }
        } else {
            for number in (current_block_number - 256)..current_block_number {
                history_hashes.push(U256::from(number));
            }
        }
        let block: GethData = TestContext::<2, 1>::new(
            Some(history_hashes),
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |block, _tx| block.number(current_block_number),
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .expect("could not handle block tx");

        test_circuits_using_witness_block(
            block_convert(&builder.block, &builder.code_db),
            BytecodeTestConfig::default(),
        )
        .unwrap();
    }
    #[test]
    fn blockhash_gadget_test() {
        test_ok(2, 5);
    }
}

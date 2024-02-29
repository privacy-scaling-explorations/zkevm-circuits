use std::marker::PhantomData;

use crate::{
    evm_circuit::{
        step::ExecutionState,
        util::{
            common_gadget::RwTablePaddingGadget,
            constraint_builder::{EVMConstraintBuilder, StepStateTransition},
            CachedRegion,
        },
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::{exec_trace::OperationRef, operation::Target};
use eth_types::Field;
use halo2_proofs::plonk::Error;

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct EndChunkGadget<F> {
    _marker: PhantomData<F>,
    rw_table_padding_gadget: RwTablePaddingGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for EndChunkGadget<F> {
    const NAME: &'static str = "EndChunk";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndChunk;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        // State transition on non-last evm step
        // TODO/FIXME make EndChunk must be in last evm step and remove below constraint
        cb.not_step_last(|cb| {
            // Propagate all the way down.
            cb.require_step_state_transition(StepStateTransition::same());
        });

        // step state write to rw_table
        cb.step_state_lookup(1.expr());

        let rw_table_padding_gadget = RwTablePaddingGadget::construct(
            cb,
            cb.curr.state.inner_rw_counter.clone().expr() - 1.expr() + cb.rw_counter_offset(), /* start from 1 */
        );

        Self {
            rw_table_padding_gadget,
            _marker: PhantomData {},
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        chunk: &Chunk<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let rwc_before_padding = step
            .bus_mapping_instance
            .iter()
            .filter(|x| {
                let OperationRef(c, _) = x;
                *c != Target::Start && *c != Target::Padding
            })
            .count();
        self.rw_table_padding_gadget.assign_exec_step(
            region,
            offset,
            block,
            chunk,
            (step.rwc_inner_chunk.0 - 1 + rwc_before_padding) as u64,
            step,
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        test_util::CircuitTestBuilder,
        witness::{block_convert, chunk_convert},
    };
    use bus_mapping::{circuit_input_builder::FixedCParams, mock::BlockData};
    use eth_types::{address, bytecode, geth_types::GethData, Word};
    use halo2_proofs::halo2curves::bn256::Fr;
    use mock::TestContext;

    macro_rules! test_2_txs_with_various_chunk_size {
        ($($name:ident: $value:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let (total_chunks, total_rws) = $value;
                test_2_txs_with_chunk_size(total_chunks, total_rws);
            }
        )*
        }
    }
    #[test]
    fn test_chunking_rwmap_logic() {
        let bytecode = bytecode! {
            GAS
            STOP
        };
        let addr_a = address!("0x000000000000000000000000000000000000AAAA");
        let addr_b = address!("0x000000000000000000000000000000000000BBBB");
        let test_ctx = TestContext::<2, 2>::new(
            None,
            |accs| {
                accs[0]
                    .address(addr_b)
                    .balance(Word::from(1u64 << 20))
                    .code(bytecode);
                accs[1].address(addr_a).balance(Word::from(1u64 << 20));
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(Word::from(1_000_000u64));
                txs[1]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(Word::from(1_000_000u64));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();
        let block: GethData = test_ctx.into();
        let builder = BlockData::new_from_geth_data_with_params(
            block.clone(),
            FixedCParams {
                total_chunks: 4,
                max_rws: 64,
                max_txs: 2,
                ..Default::default()
            },
        )
        .new_circuit_input_builder()
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
        let block = block_convert::<Fr>(&builder).unwrap();
        let chunks = chunk_convert(&block, &builder).unwrap();
        // assert last fingerprint acc are equal
        if let Some(last_chunk) = chunks.last() {
            assert_eq!(
                last_chunk.by_address_rw_fingerprints.mul_acc,
                last_chunk.chrono_rw_fingerprints.mul_acc
            )
        }
    }

    fn test_2_txs_with_chunk_size(total_chunks: usize, total_rws: usize) {
        let bytecode = bytecode! {
            GAS
            STOP
        };
        let addr_a = address!("0x000000000000000000000000000000000000AAAA");
        let addr_b = address!("0x000000000000000000000000000000000000BBBB");
        let test_ctx = TestContext::<2, 2>::new(
            None,
            |accs| {
                accs[0]
                    .address(addr_b)
                    .balance(Word::from(1u64 << 20))
                    .code(bytecode);
                accs[1].address(addr_a).balance(Word::from(1u64 << 20));
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(Word::from(1_000_000u64));
                txs[1]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(Word::from(1_000_000u64));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();
        CircuitTestBuilder::new_from_test_ctx(test_ctx)
            .params({
                FixedCParams {
                    total_chunks,
                    max_rws: total_rws / total_chunks,
                    max_txs: 2,
                    ..Default::default()
                }
            })
            .run_multiple_chunks_with_result(Some(total_chunks))
            .unwrap();
    }

    test_2_txs_with_various_chunk_size! {
        test_2_txs_with_1_400: (1, 400),
        test_2_txs_with_2_400: (2, 400),
        test_2_txs_with_3_400: (3, 400),
        test_2_txs_with_4_400: (4, 400),
        test_2_txs_with_1_600: (1, 600),
        test_2_txs_with_2_600: (2, 600),
        test_2_txs_with_3_600: (3, 600),
        test_2_txs_with_4_600: (4, 600),
        test_2_txs_with_5_600: (5, 600),
        test_2_txs_with_6_600: (6, 600),
    }
}

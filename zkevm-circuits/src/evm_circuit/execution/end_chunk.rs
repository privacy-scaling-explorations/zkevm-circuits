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
        self.rw_table_padding_gadget.assign_exec_step(
            region,
            offset,
            block,
            chunk,
            (step.rwc_inner_chunk.0 - 1 + step.bus_mapping_instance.len()) as u64,
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
    use bus_mapping::{circuit_input_builder::FixedCParams, mock::BlockData, operation::Target};
    use eth_types::{address, bytecode, geth_types::GethData, Word};
    use halo2_proofs::halo2curves::bn256::Fr;
    use mock::TestContext;

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
                total_chunks: 6,
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
        println!("num of chunk {:?}", chunks.len());
        chunks.iter().enumerate().for_each(|(idx, chunk)| {
            println!(
                "{}th chunk by_address_rw_fingerprints {:?}, chrono_rw_fingerprints {:?} ",
                idx, chunk.by_address_rw_fingerprints, chunk.chrono_rw_fingerprints,
            );
        });
    }

    #[test]
    fn test_all_chunks_ok() {
        let bytecode = bytecode! {
            PUSH1(0x0) // retLength
            PUSH1(0x0) // retOffset
            PUSH1(0x0) // argsLength
            PUSH1(0x0) // argsOffset
            PUSH1(0x0) // value
            PUSH32(0x10_0000) // addr
            PUSH32(0x10_0000) // gas
            CALL
            PUSH2(0xaa)
        };
        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
        )
        .block_modifier(Box::new(move |_block, chunk| {
            // TODO FIXME padding start as a workaround. The practical should be last chunk last row
            // rws
            // if let Some(a) = chunk.rws.0.get_mut(&Target::Start) {
            //     a.push(Rw::Start { rw_counter: 1 });
            // }
            println!(
                "=> FIXME is fixed? {:?}",
                chunk.chrono_rws.0.get_mut(&Target::Start)
            );
        }))
        .run_dynamic_chunk(4, 2);
    }

    #[test]
    fn test_all_chunks_fixed() {
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
        (0..6).for_each(|chunk_id| {
            CircuitTestBuilder::new_from_test_ctx(test_ctx.clone())
                .params({
                    FixedCParams {
                        total_chunks: 6,
                        max_rws: 64,
                        max_txs: 2,
                        ..Default::default()
                    }
                })
                .run_chunk(chunk_id);
        });
    }

    #[test]
    fn test_single_chunk() {
        let bytecode = bytecode! {
            STOP
        };
        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
        )
        .run();
    }
}

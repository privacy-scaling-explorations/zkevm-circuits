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
        // State transition
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
    use crate::{test_util::CircuitTestBuilder};
    use bus_mapping::{
        circuit_input_builder::{FixedCParams},
        operation::Target,
    };
    use eth_types::bytecode;
    use mock::TestContext;

    // fn test_ok(bytecode: bytecode::Bytecode) {
    //     CircuitTestBuilder::new_from_test_ctx(
    //         TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
    //     )
    //     .run()
    // }

    #[test]
    #[ignore] // still under development and testing
    fn test_intermediate_single_chunk() {
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
        .modifier(Box::new(move |_block, chunk| {
            // TODO FIXME padding start as a workaround. The practical should be last chunk last row
            // rws
            // if let Some(a) = chunk.rws.0.get_mut(&Target::Start) {
            //     a.push(Rw::Start { rw_counter: 1 });
            // }
            // Should be FIXED?
            println!(
                "chunk.rws.0.get_mut(&Target::Start) {:?}",
                chunk.rws.0.get_mut(&Target::Start)
            );
        }))
        .run_dynamic_chunk(4, 2);
    }

    #[test]
    #[ignore] // still under development and testing
    fn test_intermediate_single_chunk_fixed() {
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
        .params(FixedCParams {
            total_chunks: 2,
            max_rws: 60,
            ..Default::default()
        })
        .run_chunk(1);
    }

    #[test]
    #[ignore] // still under development and testing
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

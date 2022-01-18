use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition::Delta,
            },
            math_gadget::ShrWordsGadget,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ShrGadget<F> {
    same_context: SameContextGadget<F>,
    shr_words: ShrWordsGadget<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for ShrGadget<F> {
    const NAME: &'static str = "SHR";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SHR;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let a = cb.query_word();
        let shift = cb.query_word();

        cb.stack_pop(shift.expr());
        cb.stack_pop(a.expr());
        let shr_words = ShrWordsGadget::construct(cb, a, shift);
        cb.stack_push(shr_words.b().expr());

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(3.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(1.expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(
            cb,
            opcode,
            step_state_transition,
            None,
        );

        Self {
            same_context,
            shr_words,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction<F>,
        _: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;
        let indices =
            [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
        let [shift, a, b] = indices.map(|idx| block.rws[idx].stack_value());
        self.shr_words.assign(region, offset, a, shift, b)
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        test::{rand_word, run_test_circuit_incomplete_fixed_table},
        witness,
    };
    use bus_mapping::{bytecode, eth_types::Word, evm::OpcodeId};
    use rand::Rng;

    fn test_ok(opcode: OpcodeId, a: Word, shift: Word) {
        let bytecode = bytecode! {
            PUSH32(a)
            PUSH32(shift)
            #[start]
            .write_op(opcode)
            STOP
        };
        let block = witness::build_block_from_trace_code_at_start(&bytecode);
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    fn shr_gadget_simple() {
        test_ok(OpcodeId::SHR, 0x02FF.into(), 0x1.into());
    }

    #[test]
    fn shr_gadget_rand() {
        let a = rand_word();
        let mut rng = rand::thread_rng();
        let shift = rng.gen_range(0..=255);
        test_ok(OpcodeId::SHR, a, shift.into());
    }

    //this testcase manage to check the split is correct.
    #[test]
    fn shr_gadget_constant_shift() {
        let a = rand_word();
        test_ok(OpcodeId::SHR, a, 8.into());
        test_ok(OpcodeId::SHR, a, 64.into());
    }
}

use crate::{
  evm_circuit::{
      execution::ExecutionGadget,
      step::ExecutionState,
      util::{
          common_gadget::SameContextGadget,
          constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
          math_gadget::SarWordsGadget,
          CachedRegion,
      },
      witness::{Block, Call, ExecStep, Transaction},
  },
  util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct SarGadget<F> {
  same_context: SameContextGadget<F>,
  sar_words: SarWordsGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for SarGadget<F> {
  const NAME: &'static str = "SAR";

  const EXECUTION_STATE: ExecutionState = ExecutionState::SAR;

  fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
      let opcode = cb.query_cell();

      let a = cb.query_word();
      let shift = cb.query_word();

      cb.stack_pop(shift.expr());
      cb.stack_pop(a.expr());
      let sar_words = SarWordsGadget::construct(cb, a, shift);
      cb.stack_push(sar_words.b().expr());

      let step_state_transition = StepStateTransition {
          rw_counter: Delta(3.expr()),
          program_counter: Delta(1.expr()),
          stack_pointer: Delta(1.expr()),
          gas_left: Delta(-OpcodeId::SAR.constant_gas_cost().expr()),
          ..Default::default()
      };
      let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

      Self {
          same_context,
          sar_words,
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
      let indices = [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
      let [shift, a, b] = indices.map(|idx| block.rws[idx].stack_value());
      self.sar_words.assign(region, offset, a, shift, b)
  }
}

#[cfg(test)]
mod test {
  use crate::evm_circuit::test::rand_word;
  use crate::test_util::run_test_circuits;
  use eth_types::evm_types::OpcodeId;
  use eth_types::{bytecode, Word};
  use mock::TestContext;
  use rand::Rng;

  fn test_ok(opcode: OpcodeId, a: Word, shift: Word) {
      let bytecode = bytecode! {
          PUSH32(a)
          PUSH32(shift)
          #[start]
          .write_op(opcode)
          STOP
      };
      assert_eq!(
        run_test_circuits(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
            None
          ),
        Ok(())
      );
  }

  #[test]
  fn sar_gadget_simple() {
      test_ok(OpcodeId::SAR, 0x02FF.into(), 0x1.into());
      test_ok(
          OpcodeId::SAR,
          Word::from_big_endian(&[255u8; 32]),
          0x73.into(),
      );
  }

  #[test]
  fn sar_gadget_rand() {
      let a = rand_word();
      let mut rng = rand::thread_rng();
      let shift = rng.gen_range(0..=255);
      test_ok(OpcodeId::SAR, a, shift.into());
  }

  //this testcase manage to check the split is correct.
  #[test]
  fn sar_gadget_constant_shift() {
      let a = rand_word();
      test_ok(OpcodeId::SAR, a, 8.into());
      test_ok(OpcodeId::SAR, a, 64.into());
  }
}
#![allow(unused_imports)]

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{AddWordsGadget, IsZeroGadget, MulWordsGadget},
            not, select, Cell, RandomLinearCombination, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian, ToScalar, U256};
use halo2_proofs::{circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct AddModGadget<F> {
    same_context: SameContextGadget<F>,
    mul_gadget: MulWordsGadget<F>,
    sum_gadget: AddWordsGadget<F, 3, false>,
    minus_d: RandomLinearCombination<F, 32>,
}

impl<F: Field> ExecutionGadget<F> for AddModGadget<F> {
    const NAME: &'static str = "ADDMOD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ADDMOD;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        // [ -d * n ] + [ a ] + [ b ]  = r

        let a = cb.query_word();
        let b = cb.query_word();
        let n = cb.query_word();
        let minus_d = cb.query_word();
        let r = cb.query_word();

        // let n_is_zero_gadget = IsZeroGadget::construct(cb, n.clone().expr());
        // let n_is_not_zero_gadget = not::expr(n_is_zero_gadget.expr());

        let mul_gadget = MulWordsGadget::construct(cb, n.clone(), minus_d.clone());
        let sum_gadget = AddWordsGadget::construct(
            cb,
            [a.clone(), b.clone(), mul_gadget.product().clone()],
            r.clone(),
        );

        cb.stack_pop(a.expr());
        cb.stack_pop(b.expr());
        cb.stack_pop(n.expr());
        cb.stack_push(r.expr());

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(4.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(2.expr()),
            gas_left: Delta(-OpcodeId::ADDMOD.constant_gas_cost().expr()),
            ..StepStateTransition::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            mul_gadget,
            sum_gadget,
            minus_d,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let [r, n, b, a] = [3, 2, 1, 0]
            .map(|idx| step.rw_indices[idx])
            .map(|idx| block.rws[idx].stack_value());

        let d = (a + b) / n;
        let minus_d = U256::zero().overflowing_sub(d).0;
        let minus_d_mul_n = n.overflowing_mul(minus_d).0;

        // sanity check r == a + b + (n * -d)
        assert_eq!(a.overflowing_add(b).0.overflowing_add(minus_d_mul_n).0, r);

        self.minus_d
            .assign(region, offset, Some(minus_d.to_le_bytes()))?;
        self.mul_gadget
            .assign(region, offset, n, minus_d, minus_d_mul_n)?;
        self.sum_gadget
            .assign(region, offset, [a, b, minus_d_mul_n], r)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::rand_word;
    use crate::test_util::run_test_circuits;
    use eth_types::evm_types::OpcodeId;
    use eth_types::{bytecode, Word};

    fn test_ok(a: Word, b: Word, n: Word) {
        let bytecode = bytecode! {
            PUSH32(n)
            PUSH32(b)
            PUSH32(a)
            ADDMOD
            STOP
        };
        assert_eq!(run_test_circuits(bytecode), Ok(()));
    }

    #[test]
    fn addmod_simple() {
        test_ok(7.into(), 18.into(), 10.into());
        test_ok(7.into(), 1.into(), 10.into());
    }
}

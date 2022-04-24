#![allow(unused_imports)]

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::MAX_N_BYTES_INTEGER,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{
                AddWordsGadget, CmpWordsGadget, IsZeroGadget, LtGadget, MulWordsGadget,
                PairSelectGadget,
            },
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
    mul: MulWordsGadget<F>,
    sum: AddWordsGadget<F, 3, false>,
    n_is_zero: IsZeroGadget<F>,
    minus_d: RandomLinearCombination<F, 32>,
    cmp: CmpWordsGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for AddModGadget<F> {
    const NAME: &'static str = "ADDMOD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ADDMOD;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let a = cb.query_word();
        let b = cb.query_word();
        let n = cb.query_word();
        let minus_d = cb.query_word();
        let r = cb.query_word();

        let n_is_zero = IsZeroGadget::construct(cb, n.clone().expr());

        // r == [ -d * n ] + [ a ] + [ b ]  iff n != 0

        let mul = MulWordsGadget::construct(cb, n.clone(), minus_d.clone());
        let sum =
            AddWordsGadget::construct(cb, [a.clone(), b.clone(), mul.product().clone()], r.clone());
        let cmp = CmpWordsGadget::construct(cb, &r, &n);

        // r == 0 iff n == 0
        cb.require_zero(
            "",
            not::expr(n_is_zero.expr()) * not::expr(cmp.lt.expr()) * cmp.eq.expr(),
        );

        cb.stack_pop(a.expr());
        cb.stack_pop(b.expr());
        cb.stack_pop(n.expr());
        cb.stack_push(r.expr() * not::expr(n_is_zero.expr()));

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
            mul,
            sum,
            cmp,
            minus_d,
            n_is_zero,
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

        let (r, d) = if n.is_zero() {
            (a + b, U256::zero())
        } else {
            (r, (a + b) / n)
        };

        let minus_d = U256::zero().overflowing_sub(d).0;
        let minus_d_mul_n = n.overflowing_mul(minus_d).0;

        self.minus_d
            .assign(region, offset, Some(minus_d.to_le_bytes()))?;

        self.mul.assign(region, offset, n, minus_d, minus_d_mul_n)?;

        self.sum.assign(region, offset, [a, b, minus_d_mul_n], r)?;

        self.cmp.assign(region, offset, r, n)?;

        self.n_is_zero.assign(
            region,
            offset,
            Word::random_linear_combine(n.to_le_bytes(), block.randomness),
        )?;
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

    #[test]
    fn addmod_division_by_zero() {
        test_ok(7.into(), 1.into(), 0.into());
    }
}

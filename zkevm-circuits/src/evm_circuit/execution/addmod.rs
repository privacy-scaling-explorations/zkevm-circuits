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
                AddWordsGadget, CmpWordsGadget, IsZeroGadget, LtGadget, MulAddWords512Gadget,
                MulAddWordsGadget, MulWordsGadget, PairSelectGadget,
            },
            not, select, CachedRegion, Cell, RandomLinearCombination, Word,
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
    sum_areduced_b: AddWordsGadget<F, 2, false>,
    n_is_zero: IsZeroGadget<F>,
    cmp_r_n: CmpWordsGadget<F>,
    cmp_areduced_n: CmpWordsGadget<F>,
    a_reduced: RandomLinearCombination<F, 32>,
    muladd_k_n_areduced: MulAddWordsGadget<F>,
    muladd_d_n_r: MulAddWords512Gadget<F>,
}

impl<F: Field> ExecutionGadget<F> for AddModGadget<F> {
    const NAME: &'static str = "ADDMOD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ADDMOD;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        // values got from stack (original r is modified if n==0)
        let a = cb.query_word();
        let b = cb.query_word();
        let n = cb.query_word();
        let r = cb.query_word();
        
        // auxiliar witness
        let k = cb.query_word();
        let a_reduced = cb.query_word();
        let d = cb.query_word();

        let n_is_zero = IsZeroGadget::construct(cb, n.clone().expr());

        // check k * N + a_reduced == a without overflow
        let muladd_k_n_areduced = MulAddWordsGadget::construct(cb, k,n.clone(),a_reduced.clone(),a.clone());
        cb.require_zero("k * N + a_reduced does not overflow", muladd_k_n_areduced.overflow());

        // check d * n + r ==  a_reduced  + b 
        let sum_areduced_b = {
            let sum = cb.query_word();
            AddWordsGadget::construct(cb, [a_reduced.clone(), b.clone()], sum)
        };

        let muladd_d_n_r = {
            let sum_areduced_b_overflow = cb.query_word();
            let muladd_d_n_r = MulAddWords512Gadget::construct(cb, d, n.clone(), r.clone(), sum_areduced_b_overflow  , sum_areduced_b.sum().clone());

            cb.require_equal(
                "check carryset",
                muladd_d_n_r.d.expr(),
                sum_areduced_b.carry().clone().unwrap().expr() * not::expr(n_is_zero.expr()),
            );
            muladd_d_n_r
        };

        // check r < n
        let cmp_r_n = CmpWordsGadget::construct(cb, &r, &n);
        cb.require_zero(
            "if r > 0 => r < n",
            not::expr(n_is_zero.expr()) * not::expr(cmp_r_n.lt.expr()),
        );

        // check a_reduced < n
        let cmp_areduced_n = CmpWordsGadget::construct(cb, &a_reduced, &n);
        cb.require_zero(
            "if r > 0 => a_reduced < n",
            not::expr(n_is_zero.expr()) * not::expr(cmp_areduced_n.lt.expr()),
        );

        // pop/push values, taking care that if n==0 pushed value for r should be zero also
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
            muladd_d_n_r,
            a_reduced,
            muladd_k_n_areduced,
            same_context,
            cmp_r_n,
            cmp_areduced_n,
            n_is_zero,
            sum_areduced_b,
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

        let [mut r, n, b, a] = [3, 2, 1, 0]
            .map(|idx| step.rw_indices[idx])
            .map(|idx| block.rws[idx].stack_value());

        let a_reduced;
        let k;
        let d;
        let a_reduced_plus_b;
        let a_reduced_plus_b_overflow;

        if n.is_zero() {
            k = U256::zero();
            a_reduced = a;
            d = U256::zero();
            r = a.overflowing_add(b).0;

            a_reduced_plus_b = a_reduced.overflowing_add(b).0;
            a_reduced_plus_b_overflow = U256::zero();
        } else {
            let (a_div_n, a_mod_n) = a.div_mod(n);
            k = a_div_n;
            a_reduced = a_mod_n;
            d = (a_reduced + b) / n;

            let (sum, overflow) = a_reduced.overflowing_add(b);
            a_reduced_plus_b = sum;
            a_reduced_plus_b_overflow = if overflow { U256::one() } else { U256::zero() };
        };

        self.muladd_k_n_areduced
            .assign(region, offset, k, n, a_reduced, a)?;

        self.sum_areduced_b
            .assign(region, offset, [a_reduced, b], a_reduced_plus_b)?;

        dbg!(d, n, r, a_reduced_plus_b_overflow, a_reduced_plus_b);
        self.muladd_d_n_r.assign(
            region,
            offset,
            d, n, r, a_reduced_plus_b_overflow, a_reduced_plus_b,
        )?;

        self.cmp_r_n.assign(region, offset, r, n)?;
        self.cmp_areduced_n.assign(region, offset, a_reduced, n)?;

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
    use eth_types::evm_types::{OpcodeId, Stack};
    use eth_types::{bytecode, Word};
    use mock::TestContext;

    fn test(a: Word, b: Word, n: Word, r: Option<Word>) -> bool {
        let bytecode = bytecode! {
            PUSH32(n)
            PUSH32(b)
            PUSH32(a)
            ADDMOD
            STOP
        };

        let mut ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap();
        if let Some(r) = r {
            let mut last = ctx
                .geth_traces
                .first_mut()
                .unwrap()
                .struct_logs
                .last_mut()
                .unwrap();
            last.stack = Stack::from_vec(vec![r]);
        }
        run_test_circuits(ctx, None).is_ok()
    }
    fn test_u32(a: u32, b: u32, c: u32, r: Option<u32>) -> bool {
        test(a.into(), b.into(), c.into(), r.map(Word::from))
    }

    #[test]
    fn addmod_1_1_10() {
        assert_eq!(true, test_u32(1, 1, 10, None));
    }

    #[test]
    fn addmod_1_11_10() {
        assert_eq!(true, test_u32(1, 1, 10, None));
    }

    #[test]
    fn addmod_max_max_0() {
        assert_eq!(true, test(Word::MAX, Word::MAX, 0.into(), None));
    }

    #[test]
    fn addmod_max_max_1() {
        assert_eq!(true, test(Word::MAX, Word::MAX, 1.into(), None));
    }

    #[test]
    fn addmod_max_max_max() {
        assert_eq!(true, test(Word::MAX, Word::MAX, Word::MAX, None));
    }

    #[test]
    fn addmod_max_1_0() {
        assert_eq!(true, test(Word::MAX, 1.into(), 0.into(), None));
    }

    #[test]
    fn addmod_max_1_1() {
        assert_eq!(true, test(Word::MAX, 1.into(), 1.into(), None));
    }

    #[test]
    fn addmod_max_1_max() {
        assert_eq!(true, test(Word::MAX, 1.into(), Word::MAX, None));
    }

    #[test]
    fn addmod_max_0_0() {
        assert_eq!(true, test(Word::MAX, 0.into(), 0.into(), None));
    }

    #[test]
    fn addmod_max_0_1() {
        assert_eq!(true, test(Word::MAX, 0.into(), 1.into(), None));
    }

    #[test]
    fn addmod_max_0_max() {
        assert_eq!(true, test(Word::MAX, 0.into(), Word::MAX, None));
    }

    #[test]
    fn addmod_0_0_0() {
        assert_eq!(true, test(0.into(), 0.into(), 0.into(), None));
    }

    #[test]
    fn addmod_0_0_1() {
        assert_eq!(true, test(0.into(), 0.into(), 1.into(), None));
    }

    #[test]
    fn addmod_0_0_max() {
        assert_eq!(true, test(0.into(), 0.into(), Word::MAX, None));
    }
    #[test]
    fn addmod_bad_r_on_nonzero_n() {
        assert_eq!(true, test_u32(7, 18, 10, Some(5)));
        assert_eq!(false, test_u32(7, 18, 10, Some(6)));
    }

    #[test]
    fn addmod_bad_r_on_zero_n() {
        assert_eq!(true, test_u32(2, 3, 0, Some(0)));
        assert_eq!(false, test_u32(2, 3, 0, Some(1)));
    }

    #[test]
    fn addmod_bad_r_bigger_n() {
        assert_eq!(true, test_u32(2, 3, 4, Some(1)));
        assert_eq!(false, test_u32(2, 3, 4, Some(5)));
    }
}

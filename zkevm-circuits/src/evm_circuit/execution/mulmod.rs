#![allow(unused_imports)]

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::MAX_N_BYTES_INTEGER,
        step::ExecutionState,
        util::{
            self,
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{
                AddWordsGadget, ComparisonGadget, IsZeroGadget, LtGadget, MulAddWords512Gadget,
                MulAddWordsGadget, PairSelectGadget,
            },
            not, select, CachedRegion, Cell, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use digest::generic_array::typenum::{U2, U25};
use eth_types::{Field, ToLittleEndian, ToScalar, U256, U512};
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression},
};

/// MulModGadget verifies opcod MULMOD
/// Verify a * b = r (mod n)
/// where a, b, n, r are 256-bit words
#[derive(Clone, Debug)]
pub(crate) struct MulModGadget<F> {
    same_context: SameContextGadget<F>,

    // a, b, n, r
    pub words: [util::Word<F>; 4],

    k1: util::Word<F>,
    k2: util::Word<F>,
    a_reduced: util::Word<F>,
    zero: util::Word<F>,
    d: util::Word<F>,
    e: util::Word<F>,

    mul: MulAddWordsGadget<F>,
    mul512_left: MulAddWords512Gadget<F>,
    mul512_right: MulAddWords512Gadget<F>,
    n_is_zero: IsZeroGadget<F>,
    lt: [LtGadget<F, 8>; 2],
}

impl<F: Field> ExecutionGadget<F> for MulModGadget<F> {
    const NAME: &'static str = "MULMOD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::MULMOD;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let a = cb.query_word();
        let b = cb.query_word();
        let n = cb.query_word();
        let r = cb.query_word();

        let k1 = cb.query_word();
        let k2 = cb.query_word();

        let a_reduced = cb.query_word();
        let d = cb.query_word();
        let e = cb.query_word();

        // TODO Review this
        let zero = cb.query_word();

        // 1.  k1 * n + a_reduced  == a
        let mul =
            MulAddWordsGadget::construct(cb, k1.clone(), n.clone(), a_reduced.clone(), a.clone());

        // 2.  a_reduced * b + 0 == d * 2^256 + e
        let mul512_left = MulAddWords512Gadget::construct(cb, [&a_reduced, &b, &zero, &d, &e]);

        // 3.  k2 * n + r == d * 2^256 + e
        let mul512_right = MulAddWords512Gadget::construct(cb, [&k2, &n, &r, &d, &e]);

        let n_is_zero = IsZeroGadget::construct(cb, n.expr());
        let lt1 = LtGadget::construct(cb, r.expr(), n.expr());
        let lt2 = LtGadget::construct(cb, a_reduced.expr(), n.expr());

        // (a_reduced < n & r < n ) or n == 0
        let is_valid: Expression<F> = 1.expr() - ((lt1.expr() * lt2.expr()) + n_is_zero.expr());
        cb.add_constraint(" 1 - ((a_reduced < n) * (r < n) - (n==0)) ", is_valid);

        cb.stack_pop(a.expr());
        cb.stack_pop(b.expr());
        cb.stack_pop(n.expr());
        cb.stack_push(r.expr() * not::expr(n_is_zero.expr()));

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(4.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(2.expr()),
            gas_left: Delta(-OpcodeId::MULMOD.constant_gas_cost().expr()),
            ..StepStateTransition::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            words: [a, b, n, r],
            same_context,
            k1,
            k2,
            a_reduced,
            zero,
            d,
            e,
            mul,
            mul512_left,
            mul512_right,
            n_is_zero,
            lt: [lt1, lt2],
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

        let [r, n, b, a] = [3, 2, 1, 0]
            .map(|idx| step.rw_indices[idx])
            .map(|idx| block.rws[idx].stack_value());

        // 1. Reduction of a mod n
        let (a_reduced, k1) = if n.is_zero() {
            (a, U256::zero())
        } else {
            (a % n, a / n)
        };

        // 2. Compute r
        // d, e = a_reduced * b // 2^256, a_reduced*b % 2^256
        // let prod: U512 = U512::from(a_reduced) * U512::from(b);
        let prod = a_reduced.full_mul(b);
        let mut prod_bytes = [0u8; 64];
        prod.to_little_endian(&mut prod_bytes);
        let d = U256::from_little_endian(&prod_bytes[..32]);
        let e = U256::from_little_endian(&prod_bytes[32..]);

        let (r, k2) = if n.is_zero() {
            (a_reduced * b, U256::zero())
        } else {
            (r, (a_reduced * b) / n)
        };

        // 3. n == zero check
        if n.is_zero() {
            (a_reduced * b, U256::zero())
        } else {
            (r, (a_reduced * b) / n)
        };

        self.k1.assign(region, offset, Some(k1.to_le_bytes()))?;
        self.k2.assign(region, offset, Some(k2.to_le_bytes()))?;
        self.a_reduced
            .assign(region, offset, Some(a_reduced.to_le_bytes()))?;
        self.zero
            .assign(region, offset, Some(U256::from(0u32).to_le_bytes()))?;

        self.mul.assign(region, offset, [k1, n, a_reduced, a])?;
        self.mul512_left
            .assign(region, offset, [a_reduced, b, U256::from(0u32), d, e])?;
        self.mul512_right.assign(region, offset, [k2, n, r, d, e])?;

        let n_as_f = util::Word::random_linear_combine(n.to_le_bytes(), block.randomness);
        let r_as_f = util::Word::random_linear_combine(r.to_le_bytes(), block.randomness);
        let a_reduced_as_f =
            util::Word::random_linear_combine(a_reduced.to_le_bytes(), block.randomness);
        self.lt[0].assign(region, offset, a_reduced_as_f, n_as_f)?;
        self.lt[1].assign(region, offset, r_as_f, n_as_f)?;

        self.n_is_zero.assign(region, offset, n_as_f)?;
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

    fn test(a: u32, b: u32, n: u32, r: Option<u32>) -> bool {
        let bytecode = bytecode! {
            PUSH32(n)
            PUSH32(b)
            PUSH32(a)
            MULMOD
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
            last.stack = Stack::from_vec(vec![r.into()]);
        }
        run_test_circuits(ctx, None).is_ok()
    }

    #[test]
    fn mulmod_simple() {
        assert_eq!(true, test(7, 18, 10, None));
        assert_eq!(true, test(7, 1, 10, None));
    }

    #[test]
    fn mulmod_division_by_zero() {
        assert_eq!(true, test(7, 1, 0, None));
    }

    #[test]
    fn mulmod_bad_r_on_nonzero_n() {
        assert_eq!(true, test(7, 18, 10, Some(5)));
        assert_eq!(false, test(7, 18, 10, Some(6)));
    }

    #[test]
    fn mulmod_bad_r_on_zero_n() {
        assert_eq!(true, test(2, 3, 0, Some(0)));
        assert_eq!(false, test(2, 3, 0, Some(1)));
    }

    #[test]
    fn mulmod_bad_r_bigger_n() {
        assert_eq!(true, test(2, 3, 5, Some(1)));
        assert_eq!(false, test(2, 3, 5, Some(5)));
    }
}

use super::super::{
    Case, Cell, Constraint, CoreStateInstance, ExecutionStep, Word,
};
use super::utils::{
    self,
    common_cases::{OutOfGasCase, StackUnderflowCase},
    constraint_builder::ConstraintBuilder,
    StateTransition,
};
use super::{CaseAllocation, CaseConfig, OpExecutionState, OpGadget};
use crate::impl_op_gadget;
use crate::util::{Expr, ToWord};
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};
use std::convert::TryInto;

static STATE_TRANSITION: StateTransition = StateTransition {
    gc_delta: Some(3),
    pc_delta: Some(1),
    sp_delta: Some(1),
    gas_delta: Some(GasCost::FAST.as_u64()),
    next_memory_size: None,
};
const NUM_POPPED: usize = 2;

impl_op_gadget!(
    #set[MUL]
    MulGadget {
        MulSuccessCase(),
        StackUnderflowCase(NUM_POPPED),
        OutOfGasCase(STATE_TRANSITION.gas_delta.unwrap()),
    }
);

#[derive(Clone, Debug)]
struct MulSuccessCase<F> {
    case_selector: Cell<F>,
    a: Word<F>,
    b: Word<F>,
    c: Word<F>,
    t0: Cell<F>,
    t1: Cell<F>,
    t2: Cell<F>,
    t3: Cell<F>,
    v0: [Cell<F>; 9],
    v1: [Cell<F>; 9],
}

impl<F: FieldExt> MulSuccessCase<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OpcodeId::MUL];

    pub const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::Success,
        num_word: 3,
        num_cell: 22,
        will_halt: false,
    };
    
    pub fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            a: alloc.words.pop().unwrap(),
            b: alloc.words.pop().unwrap(),
            c: alloc.words.pop().unwrap(),
            t0: alloc.cells.pop().unwrap(),
            t1: alloc.cells.pop().unwrap(),
            t2: alloc.cells.pop().unwrap(),
            t3: alloc.cells.pop().unwrap(),
            v0: alloc
                .cells
                .drain(0..9)
                .collect::<Vec<Cell<F>>>()
                .try_into()
                .unwrap(),
            v1: alloc
                .cells
                .drain(0..9)
                .collect::<Vec<Cell<F>>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Vec<Constraint<F>> {
        let mut cb = ConstraintBuilder::default();

        let MulSuccessCase {
            case_selector,
            a,
            b,
            c,
            t0,
            t1,
            t2,
            t3,
            v0,
            v1,
        } = &self;
        //merge 8 8-bit cell for a 64-bit expression for a, b, c
        let mut a_digits = vec![];
        let mut b_digits = vec![];
        let mut c_digits = vec![];
        let mut cur_v0 = 0.expr();
        let mut cur_v1 = 0.expr();
        for virtual_idx in 0..4 {
            let mut tmp_a = 0.expr();
            let mut tmp_b = 0.expr();
            let mut tmp_c = 0.expr();
            let mut radix = 1.expr();
            for idx in 0..8 {
                let now_idx = (virtual_idx * 8 + idx) as usize;
                tmp_a = tmp_a + radix.clone() * a.cells[now_idx].expr();
                tmp_b = tmp_b + radix.clone() * b.cells[now_idx].expr();
                tmp_c = tmp_c + radix.clone() * c.cells[now_idx].expr();
                radix = radix * (1 << 8).expr();
            }
            a_digits.push(tmp_a);
            b_digits.push(tmp_b);
            c_digits.push(tmp_c);
        }

        //radix_constant_8 == 2^8
        let mut tmp_radix = 1.expr()/*Expression::Constant(F::from_u128(1u64))*/;
        let radix_constant_8 = 256.expr()/*Expression::Constant(F::from_u128(1u64 << 8))*/;
        for idx in 0..9 {
            cur_v0 = cur_v0 + tmp_radix.clone() * v0[idx].expr();
            cur_v1 = cur_v1 + tmp_radix.clone() * v1[idx].expr();
            tmp_radix = tmp_radix * radix_constant_8.clone();
        }

        for total_idx in 0..4 {
            let mut rhs_sum = 0.expr(); 
            for a_id in 0..=total_idx {
                let (a_idx, b_idx) = (a_id as usize, (total_idx - a_id) as usize); 
                rhs_sum = rhs_sum + a_digits[a_idx].clone() * b_digits[b_idx].clone();
            }
            cb.require_zero(
                match total_idx {
                    0 => t0.expr() - rhs_sum,
                    1 => t1.expr() - rhs_sum,
                    2 => t2.expr() - rhs_sum,
                    3 => t3.expr() - rhs_sum,
                    _ => unimplemented!(),
                }
            );
        }

        //radix_constant_64 == 2^64
        //radix_constant_128 == 2^128
        let radix_constant = (1u64 << 32).expr()/*Expression::Constant(F::from_u128(1u64 << 32))*/;
        let radix_constant_64 = radix_constant.clone() * radix_constant;
        let radix_constant_128 = radix_constant_64.clone() * radix_constant_64.clone();
        cb.require_equal(
            cur_v0.clone() * radix_constant_128.clone(),
            t0.expr() + t1.expr() * radix_constant_64.clone()
            - (c_digits[0].clone() + c_digits[1].clone() * radix_constant_64.clone())
        );
        cb.require_equal(
            cur_v1 * radix_constant_128.clone(),
            cur_v0 + t2.expr() + t3.expr() * radix_constant_64.clone()
            - (c_digits[2].clone() + c_digits[3].clone() * radix_constant_64.clone())
        );

        cb.stack_pop(a.expr());
        cb.stack_pop(b.expr());
        cb.stack_push(c.expr());

        //use rangecheck to check v0,v1
        //we need v0,v1 in range[0,2^66)
        for idx in 0..9 {
            cb.require_in_range(v0[idx].expr(), 256);
            cb.require_in_range(v1[idx].expr(), 256);
        }

        // State transitions
        STATE_TRANSITION.constraints(&mut cb, state_curr, state_next);

        vec![cb.constraint(case_selector.expr(), name)]
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: &mut CoreStateInstance,
        step: &ExecutionStep,
    ) -> Result<(), Error> {

        self.a.assign(
            region,
            offset,
            Some(step.values[0].to_word()),
        )?;
        self.b.assign(
            region,
            offset,
            Some(step.values[1].to_word()),
        )?;
        self.c.assign(
            region,
            offset,
            Some(step.values[2].to_word()),
        )?;
        let radix = F::from_u128(1u128 << 64);
        let t0_digits = step.values[3].to_u64_digits();
        let t0 = if t0_digits.is_empty() {
            F::zero()
        } else {
            let mut tmp = F::zero();
            let mut tmp_radix = F::one();
            for idx in 0.. t0_digits.len(){
                tmp = tmp + tmp_radix * F::from_u128(t0_digits[idx as usize] as u128);
                tmp_radix = tmp_radix * radix.clone()
            }
            tmp
        };
        let t1_digits = step.values[4].to_u64_digits();
        let t1 = if t1_digits.is_empty() {
            F::zero()
        } else {
            let mut tmp = F::zero();
            let mut tmp_radix = F::one();
            for idx in 0.. t1_digits.len(){
                tmp = tmp + tmp_radix * F::from_u128(t1_digits[idx as usize] as u128);
                tmp_radix = tmp_radix * radix.clone()
            }
            tmp
        };
        let t2_digits = step.values[5].to_u64_digits();
        let t2 = if t2_digits.is_empty() {
            F::zero()
        } else {
            let mut tmp = F::zero();
            let mut tmp_radix = F::one();
            for idx in 0.. t2_digits.len(){
                tmp = tmp + tmp_radix * F::from_u128(t2_digits[idx as usize] as u128);
                tmp_radix = tmp_radix * radix.clone()
            }
            tmp
        };
        let t3_digits = step.values[6].to_u64_digits();
        let t3 = if t3_digits.is_empty() {
            F::zero()
        } else {
            let mut tmp = F::zero();
            let mut tmp_radix = F::one();
            for idx in 0.. t3_digits.len(){
                tmp = tmp + tmp_radix * F::from_u128(t3_digits[idx as usize] as u128);
                tmp_radix = tmp_radix * radix.clone()
            }
            tmp
        };
        self.t0.assign(region, offset, Some(t0))?;
        self.t1.assign(region, offset, Some(t1))?;
        self.t2.assign(region, offset, Some(t2))?;
        self.t3.assign(region, offset, Some(t3))?;
        self.v0
            .iter()
            .zip(step.values[7].to_word().iter())
            .map(|(alloc, value)|{
                alloc.assign(region, offset, Some(F::from_u128(*value as u128)))
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.v1
            .iter()
            .zip(step.values[8].to_word().iter())
            .map(|(alloc, value)|{
                alloc.assign(region, offset, Some(F::from_u128(*value as u128)))
            })
            .collect::<Result<Vec<_>, _>>()?;

        STATE_TRANSITION.assign(state);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::super::super::{
        test::TestCircuit, Case, ExecutionStep, Operation,
    };
    use crate::util::ToWord;
    use bus_mapping::{evm::OpcodeId, operation::Target};
    use halo2::{arithmetic::FieldExt, dev::MockProver};
    use num::BigUint;
    use rand::Rng;
    use pairing::bn256::Fr as Fp;

    macro_rules! try_test_circuit {
        ($execution_steps:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Fp>::new($execution_steps, $operations, false);
            let prover = MockProver::<Fp>::run(11, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    fn result_generate(a: &BigUint, b: &BigUint) -> (
            BigUint, BigUint, BigUint, BigUint, BigUint, BigUint, BigUint, u128, u128, u128
        ) {
        let constant_64 = BigUint::from(1u128 << 64);
        let constant_128 = constant_64.clone() * constant_64.clone();
        let constant_256 = constant_128.clone() * constant_128.clone();
        let c = a * b % constant_256;
        let a8s = a.to_word();
        let b8s = b.to_word();
        let c8s = c.to_word();
        let mut suma :u128 = 0;
        let mut sumb :u128 = 0;
        let mut sumc :u128 = 0;
        for idx in 0..32 {
            let tmp_a = if a8s.len() >= idx + 1 { a8s[idx] as u128} else { 0u128 };
            let tmp_b = if b8s.len() >= idx + 1 { b8s[idx] as u128} else { 0u128 };
            let tmp_c = if c8s.len() >= idx + 1 { c8s[idx] as u128} else { 0u128 };
            suma = suma + tmp_a;
            sumb = sumb + tmp_b;
            sumc = sumc + tmp_c;
            print!("{} ",tmp_c);
        }println!("");
        let a_digits = a.to_u64_digits();
        let b_digits = b.to_u64_digits();
        let c_digits = c.to_u64_digits();
        let total_idx :usize = 0;
        let mut t_digits = vec![];
        for total_idx in 0..4 {
            let mut rhs_sum = BigUint::from(0u128); 
            for a_id in 0..=total_idx {
                let (a_idx, b_idx) = (a_id as usize, (total_idx - a_id) as usize); 
                let tmp_a = if a_digits.len() >= a_idx + 1 { BigUint::from(a_digits[a_idx]) } else { BigUint::from(0u128) };
                let tmp_b = if b_digits.len() >= b_idx + 1 { BigUint::from(b_digits[b_idx]) } else { BigUint::from(0u128) };
                rhs_sum = rhs_sum.clone() + tmp_a * tmp_b;
            }
            t_digits.push(rhs_sum);
        }
        let (t0, t1, t2, t3) = (t_digits[0].clone(), t_digits[1].clone(), t_digits[2].clone(), t_digits[3].clone());
        let mut c_now = vec![];
        for idx in 0..4 {
            c_now.push(
                if c_digits.len() >= idx + 1 { BigUint::from(c_digits[idx]) } else { BigUint::from(0u128) }
            )
        }
        let v0 = (
            t0.clone() + t1.clone() * constant_64.clone() 
            - c_now[0].clone() - c_now[1].clone() * constant_64.clone()
        ) / constant_128.clone();
        let v1 = (
            v0.clone() + t2.clone() + t3.clone() * constant_64.clone() 
            - c_now[2].clone() - c_now[3].clone() * constant_64.clone()
        ) / constant_128.clone();

        println!("{} {} {} {} {} {}",t0,t1,t2,t3,v0,v1);
        (
            c,
            t0,
            t1,
            t2,
            t3,
            v0,
            v1,
            suma,
            sumb,
            sumc,
        )
    }

    #[test]
    fn mul_gadget() {
        let rng = rand::thread_rng();
        let mut vec_a = vec![];
        let mut vec_b = vec![];
        for idx in 0..32 {
            vec_a.push(
                if true {rng.clone().gen_range(0..=255)}
                else {0}
            );
        }

        for idx in 0..32 {
            vec_b.push(
                if true {rng.clone().gen_range(0..=255)}
                else {0}
            );
        }

        for idx in 0..32 {
            print!("{} ",vec_a[idx]);
        }
        println!("");
        for idx in 0..32 {
            print!("{} ",vec_b[idx]);
        }
        println!("");

        let a = BigUint::from_bytes_le(&vec_a);
        let b = BigUint::from_bytes_le(&vec_b);
        let a_bits = a.bits();
        let bits_num = if a_bits % 8 == 0 {
            a_bits / 8
        } else {
            a_bits / 8 + 1
        };
        let mut push_bigint = [0u8; 32];
        for idx in 0..bits_num {
            push_bigint[idx as usize] = 1u8;
        }
        let push_bigint = BigUint::from_bytes_le(&push_bigint);
        let (
            c,
            t0,
            t1,
            t2,
            t3,
            v0,
            v1,
            suma,
            sumb,
            sumc,
        ) = result_generate(&a, &b);
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH32,
                    case: Case::Success,
                    values: vec![a.clone(),push_bigint.clone()],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH32,
                    case: Case::Success,
                    values: vec![b.clone(),push_bigint],
                },
                ExecutionStep {
                    opcode: OpcodeId::MUL,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        b.clone(),
                        c.clone(),
                        t0.clone(),
                        t1.clone(),
                        t2.clone(),
                        t3.clone(),
                        v0.clone(),
                        v1.clone(),
                    ],
                }
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Fp::zero(),
                        Fp::from_u128(1023),
                        Fp::from_u128(suma),
                        Fp::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Fp::zero(),
                        Fp::from_u128(1022),
                        Fp::from_u128(sumb),
                        Fp::zero(),
                    ]
                },
                Operation {
                    gc: 3,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Fp::zero(),
                        Fp::from_u128(1022),
                        Fp::from_u128(suma),
                        Fp::zero(),
                    ]
                },
                Operation {
                    gc: 4,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Fp::zero(),
                        Fp::from_u128(1023),
                        Fp::from_u128(sumb),
                        Fp::zero(),
                    ]
                },
                Operation {
                    gc: 5,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Fp::zero(),
                        Fp::from_u128(1023),
                        Fp::from_u128(sumc),
                        Fp::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }
}
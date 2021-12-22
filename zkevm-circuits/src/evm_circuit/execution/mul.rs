use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition::Delta,
            },
            //math_gadget::{AddWordsGadget, PairSelectGadget},
            //select,
            Cell,
            Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
//use bus_mapping::evm::OpcodeId;
use bus_mapping::eth_types::{self, ToLittleEndian};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};
use std::convert::TryInto;

// MulGadget verifies MUL: a * b mod 2^256 is equal to c,
#[derive(Clone, Debug)]
pub(crate) struct MulGadget<F> {
    same_context: SameContextGadget<F>,
    a: Word<F>,
    b: Word<F>,
    c: Word<F>,
    //a, b, c is divided into 4 64-bit digits, call them a0 ~ a3, b0 ~ b3 ...
    //a * b = a0 * b0 + a1 * b0 ...
    t0: Cell<F>, //a0 * b0, contribute 0 ~ 128 bit
    t1: Cell<F>, //a0 * b1 + a1 * b0, contribute 64 ~ 193 (notice not 192) bit
    t2: Cell<F>, //a0 * b2 + a2 * b0 + a1 * b1, contribute 128 ~ 256 bit
    t3: Cell<F>, /* a0 * b3 + a3 * b0 + a2 * b1 + a1 * b2, contribute 192
                  * bit above */

    //so t0 ~ t1 include all contributions to the low 256bit of product c,
    // with a maxium 66bit radix (the part higher than 256bit) v1 (so 9
    // bytes) it is similar that we have v0 as the radix of contributions
    // to the low 128bit of the product
    v0: [Cell<F>; 9],
    v1: [Cell<F>; 9],
    /*just prove that:
     *  t0 + t1 = <low 128 bit of c> + <radix v0>
     *  t2 + t3 + <radix v0> = <high 128 bit of c> + <radix v1> */
}

impl<F: FieldExt> MulGadget<F> {
    //assign all intermedia cells (t0 ~ t3 and v0, v1) from a and b
    fn assign_witness(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        wa: &eth_types::Word,
        wb: &eth_types::Word,
    ) -> Result<(), Error> {
        use num::BigUint;
        //    use bus_mapping::eth_types::ToWord;

        let constant_64 = BigUint::from(1u128 << 64);
        let constant_128 = constant_64.clone() * constant_64.clone();
        let constant_256 = constant_128.clone() * constant_128.clone();
        let a = BigUint::from_bytes_le(&wa.to_le_bytes());
        let b = BigUint::from_bytes_le(&wb.to_le_bytes());
        let c = a.clone() * b.clone() % constant_256;
        //TODO: would c is an invalid Field?
        /*
        //TODO: move it to test code?
        let a8s = a.to_bytes_le();
        let b8s = b.to_bytes_le();
        let c8s = c.to_bytes_le();
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
        }println!("");*/
        let a_digits = a.to_u64_digits();
        let b_digits = b.to_u64_digits();
        let c_digits = c.to_u64_digits();
        let mut t_digits = vec![];
        for total_idx in 0..4 {
            let mut rhs_sum = BigUint::from(0u128);
            for a_id in 0..=total_idx {
                let (a_idx, b_idx) =
                    (a_id as usize, (total_idx - a_id) as usize);
                let tmp_a = if a_digits.len() > a_idx {
                    BigUint::from(a_digits[a_idx])
                } else {
                    BigUint::from(0u128)
                };
                let tmp_b = if b_digits.len() > b_idx {
                    BigUint::from(b_digits[b_idx])
                } else {
                    BigUint::from(0u128)
                };
                rhs_sum = rhs_sum.clone() + tmp_a * tmp_b;
            }
            t_digits.push(rhs_sum);
        }

        for (digit, assignee) in t_digits
            .iter()
            .zip([&self.t0, &self.t1, &self.t2, &self.t3])
        {
            let mut digit_bts = digit.to_bytes_le();
            digit_bts.resize(32, 0);
            let digit_bts: [u8; 32] = digit_bts.try_into().unwrap();
            assignee.assign(
                region,
                offset,
                Some(F::from_bytes(&digit_bts).unwrap()),
            )?;
        }

        let mut c_now = vec![];
        for idx in 0..4 {
            c_now.push(if c_digits.len() > idx {
                BigUint::from(c_digits[idx])
            } else {
                BigUint::from(0u128)
            })
        }
        let v0 = (constant_64.clone() * &t_digits[1] + &t_digits[0]
            - &c_now[0]
            - constant_64.clone() * &c_now[1])
            / &constant_128;
        let v1 = (constant_64.clone() * &t_digits[3] + &v0 + &t_digits[2]
            - &c_now[2]
            - constant_64 * &c_now[3])
            / &constant_128;

        v0.to_bytes_le()
            .into_iter()
            .zip(self.v0.iter())
            .try_for_each(|(bt, assignee)| -> Result<(), Error> {
                assignee.assign(region, offset, Some(F::from(bt as u64)))?;
                Ok(())
            })?;

        v1.to_bytes_le()
            .into_iter()
            .zip(self.v1.iter())
            .try_for_each(|(bt, assignee)| -> Result<(), Error> {
                assignee.assign(region, offset, Some(F::from(bt as u64)))?;
                Ok(())
            })?;

        Ok(())

        /*        println!("{} {} {} {} {} {}",t0,t1,t2,t3,v0,v1);
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
        )*/
    }
}

impl<F: FieldExt> ExecutionGadget<F> for MulGadget<F> {
    const NAME: &'static str = "MUL";

    const EXECUTION_STATE: ExecutionState = ExecutionState::MUL;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let a = cb.query_word();
        let b = cb.query_word();
        let c = cb.query_word();
        let t0 = cb.query_cell();
        let t1 = cb.query_cell();
        let t2 = cb.query_cell();
        let t3 = cb.query_cell();
        //TODO: can the cell is just bytes so we use query_byte instead?
        let v0: [Cell<F>; 9] = (0..9)
            .map(|_| cb.query_cell())
            .collect::<Vec<Cell<F>>>()
            .try_into()
            .unwrap();
        let v1: [Cell<F>; 9] = (0..9)
            .map(|_| cb.query_cell())
            .collect::<Vec<Cell<F>>>()
            .try_into()
            .unwrap();

        //merge 8 8-bit cell for a 64-bit expression for a, b, c,
        //each digits has 4 64-bit
        let mut a_digits = vec![];
        let mut b_digits = vec![];
        let mut c_digits = vec![];
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

        for total_idx in 0..4 {
            let mut rhs_sum = 0.expr();
            for a_id in 0..=total_idx {
                let (a_idx, b_idx) =
                    (a_id as usize, (total_idx - a_id) as usize);
                rhs_sum =
                    rhs_sum + a_digits[a_idx].clone() * b_digits[b_idx].clone();
            }
            cb.require_zero(
                "mul: dissemble product",
                match total_idx {
                    //indicate the digits inside a_digits and b_digits as a0 ~ a3 and b0 ~ b3
                    0 => t0.expr() - rhs_sum, //a0 * b0
                    1 => t1.expr() - rhs_sum, //a0 * b1 + a1 * b0
                    2 => t2.expr() - rhs_sum, //a0 * b2 + a2 * b0 + a1 * b1
                    3 => t3.expr() - rhs_sum, //a0 * b3 + a3 * b0 + a2 * b1 + a1 * b2
                    _ => unimplemented!(),
                    //so all the digits contributed to the low 256bits of product has been involved
                },
            );
        }

        let mut cur_v0 = 0.expr();
        let mut cur_v1 = 0.expr();
        let mut tmp_radix = 1.expr();
        //radix_constant_8 == 2^8
        let radix_constant_8 = 256.expr();
        for idx in 0..9 {
            cur_v0 = cur_v0 + tmp_radix.clone() * v0[idx].expr();
            cur_v1 = cur_v1 + tmp_radix.clone() * v1[idx].expr();
            tmp_radix = tmp_radix * radix_constant_8.clone();
        }

        //use rangecheck to check v0,v1
        //we need v0,v1 in range[0,2^66)
        for idx in 0..9 {
            cb.range_lookup(v0[idx].expr(), 256);
            cb.range_lookup(v1[idx].expr(), 256);
        }

        //radix_constant_64 == 2^64
        //radix_constant_128 == 2^128
        let radix_constant = (1u64 << 32).expr()/*Expression::Constant(F::from_u128(1u64 << 32))*/;
        let radix_constant_64 = radix_constant.clone() * radix_constant;
        let radix_constant_128 =
            radix_constant_64.clone() * radix_constant_64.clone();
        cb.require_equal(
            "mul(multipliers_lo) == product_lo + radix_lo ⋅ 2^128",
            cur_v0.clone() * radix_constant_128.clone(),
            t0.expr() + t1.expr() * radix_constant_64.clone()
                - (c_digits[0].clone()
                    + c_digits[1].clone() * radix_constant_64.clone()),
        );
        cb.require_equal(
            "mul(multipliers_high) == product_high + radix_high ⋅ 2^128",
            cur_v1 * radix_constant_128,
            cur_v0 + t2.expr() + t3.expr() * radix_constant_64.clone()
                - (c_digits[2].clone()
                    + c_digits[3].clone() * radix_constant_64),
        );

        //Pop a and b from the stack, push c on the stack
        cb.stack_pop(a.expr());
        cb.stack_pop(b.expr());
        cb.stack_push(c.expr());

        // State transition
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
            a,
            b,
            c,
            t0,
            t1,
            t2,
            t3,
            v0,
            v1,
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

        //let opcode = step.opcode.unwrap();
        let indices =
            [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
        let [a, b, c] = indices.map(|idx| block.rws[idx].stack_value());
        self.assign_witness(region, offset, &a, &b)?;
        self.a.assign(region, offset, Some(a.to_le_bytes()))?;
        self.b.assign(region, offset, Some(b.to_le_bytes()))?;
        self.c.assign(region, offset, Some(c.to_le_bytes()))?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        test::{rand_word, run_test_circuit_incomplete_fixed_table},
        witness,
    };
    use bus_mapping::{bytecode, eth_types::Word, evm::OpcodeId};

    fn test_ok(opcode: OpcodeId, a: Word, b: Word) {
        let bytecode = bytecode! {
            PUSH32(a)
            PUSH32(b)
            #[start]
            .write_op(opcode)
            STOP
        };
        let block = witness::build_block_from_trace_code_at_start(&bytecode);
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    fn mul_gadget_simple() {
        test_ok(OpcodeId::MUL, 0x030201.into(), 0x060504.into());
    }

    #[test]
    fn mul_gadget_rand() {
        let a = rand_word();
        let b = rand_word();
        test_ok(OpcodeId::MUL, a, b);
    }
}

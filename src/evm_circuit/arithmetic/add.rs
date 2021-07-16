use crate::gadget::evm_word::{Word, WordConfig};

use halo2::{
    circuit::{Cell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
    poly::Rotation,
};

use pasta_curves::arithmetic::FieldExt;

#[derive(Clone, Debug)]
pub(crate) struct Config<F: FieldExt> {
    // Random field element used to compress a word.
    r: F,
    // Fixed column used to switch between opcodes that use 4 rows.
    q_group_4: Column<Fixed>,
    // Advice column witnessing the opcode index in group_4.
    op: Column<Advice>,
    // Advice column witnessing the global counter.
    global_counter: Column<Advice>,
    // Advice column witnessing the stack pointer.
    stack_pointer: Column<Advice>,
    // Advice columns witnessing the 32-byte representation of a 256-bit word.
    word_config: WordConfig<F>,
}

impl<F: FieldExt> Config<F> {
    pub(crate) fn configure(
        r: F,
        meta: &mut ConstraintSystem<F>,
        q_group_4: Column<Fixed>,
        op: Column<Advice>,
        global_counter: Column<Advice>,
        stack_pointer: Column<Advice>,
        bytes: [Column<Advice>; 32],
    ) -> Self {
        let rot_first_summand = Rotation(-4);
        let rot_second_summand = Rotation(-3);
        let rot_carry_bit = Rotation(-2);
        let rot_sum = Rotation(-1);
        let rot_op_switch = Rotation::cur();

        // FIXME: Integrate this code with bus mapping
        /*
        meta.create_gate("Counter checks", |meta| {
            // TODO: use is_zero to switch
            // This is fine for now since we only have ADD implemented in the codebase.
            let q_group_4 = meta.query_fixed(q_group_4, rot_op_switch);

            let one = Expression::Constant(F::one());

            // Global counter should increase consecutively
            let gc_checks = {
                // gc(first read) + 1 == gc(second read)
                let first_gc_check = {
                    let gc_first_summand = meta.query_advice(global_counter, rot_first_summand);
                    let gc_second_summand = meta.query_advice(global_counter, rot_second_summand);
                    gc_first_summand + one.clone() - gc_second_summand
                };

                // gc(second read) + 1 == gc(sum)
                let second_gc_check = {
                    let gc_second_summand = meta.query_advice(global_counter, rot_second_summand);
                    let gc_sum = meta.query_advice(global_counter, rot_sum);
                    gc_second_summand + one.clone() - gc_sum
                };

                array::IntoIter::new([
                    ("first_gc_check", first_gc_check),
                    ("second_gc_check", second_gc_check),
                ])
            };

            // Stack pointer should change as expected
            // (Read topmost two elements on stack; write to top element)
            let sp_checks = {
                // sp(first read) + 1 = sp(second read)
                let first_sp_check = {
                    let sp_first_summand = meta.query_advice(stack_pointer, rot_first_summand);
                    let sp_second_summand = meta.query_advice(stack_pointer, rot_second_summand);
                    sp_first_summand + one.clone() - sp_second_summand
                };

                // sp(second read) == sp(sum)
                let second_sp_check = {
                    let sp_second_summand = meta.query_advice(stack_pointer, rot_second_summand);
                    let sp_sum = meta.query_advice(stack_pointer, rot_sum);
                    sp_second_summand - sp_sum
                };

                array::IntoIter::new([
                    ("first_sp_check", first_sp_check),
                    ("second_sp_check", second_sp_check),
                ])
            };

            gc_checks
                .chain(sp_checks)
                .map(move |(name, poly)| (name, q_group_4.clone() * poly))
        });
        */

        // TODO: Lookup both reads in bus mapping
        // TODO: Lookup write in bus mapping

        meta.create_gate("Addition check", |meta| {
            // This is fine for now since we only have ADD implemented in the codebase.
            let q_group_4 = meta.query_fixed(q_group_4, rot_op_switch);

            let mut exprs = Vec::with_capacity(32);
            // i = 0
            // a_0 + b_0 = c_0 + carry[1] * 256
            {
                let first_summand = meta.query_advice(bytes[0], rot_first_summand);
                let second_summand = meta.query_advice(bytes[0], rot_second_summand);
                // carry_in = 0 always
                let carry_out = meta.query_advice(bytes[1], rot_carry_bit);
                let sum = meta.query_advice(bytes[0], rot_sum);

                let lhs = first_summand + second_summand;
                let rhs = sum + carry_out * F::from_u64(1 << 8);

                exprs.push(lhs - rhs);
            }

            // i = 1..=30
            // a_i + b_i + carry[i] = c_i + carry[i + 1] * 256
            for idx in 1..=30 {
                let first_summand = meta.query_advice(bytes[idx], rot_first_summand);
                let second_summand = meta.query_advice(bytes[idx], rot_second_summand);
                let carry_in = meta.query_advice(bytes[idx], rot_carry_bit);
                let carry_out = meta.query_advice(bytes[idx + 1], rot_carry_bit);
                let sum = meta.query_advice(bytes[idx], rot_sum);

                let lhs = first_summand + second_summand + carry_in;
                let rhs = sum + carry_out * F::from_u64(1 << 8);

                exprs.push(lhs - rhs);
            }

            // i = 31  // carry_out = carry[0]
            // a_31 + b_31 + carry[31] = c_31 + carry[0] * 256
            {
                let first_summand = meta.query_advice(bytes[31], rot_first_summand);
                let second_summand = meta.query_advice(bytes[31], rot_second_summand);
                let carry_in = meta.query_advice(bytes[31], rot_carry_bit);
                // Since the first carry-in is always zero, we use that cell to
                // witness the last carry-out.
                let carry_out = meta.query_advice(bytes[0], rot_carry_bit);
                let sum = meta.query_advice(bytes[31], rot_sum);

                let lhs = first_summand + second_summand + carry_in;
                let rhs = sum + carry_out * F::from_u64(1 << 8);

                exprs.push(lhs - rhs);
            }

            exprs.into_iter().map(move |expr| q_group_4.clone() * expr)
        });

        let q_compress = meta.selector();
        let byte_lookup = meta.fixed_column();
        let word_config = WordConfig::configure(meta, r, q_compress, bytes, byte_lookup);

        Self {
            r,
            q_group_4,
            op,
            global_counter,
            stack_pointer,
            word_config,
        }
    }

    // a + b = c
    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        a: [Option<u8>; 32],
        b: [Option<u8>; 32],
        c: [Option<u8>; 32],
        carry: [Option<bool>; 32],
    ) -> Result<(Word<F>, Word<F>, Word<F>), Error> {
        #[cfg(test)]
        for idx in 0..31 {
            let a = a[idx].unwrap_or(0);
            let b = b[idx].unwrap_or(0);
            let c = c[idx].unwrap_or(0);
            let carry_in = carry[idx].unwrap_or(false);
            let carry_out = carry[idx + 1].unwrap_or(false);

            assert_eq!(
                a as u16 + b as u16 + carry_in as u16,
                c as u16 + (1 << 8) * (carry_out as u16)
            );
        }

        let a = self.word_config.assign_word(region, offset, a)?;
        let offset = offset + 1;

        let b = self.word_config.assign_word(region, offset, b)?;
        let offset = offset + 1;

        let _carry: Result<Vec<Cell>, Error> = carry
            .iter()
            .enumerate()
            .map(|(idx, carry)| -> Result<Cell, Error> {
                region.assign_advice(
                    || format!("carry {}", idx),
                    self.word_config.bytes[idx],
                    offset,
                    || {
                        carry
                            .map(|carry| F::from_u64(carry as u64))
                            .ok_or(Error::SynthesisError)
                    },
                )
            })
            .collect();
        let offset = offset + 1;

        let c = self.word_config.assign_word(region, offset, c)?;
        let offset = offset + 1;

        region.assign_fixed(|| "q_group_4", self.q_group_4, offset, || Ok(F::one()))?;

        Ok((a, b, c))
    }
}

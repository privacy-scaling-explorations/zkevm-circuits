use crate::gadget::Variable;
use halo2::{
    // circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::array;

use pasta_curves::arithmetic::FieldExt;

// 32-byte representation of a 256-bit word in the circuit.
pub(crate) struct Word<F: FieldExt>([Variable<F, F>; 32]);

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
    bytes: [Column<Advice>; 32],
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
        let rot_first_read = Rotation(-4);
        let rot_second_read = Rotation(-3);
        let _rot_carry_bit = Rotation(-2);
        let rot_write = Rotation(-1);
        let rot_op_switch = Rotation::cur();

        meta.create_gate("Counter checks", |meta| {
            // TODO: use is_zero to switch
            // This is fine for now since we only have ADD implemented in the codebase.
            let q_group_4 = meta.query_fixed(q_group_4, rot_op_switch);

            let one = Expression::Constant(F::one());

            // Global counter should increase consecutively
            let gc_checks = {
                // gc(first read) + 1 == gc(second read)
                let first_gc_check = {
                    let gc_first_read = meta.query_advice(global_counter, rot_first_read);
                    let gc_second_read = meta.query_advice(global_counter, rot_second_read);
                    gc_first_read + one.clone() - gc_second_read
                };

                // gc(second read) + 1 == gc(write)
                let second_gc_check = {
                    let gc_second_read = meta.query_advice(global_counter, rot_second_read);
                    let gc_write = meta.query_advice(global_counter, rot_write);
                    gc_second_read + one.clone() - gc_write
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
                    let sp_first_read = meta.query_advice(stack_pointer, rot_first_read);
                    let sp_second_read = meta.query_advice(stack_pointer, rot_second_read);
                    sp_first_read + one.clone() - sp_second_read
                };

                // sp(second read) == sp(write)
                let second_sp_check = {
                    let sp_second_read = meta.query_advice(stack_pointer, rot_second_read);
                    let sp_write = meta.query_advice(stack_pointer, rot_write);
                    sp_second_read - sp_write
                };

                array::IntoIter::new([
                    ("first_sp_check", first_sp_check),
                    ("second_sp_check", second_sp_check),
                ])
            };

            // TODO: Lookup both reads in bus mapping
            // TODO: Lookup write in bus mapping
            // TODO: Lookup addition for first byte
            // TODO: Lookup addition for last byte
            // TODO: Lookup addition for bytes[1..=30]

            gc_checks
                .chain(sp_checks)
                .map(move |(name, poly)| (name, q_group_4.clone() * poly))
        });

        Self {
            r,
            q_group_4,
            op,
            global_counter,
            stack_pointer,
            bytes,
        }
    }

    /// Returns an expression representing the compressed form of a 256-bit word.
    fn compress(&self, meta: &mut VirtualCells<'_, F>) -> Expression<F> {
        let mut expr = meta.query_advice(self.bytes[0], Rotation::cur());
        let mut r_factor = self.r;
        for idx in 1..32 {
            expr = expr + meta.query_advice(self.bytes[idx], Rotation::cur()) * r_factor;
            r_factor *= self.r;
        }
        expr
    }
}

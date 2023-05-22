use std::cell::RefCell;

use bus_mapping::state_db::EMPTY_CODE_HASH_LE;
use chiquito::{
    ast::{ToExpr, ToField},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::TwoStepsSelectorBuilder, Compiler,
    },
    dsl::circuit,
    ir::Circuit,
    stdlib::IsZero,
};
use eth_types::Field;
use halo2_proofs::plonk::{Column, Fixed};

use crate::bytecode_circuit::bytecode_unroller::unroll;

use super::{
    circuit::{BytecodeCircuitConfigArgs, WitnessInput},
    wit_gen::BytecodeWitnessGen,
};

pub fn bytecode_circuit<F: Field + From<u64>>(
    BytecodeCircuitConfigArgs {
        bytecode_table,
        keccak_table,
        challenges,
    }: &BytecodeCircuitConfigArgs<F>,
    push_data_table_value: Column<Fixed>,
    push_data_table_size: Column<Fixed>,
) -> Circuit<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>> {
    let bytecode_circuit = circuit::<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>, _>(
        "bytecode circuit",
        |ctx| {
            use chiquito::dsl::cb::*;

            let length = ctx.forward("length");
            let push_data_left = ctx.forward("push_data_left");
            let value_rlc = ctx.forward_with_phase("value_rlc", 1); // 1 -> SecondPhase

            let index = ctx.import_halo2_advice("index", bytecode_table.index);
            let hash = ctx.import_halo2_advice("hash", bytecode_table.code_hash);
            let is_code = ctx.import_halo2_advice("is_code", bytecode_table.is_code);
            let value = ctx.import_halo2_advice("value", bytecode_table.value);
            let _tag = ctx.import_halo2_advice("tag", bytecode_table.tag); // imported for step selector

            let push_data_table_value =
                ctx.import_halo2_fixed("push_data_value", push_data_table_value);
            let push_data_table_size =
                ctx.import_halo2_fixed("push_data_size", push_data_table_size);

            let keccak_is_enabled =
                ctx.import_halo2_advice("keccak_is_enabled", keccak_table.is_enabled);
            let keccak_value_rlc =
                ctx.import_halo2_advice("keccak_value_rlc", keccak_table.input_rlc);
            let keccak_length = ctx.import_halo2_advice("keccak_length", keccak_table.input_len);
            let keccak_hash = ctx.import_halo2_advice("keccak_hash", keccak_table.output_rlc);

            let header = ctx.step_type("header");
            let byte_step = ctx.step_type("byte");

            ctx.pragma_first_step(header);
            ctx.pragma_last_step(header);

            ctx.step_type_def(header, move |ctx| {
                ctx.constr(isz(index));
                ctx.constr(eq(value, length));

                ctx.transition(if_next_step(header, isz(length)));

                let empty_hash = rlc(
                    &EMPTY_CODE_HASH_LE.map(|v| (v as u64).expr()),
                    challenges.evm_word(),
                );

                ctx.transition(if_next_step(header, eq(hash, empty_hash)));

                ctx.transition(if_next_step(byte_step, eq(length, length.next())));
                ctx.transition(if_next_step(byte_step, isz(index.next())));
                ctx.transition(if_next_step(byte_step, eq(is_code.next(), 1)));
                ctx.transition(if_next_step(byte_step, eq(hash, hash.next())));
                ctx.transition(if_next_step(byte_step, eq(value_rlc.next(), value.next())));

                ctx.wg(move |ctx, wit| {
                    let wit = wit.borrow();

                    ctx.assign(index, 0.field());
                    ctx.assign(length, wit.length.field());
                    ctx.assign(value, wit.length.field());
                    ctx.assign(is_code, 0.field());
                    ctx.assign(value_rlc, 0.field());

                    wit.code_hash.map(|v| ctx.assign(hash, v));
                })
            });

            ctx.step_type_def(byte_step, move |ctx| {
                let push_data_size = ctx.internal("push_data_size");
                let push_data_left_inv = ctx.internal("push_data_left_inv");
                let index_length_diff_inv = ctx.internal("index_length_diff_inv");

                let push_data_left_is_zero = IsZero::setup(ctx, push_data_left, push_data_left_inv);

                let index_length_diff_is_zero =
                    IsZero::<F>::setup(ctx, index + 1 - length, index_length_diff_inv);

                ctx.constr(eq(is_code, push_data_left_is_zero.is_zero()));

                ctx.add_lookup(
                    lookup()
                        .add(value, push_data_table_value)
                        .add(push_data_size, push_data_table_size),
                );

                ctx.transition(if_next_step(byte_step, eq(length, length.next())));
                ctx.transition(if_next_step(byte_step, eq(index + 1, index.next())));
                ctx.transition(if_next_step(byte_step, eq(hash, hash.next())));
                ctx.transition(if_next_step(
                    byte_step,
                    eq(
                        value_rlc.next(),
                        (value_rlc * challenges.keccak_input()) + value.next(),
                    ),
                ));
                ctx.transition(if_next_step(
                    byte_step,
                    eq(
                        push_data_left.next(),
                        select(is_code, push_data_size, push_data_left - 1),
                    ),
                ));

                ctx.transition(if_next_step(header, eq(index + 1, length)));

                ctx.transition(when(
                    index_length_diff_is_zero.is_zero(),
                    next_step_must_be(header),
                ));

                ctx.add_lookup(
                    lookup()
                        .add(1, keccak_is_enabled)
                        .add(value_rlc, keccak_value_rlc)
                        .add(length, keccak_length)
                        .add(hash, keccak_hash)
                        .enable(header.next()),
                );

                ctx.wg(move |ctx, wit| {
                    let wit = wit.borrow();

                    ctx.assign(index, wit.index());
                    ctx.assign(length, wit.length.field());
                    ctx.assign(value, wit.value());
                    ctx.assign(is_code, wit.is_code());

                    wit.value_rlc.map(|v| ctx.assign(value_rlc, v));
                    wit.code_hash.map(|v| ctx.assign(hash, v));

                    ctx.assign(push_data_size, wit.push_data_size.field());
                    ctx.assign(push_data_left, wit.push_data_left.field());
                    push_data_left_is_zero.wg(ctx, wit.push_data_left.field());
                    index_length_diff_is_zero.wg(
                        ctx,
                        wit.index() + <i32 as chiquito::ast::ToField<F>>::field(&1)
                            - <usize as chiquito::ast::ToField<F>>::field(&wit.length),
                    );
                });
            });

            ctx.trace(
                move |ctx, (bytecodes, challenges, last_row_offset, overwrite_len)| {
                    ctx.set_height(last_row_offset + 1);

                    let mut offset = 0;
                    for bytecode in bytecodes.iter() {
                        let wit = if overwrite_len == 0 {
                            RefCell::new(BytecodeWitnessGen::new(bytecode, &challenges))
                        } else {
                            RefCell::new(BytecodeWitnessGen::new_overwrite_len(
                                bytecode,
                                &challenges,
                                overwrite_len,
                            ))
                        };

                        println!("start wit gen");

                        if offset < last_row_offset - 1 {
                            ctx.add(&header, wit.clone());
                            offset += 1;
                        }

                        while wit.borrow_mut().has_more() && offset < last_row_offset - 1 {
                            wit.borrow_mut().next_row();
                            ctx.add(&byte_step, wit.clone());
                            offset += 1;
                        }
                    }

                    // padding
                    let wit = RefCell::new(BytecodeWitnessGen::new(&unroll(vec![]), &challenges));

                    while offset <= last_row_offset {
                        ctx.add(&header, wit.clone());
                        offset += 1;
                    }
                },
            )
        },
    );

    let compiler = Compiler::new(
        SingleRowCellManager::default(),
        TwoStepsSelectorBuilder {
            halo2_column: Some(bytecode_table.tag),
            hint_one: Some("byte".to_string()),
        },
    );

    compiler.compile(&bytecode_circuit)
}

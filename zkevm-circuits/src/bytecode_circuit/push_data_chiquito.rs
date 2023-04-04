use chiquito::{
    ast::ToField,
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Circuit,
        Compiler,
    },
    dsl::circuit,
};
use eth_types::Field;
use halo2_proofs::plonk::{Column, Fixed};

use crate::util::get_push_size;

pub fn push_data_table_circuit<F: Field>(
    push_data_value: Column<Fixed>,
    push_data_size: Column<Fixed>,
) -> Circuit<F, (), ()> {
    let mut push_data_table_circuit = circuit::<F, (), (), _>("push_table", |ctx| {
        let push_data_value = ctx.import_halo2_fixed("push_data_value", push_data_value);
        let push_data_size = ctx.import_halo2_fixed("push_data_size", push_data_size);

        ctx.fixed_gen(move |ctx| {
            for byte in 0usize..256 {
                let push_size = get_push_size(byte as u8);
                ctx.assign(byte, push_data_value, byte.field());
                ctx.assign(byte, push_data_size, push_size.field());
            }
        });
    });

    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    compiler.compile(&mut push_data_table_circuit)
}

use super::helpers::Indexable;
use crate::circuit_tools::constraint_builder::{RLCable, RLCableValue};
use crate::{
    assign, circuit,
    mpt_circuit::helpers::{key_memory, parent_memory, KeyData, MPTConstraintBuilder, ParentData},
    mpt_circuit::{witness_row::MptWitnessRow, MPTContext},
    mpt_circuit::{MPTConfig, ProofValues},
};
use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct StartConfig<F> {
    key_data: [KeyData<F>; 2],
    parent_data: [ParentData<F>; 2],
}

impl<F: Field> StartConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let r = ctx.r.clone();

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = StartConfig::default();

        circuit!([meta, cb.base], {
            let root_bytes = [
                ctx.expr(meta, 0)[..32].to_owned(),
                ctx.expr(meta, 0)[34..66].to_owned(),
            ];

            for is_s in [true, false] {
                let root_test = a!(ctx.inter_root(is_s));
                let root = root_bytes[is_s.idx()].rlc(&r);
                require!(root => root_test);
                ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [root.expr(), true.expr(), false.expr(), root.expr()],
                );
                KeyData::store(
                    &mut cb.base,
                    &ctx.memory[key_memory(is_s)],
                    KeyData::default_values_expr(),
                );
            }
        });

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        ctx: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        pv: &mut ProofValues<F>,
        offset: usize,
        idx: usize,
    ) -> Result<(), Error> {
        let row = &witness[idx];

        let root_bytes = [row.s_root_bytes().to_owned(), row.c_root_bytes().to_owned()];

        let columns = [ctx.s_main.bytes.to_owned(), ctx.c_main.bytes.to_owned()];

        for is_s in [true, false] {
            for (byte, column) in root_bytes[is_s.idx()].iter().zip(columns[is_s.idx()]) {
                assign!(region, (column, offset) => byte.scalar())?;
            }

            let root = root_bytes[is_s.idx()].rlc_value(ctx.r);
            pv.memory[parent_memory(is_s)]
                .witness_store(offset, &[root, true.scalar(), false.scalar(), root]);

            pv.memory[key_memory(is_s)].witness_store(offset, &KeyData::default_values());
        }

        Ok(())
    }
}

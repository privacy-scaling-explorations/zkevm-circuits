use super::helpers::Indexable;
use super::witness_row::{Node, StartRowType};
use crate::circuit_tools::cell_manager::Cell;
use crate::circuit_tools::constraint_builder::{RLCable, RLCableValue};
use crate::mpt_circuit::helpers::{main_memory, MainData};
use crate::{
    circuit,
    mpt_circuit::helpers::{key_memory, parent_memory, KeyData, MPTConstraintBuilder, ParentData},
    mpt_circuit::MPTContext,
    mpt_circuit::{MPTConfig, MPTState},
};
use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, VirtualCells},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct StartConfig<F> {
    proof_type: Cell<F>,
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
                ctx.s(meta, StartRowType::RootS as i32),
                ctx.s(meta, StartRowType::RootC as i32),
            ];

            config.proof_type = cb.base.query_cell();

            let mut root = vec![0.expr(); 2];
            for is_s in [true, false] {
                root[is_s.idx()] = root_bytes[is_s.idx()].rlc(&r);
            }

            MainData::store(
                &mut cb.base,
                &ctx.memory[main_memory()],
                [
                    config.proof_type.expr(),
                    false.expr(),
                    0.expr(),
                    root[true.idx()].expr(),
                    root[false.idx()].expr(),
                ],
            );

            for is_s in [true, false] {
                ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [
                        root[is_s.idx()].expr(),
                        true.expr(),
                        false.expr(),
                        root[is_s.idx()].expr(),
                    ],
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
        pv: &mut MPTState<F>,
        offset: usize,
        node: &Node,
    ) -> Result<(), Error> {
        let start = &node.start.clone().unwrap();

        let root_bytes = [
            node.values[StartRowType::RootS as usize].clone(),
            node.values[StartRowType::RootC as usize].clone(),
        ];

        self.proof_type
            .assign(region, offset, start.proof_type.scalar())?;

        let mut root = vec![0.scalar(); 2];
        for is_s in [true, false] {
            root[is_s.idx()] = root_bytes[is_s.idx()].rlc_value(ctx.r);
        }

        MainData::witness_store(
            region,
            offset,
            &mut pv.memory[main_memory()],
            start.proof_type as usize,
            false,
            0.scalar(),
            root[true.idx()],
            root[false.idx()],
        )?;

        for is_s in [true, false] {
            ParentData::witness_store(
                region,
                offset,
                &mut pv.memory[parent_memory(is_s)],
                root[is_s.idx()],
                true,
                false,
                root[is_s.idx()],
            )?;
            KeyData::witness_store(
                region,
                offset,
                &mut pv.memory[key_memory(is_s)],
                F::zero(),
                F::one(),
                0,
                false,
                F::zero(),
                F::one(),
            )?;
        }

        Ok(())
    }
}

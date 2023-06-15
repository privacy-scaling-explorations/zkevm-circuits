use super::{
    helpers::Indexable,
    rlp_gadgets::RLPItemWitness,
    witness_row::{Node, StartRowType},
};
use crate::{
    circuit,
    circuit_tools::{
        cached_region::{CachedRegion, ChallengeSet},
        cell_manager::Cell,
    },
    mpt_circuit::{
        helpers::{
            key_memory, main_memory, parent_memory, KeyData, MPTConstraintBuilder, MainData,
            ParentData,
        },
        MPTConfig, MPTContext, MPTState,
    },
};
use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::plonk::{Error, VirtualCells};

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
        cb.base
            .cell_manager
            .as_mut()
            .unwrap()
            .reset(StartRowType::Count as usize);
        let mut config = StartConfig::default();

        circuit!([meta, cb], {
            let root_items = [
                ctx.rlp_item(meta, cb, StartRowType::RootS as usize, true),
                ctx.rlp_item(meta, cb, StartRowType::RootC as usize, true),
            ];

            config.proof_type = cb.query_cell();

            let mut root = vec![0.expr(); 2];
            for is_s in [true, false] {
                root[is_s.idx()] = root_items[is_s.idx()].rlc_content();
            }

            MainData::store(
                cb,
                &ctx.memory[main_memory()],
                [
                    config.proof_type.expr(),
                    false.expr(),
                    false.expr(),
                    0.expr(),
                    root[true.idx()].expr(),
                    root[false.idx()].expr(),
                ],
            );

            for is_s in [true, false] {
                ParentData::store(
                    cb,
                    &ctx.memory[parent_memory(is_s)],
                    root[is_s.idx()].expr(),
                    true.expr(),
                    false.expr(),
                    root[is_s.idx()].expr(),
                );
                KeyData::store_defaults(cb, &ctx.memory[key_memory(is_s)]);
            }
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        _challenges: &S,
        _mpt_config: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let start = &node.start.clone().unwrap();

        let _root_items = [
            rlp_values[StartRowType::RootS as usize].clone(),
            rlp_values[StartRowType::RootC as usize].clone(),
        ];

        self.proof_type
            .assign(region, offset, start.proof_type.scalar())?;

        let mut root = vec![0.scalar(); 2];
        for is_s in [true, false] {
            root[is_s.idx()] = rlp_values[is_s.idx()].rlc_content(pv.r);
            // println!("root {}: {:?}", is_s, root[is_s.idx()]);
        }

        MainData::witness_store(
            region,
            offset,
            &mut pv.memory[main_memory()],
            start.proof_type as usize,
            false,
            false.scalar(),
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
                F::ZERO,
                F::ONE,
                0,
                F::ZERO,
                F::ONE,
                0,
            )?;
        }

        Ok(())
    }
}

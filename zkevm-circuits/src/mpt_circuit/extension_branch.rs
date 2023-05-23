use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    plonk::{Error, VirtualCells},
};

use super::{
    branch::BranchGadget,
    extension::ExtensionGadget,
    helpers::{MPTConstraintBuilder, ParentDataWitness},
    rlp_gadgets::RLPItemWitness,
    witness_row::Node,
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{cell_manager::{Cell, EvmCellType}, cached_region::{CachedRegion, ChallengeSet}},
    mpt_circuit::{
        helpers::{key_memory, parent_memory, Indexable, KeyData, ParentData},
        witness_row::ExtensionBranchRowType,
        MPTConfig, MPTState,
    },
};

#[derive(Clone, Debug, Default)]
pub(crate) struct ExtensionBranchConfig<F> {
    key_data: KeyData<F>,
    parent_data: [ParentData<F>; 2],
    is_placeholder: [Cell<F>; 2],
    is_extension: Cell<F>,
    extension: ExtensionGadget<F>,
    branch: BranchGadget<F>,
}

impl<F: Field> ExtensionBranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        cb.base
            .cell_manager
            .as_mut()
            .unwrap()
            .reset(meta, ExtensionBranchRowType::Count as usize);
        let mut config = ExtensionBranchConfig::default();

        circuit!([meta, cb], {
            // General inputs
            config.is_extension = cb.query_bool();
            // If we're in a placeholder, both the extension and the branch parts are
            // placeholders
            for is_s in [true, false] {
                config.is_placeholder[is_s.idx()] = cb.query_bool();
            }
            // Don't allow both branches to be placeholders
            require!(config.is_placeholder[true.idx()].expr() + config.is_placeholder[false.idx()].expr() => bool);

            // Load the last key values
            config.key_data = KeyData::load(cb, &ctx.memory[key_memory(true)], 0.expr());
            // Load the parent values
            for is_s in [true, false] {
                config.parent_data[is_s.idx()] = ParentData::load(
                    "branch load",
                    cb,
                    &ctx.memory[parent_memory(is_s)],
                    0.expr(),
                );
                // A branch cannot follow a placeholder branch
                require!(config.parent_data[is_s.idx()].is_placeholder => false);
            }

            // Extension
            let (
                num_nibbles,
                is_key_odd,
                key_rlc_post_ext,
                key_mult_post_ext,
                is_root_s,
                is_root_c,
                parent_rlc_s,
                parent_rlc_c,
            ) = ifx! {config.is_extension => {
                config.extension = ExtensionGadget::configure(
                    meta,
                    cb,
                    ctx.clone(),
                    &config.key_data,
                    &config.parent_data,
                    &config.is_placeholder,
                );
                let ext = config.extension.get_post_state();
                (
                    ext.num_nibbles,
                    ext.is_key_odd,
                    ext.key_rlc,
                    ext.key_mult,
                    false.expr(),
                    false.expr(),
                    ext.branch_rlp_rlc[true.idx()].expr(),
                    ext.branch_rlp_rlc[false.idx()].expr(),
                )
            } elsex {
                (
                    config.key_data.num_nibbles.expr(),
                    config.key_data.is_odd.expr(),
                    config.key_data.rlc.expr(),
                    config.key_data.mult.expr(),
                    config.parent_data[true.idx()].is_root.expr(),
                    config.parent_data[false.idx()].is_root.expr(),
                    config.parent_data[true.idx()].rlc.expr(),
                    config.parent_data[false.idx()].rlc.expr(),
                )
            }};
            let parent_rlc = [parent_rlc_s, parent_rlc_c];
            let is_root = [is_root_s, is_root_c];

            // Branch
            config.branch = BranchGadget::configure(
                meta,
                cb,
                ctx.clone(),
                &config.is_placeholder,
                &parent_rlc,
                &is_root,
                key_rlc_post_ext.expr(),
                key_mult_post_ext.expr(),
                num_nibbles.expr(),
                is_key_odd.expr(),
            );
            let branch = config.branch.get_post_state();

            // Set the new keys
            for is_s in [true, false] {
                ifx! {not!(config.is_placeholder[is_s.idx()].expr()) => {
                    KeyData::store(
                        cb,
                        &ctx.memory[key_memory(is_s)],
                        branch.key_rlc_post_branch.expr(),
                        branch.key_mult_post_branch.expr(),
                        branch.num_nibbles.expr(),
                        branch.is_key_odd.expr(),
                        0.expr(),
                        0.expr(),
                        0.expr(),
                        false.expr(),
                    );
                    ParentData::store(
                        cb,
                        &ctx.memory[parent_memory(is_s)],
                        branch.mod_rlc[is_s.idx()].expr(),
                        false.expr(),
                        false.expr(),
                        0.expr(),
                    );
                 } elsex {
                    KeyData::store(
                        cb,
                        &ctx.memory[key_memory(is_s)],
                        config.key_data.rlc.expr(),
                        config.key_data.mult.expr(),
                        config.key_data.num_nibbles.expr(),
                        config.key_data.is_odd.expr(),
                        branch.key_rlc_post_drifted.expr(),
                        branch.key_mult_post_drifted.expr(),
                        branch.num_nibbles.expr(),
                        branch.is_key_odd.expr(),
                    );
                    ParentData::store(
                        cb,
                        &ctx.memory[parent_memory(is_s)],
                        config.parent_data[is_s.idx()].rlc.expr(),
                        config.parent_data[is_s.idx()].is_root.expr(),
                        true.expr(),
                        branch.mod_rlc[is_s.idx()].expr(),
                    );
                }}
            }
        });

        config
    }

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        mpt_config: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let extension_branch = &node.extension_branch.clone().unwrap();

        self.is_extension
            .assign(region, offset, extension_branch.is_extension.scalar())?;

        let key_data =
            self.key_data
                .witness_load(region, offset, &pv.memory[key_memory(true)], 0)?;
        let mut parent_data = vec![ParentDataWitness::default(); 2];
        for is_s in [true, false] {
            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut pv.memory[parent_memory(is_s)],
                0,
            )?;
            self.is_placeholder[is_s.idx()].assign(
                region,
                offset,
                extension_branch.is_placeholder[is_s.idx()].scalar(),
            )?;
        }

        let mut key_rlc = key_data.rlc;
        let mut key_mult = key_data.mult;
        let mut num_nibbles = key_data.num_nibbles;
        let mut is_key_odd = key_data.is_odd;

        // Extension
        if extension_branch.is_extension {
            self.extension.assign(
                region,
                mpt_config,
                pv,
                offset,
                &key_data,
                &mut key_rlc,
                &mut key_mult,
                &mut num_nibbles,
                &mut is_key_odd,
                node,
                rlp_values,
            )?;
        }

        // Branch
        let (key_rlc_post_branch, key_rlc_post_drifted, key_mult_post_branch, mod_node_hash_rlc) =
            self.branch.assign(
                region,
                mpt_config,
                pv,
                offset,
                &extension_branch.is_placeholder,
                &mut key_rlc,
                &mut key_mult,
                &mut num_nibbles,
                &mut is_key_odd,
                node,
                rlp_values,
            )?;

        // Set the new parent and key
        for is_s in [true, false] {
            if !extension_branch.is_placeholder[is_s.idx()] {
                KeyData::witness_store(
                    region,
                    offset,
                    &mut pv.memory[key_memory(is_s)],
                    key_rlc_post_branch,
                    key_mult_post_branch,
                    num_nibbles,
                    0.scalar(),
                    0.scalar(),
                    0,
                )?;
                ParentData::witness_store(
                    region,
                    offset,
                    &mut pv.memory[parent_memory(is_s)],
                    mod_node_hash_rlc[is_s.idx()],
                    false,
                    false,
                    0.scalar(),
                )?;
            } else {
                KeyData::witness_store(
                    region,
                    offset,
                    &mut pv.memory[key_memory(is_s)],
                    key_data.rlc,
                    key_data.mult,
                    key_data.num_nibbles,
                    key_rlc_post_drifted,
                    key_mult_post_branch,
                    num_nibbles,
                )?;
                ParentData::witness_store(
                    region,
                    offset,
                    &mut pv.memory[parent_memory(is_s)],
                    parent_data[is_s.idx()].rlc,
                    parent_data[is_s.idx()].is_root,
                    true,
                    mod_node_hash_rlc[is_s.idx()],
                )?;
            }
        }

        Ok(())
    }
}

use eth_types::{Field, OpsIdentity};
use gadgets::util::Scalar;
use halo2_proofs::plonk::{Error, Expression, VirtualCells};

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
    circuit_tools::{cached_region::CachedRegion, cell_manager::Cell},
    mpt_circuit::{
        helpers::{key_memory, parent_memory, Indexable, KeyData, ParentData},
        MPTConfig, MptMemory,
    },
    util::word::WordLoHi,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct ExtensionBranchConfig<F> {
    key_data: KeyData<F>,
    parent_data: [ParentData<F>; 2],
    is_placeholder: [Cell<F>; 2],
    is_extension: Cell<F>,
    is_last_level_and_wrong_ext_case: Cell<F>,
    extension: ExtensionGadget<F>,
    branch: BranchGadget<F>,
}

impl<F: Field> ExtensionBranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: &mut MPTContext<F>,
    ) -> Self {
        let mut config = ExtensionBranchConfig::default();

        circuit!([meta, cb], {
            // General inputs
            config.is_extension = cb.query_bool();
            config.is_last_level_and_wrong_ext_case = cb.query_bool();
            // If we're in a placeholder, both the extension and the branch parts are
            // placeholders
            for is_s in [true, false] {
                config.is_placeholder[is_s.idx()] = cb.query_bool();
            }
            // Don't allow both branches to be placeholders
            require!(config.is_placeholder[true.idx()].expr() + config.is_placeholder[false.idx()].expr() => bool);

            // Load the last key values
            config.key_data = KeyData::load(cb, &mut ctx.memory[key_memory(true)], 0.expr());
            // Load the parent values
            for is_s in [true, false] {
                config.parent_data[is_s.idx()] =
                    ParentData::load(cb, &mut ctx.memory[parent_memory(is_s)], 0.expr());
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
                parent_word_s_lo,
                parent_word_s_hi,
                parent_word_c_lo,
                parent_word_c_hi,
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
                    ext.branch_rlp_word[true.idx()].lo(),
                    ext.branch_rlp_word[true.idx()].hi(),
                    ext.branch_rlp_word[false.idx()].lo(),
                    ext.branch_rlp_word[false.idx()].hi(),
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
                    config.parent_data[true.idx()].hash.lo().expr(),
                    config.parent_data[true.idx()].hash.hi().expr(),
                    config.parent_data[false.idx()].hash.lo().expr(),
                    config.parent_data[false.idx()].hash.hi().expr(),
                    config.parent_data[true.idx()].rlc.expr(),
                    config.parent_data[false.idx()].rlc.expr(),
                )
            }};
            let parent_word = [
                WordLoHi::<Expression<F>>::new([parent_word_s_lo, parent_word_s_hi]),
                WordLoHi::<Expression<F>>::new([parent_word_c_lo, parent_word_c_hi]),
            ];
            let parent_rlc = [parent_rlc_s, parent_rlc_c];
            let is_root = [is_root_s, is_root_c];

            // Branch
            config.branch = BranchGadget::configure(
                meta,
                cb,
                ctx.clone(),
                &config.is_placeholder,
                &parent_word,
                &parent_rlc,
                &is_root,
                key_rlc_post_ext.expr(),
                key_mult_post_ext.expr(),
                num_nibbles.expr(),
                is_key_odd.expr(),
                config.is_last_level_and_wrong_ext_case.expr(),
            );
            let branch = config.branch.get_post_state();

            // Set the new keys
            for is_s in [true, false] {
                // The extension_branch in the last level needs to have `is_ext_last_level = true`
                // (checked in account_leaf.rs / storage_leaf.rs).
                // All other extension_branches need to have it `false`:
                require!(config.parent_data[is_s.idx()].is_last_level_and_wrong_ext_case.expr() => false.expr());

                ifx! {not!(config.is_placeholder[is_s.idx()].expr()) => {
                    KeyData::store(
                        cb,
                        &mut ctx.memory[key_memory(is_s)],
                        branch.key_rlc_post_branch.expr(),
                        branch.key_mult_post_branch.expr(),
                        branch.num_nibbles.expr(),
                        branch.is_key_odd.expr(),
                        branch.key_rlc_post_drifted.expr(),
                        0.expr(),
                        0.expr(),
                        false.expr(),
                    );
                    ParentData::store(
                        cb,
                        &mut ctx.memory[parent_memory(is_s)],
                        branch.mod_word[is_s.idx()].clone(),
                        branch.mod_rlc[is_s.idx()].expr(),
                        false.expr(),
                        false.expr(),
                        config.is_extension.expr(),
                        config.is_last_level_and_wrong_ext_case.expr(),
                        WordLoHi::zero(),
                    );
                 } elsex {
                    // For the placeholder branch / extension node the values did not change, we reuse
                    // the previous values. These values are used in the leaf after the placeholder branch
                    // - this way we can use `KeyData` and `ParentData` in the leaf as in the cases of
                    // the leaf after the non-placeholder branch.
                    KeyData::store(
                        cb,
                        &mut ctx.memory[key_memory(is_s)],
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
                        &mut ctx.memory[parent_memory(is_s)],
                        config.parent_data[is_s.idx()].hash.expr(),
                        config.parent_data[is_s.idx()].rlc.expr(),
                        config.parent_data[is_s.idx()].is_root.expr(),
                        true.expr(),
                        config.is_extension.expr(),
                        config.is_last_level_and_wrong_ext_case.expr(),
                        branch.mod_word[is_s.idx()].clone(),
                    );
                }}
            }
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        mpt_config: &MPTConfig<F>,
        memory: &mut MptMemory<F>,
        offset: usize,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let extension_branch = &node.extension_branch.clone().unwrap();

        let is_extension = extension_branch.is_extension.scalar();
        self.is_extension.assign(region, offset, is_extension)?;

        let is_last_level_and_wrong_ext_case =
            extension_branch.is_last_level_and_wrong_ext_case.scalar();
        self.is_last_level_and_wrong_ext_case.assign(
            region,
            offset,
            is_last_level_and_wrong_ext_case,
        )?;

        let key_data =
            self.key_data
                .witness_load(region, offset, &mut memory[key_memory(true)], 0)?;
        let mut parent_data = vec![ParentDataWitness::default(); 2];
        for is_s in [true, false] {
            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut memory[parent_memory(is_s)],
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
                memory,
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
        let (
            key_rlc_post_branch,
            key_rlc_post_drifted,
            key_mult_post_branch,
            mod_node_hash_word,
            mod_node_hash_rlc,
        ) = self.branch.assign(
            region,
            mpt_config,
            memory,
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
                    &mut memory[key_memory(is_s)],
                    key_rlc_post_branch,
                    key_mult_post_branch,
                    num_nibbles,
                    key_rlc_post_drifted,
                    0.scalar(),
                    0,
                )?;
                ParentData::witness_store(
                    region,
                    offset,
                    &mut memory[parent_memory(is_s)],
                    mod_node_hash_word[is_s.idx()],
                    mod_node_hash_rlc[is_s.idx()],
                    false,
                    false,
                    is_extension == 1.into(),
                    is_last_level_and_wrong_ext_case == 1.into(),
                    WordLoHi::zero(),
                )?;
            } else {
                KeyData::witness_store(
                    region,
                    offset,
                    &mut memory[key_memory(is_s)],
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
                    &mut memory[parent_memory(is_s)],
                    parent_data[is_s.idx()].hash,
                    parent_data[is_s.idx()].rlc,
                    parent_data[is_s.idx()].is_root,
                    true,
                    is_extension == 1.into(),
                    is_last_level_and_wrong_ext_case == 1.into(),
                    mod_node_hash_word[is_s.idx()],
                )?;
            }
        }

        Ok(())
    }
}

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, VirtualCells},
};

use super::{
    branch::BranchGadget,
    extension::ExtensionGadget,
    helpers::{MPTConstraintBuilder, ParentDataWitness},
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::cell_manager::Cell,
    mpt_circuit::helpers::{key_memory, parent_memory, Indexable, KeyData, ParentData},
    mpt_circuit::param::{ARITY, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS},
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{MPTConfig, MPTState},
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
        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = ExtensionBranchConfig::default();

        circuit!([meta, cb.base], {
            // General inputs
            config.is_extension = cb.base.query_bool();
            // If we're in a placeholder, both the extension and the branch parts are
            // placeholders
            for is_s in [true, false] {
                config.is_placeholder[is_s.idx()] = cb.base.query_bool();
            }
            // Don't allow both branches to be placeholders
            require!(config.is_placeholder[true.idx()].expr() + config.is_placeholder[false.idx()].expr() => bool);

            // Load the last key values
            config.key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(true)], 0.expr());
            // Load the parent values
            for is_s in [true, false] {
                config.parent_data[is_s.idx()] = ParentData::load(
                    "branch load",
                    &mut cb.base,
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
                config.is_extension.expr(),
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
                        &mut cb.base,
                        &ctx.memory[key_memory(is_s)],
                        [
                            branch.key_rlc_post_branch.expr(),
                            branch.key_mult_post_branch.expr(),
                            branch.num_nibbles.expr(),
                            branch.is_key_odd.expr(),
                            false.expr(),
                            0.expr(),
                            0.expr(),
                        ],
                    );
                    ParentData::store(
                        &mut cb.base,
                        &ctx.memory[parent_memory(is_s)],
                        [branch.mod_rlc[is_s.idx()].expr(), false.expr(), false.expr(), 0.expr()]
                    );
                 } elsex {
                    KeyData::store(
                        &mut cb.base,
                        &ctx.memory[key_memory(is_s)],
                        [
                            config.key_data.rlc.expr(),
                            config.key_data.mult.expr(),
                            config.key_data.num_nibbles.expr(),
                            config.key_data.is_odd.expr(),
                            branch.is_key_odd.expr(),
                            branch.key_rlc_post_drifted.expr(),
                            branch.key_mult_post_drifted.expr(),
                        ],
                    );
                    ParentData::store(
                        &mut cb.base,
                        &ctx.memory[parent_memory(is_s)],
                        [
                            config.parent_data[is_s.idx()].rlc.expr(),
                            config.parent_data[is_s.idx()].is_root.expr(),
                            true.expr(),
                            branch.mod_rlc[is_s.idx()].expr()
                        ]
                    );
                }}
            }
        });

        config
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        witness: &mut [MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        idx: usize,
    ) -> Result<(), Error> {
        let row_init = witness[idx].to_owned();
        let is_placeholder = [
            row_init.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 1,
            row_init.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 1,
        ];

        let is_extension_node = row_init.is_extension;
        self.is_extension
            .assign(region, offset, is_extension_node.scalar())?;

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
                is_placeholder[is_s.idx()].scalar(),
            )?;
        }

        let mut key_rlc = key_data.rlc;
        let mut key_mult = key_data.mult;
        let mut num_nibbles = key_data.num_nibbles;
        let mut is_key_odd = key_data.is_odd;

        // Extension
        if is_extension_node {
            self.extension.assign(
                region,
                witness,
                mpt_config,
                pv,
                offset,
                idx,
                &key_data,
                &mut key_rlc,
                &mut key_mult,
                &mut num_nibbles,
                &mut is_key_odd,
            )?;
        }

        // Branch
        let (key_rlc_post_branch, key_rlc_post_drifted, key_mult_post_branch, mod_node_hash_rlc) =
            self.branch.assign(
                region,
                witness,
                mpt_config,
                pv,
                offset,
                idx,
                &is_placeholder,
                &mut key_rlc,
                &mut key_mult,
                &mut num_nibbles,
                &mut is_key_odd,
            )?;

        // Set the new parent and key
        for is_s in [true, false] {
            if !is_placeholder[is_s.idx()] {
                KeyData::witness_store(
                    region,
                    offset,
                    &mut pv.memory[key_memory(is_s)],
                    key_rlc_post_branch,
                    key_mult_post_branch,
                    num_nibbles,
                    false,
                    0.scalar(),
                    0.scalar(),
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
                    is_key_odd,
                    key_rlc_post_drifted,
                    key_mult_post_branch,
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

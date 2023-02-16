use eth_types::Field;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use super::{
    helpers::MPTConstraintBuilder,
    param::{
        ARITY, IS_C_BRANCH_NON_HASHED_POS, IS_C_EXT_NODE_NON_HASHED_POS,
        IS_S_BRANCH_NON_HASHED_POS, IS_S_EXT_NODE_NON_HASHED_POS,
    },
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cell_manager::{CellManager, DataTransition},
        constraint_builder::{RLCChainable, RLCable},
    },
    mpt_circuit::account_leaf::AccountLeaf,
    mpt_circuit::helpers::bytes_into_rlc,
    mpt_circuit::{
        helpers::{
            contains_placeholder_leaf, get_num_nibbles, key_memory, parent_memory, Indexable,
            KeyData, ParentData,
        },
        param::{RLP_LIST_LONG, RLP_NIL},
        storage_leaf::StorageLeaf,
        FixedTableTag,
    },
    mpt_circuit::{
        helpers::{BranchChildInfo, BranchNodeInfo},
        param::{
            BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, BRANCH_ROWS_NUM, C_RLP_START,
            C_START, DRIFTED_POS, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
            IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS,
            IS_EXT_SHORT_C1_POS, NIBBLES_COUNTER_POS, RLP_NUM, S_RLP_START, S_START,
        },
    },
    mpt_circuit::{param::RLP_HASH_VALUE, witness_row::MptWitnessRow},
    mpt_circuit::{MPTConfig, ProofValues},
};

#[derive(Default, Debug)]
pub(crate) struct Branch {
    pub(crate) is_branch_init: bool,
    pub(crate) is_branch_child: bool,
    pub(crate) is_last_branch_child: bool,
    pub(crate) node_index: u8,
    pub(crate) modified_index: u8,
    pub(crate) drifted_index: u8,
    pub(crate) is_extension_node_s: bool,
    pub(crate) is_extension_node_c: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct BranchCols<F> {
    pub(crate) is_init: Column<Advice>,
    pub(crate) is_child: Column<Advice>,
    pub(crate) is_last_child: Column<Advice>,
    pub(crate) node_index: Column<Advice>,
    pub(crate) is_modified: Column<Advice>, // whether this branch node is modified
    pub(crate) modified_index: Column<Advice>, // index of the modified node
    pub(crate) is_drifted: Column<Advice>,  // needed when leaf is turned into branch
    pub(crate) drifted_index: Column<Advice>, /* needed when leaf is turned into branch - first
                                             * nibble of
                                             * the key stored in a leaf (because the existing
                                             * leaf will
                                             * jump to this position in added branch) */
    pub(crate) is_extension_node_s: Column<Advice>, /* contains extension node key (s_advices)
                                                     * and hash of
                                                     * the branch (c_advices) */
    pub(crate) is_extension_node_c: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: Field> BranchCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_init: meta.advice_column(),
            is_child: meta.advice_column(),
            is_last_child: meta.advice_column(),
            node_index: meta.advice_column(),
            is_modified: meta.advice_column(),
            modified_index: meta.advice_column(),
            is_drifted: meta.advice_column(),
            drifted_index: meta.advice_column(),
            is_extension_node_s: meta.advice_column(),
            is_extension_node_c: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BranchConfig<F> {
    key_data: KeyData<F>,
    parent_data: [ParentData<F>; 2],
}

impl<F: Field> BranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let position_cols = ctx.position_cols;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let r = ctx.r.clone();

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = BranchConfig::default();

        circuit!([meta, cb.base], {
            let mut offset = -1;
            let rot_branch_init = offset;

            for is_s in [true, false] {
                let branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, offset);
                // Selector constraints
                branch.init_selector_checks(meta, &mut cb.base);
                // Check that stored rlc/mult values are correct.
                let rlp = branch.rlp_bytes(meta);
                let (rlc, mult) = matchx! {
                    branch.is_branch_short(meta) => (rlp[..1].rlc(&r), r[0].expr()),
                    branch.is_branch_long(meta) => (rlp[..2].rlc(&r), r[1].expr()),
                    branch.is_branch_very_long(meta) => (rlp[..3].rlc(&r), r[2].expr()),
                };
                require!(a!(accs.acc(is_s).rlc, offset) => rlc);
                require!(a!(accs.acc(is_s).mult, offset) => mult);
            }

            // These selectors are only stored in branch init rows
            let branch = BranchNodeInfo::new(meta, ctx.clone(), true, offset);
            // Boolean checks
            for selector in [
                branch.is_placeholder_s(),
                branch.is_placeholder_c(),
                branch.is_not_hashed_s(),
                branch.is_not_hashed_c(),
            ] {
                require!(selector => bool);
            }
            // Update the nibble counter
            ifx! {not!(branch.is_extension()) => {
                let nibbles_counter_prev = ifx!{not!(branch.is_at_tree_top(meta)) => {
                    branch.nibbles_counter().prev()
                }};
                require!(branch.nibbles_counter() => nibbles_counter_prev + 1.expr());
            }}

            offset += 1;

            for node_index in 0..ARITY {
                // Keep track of how many branch bytes we've processed.
                for is_s in [true, false] {
                    let child = BranchChildInfo::new(meta, ctx.clone(), is_s, offset);
                    // Get the number of bytes used by the current branch.
                    let num_bytes = child.num_bytes(meta);
                    // Fetch the number of bytes left from the previous row.
                    // TODO(Brecht): just store it in branch init in its own column.
                    let num_bytes_left = if node_index == 0 {
                        // Length of full branch
                        BranchNodeInfo::new(meta, ctx.clone(), is_s, offset - 1).len(meta)
                    } else {
                        // Simply stored in rlp1 otherwise
                        a!(ctx.main(is_s).rlp1, offset - 1)
                    };
                    // Update number of bytes left
                    require!(a!(ctx.main(is_s).rlp1, offset) => num_bytes_left - num_bytes.expr());
                    // In the final branch child `rlp1` needs to be 1 (because RLP length
                    // specifies also ValueNode which occupies 1 byte).
                    // TODO: ValueNode
                    if node_index == ARITY - 1 {
                        require!(a!(ctx.main(is_s).rlp1, offset) => 1);
                    }

                    // RLC
                    {
                        let main = ctx.main(is_s);
                        let branch = ctx.accumulators.acc(is_s);
                        let mult_diff = ctx.accumulators.node_mult_diff(is_s);

                        let child = BranchChildInfo::new(meta, ctx.clone(), is_s, offset);
                        let branch_mult =
                            DataTransition::new_with_rot(meta, branch.mult, offset - 1, offset);
                        let branch_rlc =
                            DataTransition::new_with_rot(meta, branch.rlc, offset - 1, offset);
                        // Calculate the RLC
                        let rlc = child.rlc(meta, &mut cb.base);
                        require!(branch_rlc => (branch_rlc.prev(), branch_mult.prev()).rlc_chain(rlc));
                        require!(branch_mult => branch_mult.prev() * a!(mult_diff, offset));
                        // RLC bytes zero check
                        //cb.set_length_sc(is_s, child.num_bytes_on_row(meta));
                        // We need to check that the multiplier changes according to `num_bytes` and
                        // update it.
                        require!((FixedTableTag::RMult, child.num_bytes(meta), a!(mult_diff, offset)) => @format!("fixed"));
                        // When a value is being added (and reverse situation when deleted) to the
                        // trie and there is no other leaf at the position
                        // where it is to be added, we have empty branch
                        // child in `S` proof and hash of a newly added leaf
                        // at the parallel position in `C` proof. That means
                        // we have empty node in `S` proof at `modified_node`.
                        // When this happens, we denote this situation by having a placeholder leaf.
                        // In this case we need to make sure the node is seen as empty.
                        ifx! {a!(ctx.branch.is_modified, offset), contains_placeholder_leaf(meta, ctx.clone(), is_s, offset) => {
                            require!(child.is_hashed(meta) => true);
                            require!(a!(main.rlp2, offset) => 0);
                        }}
                    }
                }

                // Check that `is_modified` is enabled for the correct branch child.
                ifx! {a!(ctx.branch.is_modified, offset) => {
                    require!(a!(ctx.branch.node_index, offset) => a!(ctx.branch.modified_index, offset));
                }}
                // Check that `is_drifted` is enabled for the correct branch child.
                ifx! {a!(ctx.branch.is_drifted, offset) => {
                    require!(a!(ctx.branch.node_index, offset) => a!(ctx.branch.drifted_index, offset));
                }}

                // Check values that need to remain the same for all branch children.
                /*ifx!{a!(branch.node_index, offset) => {
                    // `modified_index` needs to be the same for all branch children.
                    require!(modified_index => modified_index.prev());
                    // `drifted_index` needs to be the same for all branch children.
                    require!(drifted_index => drifted_index.prev());
                    for is_s in [true, false] {
                        // `mod_node_hash_rlc` the same for all branch children
                        let mod_node_hash_rlc = ctx.accumulators.mod_node_rlc(is_s);
                        require!(a!(mod_node_hash_rlc) => a!(mod_node_hash_rlc, -1));
                        // `contains_placeholder_leaf` the same for all branch children
                        require!(contains_placeholder_leaf(meta, ctx.clone(), is_s, 0)
                            => contains_placeholder_leaf(meta, ctx.clone(), is_s, -1));
                    }
                }}*/

                // If we have a branch child, we can only have branch child or branch init in
                // the previous row.
                /*require!(or::expr([is_branch_child.prev(), is_branch_init.prev()]) => true);
                // When `node_index` != 0
                ifx!{node_index => {
                    // `node_index` increases by 1 for each branch child.
                    require!(node_index => node_index.prev() + 1.expr());
                }}*/

                // We need to ensure that the only change in `S` and `C` proof occurs
                // at `modified_index` so that only a single change can be done.
                // We check `s_main.rlp = c_main.rlp` everywhere except at `modified_index`.
                // (except rlp1, rlp1 is used to keep track of number of bytes processed).
                /*let not_at_modification = node_index.expr() - modified_index.expr();
                ifx!{not_at_modification => {
                    for (s_byte, c_byte) in s_main.rlp_bytes().iter().skip(1)
                        .zip(c_main.rlp_bytes().iter().skip(1))
                    {
                        require!(a!(s_byte) => a!(c_byte));
                    }
                }}*/

                // Make sure `is_branch_child`, `node_index` and `is_last_child` are set
                // correctly.
                /*ifx!{is_branch_init.prev() => {
                    // First child when previous row is a branch init row
                    require!(is_branch_child => true);
                    require!(node_index => 0);
                } elsex {
                    // When `is_branch_child` changes back to 0, previous `node_index` needs to be 15
                    // and previous `is_last_child` needs to be 1.
                    ifx!{is_branch_child.delta() => {
                        require!(node_index.prev() => 15);
                        require!(is_last_child.prev() => true);
                    }}
                }}*/

                if node_index == ARITY - 1 {
                    // Rotations could be avoided but we would need additional is_branch_placeholder
                    // column.
                    let mut branch =
                        BranchNodeInfo::new(meta, ctx.clone(), true, offset - (ARITY as i32));

                    // `is_modified` needs to be set to 1 at exactly 1 branch child
                    let is_modified_values = (0..ARITY)
                        .map(|rot| a!(ctx.branch.is_modified, offset - (rot as i32)))
                        .collect::<Vec<_>>();
                    require!(sum::expr(&is_modified_values) => 1);

                    ifx! {branch.is_placeholder() => {
                        // `is_drifted` needs to be set to 1 at exactly 1 branch child
                        let is_drifted_values = (0..ARITY).map(|rot| a!(ctx.branch.is_drifted, offset - (rot as i32))).collect::<Vec<_>>();
                        require!(sum::expr(&is_drifted_values) => 1);
                    }}

                    for is_s in [true, false] {
                        branch.set_is_s(is_s);

                        // Check if the branch is in its parent.
                        let (rlc, num_bytes, is_not_hashed) = ifx! {branch.is_extension() => {
                            // Note: acc_c in both cases.
                            let ext_rlc = a!(branch.ctx.accumulators.acc_c.rlc, offset + if is_s {1} else {2});
                            (ext_rlc, branch.ext_num_bytes(meta, offset + 1), branch.ext_is_not_hashed())
                        } elsex {
                            let acc = branch.ctx.accumulators.acc(is_s);
                            // TODO: acc currently doesn't have branch ValueNode info
                            let branch_rlc = (a!(acc.rlc, offset), a!(acc.mult, offset)).rlc_chain(RLP_NIL.expr());
                            (branch_rlc, branch.num_bytes(meta), branch.is_not_hashed())
                        }};

                        config.parent_data[is_s.idx()] = ParentData::load(
                            "branch load",
                            &mut cb.base,
                            &ctx.memory[parent_memory(is_s)],
                            0.expr(),
                        );
                        ifx! {not!(branch.is_placeholder()) => {
                            ifx!{or::expr(&[config.parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                                // Hashed branch hash in parent branch
                                // TODO(Brecht): fix
                                //require!((1, rlc, num_bytes, config.parent_data[is_s.idx()].rlc) => @"keccak");
                            } elsex {
                                // Non-hashed branch hash in parent branch
                                require!(rlc => config.parent_data[is_s.idx()].rlc);
                            }}
                        }}
                    }

                    // - For a branch placeholder we do not have any constraints. However, in the
                    //   parallel
                    // (regular) branch we have an additional constraint (besides `is_modified` row
                    // corresponding to `mod_nod_hash_rlc`) in this case: `is_drifted` `main.bytes`
                    // RLC is stored in the placeholder `mod_node_hash_rlc`. For
                    // example, if there is a placeholder branch in `S` proof,
                    // we have:
                    //   - c_mod_node_hash_rlc := `is_modified` `c_main.bytes RLC`
                    //   - s_mod_node_hash_rlc := `is_drifted` `c_main.bytes RLC`
                    // - When `S` branch is NOT a placeholder:
                    //   - s_mod_node_rlc := `is_modified` `s_main.bytes RLC`
                    // Run over all branch children
                    for rot in -(ARITY as i32) + 1..=0 {
                        for is_s in [true, false] {
                            branch.set_is_s(is_s);
                            ifx! {branch.is_placeholder() => {
                                ifx!{a!(ctx.branch.is_drifted, offset + rot) => {
                                    let branch_rlc = ctx.main(!is_s).bytes(meta, offset + rot).rlc(&r);
                                    require!(a!(accs.mod_node_rlc(is_s), offset + rot) => branch_rlc);
                                    ParentData::store(
                                        &mut cb.base,
                                        &ctx.memory[parent_memory(is_s)],
                                        [config.parent_data[is_s.idx()].rlc.expr(), config.parent_data[is_s.idx()].is_root.expr(), true.expr(), branch_rlc]
                                    );
                                }}
                            } elsex {
                                ifx!{a!(ctx.branch.is_modified, offset + rot) => {
                                    let branch_rlc = ctx.main(is_s).bytes(meta, offset + rot).rlc(&r);
                                    require!(a!(accs.mod_node_rlc(is_s), offset + rot) => branch_rlc);
                                    ParentData::store(
                                        &mut cb.base,
                                        &ctx.memory[parent_memory(is_s)],
                                        [branch_rlc.expr(), false.expr(), false.expr(), branch_rlc.expr()]
                                    );
                                }}
                            }}
                        }
                    }

                    // When in a placeholder branch, both branches are the same - the placeholder
                    // branch and its parallel counterpart, which is not a
                    // placeholder, but a regular branch (newly added branch).
                    // The regular branch has only two non-nil nodes,
                    // because the placeholder branch appears only when an existing
                    // leaf drifts down into a newly added branch. Besides an
                    // existing leaf, we have a leaf that was being added and that caused
                    // a new branch to be added. So we need to check that there are exactly two
                    // non-nil nodes (otherwise the attacker could add more
                    // new leaves at the same time). The non-nil nodes need to be at
                    // `is_modified` and `is_drifted`, elsewhere there have
                    // to be zeros.
                    for is_s in [true, false] {
                        // So many rotation is not optimal, but most of these rotations are used
                        // elsewhere, so it should not be much of an overhead.
                        // Alternative approach would be to have a column specifying
                        // whether there is a placeholder branch or not (we currently have this info
                        // only in branch init). Another alternative would be to have a column where
                        // we add `rlp2` value from the current row in each
                        // of the 16 rows. Both alternative would require
                        // additional column.
                        let branch =
                            BranchNodeInfo::new(meta, ctx.clone(), is_s, offset - (ARITY as i32));
                        ifx! {branch.is_placeholder() => {
                            let sum_rlp2 = (0..ARITY).into_iter().fold(0.expr(), |acc, idx| {
                                acc + a!(ctx.main(is_s).rlp2, offset - (idx as i32))
                            });
                            // There are constraints which ensure there is only 0 or 160 at rlp2 for
                            // branch children.
                            require!(sum_rlp2 => (RLP_HASH_VALUE as u64) * 2);
                        }}
                    }
                }
                offset += 1;
            }

            for is_s in [true, false] {
                let rot_s = offset - if is_s { 0 } else { 1 };
                let rot_last_child = rot_s - 1;

                let not_first_level = a!(position_cols.not_first_level, offset);
                let ext = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);

                ifx! {ext.is_extension() => {
                    let ext_rlc = DataTransition::from(a!(accs.acc_s.rlc, rot_s), a!(accs.acc_c.rlc, offset));

                    // There are two cases:
                    // - hashed branch has RLP_HASH_VALUE at c_rlp2 and hash in c_advices,
                    // - non-hashed branch has 0 at c_rlp2 and all the bytes in c_advices
                    // TODO(Brecht): why different layout for hashed values? If for hash detection
                    // just do == 32?
                    require!(a!(c_main.rlp2, offset) => [0, RLP_HASH_VALUE]);

                    // `short` means there is only one nibble in the extension node, `long` means
                    // there are at least two. `even` means the number of nibbles is
                    // even, `odd` means the number of nibbles is odd. `c16` means that
                    // above the branch there are even number of nibbles, `c1` means that above
                    // the branch there are odd number of nibbles.
                    let type_selectors_c1 = [
                        ext.is_short_c1.expr(),
                        ext.is_long_even_c1.expr(),
                        ext.is_long_odd_c1.expr(),
                    ];
                    let type_selectors_c16 = [
                        ext.is_short_c16.expr(),
                        ext.is_long_even_c16.expr(),
                        ext.is_long_odd_c16.expr(),
                    ];
                    let type_selectors = [type_selectors_c1.clone(), type_selectors_c16.clone()].concat();
                    let misc_selectors = [
                        ext.is_longer_than_55_s.expr(),
                        ext.is_ext_not_hashed_s.expr(),
                    ];

                    // Check that the selectors are boolean
                    for selector in type_selectors.iter().chain(misc_selectors.iter()) {
                        require!(selector => bool);
                    }
                    // For extension nodes exactly 1 type selector needs to be enabled.
                    require!(sum::expr(&type_selectors) => 1);
                    // `is_key_odd` is set using the extension node type selector data.
                    // (while in case of a regular branch the extension node selectors do not hold this information).
                    require!(ext.is_key_odd() => not!(sum::expr(&type_selectors_c1)));
                    require!(ext.is_key_odd() => sum::expr(&type_selectors_c16));

                    // RLP encoding checks: [key, branch]
                    // In C we have nibbles, we check below only for S.
                    if is_s {
                        ifx! {ext.is_longer_than_55_s => {
                            require!(a!(s_main.rlp1, offset) => RLP_LIST_LONG + 1);
                        }}
                        // Verify that the lenghts are consistent.
                        require!(ext.ext_len(meta, offset) => ext.ext_key_num_bytes(meta, offset) + ext.ext_branch_num_bytes(meta, offset));
                    }

                    // Calculate the extension node RLC.
                    // The intermediate RLC after `s_main` bytes needs to be properly computed.
                    // s_rlp1, s_rlp2, s_bytes need to be the same in both extension rows.
                    // However, to make space for nibble witnesses, we put nibbles in
                    // extension row C s_bytes. So we use s_bytes from S row.
                    // TODO(Brecht): Do we need to store the RLC here? we can just use `rlc`
                    // directly below...
                    require!(ext_rlc.prev() => s_main.expr(meta, rot_s).rlc(&r));
                    // Update the multiplier with the number of bytes on the first row
                    let mult = a!(accs.acc_s.mult, offset);
                    require!((FixedTableTag::RMult, ext.ext_num_bytes_on_key_row(meta, rot_s), mult) => @"fixed");

                    let rlc = ifx! {ext.contains_hashed_branch(meta, offset) => {
                        c_main.expr(meta, offset)[1..].rlc(&r)
                    } elsex {
                        // RLC bytes zero check (+2 because data starts at bytes[0])
                        //cb.set_length_c(2.expr() + ext.ext_branch_num_bytes(meta));

                        c_main.expr(meta, offset)[2..].rlc(&r)
                    }};
                    require!(ext_rlc => (ext_rlc.prev(), mult.expr()).rlc_chain(rlc));

                    // We check that the branch hash RLC corresponds to the extension node RLC
                    // stored in the extension node row. TODO: acc currently doesn't
                    // have branch ValueNode info (which 128 if nil)
                    let branch_rlc = (
                        a!(accs.acc(is_s).rlc, rot_last_child),
                        a!(accs.acc(is_s).mult, rot_last_child),
                    )
                        .rlc_chain(RLP_NIL.expr());
                    let branch_rlc_in_ext = c_main.bytes(meta, offset).rlc(&r);
                    ifx! {ext.contains_hashed_branch(meta, offset) => {
                        // Check that `(branch_rlc, extension_node_hash_rlc`) is in the keccak table.
                        require!((1, branch_rlc, ext.num_bytes(meta), branch_rlc_in_ext) => @"keccak");
                    } elsex {
                        // Check if the RLC matches
                        require!(branch_rlc => branch_rlc_in_ext);
                    }}

                    // Update the number of nibbles processed up to this point.
                    if is_s {
                        // Calculate the number of bytes
                        let key_len = ext.ext_key_len(meta, offset);
                        // Calculate the number of nibbles
                        let num_nibbles =
                            get_num_nibbles(key_len.expr(), ext.is_key_part_in_ext_odd());
                        // Make sure the nibble counter is updated correctly
                        let nibbles_count_prev = ifx! {f!(ctx.position_cols.q_not_first), not!(ext.is_below_account(meta)), not_first_level.expr() => {
                            ext.nibbles_counter().prev()
                        }};
                        require!(ext.nibbles_counter() => nibbles_count_prev.expr() + num_nibbles.expr() + 1.expr());
                    }
                }}

                offset += 1;
            }

            offset -= 2;

            let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
            ifx! {branch.is_extension() => {
                // RLC bytes zero check
                // TODO(Brecht): fix
                //cb.set_length(1.expr() + branch.ext_num_bytes_on_key_row(meta, 0));
            }}

            offset += 1;

            let key = ctx.accumulators.key;
            let mult_diff = ctx.accumulators.mult_diff;

            let rot_first_child = rot_branch_init + 1;

            let mut branch = BranchNodeInfo::new(meta, ctx.clone(), false, rot_branch_init);
            let modified_index = a!(ctx.branch.modified_index, rot_first_child);
            let key_rlc = a!(key.rlc, rot_first_child);
            let key_mult = a!(key.mult, rot_first_child);

            // `is_key_odd` needs to be boolean
            require!(branch.is_key_odd() => bool);

            // Load the last key values
            config.key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(true)], 0.expr());

            // Calculate the extension node key RLC when in an extension node
            let key_rlc_post_ext = ifx! {branch.is_extension() => {
                let key_rlc_ext = DataTransition::new_with_rot(meta, key.rlc, offset - 1, offset);
                // Extension key rlc
                let ext_key_rlc = config.key_data.rlc.expr() + branch.ext_key_rlc(meta, &mut cb.base, config.key_data.mult.expr(), offset);
                // Currently, the extension node S and extension node C both have the same key RLC -
                // however, sometimes extension node can be replaced by a shorter extension node
                // (in terms of nibbles), this is still to be implemented.
                // TODO: extension nodes of different nibbles length
                require!(key_rlc_ext => key_rlc_ext.prev());
                // Store it
                require!(key_rlc_ext => ext_key_rlc);
                ext_key_rlc.expr()
            } elsex {
                config.key_data.rlc.expr()
            }};

            // Get the length of the key
            let key_num_bytes_for_mult = ifx! {branch.is_extension() => {
                // Unless both parts of the key are odd, subtract 1 from the key length.
                let key_len = branch.ext_key_len(meta, offset - 1);
                key_len - ifx! {not!(config.key_data.is_odd.expr() * branch.is_key_part_in_ext_odd()) => { 1.expr() }}
            }};
            // Get the multiplier for this key length
            let mult_diff = a!(mult_diff, rot_first_child);
            require!((FixedTableTag::RMult, key_num_bytes_for_mult, mult_diff) => @"fixed");

            // Now update the key RLC and multiplier for the branch nibble.
            let mult = config.key_data.mult.expr() * mult_diff.expr();
            let (nibble_mult, mult_mult) = ifx! {branch.is_key_odd() => {
                // The nibble will be added as the most significant nibble using the same multiplier
                (16.expr(), 1.expr())
            } elsex {
                // The nibble will be added as the least significant nibble, the multiplier needs to advance
                (1.expr(), r[0].expr())
            }};
            require!(key_rlc => key_rlc_post_ext.expr() + modified_index.expr() * nibble_mult.expr() * mult.expr());
            require!(key_mult => mult.expr() * mult_mult.expr());

            // Update key parity
            ifx! {branch.is_extension() => {
                // We need to take account the nibbles of the extension node.
                // The parity alternates when there's an even number of nibbles, remains the same otherwise
                ifx!{branch.is_key_part_in_ext_even() => {
                    require!(branch.is_key_odd() => not!(config.key_data.is_odd));
                } elsex {
                    require!(branch.is_key_odd() => config.key_data.is_odd);
                }}
            } elsex {
                // The parity simply alternates for regular branches.
                require!(branch.is_key_odd() => not!(config.key_data.is_odd));
            }}

            for is_s in [true, false] {
                branch.set_is_s(is_s);
                ifx! {not!(branch.is_placeholder()) => {
                    KeyData::store(
                        &mut cb.base,
                        &ctx.memory[key_memory(is_s)],
                        [
                            key_rlc.expr(),
                            key_mult.expr(),
                            branch.nibbles_counter().expr(),
                            branch.is_key_odd(),
                            branch.contains_placeholder_leaf(meta, true),
                            branch.contains_placeholder_leaf(meta, false),
                            0.expr(),
                            branch.is_key_odd(),
                            key_rlc.expr(),
                            key_mult.expr(),
                        ],
                    );
                 } elsex {
                    let (parent_rlc, parent_mult) = ifx! {branch.is_extension() => {
                        (key_rlc_post_ext.expr(), mult.expr())
                    } elsex {
                        (config.key_data.rlc.expr(), config.key_data.mult.expr())
                    }};
                    KeyData::store(
                        &mut cb.base,
                        &ctx.memory[key_memory(is_s)],
                        [
                            config.key_data.rlc.expr(),
                            config.key_data.mult.expr(),
                            config.key_data.num_nibbles.expr(),
                            config.key_data.is_odd.expr(),
                            branch.contains_placeholder_leaf(meta, true),
                            branch.contains_placeholder_leaf(meta, false),
                            a!(ctx.branch.drifted_index, rot_first_child),
                            branch.is_key_odd(),
                            parent_rlc,
                            parent_mult,
                        ],
                    );
                }}
            }

            // We need to check that the nibbles we stored in s are between 0
            // and 15. cb.set_range_s(FixedTableTag::RangeKeyLen16.
            // expr());
        });

        config
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        witness: &[MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let base_offset = offset;
        let mut offset = offset - 1;

        /* INIT */
        let row = &witness[offset];

        pv.nibbles_num_prev = pv.nibbles_num;

        pv.modified_node = row.get_byte(BRANCH_0_KEY_POS);
        pv.node_index = 0;
        pv.drifted_pos = row.get_byte(DRIFTED_POS);

        // Get the child that is being changed and convert it to words to enable
        // lookups:
        let mut s_hash = witness[offset + 1 + pv.modified_node as usize]
            .s_hash_bytes()
            .to_vec();
        let mut c_hash = witness[offset + 1 + pv.modified_node as usize]
            .c_hash_bytes()
            .to_vec();
        pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, mpt_config.randomness);
        pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, mpt_config.randomness);

        if row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 1 {
            println!("{}: s_placeholder", offset);
            // We put hash of a node that moved down to the added branch.
            // This is needed to check the hash of leaf_in_added_branch.
            s_hash = witness[offset + 1 + pv.drifted_pos as usize]
                .s_hash_bytes()
                .to_vec();
            pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, mpt_config.randomness);
            pv.is_branch_s_placeholder = true
        } else {
            pv.is_branch_s_placeholder = false
        }
        if row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 1 {
            println!("{}: c_placeholder", offset);
            c_hash = witness[offset + 1 + pv.drifted_pos as usize]
                .c_hash_bytes()
                .to_vec();
            pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, mpt_config.randomness);
            pv.is_branch_c_placeholder = true
        } else {
            pv.is_branch_c_placeholder = false
        }
        /*
        If no placeholder branch, we set `drifted_pos = modified_node`. This
        is needed just to make some other constraints (`s_mod_node_hash_rlc`
        and `c_mod_node_hash_rlc` correspond to the proper node) easier to write.
        */
        if row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 0
            && row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 0
        {
            pv.drifted_pos = pv.modified_node
        }

        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();
        let branch = Branch {
            is_branch_init: true,
            ..Default::default()
        };

        row.assign(
            region,
            mpt_config,
            account_leaf,
            storage_leaf,
            branch,
            offset,
        )?;

        // reassign (it was assigned to 0 in assign_row) branch_acc and
        // branch_mult to proper values

        // Branch (length 83) with two bytes of RLP meta data
        // [248,81,128,128,...

        // Branch (length 340) with three bytes of RLP meta data
        // [249,1,81,128,16,...

        let s_len = [0, 1, 2].map(|i| row.get_byte(BRANCH_0_S_START + i) as u64);
        pv.acc_s = F::from(s_len[0]);
        pv.acc_mult_s = mpt_config.randomness;

        if s_len[0] == 249 {
            pv.acc_s += F::from(s_len[1]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.randomness;
            pv.acc_s += F::from(s_len[2]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.randomness;

            pv.rlp_len_rem_s = s_len[1] as i32 * 256 + s_len[2] as i32;
        } else if s_len[0] == 248 {
            pv.acc_s += F::from(s_len[1]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.randomness;

            pv.rlp_len_rem_s = s_len[1] as i32;
        } else {
            pv.rlp_len_rem_s = s_len[0] as i32 - 192;
        }

        let c_len = [0, 1, 2].map(|i| row.get_byte(BRANCH_0_C_START + i) as u64);
        pv.acc_c = F::from(c_len[0]);
        pv.acc_mult_c = mpt_config.randomness;

        if c_len[0] == 249 {
            pv.acc_c += F::from(c_len[1]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.randomness;
            pv.acc_c += F::from(c_len[2]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.randomness;

            pv.rlp_len_rem_c = c_len[1] as i32 * 256 + c_len[2] as i32;
        } else if c_len[0] == 248 {
            pv.acc_c += F::from(c_len[1]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.randomness;

            pv.rlp_len_rem_c = c_len[1] as i32;
        } else {
            pv.rlp_len_rem_c = c_len[0] as i32 - 192;
        }

        mpt_config.assign_acc(
            region,
            pv.acc_s,
            pv.acc_mult_s,
            pv.acc_c,
            pv.acc_mult_c,
            offset,
        )?;

        pv.is_even =
            row.get_byte(IS_EXT_LONG_EVEN_C16_POS) + row.get_byte(IS_EXT_LONG_EVEN_C1_POS) == 1;
        pv.is_odd = row.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
            + row.get_byte(IS_EXT_SHORT_C16_POS)
            + row.get_byte(IS_EXT_SHORT_C1_POS)
            == 1;
        pv.is_short = row.get_byte(IS_EXT_SHORT_C16_POS) + row.get_byte(IS_EXT_SHORT_C1_POS) == 1;
        pv.is_short_c1 = row.get_byte(IS_EXT_SHORT_C1_POS) == 1;
        pv.is_long = row.get_byte(IS_EXT_LONG_EVEN_C16_POS)
            + row.get_byte(IS_EXT_LONG_EVEN_C1_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
            == 1;
        pv.is_extension_node = pv.is_even || pv.is_odd;

        // Assign how many nibbles have been used in the previous extension node +
        // branch.
        pv.nibbles_num += 1; // one nibble is used for position in branch
        if pv.is_extension_node {
            // Get into extension node S
            let row_ext = &witness[offset + BRANCH_ROWS_NUM as usize - 2];
            let ext_nibbles: usize;
            if row_ext.get_byte(1) <= 32 {
                ext_nibbles = 1
            } else if row_ext.get_byte(0) < 248 {
                if row_ext.get_byte(2) == 0 {
                    // even number of nibbles
                    ext_nibbles = ((row_ext.get_byte(1) - 128) as usize - 1) * 2;
                } else {
                    ext_nibbles = (row_ext.get_byte(1) - 128) as usize * 2 - 1;
                }
            } else if row_ext.get_byte(3) == 0 {
                // even number of nibbles
                ext_nibbles = ((row_ext.get_byte(2) - 128) as usize - 1) * 2;
            } else {
                ext_nibbles = (row_ext.get_byte(2) - 128) as usize * 2 - 1;
            }

            pv.nibbles_num += ext_nibbles;
        }
        region.assign_advice(
            || "assign number of nibbles".to_string(),
            mpt_config.s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
            offset,
            || Value::known(F::from(pv.nibbles_num as u64)),
        )?;

        pv.is_hashed_s = row.get_byte(IS_S_BRANCH_NON_HASHED_POS) != 1;
        pv.is_hashed_c = row.get_byte(IS_C_BRANCH_NON_HASHED_POS) != 1;
        pv.ext_is_hashed_s = row.get_byte(IS_S_EXT_NODE_NON_HASHED_POS) != 1;
        pv.ext_is_hashed_c = row.get_byte(IS_C_EXT_NODE_NON_HASHED_POS) != 1;

        offset += 1;

        /* CHILD */

        for node_index in 0..ARITY {
            let row = &witness[offset];

            let mut node_mult_diff_s = F::one();
            let mut node_mult_diff_c = F::one();

            let len = if row.get_byte(S_RLP_START + 1) == 160 {
                pv.rlp_len_rem_s -= 33;
                33
            } else if row.get_byte(S_RLP_START + 1) == 0 && row.get_byte(S_START) > 192 {
                let len = 1 + (row.get_byte(S_START) as i32 - 192);
                pv.rlp_len_rem_s -= len;
                len
            } else if row.get_byte(S_RLP_START + 1) == 0 {
                pv.rlp_len_rem_s -= 1;
                1
            } else {
                0
            };
            for _ in 0..len {
                node_mult_diff_s *= mpt_config.randomness;
            }

            let len = if row.get_byte(C_RLP_START + 1) == 160 {
                pv.rlp_len_rem_c -= 33;
                33
            } else if row.get_byte(C_RLP_START + 1) == 0 && row.get_byte(C_START) > 192 {
                let len = 1 + (row.get_byte(C_START) as i32 - 192);
                pv.rlp_len_rem_c -= len;
                len
            } else if row.get_byte(C_RLP_START + 1) == 0 {
                pv.rlp_len_rem_c -= 1;
                1
            } else {
                0
            };
            for _ in 0..len {
                node_mult_diff_c *= mpt_config.randomness;
            }

            region.assign_advice(
                || "node_mult_diff_s".to_string(),
                mpt_config.accumulators.node_mult_diff_s,
                offset,
                || Value::known(node_mult_diff_s),
            )?;
            region.assign_advice(
                || "node_mult_diff_c".to_string(),
                mpt_config.accumulators.node_mult_diff_c,
                offset,
                || Value::known(node_mult_diff_c),
            )?;

            if pv.node_index == 0 {
                // If it's not extension node, rlc and rlc_mult in extension row
                // will be the same as for branch rlc.
                pv.extension_node_rlc = pv.key_rlc;

                pv.key_rlc_prev = pv.key_rlc;
                pv.key_rlc_mult_prev = pv.key_rlc_mult;

                // Extension node
                // We need nibbles here to be able to compute key RLC
                if pv.is_extension_node {
                    // For key RLC, we need to first take into account
                    // extension node key.
                    // witness[offset + 16]
                    let ext_row = &witness[offset + 16];
                    let mut key_len_pos = 1;
                    if ext_row.get_byte(0) == 248 {
                        key_len_pos = 2;
                    }

                    if pv.key_rlc_sel {
                        // Note: it can't be is_even = 1 && is_short = 1.
                        if pv.is_even && pv.is_long {
                            // extension node part:
                            let key_len = ext_row.get_byte(key_len_pos) as usize - 128 - 1; // -1 because the first byte is 0 (is_even)
                            mpt_config.compute_acc_and_mult(
                                &ext_row.bytes,
                                &mut pv.extension_node_rlc,
                                &mut pv.key_rlc_mult,
                                key_len_pos + 2, /* first position behind key_len_pos
                                                  * is 0 (because is_even), we start
                                                  * with the next one */
                                key_len,
                            );
                            pv.mult_diff = F::one();
                            for _ in 0..key_len {
                                pv.mult_diff *= mpt_config.randomness;
                            }
                            pv.key_rlc = pv.extension_node_rlc;
                            pv.extension_node_mult = pv.key_rlc_mult;
                            // branch part:
                            pv.key_rlc +=
                                F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                            // key_rlc_mult stays the same
                            pv.key_rlc_sel = !pv.key_rlc_sel;
                        } else if pv.is_odd && pv.is_long {
                            // extension node part:
                            pv.extension_node_rlc +=
                                F::from((ext_row.get_byte(key_len_pos + 1) - 16) as u64)
                                    * F::from(16)
                                    * pv.key_rlc_mult;

                            let ext_row_c = &witness[offset + 17];
                            let key_len = ext_row.get_byte(key_len_pos) as usize - 128;

                            pv.mult_diff = F::one();
                            for k in 0..key_len - 1 {
                                let second_nibble = ext_row_c.get_byte(S_START + k);
                                let first_nibble =
                                    (ext_row.get_byte(key_len_pos + 2 + k) - second_nibble) / 16;
                                assert_eq!(
                                    first_nibble * 16 + second_nibble,
                                    ext_row.get_byte(key_len_pos + 2 + k),
                                );
                                pv.extension_node_rlc +=
                                    F::from(first_nibble as u64) * pv.key_rlc_mult;

                                pv.key_rlc_mult *= mpt_config.randomness;
                                pv.mult_diff *= mpt_config.randomness;

                                pv.extension_node_rlc +=
                                    F::from(second_nibble as u64) * F::from(16) * pv.key_rlc_mult;
                            }

                            pv.key_rlc = pv.extension_node_rlc;
                            pv.extension_node_mult = pv.key_rlc_mult;
                            // branch part:
                            pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                            pv.key_rlc_mult *= mpt_config.randomness;
                        } else if pv.is_short {
                            pv.extension_node_rlc += F::from((ext_row.get_byte(1) - 16) as u64)
                                * F::from(16)
                                * pv.key_rlc_mult;
                            pv.key_rlc = pv.extension_node_rlc;
                            pv.extension_node_mult = pv.key_rlc_mult;
                            // branch part:
                            pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                            pv.key_rlc_mult *= mpt_config.randomness;
                            pv.mult_diff = if pv.is_short_c1 {
                                F::one()
                            } else {
                                mpt_config.randomness
                            };
                        }
                    } else if pv.is_even && pv.is_long {
                        // extension node part:
                        let ext_row_c = &witness[offset + 17];
                        let key_len = ext_row.get_byte(key_len_pos) as usize - 128 - 1; // -1 because the first byte is 0 (is_even)

                        pv.mult_diff = F::one();
                        for k in 0..key_len {
                            let second_nibble = ext_row_c.get_byte(S_START + k);
                            let first_nibble =
                                (ext_row.get_byte(key_len_pos + 2 + k) - second_nibble) / 16;
                            assert_eq!(
                                first_nibble * 16 + second_nibble,
                                ext_row.get_byte(key_len_pos + 2 + k),
                            );
                            pv.extension_node_rlc += F::from(first_nibble as u64) * pv.key_rlc_mult;

                            pv.key_rlc_mult *= mpt_config.randomness;
                            pv.mult_diff *= mpt_config.randomness;

                            pv.extension_node_rlc +=
                                F::from(16) * F::from(second_nibble as u64) * pv.key_rlc_mult;
                        }

                        pv.key_rlc = pv.extension_node_rlc;
                        pv.extension_node_mult = pv.key_rlc_mult;
                        // branch part:
                        pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.randomness;
                        pv.key_rlc_sel = !pv.key_rlc_sel;
                    } else if pv.is_odd && pv.is_long {
                        pv.extension_node_rlc +=
                            F::from((ext_row.get_byte(key_len_pos + 1) - 16) as u64)
                                * pv.key_rlc_mult;

                        pv.key_rlc_mult *= mpt_config.randomness;

                        let key_len = ext_row.get_byte(key_len_pos) as usize - 128;

                        mpt_config.compute_acc_and_mult(
                            &ext_row.bytes,
                            &mut pv.extension_node_rlc,
                            &mut pv.key_rlc_mult,
                            key_len_pos + 2, /* the first position after key_len_pos
                                              * is single nibble which is taken into
                                              * account above, we start
                                              * with fourth */
                            key_len - 1, // one byte is occupied by single nibble
                        );
                        pv.mult_diff = F::one();
                        for _ in 0..key_len {
                            pv.mult_diff *= mpt_config.randomness;
                        }
                        pv.key_rlc = pv.extension_node_rlc;
                        pv.extension_node_mult = pv.key_rlc_mult;
                        // branch part:
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                        // key_rlc_mult stays the same
                    } else if pv.is_short {
                        pv.extension_node_rlc +=
                            F::from((ext_row.get_byte(1) - 16) as u64) * pv.key_rlc_mult;

                        pv.key_rlc = pv.extension_node_rlc;

                        pv.key_rlc_mult *= mpt_config.randomness;
                        pv.extension_node_mult = pv.key_rlc_mult;
                        // branch part:
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                        pv.mult_diff = if pv.is_short_c1 {
                            F::one()
                        } else {
                            mpt_config.randomness
                        };
                    }
                } else {
                    if pv.key_rlc_sel {
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                        // key_rlc_mult stays the same
                    } else {
                        pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.randomness;
                    }
                    pv.key_rlc_sel = !pv.key_rlc_sel;
                    pv.mult_diff = F::one();
                }
                row.assign_branch_row(region, mpt_config, pv, offset)?;
            } else {
                row.assign_branch_row(region, mpt_config, pv, offset)?;
            }

            //println!("node index: {} ({})", pv.node_index, offset);

            if pv.node_index == 15 {
                let parent_values_s = self.parent_data[true.idx()].witness_load(
                    region,
                    base_offset,
                    &mut pv.memory[parent_memory(true)],
                    0,
                )?;
                let parent_values_c = self.parent_data[false.idx()].witness_load(
                    region,
                    base_offset,
                    &mut pv.memory[parent_memory(false)],
                    0,
                )?;

                if !pv.is_branch_s_placeholder {
                    self.parent_data[true.idx()].witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[parent_memory(true)],
                        pv.s_mod_node_hash_rlc,
                        false,
                        false,
                        pv.s_mod_node_hash_rlc,
                    )?;
                } else {
                    //println!("placeholder store s");
                    self.parent_data[true.idx()].witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[parent_memory(true)],
                        parent_values_s[0],
                        parent_values_s[1] != F::zero(),
                        true,
                        pv.s_mod_node_hash_rlc,
                    )?;
                    //self.parent_data_s.witness_store(region, offset, &mut
                    // pv.memory[parent_memory(true)], pv.c_mod_node_hash_rlc,
                    // false)?;
                }
                if !pv.is_branch_c_placeholder {
                    self.parent_data[false.idx()].witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[parent_memory(false)],
                        pv.c_mod_node_hash_rlc,
                        false,
                        false,
                        pv.c_mod_node_hash_rlc,
                    )?;
                } else {
                    //println!("placeholder store c: {:?}", parent_values_c);
                    self.parent_data[false.idx()].witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[parent_memory(false)],
                        parent_values_c[0],
                        parent_values_c[1] != F::zero(),
                        true,
                        pv.c_mod_node_hash_rlc,
                    )?;

                    //self.parent_data_c.witness_store(region, offset, &mut
                    // pv.memory[parent_memory(false)], pv.s_mod_node_hash_rlc,
                    // false)?;
                }
            }

            /*
            `sel1` is to distinguish whether the S node at `modified_node` position is empty.
            `sel2` is to distinguish whether the C node at `modified_node` position is empty.
            Note that 128 comes from the RLP byte denoting empty leaf.
            Having 128 for `*_mod_node_hash_rlc` means there is no node at
            this position in branch - for example,
            `s_mode_node_hash_rlc = 128` and `c_words` is some other value
            when new value is added to the trie
            (as opposed to just updating the value).
            Note that there is a potential attack if a leaf node
            is found with hash `[128, 0, ..., 0]`,
            but the probability is negligible.
            */
            let mut sel1 = false;
            let mut sel2 = false;
            if pv.s_mod_node_hash_rlc == F::from(128_u64) {
                sel1 = true;
            }
            if pv.c_mod_node_hash_rlc == F::from(128_u64) {
                sel2 = true;
            }
            pv.is_placeholder_leaf_s = sel1;
            pv.is_placeholder_leaf_c = sel2;

            region.assign_advice(
                || "assign sel1".to_string(),
                mpt_config.denoter.sel1,
                offset,
                || Value::known(F::from(sel1)),
            )?;
            region.assign_advice(
                || "assign sel2".to_string(),
                mpt_config.denoter.sel2,
                offset,
                || Value::known(F::from(sel2)),
            )?;

            // reassign (it was assigned to 0 in assign_row) branch_acc and
            // branch_mult to proper values

            // We need to distinguish between empty and non-empty node:
            // empty node at position 1: 0
            // non-empty node at position 1: 160

            let c128 = F::from(128_u64);
            let c160 = F::from(160_u64);

            let compute_branch_acc_and_mult =
                |branch_acc: &mut F, branch_mult: &mut F, rlp_start: usize, start: usize| {
                    if row.get_byte(rlp_start + 1) == 0 && row.get_byte(start) == 128 {
                        *branch_acc += c128 * *branch_mult;
                        *branch_mult *= mpt_config.randomness;
                    } else if row.get_byte(rlp_start + 1) == 160 {
                        *branch_acc += c160 * *branch_mult;
                        *branch_mult *= mpt_config.randomness;
                        for i in 0..HASH_WIDTH {
                            *branch_acc += F::from(row.get_byte(start + i) as u64) * *branch_mult;
                            *branch_mult *= mpt_config.randomness;
                        }
                    } else {
                        *branch_acc += F::from(row.get_byte(start) as u64) * *branch_mult;
                        *branch_mult *= mpt_config.randomness;
                        let len = row.get_byte(start) as usize - 192;
                        for i in 0..len {
                            *branch_acc +=
                                F::from(row.get_byte(start + 1 + i) as u64) * *branch_mult;
                            *branch_mult *= mpt_config.randomness;
                        }
                    }
                };

            // TODO: add branch ValueNode info

            compute_branch_acc_and_mult(&mut pv.acc_s, &mut pv.acc_mult_s, S_RLP_START, S_START);
            compute_branch_acc_and_mult(&mut pv.acc_c, &mut pv.acc_mult_c, C_RLP_START, C_START);
            mpt_config.assign_acc(
                region,
                pv.acc_s,
                pv.acc_mult_s,
                pv.acc_c,
                pv.acc_mult_c,
                offset,
            )?;

            // This is to avoid Poisoned Constraint in extension_node_key.
            region.assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(pv.key_rlc),
            )?;
            region.assign_advice(
                || "assign key_rlc_mult".to_string(),
                mpt_config.accumulators.key.mult,
                offset,
                || Value::known(pv.key_rlc_mult),
            )?;

            pv.node_index += 1;

            offset += 1;
        }

        /* EXTENSION */

        if pv.is_extension_node {
            for is_s in [true, false] {
                let row = &witness[offset];
                if is_s {
                    // [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,
                    // 48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

                    // One nibble:
                    // [226,16,160,172,105,12...
                    // Could also be non-hashed branch:
                    // [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,
                    // 128,128,128,128,128,128,128,128,128]

                    // [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                    // 213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,
                    // 128,128] [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                    // 0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,
                    // 128,128,128,128,128,128,128,128,128,128,128]

                    // Intermediate RLC value and mult (after key)
                    // to know which mult we need to use in c_advices.
                    pv.acc_s = F::zero();
                    pv.acc_mult_s = F::one();
                    let len: usize;
                    if row.get_byte(1) <= 32 {
                        // key length is 1
                        len = 2 // [length byte, key]
                    } else if row.get_byte(0) < 248 {
                        len = (row.get_byte(1) - 128) as usize + 2;
                    } else {
                        len = (row.get_byte(2) - 128) as usize + 3;
                    }
                    mpt_config.compute_acc_and_mult(
                        &row.bytes,
                        &mut pv.acc_s,
                        &mut pv.acc_mult_s,
                        0,
                        len,
                    );

                    // Final RLC value.
                    pv.acc_c = pv.acc_s;
                    pv.acc_mult_c = pv.acc_mult_s;
                    let mut start = C_RLP_START + 1;
                    let mut len = HASH_WIDTH + 1;
                    if row.get_byte(C_RLP_START + 1) == 0 {
                        // non-hashed branch in extension node
                        start = C_START;
                        len = HASH_WIDTH;
                    }
                    mpt_config.compute_acc_and_mult(
                        &row.bytes,
                        &mut pv.acc_c,
                        &mut pv.acc_mult_c,
                        start,
                        len,
                    );

                    mpt_config
                        .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                        .ok();
                } else {
                    let key_values = self.key_data.witness_load(
                        region,
                        base_offset,
                        &pv.memory[key_memory(true)],
                        0,
                    )?;
                    for is_s in [true, false] {
                        let is_placeholder = if is_s {
                            pv.is_branch_s_placeholder
                        } else {
                            pv.is_branch_c_placeholder
                        };
                        if !is_placeholder {
                            self.key_data.witness_store(
                                region,
                                base_offset,
                                &mut pv.memory[key_memory(is_s)],
                                pv.key_rlc,
                                pv.key_rlc_mult,
                                pv.nibbles_num,
                                pv.is_placeholder_leaf_s,
                                pv.is_placeholder_leaf_c,
                                0,
                                pv.nibbles_num % 2 == 1,
                                pv.key_rlc,
                                pv.key_rlc_mult,
                            )?;
                        } else {
                            println!("ext drifted pos: {}", pv.drifted_pos);
                            self.key_data.witness_store(
                                region,
                                base_offset,
                                &mut pv.memory[key_memory(is_s)],
                                key_values[0],
                                key_values[1],
                                key_values[2].get_lower_32() as usize,
                                pv.is_placeholder_leaf_s,
                                pv.is_placeholder_leaf_c,
                                pv.drifted_pos,
                                pv.nibbles_num % 2 == 1,
                                pv.extension_node_rlc,
                                pv.extension_node_mult,
                            )?;
                        }
                    }

                    // We use intermediate value from previous row (because
                    // up to acc_s it's about key and this is the same
                    // for both S and C).
                    pv.acc_c = pv.acc_s;
                    pv.acc_mult_c = pv.acc_mult_s;
                    let mut start = C_RLP_START + 1;
                    let mut len = HASH_WIDTH + 1;
                    if row.get_byte(C_RLP_START + 1) == 0 {
                        // non-hashed branch in extension node
                        start = C_START;
                        len = HASH_WIDTH;
                    }
                    mpt_config.compute_acc_and_mult(
                        &row.bytes,
                        &mut pv.acc_c,
                        &mut pv.acc_mult_c,
                        start,
                        len,
                    );

                    mpt_config
                        .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                        .ok();
                }
                region
                    .assign_advice(
                        || "assign key_rlc".to_string(),
                        mpt_config.accumulators.key.rlc,
                        offset,
                        || Value::known(pv.extension_node_rlc),
                    )
                    .ok();

                offset += 1;
            }
        } else {
            offset += 1;

            let key_values =
                self.key_data
                    .witness_load(region, base_offset, &pv.memory[key_memory(true)], 0)?;
            for is_s in [true, false] {
                let is_placeholder = if is_s {
                    pv.is_branch_s_placeholder
                } else {
                    pv.is_branch_c_placeholder
                };
                if !is_placeholder {
                    self.key_data.witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[key_memory(is_s)],
                        pv.key_rlc,
                        pv.key_rlc_mult,
                        pv.nibbles_num,
                        pv.is_placeholder_leaf_s,
                        pv.is_placeholder_leaf_c,
                        0,
                        pv.nibbles_num % 2 == 1,
                        pv.key_rlc,
                        pv.key_rlc_mult,
                    )?;
                } else {
                    println!("bra drifted pos: {}", pv.drifted_pos);
                    self.key_data.witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[key_memory(is_s)],
                        key_values[0],
                        key_values[1],
                        key_values[2].get_lower_32() as usize,
                        pv.is_placeholder_leaf_s,
                        pv.is_placeholder_leaf_c,
                        pv.drifted_pos,
                        pv.nibbles_num % 2 == 1,
                        key_values[0],
                        key_values[1],
                    )?;
                }
            }
        }

        Ok(())
    }
}

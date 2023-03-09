use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    helpers::{ListKeyGadget, MPTConstraintBuilder, ParentDataWitness},
    param::{ARITY, IS_BRANCH_C_PLACEHOLDER_POS},
    rlp_gadgets::{RLPItemGadget, RLPItemWitness, RLPListDataGadget},
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cell_manager::Cell,
        constraint_builder::RLCChainable,
        gadgets::{IsEqualGadget, IsZeroGadget, LtGadget},
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        helpers::{
            ext_key_rlc_calc_value, ext_key_rlc_expr, key_memory, parent_memory, Indexable,
            KeyData, ParentData,
        },
        param::RLP_NIL,
        FixedTableTag,
    },
    mpt_circuit::{
        helpers::{nibble_rlc, num_nibbles},
        param::{
            BRANCH_0_KEY_POS, DRIFTED_POS, HASH_WIDTH, IS_BRANCH_S_PLACEHOLDER_POS,
            IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
            IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
        },
    },
    mpt_circuit::{MPTConfig, MPTState},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct BranchChildConfig<F> {
    rlp: RLPItemGadget<F>,
    mult: Cell<F>,
    rlc_branch: Cell<F>,
    is_hashed: IsEqualGadget<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BranchConfig<F> {
    key_data: KeyData<F>,
    parent_data: [ParentData<F>; 2],
    rlp_list: [RLPListDataGadget<F>; 2],
    branches: [[BranchChildConfig<F>; ARITY]; 2],
    is_modified: [Cell<F>; ARITY],
    is_drifted: [Cell<F>; ARITY],
    mod_branch_rlc: [Cell<F>; 2],
    mod_branch_is_hashed: [Cell<F>; 2],
    mod_branch_is_empty: [IsZeroGadget<F>; 2],
    is_not_hashed: [LtGadget<F, 2>; 2],
    is_placeholder: [Cell<F>; 2],

    is_extension: Cell<F>,
    ext_rlp_key: ListKeyGadget<F>,
    ext_rlp_value: [RLPItemGadget<F>; 2],
    ext_mult: Cell<F>,
    ext_is_not_hashed: LtGadget<F, 2>,
    ext_is_key_part_odd: Cell<F>,
    ext_mult_key: Cell<F>,
}

impl<F: Field> BranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let r = ctx.r.clone();

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = BranchConfig::default();

        circuit!([meta, cb.base], {
            // Data
            let branch_bytes: [[Vec<Expression<F>>; ARITY]; 2] = [
                array_init::array_init(|i| ctx.s(meta, 1 + i as i32)),
                array_init::array_init(|i| ctx.c(meta, 1 + i as i32)),
            ];
            let ext_key_bytes: [Vec<Expression<F>>; 2] = [ctx.s(meta, 17), ctx.s(meta, 18)];
            let ext_value_bytes: [Vec<Expression<F>>; 2] = [ctx.c(meta, 17), ctx.c(meta, 18)];

            // General inputs
            config.is_extension = cb.base.query_cell();
            for is_s in [true, false] {
                config.is_placeholder[is_s.idx()] = cb.base.query_cell();
                require!(config.is_placeholder[is_s.idx()] => bool);
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

            /* Extension */

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
                config.ext_rlp_key = ListKeyGadget::construct(&mut cb.base, &ext_key_bytes[0]);
                // TODO(Brecht): add lookup constraint
                config.ext_is_key_part_odd = cb.base.query_cell();

                // We need to check that the nibbles we stored in s are between 0 and 15.
                cb.set_range_s(FixedTableTag::RangeKeyLen16.expr());

                let mut ext_branch_rlp_rlc = vec![0.expr(); 2];
                for is_s in [true, false] {
                    config.ext_rlp_value[is_s.idx()] = RLPItemGadget::construct(&mut cb.base, &ext_value_bytes[is_s.idx()]);

                    // In C we have nibbles, we check below only for S.
                    if is_s {
                        // RLP encoding checks: [key, branch]
                        // Verify that the lenghts are consistent.
                        require!(config.ext_rlp_key.rlp_list.len() => config.ext_rlp_key.key_value.num_bytes() + config.ext_rlp_value[is_s.idx()].num_bytes());

                        // Update the multiplier with the number of bytes on the first row
                        config.ext_mult = cb.base.query_cell();
                        require!((FixedTableTag::RMult, config.ext_rlp_key.num_bytes_on_key_row(), config.ext_mult.expr()) => @"fixed");
                    }

                    // Extension node RLC
                    let ext_node_rlc = (config.ext_rlp_key.rlc(&r), config.ext_mult.expr()).rlc_chain(
                        config.ext_rlp_value[is_s.idx()].rlc_rlp(&mut cb.base, &r)
                    );
                    // Branch value data zero check
                    cb.set_length_c(config.ext_rlp_value[is_s.idx()].num_bytes());

                    // The branch expected in the extension node
                    ext_branch_rlp_rlc[is_s.idx()] = config.ext_rlp_value[is_s.idx()].rlc_rlp(&mut cb.base, &r);

                    // Check if the extension node is in its parent.
                    let (rlc, num_bytes, is_not_hashed) = {
                        if is_s {
                            config.ext_is_not_hashed = LtGadget::construct(&mut cb.base, config.ext_rlp_key.rlp_list.num_bytes(), HASH_WIDTH.expr());
                        }
                        (ext_node_rlc.expr(), config.ext_rlp_key.rlp_list.num_bytes(), config.ext_is_not_hashed.expr())
                    };
                    // TODO(Brecht): why not if it's a placeholder?
                    ifx! {not!(config.is_placeholder[is_s.idx()]) => {
                        ifx!{or::expr(&[config.parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                            // Hashed branch hash in parent branch
                            require!((1, rlc, num_bytes, config.parent_data[is_s.idx()].rlc) => @"keccak");
                        } elsex {
                            // Non-hashed branch hash in parent branch
                            require!(rlc => config.parent_data[is_s.idx()].rlc);
                        }}
                    }}
                }

                // Extension key zero check
                cb.set_length(config.ext_rlp_key.num_bytes_on_key_row());

                // Calculate the number of bytes
                let key_len = config.ext_rlp_key.key_value.len();
                // Calculate the number of nibbles
                let num_nibbles = num_nibbles::expr(key_len.expr(), config.ext_is_key_part_odd.expr());
                // Make sure the nibble counter is updated correctly
                let num_nibbles = config.key_data.num_nibbles.expr() + num_nibbles.expr();

                // We need to take account the nibbles of the extension node.
                // The parity alternates when there's an even number of nibbles, remains the same otherwise
                let is_key_odd = ifx!{config.ext_is_key_part_odd => {
                    not!(config.key_data.is_odd)
                } elsex {
                    config.key_data.is_odd.expr()
                }};

                // Calculate the extension node key RLC when in an extension node
                // Currently, the extension node S and extension node C both have the same key RLC -
                // however, sometimes extension node can be replaced by a shorter extension node
                // (in terms of nibbles), this is still to be implemented.
                let key_rlc_post_ext = config.key_data.rlc.expr() +
                    ext_key_rlc_expr(
                        &mut cb.base,
                        config.ext_rlp_key.key_value.clone(),
                        config.key_data.mult.expr(),
                        config.ext_is_key_part_odd.expr(),
                        not!(is_key_odd),
                        ext_key_bytes.clone(),
                        &ctx.r
                );

                // Get the length of the key
                // Unless both parts of the key are odd, subtract 1 from the key length.
                let key_len = config.ext_rlp_key.key_value.len();
                let key_num_bytes_for_mult = key_len - ifx! {not!(config.key_data.is_odd.expr() * config.ext_is_key_part_odd.expr()) => { 1.expr() }};
                // Get the multiplier for this key length
                config.ext_mult_key = cb.base.query_cell();
                require!((FixedTableTag::RMult, key_num_bytes_for_mult, config.ext_mult_key.expr()) => @"fixed");

                (
                    num_nibbles,
                    is_key_odd,
                    key_rlc_post_ext,
                    config.key_data.mult.expr() * config.ext_mult_key.expr(),
                    false.expr(),
                    false.expr(),
                    ext_branch_rlp_rlc[true.idx()].expr(),
                    ext_branch_rlp_rlc[false.idx()].expr(),
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
            let is_root = [is_root_s, is_root_c];
            let parent_rlc = [parent_rlc_s, parent_rlc_c];

            /* Branch */

            let mut num_bytes_left = vec![0.expr(); 2];
            let mut branch_node_rlc = vec![0.expr(); 2];
            let mut mult = vec![1.expr(); 2];
            for is_s in [true, false] {
                // Read the list
                config.rlp_list[is_s.idx()] = RLPListDataGadget::construct(&mut cb.base);
                // Start the RLC encoding of the branch
                (branch_node_rlc[is_s.idx()], mult[is_s.idx()]) =
                    config.rlp_list[is_s.idx()].rlp_list.rlc_rlp_only(&r);

                // Keep track of how many bytes the branch contains to make sure it's correct.
                num_bytes_left[is_s.idx()] = config.rlp_list[is_s.idx()].rlp_list.len();

                config.mod_branch_rlc[is_s.idx()] = cb.base.query_cell();
                config.mod_branch_is_hashed[is_s.idx()] = cb.base.query_cell();

                // Check if the branch is hashed or not
                config.is_not_hashed[is_s.idx()] = LtGadget::construct(
                    &mut cb.base,
                    config.rlp_list[is_s.idx()].rlp_list.num_bytes(),
                    HASH_WIDTH.expr(),
                );
            }

            // Process the branch children
            let mut mod_branch_len = vec![0.expr(); 2];
            let mut modified_index = 0.expr();
            let mut drifted_index = 0.expr();
            for node_index in 0..ARITY {
                config.is_modified[node_index] = cb.base.query_cell();
                config.is_drifted[node_index] = cb.base.query_cell();
                require!(config.is_modified[node_index] => bool);
                require!(config.is_drifted[node_index] => bool);

                // Calculate the modified and drifted index from `is_modified`/`is_drifted`
                modified_index = modified_index.expr()
                    + config.is_modified[node_index].expr() * node_index.expr();
                drifted_index =
                    drifted_index.expr() + config.is_drifted[node_index].expr() * node_index.expr();

                for is_s in [true, false] {
                    let branch = &mut config.branches[is_s.idx()][node_index];
                    // Read the branch
                    branch.rlp = RLPItemGadget::construct(
                        &mut cb.base,
                        &branch_bytes[is_s.idx()][node_index],
                    );
                    let num_bytes = branch.rlp.num_bytes();
                    // Bookkeeping for RLC
                    branch.mult = cb.base.query_cell();
                    let mult_diff = branch.mult.expr();
                    require!((FixedTableTag::RMult, num_bytes.expr(), mult_diff) => @format!("fixed"));
                    // RLC bytes zero check
                    cb.set_length_sc(is_s, num_bytes.expr());

                    // Keep track of how many bytes of the list we've processed
                    num_bytes_left[is_s.idx()] =
                        num_bytes_left[is_s.idx()].expr() - num_bytes.expr();

                    // Update the full branch node RLC with the data of this branch
                    branch_node_rlc[is_s.idx()] =
                        (branch_node_rlc[is_s.idx()].expr(), mult[is_s.idx()].expr())
                            .rlc_chain(branch.rlp.rlc_rlp(&mut cb.base, &r));

                    // Store the rlc of the branch
                    // TODO(Brecht): useless now, but useful when this work is spread over multiple
                    // rows
                    branch.rlc_branch = cb.base.query_cell();
                    require!(branch.rlc_branch => branch.rlp.rlc_branch(&r));

                    // Store if this branch is hashed
                    branch.is_hashed =
                        IsEqualGadget::construct(&mut cb.base, branch.rlp.len(), 32.expr());

                    // Update the branch node multiplier
                    mult[is_s.idx()] = mult[is_s.idx()].expr() * mult_diff;

                    // Calculate the length of the modified branch
                    mod_branch_len[is_s.idx()] = mod_branch_len[is_s.idx()].expr()
                        + branch.rlp.len() * config.is_modified[node_index].expr();

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
                    // TODO(Brecht): still need to check that `modified_index != drifted_index`?
                    ifx! {config.is_placeholder[is_s.idx()] => {
                        ifx! {or::expr(&[config.is_modified[node_index].expr(), config.is_drifted[node_index].expr()]) => {
                            require!(branch.rlp.len() => HASH_WIDTH);
                        } elsex {
                            require!(branch.rlp.len() => 0);
                        }}
                    }}
                }

                // We need to ensure that the only change in `S` and `C` proof occurs
                // at `modified_index` so that only a single change can be done.
                // TODO(Brecht): optimize, only insert the modified branch in the circuit
                ifx! {not!(config.is_modified[node_index]) => {
                    let branch_s = config.branches[true.idx()][node_index].rlp.rlc_rlp(&mut cb.base, &r);
                    let branch_c = config.branches[false.idx()][node_index].rlp.rlc_rlp(&mut cb.base, &r);
                    require!(branch_s => branch_c);
                }}
            }
            for is_s in [true, false] {
                // Number of bytes left needs to be 1 because ValueNode which occupies 1 byte
                require!(num_bytes_left[is_s.idx()] => 1);
                // TODO: acc currently doesn'thave branch ValueNode info (which 128 if nil)
                branch_node_rlc[is_s.idx()] =
                    (branch_node_rlc[is_s.idx()].expr(), mult[is_s.idx()].expr())
                        .rlc_chain(RLP_NIL.expr());

                // Check if the modified branch is empty, and so a placeholder leaf will follow
                config.mod_branch_is_empty[is_s.idx()] =
                    IsZeroGadget::construct(&mut cb.base, mod_branch_len[is_s.idx()].expr());
            }

            // `is_modified` needs to be set to 1 at exactly 1 branch child
            let is_modified_values = (0..ARITY)
                .map(|rot| config.is_modified[rot].expr())
                .collect::<Vec<_>>();
            require!(sum::expr(&is_modified_values) => 1);

            // When there's a placeholder, `is_drifted` needs to be set to 1 at exactly 1
            // branch child
            ifx! {or::expr(&[config.is_placeholder[true.idx()].expr(), config.is_placeholder[false.idx()].expr()]) => {
                let is_drifted_values = (0..ARITY).map(|rot| config.is_drifted[rot].expr()).collect::<Vec<_>>();
                require!(sum::expr(&is_drifted_values) => 1);
            }}

            // Check if the branch is in its parent
            for is_s in [true, false] {
                let (rlc, num_bytes, is_not_hashed) = {
                    (
                        branch_node_rlc[is_s.idx()].expr(),
                        config.rlp_list[is_s.idx()].rlp_list.num_bytes(),
                        config.is_not_hashed[is_s.idx()].expr(),
                    )
                };

                // TODO(Brecht): should not need is_extension check
                ifx! {not!(config.is_extension) => {
                    ifx! {not!(config.is_placeholder[is_s.idx()]) => {
                        ifx!{or::expr(&[is_root[is_s.idx()].expr(), not!(is_not_hashed)]) => {
                            // Hashed branch hash in parent branch
                            require!((1, rlc, num_bytes, parent_rlc[is_s.idx()].expr()) => @"keccak");
                        } elsex {
                            // Non-hashed branch hash in parent branch
                            require!(rlc => parent_rlc[is_s.idx()].expr());
                        }}
                    }}
                }}
            }

            // Update the key RLC and multiplier for the branch nibble.
            let (key_rlc_post_branch, key_mult_post_branch) = nibble_rlc(
                &mut cb.base,
                key_rlc_post_ext.expr(),
                key_mult_post_ext.expr(),
                is_key_odd.expr(),
                modified_index.expr(),
                &r,
            );
            // Also calculate the key RLC and multiplier for the drifted nibble.
            let (key_rlc_post_drifted, key_mult_post_drifted) = nibble_rlc(
                &mut cb.base,
                key_rlc_post_ext.expr(),
                key_mult_post_ext.expr(),
                is_key_odd.expr(),
                drifted_index.expr(),
                &r,
            );

            // Update the nibble counter
            let num_nibbles = num_nibbles + 1.expr();
            // Update key parity
            let is_key_odd = not!(is_key_odd);

            // Set the new keys
            for is_s in [true, false] {
                ifx! {not!(config.is_placeholder[is_s.idx()].expr()) => {
                    KeyData::store(
                        &mut cb.base,
                        &ctx.memory[key_memory(is_s)],
                        [
                            key_rlc_post_branch.expr(),
                            key_mult_post_branch.expr(),
                            num_nibbles.expr(),
                            is_key_odd.expr(),
                            false.expr(),
                            0.expr(),
                            0.expr(),
                        ],
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
                            is_key_odd.expr(),
                            key_rlc_post_drifted.expr(),
                            key_mult_post_drifted.expr(),
                        ],
                    );
                }}
            }

            // Set the branch we'll take
            for node_index in 0..ARITY {
                for is_s in [true, false] {
                    ifx! {config.is_placeholder[is_s.idx()] => {
                        ifx!{config.is_drifted[node_index].expr() => {
                            let child_rlc = config.branches[(!is_s).idx()][node_index].rlp.rlc_branch(&r);
                            require!(config.mod_branch_rlc[is_s.idx()] => child_rlc);
                            ParentData::store(
                                &mut cb.base,
                                &ctx.memory[parent_memory(is_s)],
                                [config.parent_data[is_s.idx()].rlc.expr(), config.parent_data[is_s.idx()].is_root.expr(), true.expr(), child_rlc]
                            );
                        }}
                    } elsex {
                        ifx!{config.is_modified[node_index].expr() => {
                            let child_rlc = config.branches[is_s.idx()][node_index].rlp.rlc_branch(&r);
                            require!(config.mod_branch_rlc[is_s.idx()] => child_rlc);
                            ParentData::store(
                                &mut cb.base,
                                &ctx.memory[parent_memory(is_s)],
                                [child_rlc.expr(), false.expr(), false.expr(), child_rlc]
                            );
                        }}
                    }}
                }
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

        let modified_index = row_init.get_byte(BRANCH_0_KEY_POS) as usize;
        let mut drifted_index = row_init.get_byte(DRIFTED_POS) as usize;
        // If no placeholder branch, we set `drifted_pos = modified_node`. This
        // is needed just to make some other constraints (`s_mod_node_hash_rlc`
        // and `c_mod_node_hash_rlc` correspond to the proper node) easier to write.
        if !is_placeholder[true.idx()] && !is_placeholder[false.idx()] {
            drifted_index = modified_index;
        }

        let is_extension_node = row_init.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row_init.get_byte(IS_EXT_LONG_ODD_C1_POS)
            + row_init.get_byte(IS_EXT_SHORT_C16_POS)
            + row_init.get_byte(IS_EXT_SHORT_C1_POS)
            + row_init.get_byte(IS_EXT_LONG_EVEN_C16_POS)
            + row_init.get_byte(IS_EXT_LONG_EVEN_C1_POS)
            == 1;

        // Data
        let branch_list_rlp_bytes = [
            row_init.rlp_bytes[0..3].to_owned(),
            row_init.rlp_bytes[3..6].to_owned(),
        ];
        let branch_bytes: [[Vec<u8>; ARITY]; 2] = [
            array_init::array_init(|i| witness[idx + 1 + i].s()),
            array_init::array_init(|i| witness[idx + 1 + i].c()),
        ];
        let ext_list_rlp_bytes = witness[idx + 17].rlp_bytes.to_owned();
        let ext_key_bytes: [Vec<u8>; 2] = [witness[idx + 17].s(), witness[idx + 18].s()];
        let ext_value_bytes: [Vec<u8>; 2] = [witness[idx + 17].c(), witness[idx + 18].c()];

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
        }

        let mut num_nibbles = key_data.num_nibbles;
        let mut key_rlc_post_ext = key_data.rlc;
        let mut key_mult_post_ext = key_data.mult;
        let mut is_key_odd = key_data.is_odd;

        /* Extension */

        if is_extension_node {
            let ext_rlp_key = self.ext_rlp_key.assign(
                region,
                offset,
                &ext_list_rlp_bytes,
                &ext_key_bytes[true.idx()],
            )?;

            let mut ext_mult = F::one();
            for _ in 0..ext_rlp_key.num_bytes_on_key_row() {
                ext_mult *= mpt_config.r;
            }
            self.ext_mult.assign(region, offset, ext_mult)?;

            let ext_is_key_part_odd =
                ext_key_bytes[0][ext_rlp_key.key_value.num_rlp_bytes()] >> 4 == 1;
            self.ext_is_key_part_odd
                .assign(region, offset, ext_is_key_part_odd.scalar())?;

            self.ext_is_not_hashed.assign(
                region,
                offset,
                ext_rlp_key.rlp_list.num_bytes().scalar(),
                HASH_WIDTH.scalar(),
            )?;

            let mut key_len_mult = ext_rlp_key.key_value.len();
            if !(is_key_odd && ext_is_key_part_odd) {
                key_len_mult -= 1;
            }

            // Update number of nibbles
            num_nibbles += num_nibbles::value(ext_rlp_key.key_value.len(), ext_is_key_part_odd);

            // Update parity
            is_key_odd = if ext_is_key_part_odd {
                !is_key_odd
            } else {
                is_key_odd
            };

            // Key RLC
            let (key_rlc_ext, _) = ext_key_rlc_calc_value(
                ext_rlp_key.key_value.clone(),
                key_data.mult,
                ext_is_key_part_odd,
                !is_key_odd,
                ext_key_bytes.clone(),
                mpt_config.r,
            );
            key_rlc_post_ext = key_data.rlc + key_rlc_ext;

            // Key mult
            let mut ext_mult_key = 1.scalar();
            for _ in 0..key_len_mult {
                ext_mult_key = ext_mult_key * mpt_config.r;
            }
            self.ext_mult_key.assign(region, offset, ext_mult_key)?;
            key_mult_post_ext = key_data.mult * ext_mult_key;
        }
        for is_s in [true, false] {
            self.ext_rlp_value[is_s.idx()].assign(region, offset, &ext_value_bytes[is_s.idx()])?;
        }

        /* Branch */

        for is_s in [true, false] {
            let rlp_list_witness = self.rlp_list[is_s.idx()].assign(
                region,
                offset,
                &branch_list_rlp_bytes[is_s.idx()],
            )?;

            self.is_placeholder[is_s.idx()].assign(
                region,
                offset,
                is_placeholder[is_s.idx()].scalar(),
            )?;
            self.is_not_hashed[is_s.idx()].assign(
                region,
                offset,
                rlp_list_witness.num_bytes().scalar(),
                HASH_WIDTH.scalar(),
            )?;
        }

        let mut mod_node_hash_rlc = [0.scalar(); 2];
        let mut branch_witnesses = vec![vec![RLPItemWitness::default(); ARITY]; 2];
        for node_index in 0..ARITY {
            for is_s in [true, false] {
                let child_witness = self.branches[is_s.idx()][node_index].rlp.assign(
                    region,
                    offset,
                    &branch_bytes[is_s.idx()][node_index],
                )?;
                branch_witnesses[is_s.idx()][node_index] = child_witness.clone();

                let mut node_mult_diff = F::one();
                for _ in 0..child_witness.num_bytes() {
                    node_mult_diff *= mpt_config.r;
                }

                self.branches[is_s.idx()][node_index].mult.assign(
                    region,
                    offset,
                    node_mult_diff,
                )?;
                self.branches[is_s.idx()][node_index].rlc_branch.assign(
                    region,
                    offset,
                    child_witness.rlc_branch(mpt_config.r),
                )?;
                let _is_hashed = self.branches[is_s.idx()][node_index].is_hashed.assign(
                    region,
                    offset,
                    child_witness.len().scalar(),
                    32.scalar(),
                )?;
            }
            self.is_modified[node_index].assign(
                region,
                offset,
                (node_index == modified_index).scalar(),
            )?;
            self.is_drifted[node_index].assign(
                region,
                offset,
                (node_index == drifted_index).scalar(),
            )?;
        }

        for is_s in [true, false] {
            let (mod_is_s, mod_pos) = if is_placeholder[is_s.idx()] {
                (!is_s, drifted_index)
            } else {
                (is_s, modified_index)
            };
            mod_node_hash_rlc[is_s.idx()] =
                branch_witnesses[mod_is_s.idx()][mod_pos].rlc_branch(mpt_config.r);
            self.mod_branch_rlc[is_s.idx()].assign(
                region,
                offset,
                mod_node_hash_rlc[is_s.idx()],
            )?;
            let is_hashed = branch_witnesses[mod_is_s.idx()][mod_pos].len() == 32;
            self.mod_branch_is_hashed[is_s.idx()].assign(region, offset, is_hashed.scalar())?;
        }

        let mut is_placeholder_leaf = [0.scalar(); 2];
        for is_s in [true, false] {
            is_placeholder_leaf[is_s.idx()] = self.mod_branch_is_empty[is_s.idx()].assign(
                region,
                offset,
                branch_witnesses[is_s.idx()][modified_index].len().scalar(),
            )?;
        }

        // one nibble is used for position in branch
        num_nibbles += 1;

        // Update key parity
        let is_key_odd = !is_key_odd;

        // Update the key RLC and multiplier for the branch nibble.
        let (nibble_mult, mult): (F, F) = if is_key_odd {
            // The nibble will be added as the most significant nibble using the same
            // multiplier
            (16.scalar(), 1.scalar())
        } else {
            // The nibble will be added as the least significant nibble, the multiplier
            // needs to advance
            (1.scalar(), mpt_config.r)
        };
        let key_rlc_post_branch =
            key_rlc_post_ext + F::from(modified_index as u64) * nibble_mult * key_mult_post_ext;
        let key_rlc_post_drifted =
            key_rlc_post_ext + F::from(drifted_index as u64) * nibble_mult * key_mult_post_ext;
        let key_mult_post_branch = key_mult_post_ext * mult;

        // Set the new key
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
            }
        }
        // Set the new parents
        for is_s in [true, false] {
            if !is_placeholder[is_s.idx()] {
                ParentData::witness_store(
                    region,
                    offset,
                    &mut pv.memory[parent_memory(is_s)],
                    mod_node_hash_rlc[is_s.idx()],
                    false,
                    false,
                    mod_node_hash_rlc[is_s.idx()],
                )?;
            } else {
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

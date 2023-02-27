use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::{Region},
    plonk::{Error, VirtualCells, Expression},
};

use super::{
    helpers::{MPTConstraintBuilder, RLPListGadget, RLPItemGadget, LeafKeyGadget, RLPItemWitness},
    param::{
        ARITY, IS_BRANCH_C_PLACEHOLDER_POS,
    },
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cell_manager::{Cell},
        constraint_builder::{RLCChainable}, gadgets::{IsEqualGadget, LtGadget, IsZeroGadget},
    },
    mpt_circuit::{
        helpers::{
            get_num_nibbles, key_memory, parent_memory, Indexable,
            KeyData, ParentData,
        },
        param::{RLP_NIL},
        FixedTableTag,
    },
    mpt_circuit::{
        param::{
            BRANCH_0_KEY_POS,
            DRIFTED_POS, HASH_WIDTH,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
            IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS,
            IS_EXT_SHORT_C1_POS,
        },
    },
    mpt_circuit::{witness_row::MptWitnessRow},
    mpt_circuit::{MPTConfig, ProofValues},
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
    rlp_list: [RLPListGadget<F>; 2],
    branches: [[BranchChildConfig<F>; ARITY]; 2],
    is_modified: [Cell<F>; ARITY],
    is_drifted: [Cell<F>; ARITY],
    mod_branch_rlc: [Cell<F>; 2],
    mod_branch_is_hashed: [Cell<F>; 2],
    mod_branch_is_empty: [IsZeroGadget<F>; 2],
    is_not_hashed: [LtGadget<F, 2>; 2],
    is_placeholder: [Cell<F>; 2],

    is_extension: Cell<F>,
    ext_rlp_key: LeafKeyGadget<F>,
    ext_rlp_value: [RLPItemGadget<F>; 2],
    ext_mult_key: Cell<F>,
    ext_is_not_hashed: LtGadget<F, 2>,
    ext_is_key_part_odd: Cell<F>,
    ext_mult_key_len: Cell<F>,
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
            let offset = -1;

            // Data
            let rlp_bytes = [ctx.expr(meta, -1)[4..7].to_owned(), ctx.expr(meta, -1)[7..10].to_owned()];
            let branch_bytes: [[Vec<Expression<F>>; ARITY]; 2] = [
                array_init::array_init(|i| ctx.expr(meta, i as i32)[0..34].to_owned()),
                array_init::array_init(|i| ctx.expr(meta, i as i32)[34..68].to_owned()),
            ];
            let ext_key_bytes: [Vec<Expression<F>>; 2] = [
                ctx.expr(meta, offset + 17)[0..34].to_owned(),
                ctx.expr(meta, offset + 18)[0..34].to_owned(),
            ];
            let ext_value_bytes: [Vec<Expression<F>>; 2] = [
                ctx.expr(meta, offset + 17)[34..68].to_owned(),
                ctx.expr(meta, offset + 18)[34..68].to_owned(),
            ];

            // General inputs
            config.is_extension = cb.base.query_cell();
            for is_s in [true, false] {
                config.is_placeholder[is_s.idx()] = cb.base.query_cell();
                require!(config.is_placeholder[is_s.idx()] => bool);
            }

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
                config.ext_rlp_key = LeafKeyGadget::construct(&mut cb.base, &ext_key_bytes[0]);
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
                        require!(config.ext_rlp_key.len() => config.ext_rlp_key.key_num_bytes() + config.ext_rlp_value[is_s.idx()].num_bytes());

                        // Update the multiplier with the number of bytes on the first row
                        config.ext_mult_key = cb.base.query_cell();
                        require!((FixedTableTag::RMult, config.ext_rlp_key.num_bytes_on_key_row(), config.ext_mult_key.expr()) => @"fixed");
                    }

                    // Extension node RLC
                    let ext_node_rlc = (config.ext_rlp_key.rlc(&r), config.ext_mult_key.expr()).rlc_chain(
                        config.ext_rlp_value[is_s.idx()].rlc_rlp(&mut cb.base, &r)
                    );
                    // Branch value data zero check
                    cb.set_length_c(config.ext_rlp_value[is_s.idx()].num_bytes());

                    // The branch expected in the extension node
                    ext_branch_rlp_rlc[is_s.idx()] = config.ext_rlp_value[is_s.idx()].rlc_rlp(&mut cb.base, &r);

                    // Check if the extension node is in its parent.
                    let (rlc, num_bytes, is_not_hashed) = {
                        if is_s {
                            config.ext_is_not_hashed = LtGadget::construct(&mut cb.base, config.ext_rlp_key.num_bytes(), HASH_WIDTH.expr());
                        }
                        (ext_node_rlc.expr(), config.ext_rlp_key.num_bytes(), config.ext_is_not_hashed.expr())
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
                let key_len = config.ext_rlp_key.key_len();
                // Calculate the number of nibbles
                let num_nibbles = get_num_nibbles(key_len.expr(), config.ext_is_key_part_odd.expr());
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
                // TODO: extension nodes of different nibbles length
                let key_rlc_post_ext = config.key_data.rlc.expr() +
                    config.ext_rlp_key.ext_key_rlc(
                        &mut cb.base,
                        config.key_data.mult.expr(),
                        config.ext_is_key_part_odd.expr(),
                        not!(is_key_odd),
                        ext_key_bytes.clone(),
                        &ctx.r
                );

                // Get the length of the key
                // Unless both parts of the key are odd, subtract 1 from the key length.
                let key_len = config.ext_rlp_key.key_len();
                let key_num_bytes_for_mult = key_len - ifx! {not!(config.key_data.is_odd.expr() * config.ext_is_key_part_odd.expr()) => { 1.expr() }};
                // Get the multiplier for this key length
                config.ext_mult_key_len = cb.base.query_cell();
                require!((FixedTableTag::RMult, key_num_bytes_for_mult, config.ext_mult_key_len.expr()) => @"fixed");

                (
                    num_nibbles,
                    is_key_odd,
                    key_rlc_post_ext,
                    config.key_data.mult.expr() * config.ext_mult_key_len.expr(),
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
                config.rlp_list[is_s.idx()] = RLPListGadget::construct(&mut cb.base, &rlp_bytes[is_s.idx()]);
                // Start the RLC encoding of the branch
                (branch_node_rlc[is_s.idx()], mult[is_s.idx()]) = config.rlp_list[is_s.idx()].rlc_rlp(&r);

                // Keep track of how many bytes the branch contains to make sure it's correct.
                num_bytes_left[is_s.idx()] = config.rlp_list[is_s.idx()].len();

                config.mod_branch_rlc[is_s.idx()] = cb.base.query_cell();
                config.mod_branch_is_hashed[is_s.idx()] = cb.base.query_cell();

                // Check if the branch is hashed or not
                config.is_not_hashed[is_s.idx()] = LtGadget::construct(&mut cb.base, config.rlp_list[is_s.idx()].num_bytes(), HASH_WIDTH.expr());
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
                modified_index = modified_index.expr() + config.is_modified[node_index].expr() * node_index.expr();
                drifted_index = drifted_index.expr() + config.is_drifted[node_index].expr() * node_index.expr();

                for is_s in [true, false] {
                    let branch = &mut config.branches[is_s.idx()][node_index];
                    // Read the branch
                    branch.rlp = RLPItemGadget::construct(&mut cb.base, &branch_bytes[is_s.idx()][node_index]);
                    let num_bytes = branch.rlp.num_bytes();
                    // Bookkeeping for RLC
                    branch.mult = cb.base.query_cell();
                    let mult_diff = branch.mult.expr();
                    require!((FixedTableTag::RMult, num_bytes.expr(), mult_diff) => @format!("fixed"));
                    // RLC bytes zero check
                    cb.set_length_sc(is_s, num_bytes.expr());

                    // Keep track of how many bytes of the list we've processed
                    num_bytes_left[is_s.idx()] = num_bytes_left[is_s.idx()].expr() - num_bytes.expr();

                    // Update the full branch node RLC with the data of this branch
                    branch_node_rlc[is_s.idx()] = (branch_node_rlc[is_s.idx()].expr(), mult[is_s.idx()].expr()).rlc_chain(
                        branch.rlp.rlc_rlp(&mut cb.base, &r)
                    );

                    // Store the rlc of the branch
                    // TODO(Brecht): useless now, but useful when this work is spread over multiple rows
                    branch.rlc_branch = cb.base.query_cell();
                    require!(branch.rlc_branch => branch.rlp.rlc_branch(&r));

                    // Store if this branch is hashed
                    branch.is_hashed = IsEqualGadget::construct(&mut cb.base, branch.rlp.len(), 32.expr());

                    // Update the branch node multiplier
                    mult[is_s.idx()] = mult[is_s.idx()].expr() * mult_diff;

                    // Calculate the length of the modified branch
                    mod_branch_len[is_s.idx()] = mod_branch_len[is_s.idx()].expr() + branch.rlp.len() * config.is_modified[node_index].expr();

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
                ifx!{not!(config.is_modified[node_index]) => {
                    let branch_s = config.branches[true.idx()][node_index].rlp.rlc_rlp(&mut cb.base, &r);
                    let branch_c = config.branches[false.idx()][node_index].rlp.rlc_rlp(&mut cb.base, &r);
                    require!(branch_s => branch_c);
                }}
            }
            for is_s in [true, false] {
                // Number of bytes left needs to be 1 because ValueNode which occupies 1 byte
                require!(num_bytes_left[is_s.idx()] => 1);
                // TODO: acc currently doesn'thave branch ValueNode info (which 128 if nil)
                branch_node_rlc[is_s.idx()] = (branch_node_rlc[is_s.idx()].expr(), mult[is_s.idx()].expr()).rlc_chain(RLP_NIL.expr());

                // Check if the modified branch is empty, and so a placeholder leaf will follow
                config.mod_branch_is_empty[is_s.idx()] = IsZeroGadget::construct(&mut cb.base, mod_branch_len[is_s.idx()].expr());
            }

            // `is_modified` needs to be set to 1 at exactly 1 branch child
            let is_modified_values = (0..ARITY)
                .map(|rot| config.is_modified[rot].expr())
                .collect::<Vec<_>>();
            require!(sum::expr(&is_modified_values) => 1);

            // When there's a placeholder, `is_drifted` needs to be set to 1 at exactly 1 branch child
            ifx! {or::expr(&[config.is_placeholder[true.idx()].expr(), config.is_placeholder[false.idx()].expr()]) => {
                let is_drifted_values = (0..ARITY).map(|rot| config.is_drifted[rot].expr()).collect::<Vec<_>>();
                require!(sum::expr(&is_drifted_values) => 1);
            }}

            // Check if the branch is in its parent
            for is_s in [true, false] {
                let (rlc, num_bytes, is_not_hashed) = {
                    (branch_node_rlc[is_s.idx()].expr(), config.rlp_list[is_s.idx()].num_bytes(), config.is_not_hashed[is_s.idx()].expr())
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

            // Set the branch we'll take
            for node_index in 0..ARITY {
                for is_s in [true, false] {
                    ifx! {config.is_placeholder[is_s.idx()] => {
                        ifx!{config.is_drifted[node_index].expr() => {
                            // TODO(Brecht): should we actually do !is_s
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

            // Update the nibble counter
            let num_nibbles = num_nibbles + 1.expr();

            // Update key parity
            let is_key_odd = not!(is_key_odd);

            // Update the key RLC and multiplier for the branch nibble.
            let (nibble_mult, mult) = ifx! {is_key_odd.expr() => {
                // The nibble will be added as the most significant nibble using the same multiplier
                (16.expr(), 1.expr())
            } elsex {
                // The nibble will be added as the least significant nibble, the multiplier needs to advance
                (1.expr(), r[0].expr())
            }};
            let key_rlc_post_branch = key_rlc_post_ext.expr() + modified_index.expr() * nibble_mult.expr() * key_mult_post_ext.expr();
            let key_mult_post_branch = key_mult_post_ext.expr() * mult.expr();

            // TODO(Brecht): Probably best to add checks that when placeholder another branch cannot follow etc..
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
                            config.mod_branch_is_empty[true.idx()].expr(),
                            config.mod_branch_is_empty[false.idx()].expr(),
                            0.expr(),
                            is_key_odd.expr(),
                            key_rlc_post_branch.expr(),
                            key_mult_post_branch.expr(),
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
                            config.mod_branch_is_empty[true.idx()].expr(),
                            config.mod_branch_is_empty[false.idx()].expr(),
                            drifted_index.expr(),
                            is_key_odd.expr(),
                            key_rlc_post_ext.expr(),
                            key_mult_post_ext.expr(),
                        ],
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
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let base_offset = offset;
        let offset = offset - 1;

        let row_init = witness[offset].to_owned();
        //let row_branches: [MptWitnessRow<F>; ARITY] = array_init::array_init(|i| witness[offset + 1 + i].to_owned());
        let row_ext_s = witness[offset + 1 + ARITY].to_owned();

        let rlp_bytes = [
            row_init.bytes[4..7].to_owned(),
            row_init.bytes[7..10].to_owned(),
        ];
        let branch_bytes: [[Vec<u8>; ARITY]; 2] = [
            array_init::array_init(|i| witness[base_offset + i].bytes[0..34].to_owned()),
            array_init::array_init(|i| witness[base_offset + i].bytes[34..68].to_owned()),
        ];
        let ext_key_bytes: [Vec<u8>; 2] = [
            witness[offset + 17].bytes[0..34].to_owned(),
            witness[offset + 18].bytes[0..34].to_owned(),
        ];
        let ext_value_bytes: [Vec<u8>; 2] = [
            witness[offset + 17].bytes[34..68].to_owned(),
            witness[offset + 18].bytes[34..68].to_owned(),
        ];

        pv.modified_node = row_init.get_byte(BRANCH_0_KEY_POS);
        pv.drifted_pos = row_init.get_byte(DRIFTED_POS);

        pv.is_even =
            row_init.get_byte(IS_EXT_LONG_EVEN_C16_POS) + row_init.get_byte(IS_EXT_LONG_EVEN_C1_POS) == 1;
        pv.is_odd = row_init.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row_init.get_byte(IS_EXT_LONG_ODD_C1_POS)
            + row_init.get_byte(IS_EXT_SHORT_C16_POS)
            + row_init.get_byte(IS_EXT_SHORT_C1_POS)
            == 1;
        let is_extension_node = pv.is_even || pv.is_odd;

        pv.is_branch_s_placeholder = row_init.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 1;
        pv.is_branch_c_placeholder = row_init.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 1;

        let is_placeholder = [
            pv.is_branch_s_placeholder,
            pv.is_branch_c_placeholder,
        ];

        // If no placeholder branch, we set `drifted_pos = modified_node`. This
        // is needed just to make some other constraints (`s_mod_node_hash_rlc`
        // and `c_mod_node_hash_rlc` correspond to the proper node) easier to write.
        if !is_placeholder[true.idx()] && !is_placeholder[false.idx()] {
            pv.drifted_pos = pv.modified_node;
        }

        let modified_index = pv.modified_node as usize;
        let drifted_index = pv.drifted_pos as usize;

        self.is_extension.assign(region, base_offset, is_extension_node.scalar())?;

        let key_values = self.key_data.witness_load(
            region,
            base_offset,
            &pv.memory[key_memory(true)],
            0,
        )?;

        /* Extension */

        let ext_key_witness = self.ext_rlp_key.assign(region, base_offset, &ext_key_bytes[0])?;
        let mut ext_is_key_part_odd = false;
        if is_extension_node {
            let first_byte_index = if ext_key_witness.rlp_list.is_short() {
                if ext_key_witness.short_list_value.is_short() {
                    1
                } else {
                    2
                }
            } else {
                if ext_key_witness.short_list_value.is_long() {
                    2
                } else {
                    3
                }
            };
            ext_is_key_part_odd = ext_key_bytes[0][first_byte_index] >> 4 == 1;
            self.ext_is_not_hashed.assign(region, base_offset, ext_key_witness.num_bytes().scalar(), HASH_WIDTH.scalar())?;
            self.ext_is_key_part_odd.assign(region, base_offset, ext_is_key_part_odd.scalar())?;
            let mut ext_mult_key= F::one();
            for _ in 0..ext_key_witness.num_bytes_on_key_row() {
                ext_mult_key *= mpt_config.randomness;
            }
            self.ext_mult_key.assign(region, base_offset, ext_mult_key)?;
        }
        for is_s in [true, false] {
            self.ext_rlp_value[is_s.idx()].assign(region, base_offset, &ext_value_bytes[is_s.idx()])?;
        }

        pv.key_rlc_prev = pv.key_rlc;
        pv.key_rlc_mult_prev = pv.key_rlc_mult;

        let mut key_rlc_post_ext = pv.key_rlc;
        let mut key_mult_post_ext = pv.key_rlc_mult;
        let mut is_key_odd = pv.nibbles_num % 2 == 1;
        if is_extension_node {
            is_key_odd = if ext_is_key_part_odd {
                !is_key_odd
            } else {
                is_key_odd
            };

            let (key_rlc_ext, _) = ext_key_witness.ext_key_rlc(
            pv.key_rlc_mult,
                ext_is_key_part_odd,
                !is_key_odd,
                ext_key_bytes.clone(),
                mpt_config.randomness,
            );
            key_rlc_post_ext = pv.key_rlc + key_rlc_ext;

            let mut key_len = ext_key_witness.key_len();
            if !((key_values[3].get_lower_32() % 2 == 1) && ext_is_key_part_odd) {
                key_len -= 1;
            }
            let mut ext_mult_key_len = 1.scalar();
            for _ in 0..key_len {
                ext_mult_key_len = ext_mult_key_len * mpt_config.randomness;
            }
            self.ext_mult_key_len.assign(region, base_offset, ext_mult_key_len)?;

            key_mult_post_ext = pv.key_rlc_mult * ext_mult_key_len;
        }

        if is_extension_node {
            let ext_nibbles: usize;
            if row_ext_s.get_byte(1) <= 32 {
                ext_nibbles = 1
            } else if row_ext_s.get_byte(0) < 248 {
                if row_ext_s.get_byte(2) == 0 {
                    // even number of nibbles
                    ext_nibbles = ((row_ext_s.get_byte(1) - 128) as usize - 1) * 2;
                } else {
                    ext_nibbles = (row_ext_s.get_byte(1) - 128) as usize * 2 - 1;
                }
            } else if row_ext_s.get_byte(3) == 0 {
                // even number of nibbles
                ext_nibbles = ((row_ext_s.get_byte(2) - 128) as usize - 1) * 2;
            } else {
                ext_nibbles = (row_ext_s.get_byte(2) - 128) as usize * 2 - 1;
            }

            pv.nibbles_num += ext_nibbles;
        }

        /* Branch */

        for is_s in [true, false] {
            let rlp_list_witness =
                self.rlp_list[is_s.idx()].assign(region, base_offset, &rlp_bytes[is_s.idx()])?;

            self.is_placeholder[is_s.idx()].assign(region, base_offset, is_placeholder[is_s.idx()].scalar())?;
            self.is_not_hashed[is_s.idx()].assign(region, base_offset, rlp_list_witness.num_bytes().scalar(), HASH_WIDTH.scalar())?;
        }

        let mut mod_node_hash_rlc = [0.scalar(); 2];
        let mut branch_witnesses = vec![vec![RLPItemWitness::default(); ARITY]; 2];
        for node_index in 0..ARITY {
            for is_s in [true, false] {
                let child_witness = self.branches[is_s.idx()][node_index].rlp.assign(region, base_offset, &branch_bytes[is_s.idx()][node_index])?;
                branch_witnesses[is_s.idx()][node_index] = child_witness.clone();

                let mut node_mult_diff = F::one();
                for _ in 0..child_witness.num_bytes() {
                    node_mult_diff *= mpt_config.randomness;
                }

                self.branches[is_s.idx()][node_index].mult.assign(region, base_offset, node_mult_diff)?;
                self.branches[is_s.idx()][node_index].rlc_branch.assign(region, base_offset, child_witness.rlc_branch(mpt_config.randomness))?;
                let is_hashed = self.branches[is_s.idx()][node_index].is_hashed.assign(region, base_offset, child_witness.len().scalar(), 32.scalar())?;

                let mod_pos = if is_placeholder[is_s.idx()] { drifted_index } else { modified_index };
                if mod_pos == node_index {
                    mod_node_hash_rlc[is_s.idx()] = child_witness.rlc_branch(mpt_config.randomness);
                    self.mod_branch_rlc[is_s.idx()].assign(region, base_offset, mod_node_hash_rlc[is_s.idx()])?;
                    self.mod_branch_is_hashed[is_s.idx()].assign(region, base_offset, is_hashed)?;
                }
            }
            self.is_modified[node_index].assign(region, base_offset, (node_index == modified_index).scalar())?;
            self.is_drifted[node_index].assign(region, base_offset, (node_index == drifted_index).scalar())?;
        }

        let mut is_placeholder_leaf = [0.scalar(); 2];
        for is_s in [true, false] {
            is_placeholder_leaf[is_s.idx()] = self.mod_branch_is_empty[is_s.idx()].assign(region, base_offset, branch_witnesses[is_s.idx()][modified_index].len().scalar())?;
        }

        let mut parent_values = vec![Vec::new(); 2];
        for is_s in [true, false] {
            parent_values[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                base_offset,
                &mut pv.memory[parent_memory(is_s)],
                0,
            )?;

            if !is_placeholder[is_s.idx()] {
                self.parent_data[is_s.idx()].witness_store(
                    region,
                    base_offset,
                    &mut pv.memory[parent_memory(is_s)],
                    mod_node_hash_rlc[is_s.idx()],
                    false,
                    false,
                    mod_node_hash_rlc[is_s.idx()],
                )?;
            } else {
                self.parent_data[is_s.idx()].witness_store(
                    region,
                    base_offset,
                    &mut pv.memory[parent_memory(is_s)],
                    parent_values[is_s.idx()][0],
                    parent_values[is_s.idx()][1] != F::zero(),
                    true,
                    mod_node_hash_rlc[is_s.idx()],
                )?;
            }
        }

        // one nibble is used for position in branch
        pv.nibbles_num += 1;

        // Update key parity
        let is_key_odd = !is_key_odd;

        // Update the key RLC and multiplier for the branch nibble.
        let (nibble_mult, mult): (F, F) = if is_key_odd {
            // The nibble will be added as the most significant nibble using the same multiplier
            (16.scalar(), 1.scalar())
        } else {
            // The nibble will be added as the least significant nibble, the multiplier needs to advance
            (1.scalar(), mpt_config.randomness)
        };
        let key_rlc_post_branch: F = key_rlc_post_ext + F::from(modified_index as u64) * nibble_mult * key_mult_post_ext;
        let key_mult_post_branch = key_mult_post_ext * mult;

        pv.key_rlc = key_rlc_post_branch;
        pv.key_rlc_mult = key_mult_post_branch;

        for is_s in [true, false] {
            if !is_placeholder[is_s.idx()] {
                self.key_data.witness_store(
                    region,
                    base_offset,
                    &mut pv.memory[key_memory(is_s)],
                    pv.key_rlc,
                    pv.key_rlc_mult,
                    pv.nibbles_num,
                    is_placeholder_leaf[true.idx()] == 1.scalar(),
                    is_placeholder_leaf[false.idx()] == 1.scalar(),
                    0,
                    pv.nibbles_num % 2 == 1,
                    key_rlc_post_branch,
                    key_mult_post_branch,
                )?;
            } else {
                self.key_data.witness_store(
                    region,
                    base_offset,
                    &mut pv.memory[key_memory(is_s)],
                    key_values[0],
                    key_values[1],
                    key_values[2].get_lower_32() as usize,
                    is_placeholder_leaf[true.idx()] == 1.scalar(),
                    is_placeholder_leaf[false.idx()] == 1.scalar(),
                    pv.drifted_pos,
                    pv.nibbles_num % 2 == 1,
                    key_rlc_post_ext,
                    key_mult_post_ext,
                )?;
            }
        }

        Ok(())
    }
}

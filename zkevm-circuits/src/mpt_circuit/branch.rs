use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    helpers::MPTConstraintBuilder,
    param::ARITY,
    rlp_gadgets::{RLPItemGadget, RLPItemWitness, RLPListDataGadget},
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cell_manager::Cell,
        constraint_builder::RLCChainable,
        gadgets::{IsEqualGadget, LtGadget},
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        helpers::nibble_rlc,
        param::{BRANCH_0_KEY_POS, DRIFTED_POS, HASH_WIDTH},
    },
    mpt_circuit::{helpers::Indexable, param::RLP_NIL, FixedTableTag},
    mpt_circuit::{MPTConfig, MPTState},
};

#[derive(Clone, Debug)]
pub(crate) struct BranchState<F> {
    pub(crate) key_rlc_post_branch: Expression<F>,
    pub(crate) key_mult_post_branch: Expression<F>,
    pub(crate) key_rlc_post_drifted: Expression<F>,
    pub(crate) key_mult_post_drifted: Expression<F>,
    pub(crate) num_nibbles: Expression<F>,
    pub(crate) is_key_odd: Expression<F>,
    pub(crate) mod_rlc: [Expression<F>; 2],
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BranchChildConfig<F> {
    rlp: RLPItemGadget<F>,
    mult: Cell<F>,
    rlc: Cell<F>,
    is_hashed: IsEqualGadget<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BranchGadget<F> {
    rlp_list: [RLPListDataGadget<F>; 2],
    children: [[BranchChildConfig<F>; ARITY]; 2],
    is_modified: [Cell<F>; ARITY],
    is_drifted: [Cell<F>; ARITY],
    mod_rlc: [Cell<F>; 2],
    mod_is_hashed: [Cell<F>; 2],
    is_not_hashed: [LtGadget<F, 2>; 2],

    // Post branch state
    post_state: Option<BranchState<F>>,
}

impl<F: Field> BranchGadget<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_placeholder: &[Cell<F>; 2],
        is_extension: Expression<F>,
        parent_rlc: &[Expression<F>; 2],
        is_root: &[Expression<F>; 2],
        key_rlc: Expression<F>,
        key_mult: Expression<F>,
        num_nibbles: Expression<F>,
        is_key_odd: Expression<F>,
    ) -> Self {
        let r = ctx.r.clone();

        let mut config = BranchGadget::default();

        circuit!([meta, cb.base], {
            // Data
            let branch_bytes: [[Vec<Expression<F>>; ARITY]; 2] = [
                array_init::array_init(|i| ctx.s(meta, 1 + i as i32)),
                array_init::array_init(|i| ctx.c(meta, 1 + i as i32)),
            ];

            let mut num_bytes_left = vec![0.expr(); 2];
            let mut node_rlc = vec![0.expr(); 2];
            let mut mult = vec![1.expr(); 2];
            for is_s in [true, false] {
                // Read the list
                config.rlp_list[is_s.idx()] = RLPListDataGadget::construct(&mut cb.base);
                // Start RLC encoding the RLP data starting with the list RLP bytes
                (node_rlc[is_s.idx()], mult[is_s.idx()]) =
                    config.rlp_list[is_s.idx()].rlp_list.rlc_rlp_only(&r);

                // Keep track of how many bytes the branch contains to make sure it's correct.
                num_bytes_left[is_s.idx()] = config.rlp_list[is_s.idx()].rlp_list.len();

                config.mod_rlc[is_s.idx()] = cb.base.query_cell();
                config.mod_is_hashed[is_s.idx()] = cb.base.query_cell();

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
                config.is_modified[node_index] = cb.base.query_bool();
                config.is_drifted[node_index] = cb.base.query_bool();

                // Calculate the modified and drifted index from `is_modified`/`is_drifted`
                modified_index = modified_index.expr()
                    + config.is_modified[node_index].expr() * node_index.expr();
                drifted_index =
                    drifted_index.expr() + config.is_drifted[node_index].expr() * node_index.expr();

                for is_s in [true, false] {
                    let branch = &mut config.children[is_s.idx()][node_index];
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
                    node_rlc[is_s.idx()] = (node_rlc[is_s.idx()].expr(), mult[is_s.idx()].expr())
                        .rlc_chain(branch.rlp.rlc_rlp(&mut cb.base, &r));

                    // Store the rlc of the branch
                    // TODO(Brecht): useless now, but useful when this work is spread over multiple
                    // rows
                    branch.rlc = cb.base.query_cell();
                    require!(branch.rlc => branch.rlp.rlc_branch(&r));

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
                    ifx! {is_placeholder[is_s.idx()] => {
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
                    let branch_s = config.children[true.idx()][node_index].rlp.rlc_rlp(&mut cb.base, &r);
                    let branch_c = config.children[false.idx()][node_index].rlp.rlc_rlp(&mut cb.base, &r);
                    require!(branch_s => branch_c);
                }}
            }
            for is_s in [true, false] {
                // Number of bytes left needs to be 1 because ValueNode which occupies 1 byte
                require!(num_bytes_left[is_s.idx()] => 1);
                // TODO: acc currently doesn'thave branch ValueNode info (which 128 if nil)
                node_rlc[is_s.idx()] = (node_rlc[is_s.idx()].expr(), mult[is_s.idx()].expr())
                    .rlc_chain(RLP_NIL.expr());
            }

            // `is_modified` needs to be set to 1 at exactly 1 branch child
            let is_modified_values = (0..ARITY)
                .map(|rot| config.is_modified[rot].expr())
                .collect::<Vec<_>>();
            require!(sum::expr(&is_modified_values) => 1);
            // When there's a placeholder, `is_drifted` needs to be set to 1 at exactly 1
            // branch child
            ifx! {or::expr(&[is_placeholder[true.idx()].expr(), is_placeholder[false.idx()].expr()]) => {
                let is_drifted_values = (0..ARITY).map(|rot| config.is_drifted[rot].expr()).collect::<Vec<_>>();
                require!(sum::expr(&is_drifted_values) => 1);
            }}

            // Check if the branch is in its parent
            for is_s in [true, false] {
                let (rlc, num_bytes, is_not_hashed) = {
                    (
                        node_rlc[is_s.idx()].expr(),
                        config.rlp_list[is_s.idx()].rlp_list.num_bytes(),
                        config.is_not_hashed[is_s.idx()].expr(),
                    )
                };

                // TODO(Brecht): should not need is_extension check
                ifx! {not!(is_extension) => {
                    ifx! {not!(is_placeholder[is_s.idx()]) => {
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
                key_rlc.expr(),
                key_mult.expr(),
                is_key_odd.expr(),
                modified_index.expr(),
                &r,
            );
            // Also calculate the key RLC and multiplier for the drifted nibble.
            let (key_rlc_post_drifted, key_mult_post_drifted) = nibble_rlc(
                &mut cb.base,
                key_rlc.expr(),
                key_mult.expr(),
                is_key_odd.expr(),
                drifted_index.expr(),
                &r,
            );

            // Update the nibble counter
            let num_nibbles = num_nibbles + 1.expr();
            // Update key parity
            let is_key_odd = not!(is_key_odd);

            // Set the branch we'll take
            for node_index in 0..ARITY {
                for is_s in [true, false] {
                    ifx! {is_placeholder[is_s.idx()] => {
                        ifx!{config.is_drifted[node_index].expr() => {
                            let child_rlc = config.children[(!is_s).idx()][node_index].rlp.rlc_branch(&r);
                            require!(config.mod_rlc[is_s.idx()] => child_rlc);
                        }}
                    } elsex {
                        ifx!{config.is_modified[node_index].expr() => {
                            let child_rlc = config.children[is_s.idx()][node_index].rlp.rlc_branch(&r);
                            require!(config.mod_rlc[is_s.idx()] => child_rlc);
                        }}
                    }}
                }
            }

            // Store the post ext state
            config.post_state = Some(BranchState {
                key_rlc_post_branch,
                key_mult_post_branch,
                key_rlc_post_drifted,
                key_mult_post_drifted,
                num_nibbles,
                is_key_odd,
                mod_rlc: [
                    config.mod_rlc[true.idx()].expr(),
                    config.mod_rlc[false.idx()].expr(),
                ],
            });
        });

        config
    }

    pub(crate) fn get_post_state(&self) -> BranchState<F> {
        self.post_state.as_ref().unwrap().clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        witness: &mut [MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        _pv: &mut MPTState<F>,
        offset: usize,
        idx: usize,
        is_placeholder: &[bool; 2],
        key_rlc: &mut F,
        key_mult: &mut F,
        num_nibbles: &mut usize,
        is_key_odd: &mut bool,
    ) -> Result<(F, F, F, [F; 2]), Error> {
        let row_init = witness[idx].to_owned();

        let modified_index = row_init.get_byte(BRANCH_0_KEY_POS) as usize;
        let mut drifted_index = row_init.get_byte(DRIFTED_POS) as usize;
        // If no placeholder branch, we set `drifted_pos = modified_node`. This
        // is needed just to make some other constraints (`s_mod_node_hash_rlc`
        // and `c_mod_node_hash_rlc` correspond to the proper node) easier to write.
        if !is_placeholder[true.idx()] && !is_placeholder[false.idx()] {
            drifted_index = modified_index;
        }

        // Data
        let branch_list_rlp_bytes = [
            row_init.rlp_bytes[0..3].to_owned(),
            row_init.rlp_bytes[3..6].to_owned(),
        ];
        let branch_bytes: [[Vec<u8>; ARITY]; 2] = [
            array_init::array_init(|i| witness[idx + 1 + i].s()),
            array_init::array_init(|i| witness[idx + 1 + i].c()),
        ];

        for is_s in [true, false] {
            let rlp_list_witness = self.rlp_list[is_s.idx()].assign(
                region,
                offset,
                &branch_list_rlp_bytes[is_s.idx()],
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
                let child_witness = self.children[is_s.idx()][node_index].rlp.assign(
                    region,
                    offset,
                    &branch_bytes[is_s.idx()][node_index],
                )?;
                branch_witnesses[is_s.idx()][node_index] = child_witness.clone();

                let mut node_mult_diff = F::one();
                for _ in 0..child_witness.num_bytes() {
                    node_mult_diff *= mpt_config.r;
                }

                self.children[is_s.idx()][node_index].mult.assign(
                    region,
                    offset,
                    node_mult_diff,
                )?;
                self.children[is_s.idx()][node_index].rlc.assign(
                    region,
                    offset,
                    child_witness.rlc_branch(mpt_config.r),
                )?;
                let _is_hashed = self.children[is_s.idx()][node_index].is_hashed.assign(
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
            self.mod_rlc[is_s.idx()].assign(region, offset, mod_node_hash_rlc[is_s.idx()])?;
            let is_hashed = branch_witnesses[mod_is_s.idx()][mod_pos].len() == 32;
            self.mod_is_hashed[is_s.idx()].assign(region, offset, is_hashed.scalar())?;
        }

        // one nibble is used for position in branch
        *num_nibbles += 1;
        // Update key parity
        *is_key_odd = !*is_key_odd;

        // Update the key RLC and multiplier for the branch nibble.
        let (nibble_mult, mult): (F, F) = if *is_key_odd {
            // The nibble will be added as the most significant nibble using the same
            // multiplier
            (16.scalar(), 1.scalar())
        } else {
            // The nibble will be added as the least significant nibble, the multiplier
            // needs to advance
            (1.scalar(), mpt_config.r)
        };
        let key_rlc_post_branch =
            *key_rlc + F::from(modified_index as u64) * nibble_mult * *key_mult;
        let key_rlc_post_drifted =
            *key_rlc + F::from(drifted_index as u64) * nibble_mult * *key_mult;
        let key_mult_post_branch = *key_mult * mult;

        Ok((
            key_rlc_post_branch,
            key_rlc_post_drifted,
            key_mult_post_branch,
            mod_node_hash_rlc,
        ))
    }
}

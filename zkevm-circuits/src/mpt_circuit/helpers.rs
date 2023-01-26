use std::{marker::PhantomData, ops::Range};

use crate::{
    _cb, circuit,
    circuit_tools::{Conditionable, ConstraintBuilder, DataTransition, LRCable, LrcChainable},
    evm_circuit::util::rlc,
    mpt_circuit::param::{
        EXTENSION_ROWS_NUM, KEY_PREFIX_EVEN, KEY_TERMINAL_PREFIX_EVEN, RLP_HASH_VALUE,
        RLP_LIST_LONG, RLP_LIST_SHORT, RLP_NIL, RLP_SHORT,
    },
    util::Expr,
};
use gadgets::util::{and, not};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};

use super::{
    columns::MainCols,
    param::{
        ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_ROWS,
        ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND,
        ACCOUNT_NON_EXISTING_IND, ARITY, BRANCH_0_C_START, BRANCH_0_S_START, BRANCH_ROWS_NUM,
        IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, IS_C_BRANCH_NON_HASHED_POS, IS_C_EXT_LONGER_THAN_55_POS,
        IS_C_EXT_NODE_NON_HASHED_POS, IS_S_BRANCH_NON_HASHED_POS, IS_S_EXT_LONGER_THAN_55_POS,
        IS_S_EXT_NODE_NON_HASHED_POS, KEY_PREFIX_ODD, KEY_TERMINAL_PREFIX_ODD, NIBBLES_COUNTER_POS,
    },
    FixedTableTag, MPTContext,
};
use crate::mpt_circuit::param::{
    IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
    IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, RLP_NUM,
};

#[derive(Clone)]
pub(crate) struct BranchNodeInfo<F> {
    pub(crate) is_s: bool,
    pub(crate) ctx: MPTContext<F>,
    pub(crate) rot_branch_init: i32,
    pub(crate) is_short_c16: Expression<F>,
    pub(crate) is_short_c1: Expression<F>,
    pub(crate) is_long_even_c16: Expression<F>,
    pub(crate) is_long_even_c1: Expression<F>,
    pub(crate) is_long_odd_c16: Expression<F>,
    pub(crate) is_long_odd_c1: Expression<F>,
    pub(crate) is_longer_than_55_s: Expression<F>,
    pub(crate) is_longer_than_55_c: Expression<F>,
    pub(crate) is_not_hashed_s: Expression<F>,
    pub(crate) is_not_hashed_c: Expression<F>,
    pub(crate) is_ext_not_hashed_s: Expression<F>,
    pub(crate) is_ext_not_hashed_c: Expression<F>,
    pub(crate) is_c1: Expression<F>,
    pub(crate) is_c16: Expression<F>,
    pub(crate) is_placeholder_s: Expression<F>,
    pub(crate) is_placeholder_c: Expression<F>,
    pub(crate) nibbles_counter: DataTransition<F>,
}

impl<F: FieldExt> BranchNodeInfo<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        ctx: MPTContext<F>,
        is_s: bool,
        rot_branch_init: i32,
    ) -> Self {
        let s_main = ctx.s_main;
        let rot = Rotation(rot_branch_init);

        let mut get_value = |pos| meta.query_advice(s_main.bytes[pos - RLP_NUM], rot);

        let is_short_c16 = get_value(IS_EXT_SHORT_C16_POS);
        let is_short_c1 = get_value(IS_EXT_SHORT_C1_POS);
        let is_long_even_c16 = get_value(IS_EXT_LONG_EVEN_C16_POS);
        let is_long_even_c1 = get_value(IS_EXT_LONG_EVEN_C1_POS);
        let is_long_odd_c16 = get_value(IS_EXT_LONG_ODD_C16_POS);
        let is_long_odd_c1 = get_value(IS_EXT_LONG_ODD_C1_POS);
        let is_longer_than_55_s = get_value(IS_S_EXT_LONGER_THAN_55_POS);
        let is_longer_than_55_c = get_value(IS_C_EXT_LONGER_THAN_55_POS);
        let is_ext_not_hashed_s = get_value(IS_S_EXT_NODE_NON_HASHED_POS);
        let is_ext_not_hashed_c = get_value(IS_C_EXT_NODE_NON_HASHED_POS);
        let is_not_hashed_s = get_value(IS_S_BRANCH_NON_HASHED_POS);
        let is_not_hashed_c = get_value(IS_C_BRANCH_NON_HASHED_POS);
        let is_c1 = get_value(IS_BRANCH_C1_POS);
        let is_c16 = get_value(IS_BRANCH_C16_POS);
        let is_placeholder_s = get_value(IS_BRANCH_S_PLACEHOLDER_POS);
        let is_placeholder_c = get_value(IS_BRANCH_C_PLACEHOLDER_POS);

        let nibbles_counter = DataTransition::new_with_rot(
            meta,
            s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
            rot_branch_init - BRANCH_ROWS_NUM,
            rot_branch_init,
        );

        BranchNodeInfo {
            is_s,
            ctx: ctx.clone(),
            rot_branch_init,
            is_short_c16,
            is_short_c1,
            is_long_even_c16,
            is_long_even_c1,
            is_long_odd_c16,
            is_long_odd_c1,
            is_longer_than_55_s,
            is_longer_than_55_c,
            is_not_hashed_s,
            is_not_hashed_c,
            is_ext_not_hashed_s,
            is_ext_not_hashed_c,
            is_c1,
            is_c16,
            is_placeholder_s,
            is_placeholder_c,
            nibbles_counter,
        }
    }

    pub(crate) fn contains_placeholder_leaf(
        &self,
        meta: &mut VirtualCells<F>,
        is_s: bool,
    ) -> Expression<F> {
        // All children contain the same data so we just jump to the last child here
        contains_placeholder_leaf(
            meta,
            self.ctx.clone(),
            is_s,
            self.rot_branch_init + (ARITY as i32) - 1,
        )
    }

    /// Adds selector constraints for branch init
    pub(crate) fn init_selector_checks(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) {
        circuit!([meta, cb], {
            // Boolean checks
            let selectors = self.get_selectors(meta);
            for selector in selectors.iter() {
                require!(selector => bool);
            }
            // There should never be `rlp1, rlp2: 0, 0`
            // (we only have three cases, there is no case with both being 0).
            require!(or::expr(&selectors) => true);
        });
    }

    /// Returns true if this is a branch with an extension mode
    pub(crate) fn is_extension(&self) -> Expression<F> {
        self.is_key_part_in_ext_even() + self.is_key_part_in_ext_odd()
    }

    /// Returns if the part of the key in the extension node is even
    pub(crate) fn is_key_part_in_ext_even(&self) -> Expression<F> {
        self.is_long_even_c16.expr() + self.is_long_even_c1.expr()
    }

    /// Returns if the part of the key in the extension node is odd
    pub(crate) fn is_key_part_in_ext_odd(&self) -> Expression<F> {
        self.is_long_odd() + self.is_short()
    }

    // If more than 1 nibble is stored in the extension node and the key part in the
    // extension node is odd
    pub(crate) fn is_long_odd(&self) -> Expression<F> {
        self.is_long_odd_c16.expr() + self.is_long_odd_c1.expr()
    }

    // If more than 1 nibble is stored in the extension node and the key part in the
    // extension node is even
    pub(crate) fn is_long_even(&self) -> Expression<F> {
        self.is_key_part_in_ext_even()
    }

    // If a single nibble is stored in the extension node
    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short_c16.expr() + self.is_short_c1.expr()
    }

    // If more than 1 nibble is stored in the extension node
    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long_even() + self.is_long_odd()
    }

    /// Returns if the key up till and including this branch is even.
    pub(crate) fn is_key_even(&self) -> Expression<F> {
        self.is_c1.expr()
    }

    /// Returns if the key up till and including this branch is odd.
    pub(crate) fn is_key_odd(&self) -> Expression<F> {
        self.is_c16.expr()
    }

    pub(crate) fn is_placeholder_s(&self) -> Expression<F> {
        self.is_placeholder_s.expr()
    }

    pub(crate) fn is_placeholder_c(&self) -> Expression<F> {
        self.is_placeholder_c.expr()
    }

    pub(crate) fn is_placeholder(&self) -> Expression<F> {
        if self.is_s {
            self.is_placeholder_s()
        } else {
            self.is_placeholder_c()
        }
    }

    pub(crate) fn is_placeholder_s_or_c(&self) -> Expression<F> {
        self.is_placeholder_s() + self.is_placeholder_c()
    }

    pub(crate) fn is_not_hashed_s(&self) -> Expression<F> {
        self.is_not_hashed_s.expr()
    }

    pub(crate) fn is_not_hashed_c(&self) -> Expression<F> {
        self.is_not_hashed_c.expr()
    }

    pub(crate) fn is_not_hashed(&self) -> Expression<F> {
        if self.is_s {
            self.is_not_hashed_s()
        } else {
            self.is_not_hashed_c()
        }
    }

    pub(crate) fn is_ext_not_hashed_s(&self) -> Expression<F> {
        self.is_ext_not_hashed_s.expr()
    }

    pub(crate) fn is_ext_not_hashed_c(&self) -> Expression<F> {
        self.is_ext_not_hashed_c.expr()
    }

    pub(crate) fn is_ext_not_hashed(&self) -> Expression<F> {
        if self.is_s {
            self.is_ext_not_hashed_s()
        } else {
            self.is_ext_not_hashed_c()
        }
    }

    /// Number of key nibbles processed up till and including the current
    /// branch.
    pub(crate) fn nibbles_counter(&self) -> DataTransition<F> {
        self.nibbles_counter.clone()
    }

    pub(crate) fn set_is_s(&mut self, is_s: bool) {
        self.is_s = is_s;
    }

    pub(crate) fn is_below_account(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        self.ctx.is_account(meta, self.rot_branch_init - 1)
    }

    pub(crate) fn is_at_tree_top(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            or::expr(&[
                not!(a!(
                    self.ctx.position_cols.not_first_level,
                    self.rot_branch_init
                )),
                self.is_below_account(meta),
            ])
        })
    }

    pub(crate) fn storage_root_in_account_above(
        &self,
        meta: &mut VirtualCells<F>,
    ) -> Expression<F> {
        let storage_offset = if self.is_s {
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND
        } else {
            ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND
        };
        let rot_storage_root = self.rot_branch_init - ACCOUNT_LEAF_ROWS + storage_offset;
        // Note: storage root is always in s_main.bytes.
        self.ctx
            .s_main
            .bytes(meta, rot_storage_root)
            .rlc(&self.ctx.r)
    }

    pub(crate) fn get_selectors(&self, meta: &mut VirtualCells<F>) -> [Expression<F>; 2] {
        //`s_rlp1, s_rlp2` is used for `S` and `s_main.bytes[0], s_main.bytes[1]` is
        //`s_rlp1, used for `C`
        let (rlp_column_1, rlp_column_2) = if self.is_s {
            (self.ctx.s_main.rlp1, self.ctx.s_main.rlp2)
        } else {
            (self.ctx.s_main.bytes[0], self.ctx.s_main.bytes[1])
        };
        circuit!([meta, _cb!()], {
            [
                a!(rlp_column_1, self.rot_branch_init),
                a!(rlp_column_2, self.rot_branch_init),
            ]
        })
    }

    pub(crate) fn is_branch_short(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        // rlp1, rlp2: 1, 1 means 1 RLP byte
        let rlp = self.get_selectors(meta);
        and::expr([rlp[0].expr(), rlp[1].expr()])
    }

    pub(crate) fn is_branch_long(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        // rlp1, rlp2: 1, 0 means 2 RLP bytes
        let rlp = self.get_selectors(meta);
        and::expr([rlp[0].expr(), not::expr(rlp[1].expr())])
    }

    pub(crate) fn is_branch_very_long(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        // rlp1, rlp2: 0, 1 means 3 RLP bytes
        let rlp = self.get_selectors(meta);
        and::expr([not::expr(rlp[0].expr()), rlp[1].expr()])
    }

    pub(crate) fn rlp_bytes(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        let offset = if self.is_s {
            BRANCH_0_S_START
        } else {
            BRANCH_0_C_START
        } - RLP_NUM;
        self.ctx.s_main.bytes(meta, self.rot_branch_init)[offset..offset + 3]
            .iter()
            .map(|e| e.expr())
            .collect()
    }

    /// Total number of bytes used by the branch
    pub(crate) fn num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        self.num_rlp_bytes(meta) + self.len(meta)
    }

    /// Number of RLP bytes for the branch
    pub(crate) fn num_rlp_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_branch_short(meta) => 1.expr(),
                self.is_branch_long(meta) => 2.expr(),
                self.is_branch_very_long(meta) => 3.expr(),
            }
        })
    }

    /// Total length of the branch
    pub(crate) fn len(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let rlp_bytes = self.rlp_bytes(meta);
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_branch_short(meta) => get_len_list_short(rlp_bytes[0].expr()),
                self.is_branch_long(meta) => rlp_bytes[1].expr(),
                self.is_branch_very_long(meta) => rlp_bytes[1].expr() * 256.expr() + rlp_bytes[2].expr(),
            }
        })
    }

    /// Number of bytes in the extension node
    /// Uses data on the current row!
    pub(crate) fn ext_num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let rot_s = if self.is_s { 0 } else { -1 };
        self.ext_num_rlp_bytes(meta) + self.ext_len(meta, rot_s)
    }

    /// Length of the extension node (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_len(&self, _meta: &mut VirtualCells<F>, rel_rot: i32) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_short() + self.is_long() => get_len_list_short(a!(self.ctx.s_main.rlp1, rel_rot)),
                self.is_longer_than_55_s => get_len_short(a!(self.ctx.s_main.bytes[0], rel_rot)),
            }
        })
    }

    /// Number of RLP bytes for the extension row
    pub(crate) fn ext_num_rlp_bytes(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_short() + self.is_long() => 1.expr(),
                self.is_longer_than_55_s => 2.expr(),
            }
        })
    }

    /// Length of the key (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_key_len(&self, _meta: &mut VirtualCells<F>, rel_rot: i32) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_short() => 1.expr(), // Only a single nibble (stored in s_rlp2)
                self.is_long() => get_len_short(a!(self.ctx.s_main.rlp2, rel_rot)),
                self.is_longer_than_55_s => get_len_short(a!(self.ctx.s_main.bytes[0], rel_rot)),
            }
        })
    }

    /// Number of bytes of the key (including RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_key_num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! (
                self.is_short() => 0.expr(),
                self.is_long() => 1.expr(),
                self.is_longer_than_55_s => 2.expr(),
            ) + self.ext_key_len(meta, 0)
        })
    }

    /// Length of the included branch (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_branch_len(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx! {self.contains_hashed_branch(meta) => {
                32.expr()
            } elsex {
                get_len_list_short(a!(self.ctx.c_main.bytes[0]))
            }}
        })
    }

    /// Length of the included branch (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_branch_num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        1.expr() + self.ext_branch_len(meta)
    }

    /// Length of the key (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn contains_hashed_branch(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            a!(self.ctx.c_main.rlp2) * invert!(RLP_HASH_VALUE)
        })
    }

    pub(crate) fn require_in_parent(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) {
        circuit!([meta, cb], {
            // The branch or extension node data
            let (rlc, num_bytes, is_not_hashed) = ifx! {self.is_extension() => {
                // Note: acc_c in both cases.
                let ext_rlc = a!(self.ctx.accumulators.acc_c.rlc);
                (ext_rlc, self.ext_num_bytes(meta), self.is_ext_not_hashed())
            } elsex {
                let acc = self.ctx.accumulators.acc(self.is_s);
                // TODO: acc currently doesn't have branch ValueNode info
                let branch_rlc = (a!(acc.rlc), a!(acc.mult)).rlc_chain(RLP_NIL.expr());
                (branch_rlc, self.num_bytes(meta), self.is_not_hashed())
            }};
            // Check against the value expected in the parent
            ifx! {not!(self.is_placeholder()) => {
                ifx!{a!(self.ctx.position_cols.not_first_level) => {
                    ifx!{self.is_below_account(meta) => {
                        // Branch in first level of storage trie - hash compared to the storage root
                        let storage_root_rlc = self.storage_root_in_account_above(meta);
                        require!((1, rlc, num_bytes, storage_root_rlc) => @"keccak");
                    } elsex {
                        // Here the branch is in some other branch
                        let rot_branch_child_prev = self.rot_branch_init - EXTENSION_ROWS_NUM - 1;
                        let mod_node_hash_rlc = a!(self.ctx.accumulators.mod_node_rlc(self.is_s), rot_branch_child_prev);
                        ifx!{is_not_hashed => {
                            // Non-hashed branch hash in parent branch
                            require!(rlc => mod_node_hash_rlc);
                        } elsex {
                            // Hashed branch hash in parent branch
                            require!((1, rlc, num_bytes, mod_node_hash_rlc) => @"keccak");
                        }}
                    }}
                } elsex {
                    // Branch in first level of account trie - hash compared to root
                    require!((1, rlc, num_bytes, a!(self.ctx.inter_root(self.is_s))) => @"keccak");
                }}
            }}
        });
    }

    /// Key data is read from the current row, not at rot_key!
    pub(crate) fn ext_key_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            let mult_first_odd = ifx! {self.is_key_even() => { 16.expr() } elsex { 1.expr() }};
            let calc_rlc = |meta: &mut VirtualCells<F>,
                            cb: &mut ConstraintBuilder<F>,
                            bytes: &[Expression<F>],
                            key_mult_first_even: Expression<F>| {
                ext_key_rlc(
                    meta,
                    cb,
                    self.ctx.clone(),
                    bytes,
                    key_mult_prev.expr(),
                    self.is_key_part_in_ext_odd(),
                    mult_first_odd.expr(),
                    key_mult_first_even,
                )
            };
            matchx! {
                self.is_long_odd_c1.expr() + self.is_long_even_c1.expr() => {
                    // Here we need to multiply nibbles over bytes with different r's so we need to rlc over separate nibbles.
                    // Note that there can be at max 31 key bytes because 32 same bytes would mean
                    // the two keys being the same - update operation, not splitting into extension node.
                    // So, we do not need to look further than `s_main.bytes` even if `s_main.bytes[0]`
                    // is not used (when even number of nibbles).
                    let mut key_bytes = vec![a!(self.ctx.s_main.bytes[0], -1)];
                    key_bytes.append(&mut self.ctx.s_main.bytes.iter().skip(1).zip(self.ctx.s_main.bytes.iter()).map(|(byte, byte_hi)| {
                        let byte = a!(byte, -1);
                        let nibble_hi = a!(byte_hi);
                        let nibble_lo = (byte.expr() - nibble_hi.expr()) * invert!(16);
                        // Check that `nibble_hi` is correct.
                        require!(byte => nibble_lo.expr() * 16.expr() + nibble_hi.expr());
                        // Collect bytes
                        (nibble_hi.expr() * 16.expr() * self.ctx.r[0].expr()) + nibble_lo.expr()
                    }).collect::<Vec<_>>());
                    calc_rlc(meta, cb, &key_bytes, 1.expr())
                },
                self.is_long_odd_c16.expr() + self.is_long_even_c16.expr() => {
                    let additional_mult = ifx! {self.is_long_odd_c16 => { self.ctx.r[0].expr() } elsex { 1.expr() }};
                    let key_bytes = self.ctx.s_main.bytes(meta, -1);
                    calc_rlc(meta, cb, &key_bytes, additional_mult)
                },
                self.is_short() => {
                    let key_bytes = vec![a!(self.ctx.s_main.rlp2, -1)];
                    calc_rlc(meta, cb, &key_bytes, 1.expr())
                },
            }
        })
    }

    /// Add the nibble from the drifted branch
    pub(crate) fn drifted_nibble_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            // Add the nibble from the branch (drifted_index is set to the same value for
            // all children)
            let drifted_mult =
                key_mult_prev.expr() * ifx! {self.is_key_odd() => { 16.expr() } elsex { 1.expr() }};
            a!(self.ctx.branch.drifted_index, self.rot_branch_init + 1) * drifted_mult
        })
    }
}

#[derive(Clone)]
pub(crate) struct BranchChildInfo<F> {
    pub(crate) is_s: bool,
    pub(crate) ctx: MPTContext<F>,
    pub(crate) rot_branch: i32,
}

impl<F: FieldExt> BranchChildInfo<F> {
    pub(crate) fn new(
        _meta: &mut VirtualCells<F>,
        ctx: MPTContext<F>,
        is_s: bool,
        rot_branch: i32,
    ) -> Self {
        BranchChildInfo {
            is_s,
            ctx: ctx.clone(),
            rot_branch,
        }
    }

    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx! {self.is_hashed(meta) => {
                // There is `s_rlp2 = 0` when there is a nil node and `s_rlp2 = 160` when
                // non-nil node (1 or 33 respectively).
                a!(self.ctx.main(self.is_s).rlp2) * invert!(RLP_HASH_VALUE) * 32.expr() + 1.expr()
            } elsex {
                get_num_bytes_list_short(a!(self.ctx.main(self.is_s).bytes[0]))
            }}
        })
    }

    pub(crate) fn is_hashed(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            not!(a!(
                self.ctx.denoter.is_not_hashed(self.is_s),
                self.rot_branch
            ))
        })
    }

    pub(crate) fn rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        let main = self.ctx.main(self.is_s);
        let r = self.ctx.r.clone();
        circuit!([meta, cb], {
            ifx! {not!(self.is_hashed(meta)) => {
                // When a branch child is not empty and is not hashed, a list is stored in the branch and
                // we have `bytes[0] - RLP_LIST_SHORT` bytes in a row. We need to add these bytes to the RLC.
                // For example we have 6 bytes in the following child: `[0,0,198,132,48,0,0,0,1,...]`.
                main.expr(meta, self.rot_branch)[2..34].rlc(&r)
            } elsex {
                ifx!{self.is_empty(meta) => {
                    require!(a!(main.bytes[0]) => RLP_NIL);
                    // There's only one byte (128 at `bytes[0]`) that needs to be added to the RLC.
                    main.expr(meta, self.rot_branch)[2..3].rlc(&r)
                } elsex {
                    // When a branch child is non-empty and hashed, we have 33 bytes in a row.
                    main.expr(meta, self.rot_branch)[1..34].rlc(&r)
                }}
            }}
        })
    }

    /// Branch data starts at a different offset, this will return the number of
    /// bytes from the start
    pub(crate) fn num_bytes_on_row(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx!(self.is_hashed(meta) => {
                2.expr()
            } elsex {
                ifx!{self.is_empty(meta) => {
                    2.expr()
                } elsex {
                    1.expr()
                }}
            }) + self.num_bytes(meta)
        })
    }

    /// Only usable when the child isn't hashed!
    pub(crate) fn is_empty(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let main = self.ctx.main(self.is_s);
        circuit!([meta, _cb!()], {
            // Empty nodes have 0 at `rlp2`, have `RLP_NIL` at `bytes[0]` and 0 everywhere
            // else. While hashed nodes have `RLP_HASH_VALUE at `rlp2` and then
            // any byte at `bytes`.
            require!(a!(main.rlp2, self.rot_branch) => [0, RLP_HASH_VALUE]);
            (RLP_HASH_VALUE.expr() - a!(main.rlp2, self.rot_branch)) * invert!(RLP_HASH_VALUE)
        })
    }
}

#[derive(Clone)]
pub(crate) struct StorageLeafInfo<F> {
    pub(crate) is_s: bool,
    pub(crate) ctx: MPTContext<F>,
    pub(crate) rot_key: i32,
    pub(crate) flag1: Expression<F>,
    pub(crate) flag2: Expression<F>,
}

impl<F: FieldExt> StorageLeafInfo<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        ctx: MPTContext<F>,
        is_s: bool,
        rot_key: i32,
    ) -> Self {
        let rot = Rotation(rot_key);
        let flag1 = meta.query_advice(ctx.accumulators.s_mod_node_rlc, rot);
        let flag2 = meta.query_advice(ctx.accumulators.c_mod_node_rlc, rot);
        StorageLeafInfo {
            is_s,
            ctx: ctx.clone(),
            rot_key,
            flag1,
            flag2,
        }
    }

    // Override the rotation while keeping the length flags intact
    pub(crate) fn set_rot_key(&mut self, rot_key: i32) {
        self.rot_key = rot_key;
    }

    pub(crate) fn has_no_nibble(&self) -> Expression<F> {
        self.flag1.expr() * self.flag2.expr()
    }

    pub(crate) fn has_one_nibble(&self) -> Expression<F> {
        not::expr(self.flag1.expr()) * not::expr(self.flag2.expr())
    }

    pub(crate) fn is_long(&self) -> Expression<F> {
        self.flag1.expr() * not::expr(self.flag2.expr())
    }

    pub(crate) fn is_short(&self) -> Expression<F> {
        not::expr(self.flag1.expr()) * self.flag2.expr()
    }

    pub(crate) fn is_very_short(&self) -> Expression<F> {
        self.has_no_nibble() + self.has_one_nibble()
    }

    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx! {self.is_long() => {
                2.expr() + a!(self.ctx.s_main.rlp2, self.rot_key)
            } elsex {
                get_num_bytes_list_short(a!(self.ctx.s_main.rlp1, self.rot_key))
            }}
        })
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_very_short() => 1.expr(),
                self.is_short() => 2.expr(),
                self.is_long() => 3.expr(),
            }
        })
    }

    /// Length of the key (excluding RLP bytes)
    pub(crate) fn key_len(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_very_short() => 1.expr(), // 1 byte in s_rlp2
                self.is_short() => get_len_short(a!(self.ctx.s_main.rlp2, self.rot_key)),
                self.is_long() => get_len_short(a!(self.ctx.s_main.bytes[0], self.rot_key)),
            }
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        self.num_rlp_bytes(meta) + self.key_len(meta)
    }

    pub(crate) fn num_key_nibbles(
        &self,
        meta: &mut VirtualCells<F>,
        is_key_odd: Expression<F>,
    ) -> Expression<F> {
        let key_len = self.key_len(meta);
        get_num_nibbles(meta, key_len, is_key_odd)
    }

    /// Key data is read from the current row, not at rot_key!
    pub(crate) fn key_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
        is_key_odd: Expression<F>,
        key_mult_first_even: Expression<F>,
        requires_longer_than_55: bool,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            let calc_rlc = |meta: &mut VirtualCells<F>,
                            cb: &mut ConstraintBuilder<F>,
                            range: Range<usize>,
                            is_key_odd: Expression<F>| {
                leaf_key_rlc(
                    meta,
                    cb,
                    self.ctx.clone(),
                    range,
                    key_mult_prev.expr(),
                    is_key_odd.expr(),
                    key_mult_first_even.expr(),
                )
            };
            matchx! {
                self.is_short() => {
                    // First key byte is at `s_main.bytes[0]`.
                    calc_rlc(meta, cb, 2..35, is_key_odd.expr())
                },
                self.is_long() => {
                    if requires_longer_than_55 {
                        // `s_main.rlp1` needs to be 248.
                        require!(a!(self.ctx.s_main.rlp1) => (RLP_LIST_LONG + 1));
                    }
                    // First key byte is at `s_main.bytes[1]`.
                    calc_rlc(meta, cb, 3..36, is_key_odd.expr())
                },
                self.has_no_nibble() => {
                    // Single byte is at `s_main.rlp2`
                    calc_rlc(meta, cb, 1..2, false.expr())
                },
                self.has_one_nibble() => {
                    // Single byte is at `s_main.rlp2`
                    calc_rlc(meta, cb, 1..2, true.expr())
                },
            }
        })
    }

    pub(crate) fn is_below_account(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let rot_parent = if self.is_s { -1 } else { -3 };
        self.ctx.is_account(meta, self.rot_key + rot_parent)
    }

    pub(crate) fn storage_root_in_account_above(
        &self,
        meta: &mut VirtualCells<F>,
    ) -> Expression<F> {
        let rot_parent = if self.is_s { -1 } else { -3 };
        let storage_offset = if self.is_s {
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND
        } else {
            ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND
        };
        let rot_storage_root = self.rot_key + 1 + rot_parent - ACCOUNT_LEAF_ROWS + storage_offset;
        // Note: storage root is always in s_main.bytes.
        self.ctx
            .s_main
            .bytes(meta, rot_storage_root)
            .rlc(&self.ctx.r)
    }

    pub(crate) fn is_placeholder(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let rot_parent = if self.is_s { -1 } else { -3 };
        let rot_branch_init = rot_parent - (BRANCH_ROWS_NUM - 1);
        circuit!([meta, _cb!()], {
            ifx! {self.is_below_account(meta) => {
                self.is_placeholder_without_branch(meta)
            } elsex {
                let branch = BranchNodeInfo::new(meta, self.ctx.clone(), self.is_s, self.rot_key + rot_branch_init);
                branch.contains_placeholder_leaf(meta, self.is_s)
            }}
        })
    }

    pub(crate) fn is_placeholder_without_branch(
        &self,
        meta: &mut VirtualCells<F>,
    ) -> Expression<F> {
        let rot_value = 1;
        circuit!([meta, _cb!()], {
            a!(self.ctx.denoter.sel(self.is_s), self.rot_key + rot_value)
        })
    }
}

#[derive(Clone)]
pub(crate) struct AccountLeafInfo<F> {
    rot_key: i32,
    ctx: MPTContext<F>,
    _marker: PhantomData<F>,
    is_nonce_long: Expression<F>,
    is_balance_long: Expression<F>,
}

impl<F: FieldExt> AccountLeafInfo<F> {
    pub(crate) fn new(meta: &mut VirtualCells<F>, ctx: MPTContext<F>, rot_key: i32) -> Self {
        let rot = Rotation(rot_key);
        let is_nonce_long = meta.query_advice(ctx.denoter.sel1, rot);
        let is_balance_long = meta.query_advice(ctx.denoter.sel2, rot);
        AccountLeafInfo {
            rot_key,
            ctx: ctx.clone(),
            is_nonce_long,
            is_balance_long,
            _marker: PhantomData,
        }
    }

    pub(crate) fn is_wrong_leaf(&self, meta: &mut VirtualCells<F>, is_s: bool) -> Expression<F> {
        let rot_non_existing = ACCOUNT_NON_EXISTING_IND
            - if is_s {
                ACCOUNT_LEAF_KEY_S_IND
            } else {
                ACCOUNT_LEAF_KEY_C_IND
            };
        meta.query_advice(
            self.ctx.s_main.rlp1,
            Rotation(self.rot_key + rot_non_existing),
        )
    }

    pub(crate) fn is_nonce_long(&self) -> Expression<F> {
        self.is_nonce_long.expr()
    }

    pub(crate) fn is_balance_long(&self) -> Expression<F> {
        self.is_balance_long.expr()
    }

    pub(crate) fn nonce_len(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            2.expr() + a!(self.ctx.s_main.rlp2, self.rot_key)
        })
    }

    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            2.expr() + a!(self.ctx.s_main.rlp2, self.rot_key)
        })
    }

    /// Returns the length of the key
    pub(crate) fn key_len(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            get_len_short(a!(self.ctx.s_main.bytes[0], self.rot_key))
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        self.num_rlp_bytes(meta) + self.key_len(meta)
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        // 2 RLP bytes + 1 byte that contains the key length.
        3.expr()
    }

    pub(crate) fn nonce_balance_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        nonce_rlc: Expression<F>,
        balance_rlc: Expression<F>,
        mult_prev: Expression<F>,
        mult_nonce: Expression<F>,
        rot_nonce: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            rlc::expr(
                &[
                    a!(self.ctx.s_main.rlp1, rot_nonce),
                    a!(self.ctx.s_main.rlp2, rot_nonce),
                    a!(self.ctx.c_main.rlp1, rot_nonce),
                    a!(self.ctx.c_main.rlp2, rot_nonce),
                    nonce_rlc,
                ]
                .into_iter()
                .map(|value| value * mult_prev.expr())
                .collect::<Vec<_>>(),
                &self.ctx.r,
            ) + balance_rlc * mult_prev.expr() * mult_nonce.expr()
        })
    }

    pub(crate) fn storage_codehash_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        storage_rlc: Expression<F>,
        codehash_rlc: Expression<F>,
        mult_prev: Expression<F>,
        rot_storage: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            rlc::expr(
                &[
                    a!(self.ctx.s_main.rlp2, rot_storage),
                    storage_rlc,
                    a!(self.ctx.c_main.rlp2, rot_storage),
                    codehash_rlc,
                ]
                .map(|v| v * mult_prev.expr()),
                &[
                    self.ctx.r[0].expr(),
                    self.ctx.r[32].expr(),
                    self.ctx.r[33].expr(),
                ],
            )
        })
    }

    // Can be used for nonce/balance to from a value rlc to a data rlc (which
    // included the RLP bytes)
    pub(crate) fn to_data_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        main: MainCols<F>,
        value_rlc: Expression<F>,
        is_long: Expression<F>,
        rot_nonce: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx! {is_long => {
                a!(main.bytes[0], rot_nonce) + value_rlc.expr() * self.ctx.r[0].expr()
            } elsex {
                value_rlc
            }}
        })
    }

    pub(crate) fn storage_root_rlc(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let storage_offset = ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND;
        let rot_storage_root = self.rot_key + storage_offset;
        // Note: storage root is always in s_main.bytes.
        self.ctx
            .s_main
            .bytes(meta, rot_storage_root)
            .rlc(&self.ctx.r)
    }

    // Will use data on the current row!
    pub(crate) fn key_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
        is_key_odd: Expression<F>,
        key_mult_first_even: Expression<F>,
    ) -> Expression<F> {
        leaf_key_rlc(
            meta,
            cb,
            self.ctx.clone(),
            3..36,
            key_mult_prev.expr(),
            is_key_odd,
            key_mult_first_even,
        )
    }
}

pub(crate) fn contains_placeholder_leaf<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    ctx: MPTContext<F>,
    is_s: bool,
    rot_branch_child: i32,
) -> Expression<F> {
    meta.query_advice(ctx.denoter.sel(is_s), Rotation(rot_branch_child))
}

pub(crate) fn leaf_key_rlc<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    cb: &mut ConstraintBuilder<F>,
    ctx: MPTContext<F>,
    range: Range<usize>,
    key_mult_prev: Expression<F>,
    is_key_odd: Expression<F>,
    key_mult_first_even: Expression<F>,
) -> Expression<F> {
    circuit!([meta, cb], {
        // Add the odd nibble first if we have one.
        let first_byte = a!(ctx.s_main.rlp_bytes()[range.start]);
        let (rlc, mult) = ifx! {is_key_odd => {
            (get_terminal_odd_nibble(first_byte.expr()) * key_mult_prev.expr(), ctx.r[0].expr())
        } elsex {
            require!(first_byte => KEY_TERMINAL_PREFIX_EVEN);
            (0.expr(), key_mult_first_even.expr())
        }};
        (rlc, key_mult_prev * mult).rlc_chain(ctx.rlc(meta, range.start + 1..range.end, 0))
    })
}

pub(crate) fn ext_key_rlc<F: FieldExt>(
    _meta: &mut VirtualCells<F>,
    cb: &mut ConstraintBuilder<F>,
    ctx: MPTContext<F>,
    bytes: &[Expression<F>],
    key_mult_prev: Expression<F>,
    is_odd: Expression<F>,
    rlc_mult_first_odd: Expression<F>,
    key_mult_first_odd: Expression<F>,
) -> Expression<F> {
    circuit!([_meta, cb], {
        // Add the odd nibble first if we have one.
        let first_byte = bytes[0].clone();
        let (rlc, mult) = ifx! {is_odd => {
            (get_ext_odd_nibble(first_byte.expr()) * key_mult_prev.expr() * rlc_mult_first_odd, key_mult_first_odd.expr())
        } elsex {
            require!(first_byte => KEY_PREFIX_EVEN);
            (0.expr(), 1.expr())
        }};
        (rlc, key_mult_prev * mult).rlc_chain(bytes[1..].rlc(&ctx.r))
    })
}

pub(crate) fn get_terminal_odd_nibble<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_TERMINAL_PREFIX_ODD.expr()
}

pub(crate) fn get_ext_odd_nibble<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_PREFIX_ODD.expr()
}

pub(crate) fn get_len_short<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    byte - RLP_SHORT.expr()
}

pub(crate) fn get_num_bytes_short<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    // A single RLP byte + the encoded length
    1.expr() + get_len_short(byte)
}

pub(crate) fn get_len_list_short<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    byte - RLP_LIST_SHORT.expr()
}

pub(crate) fn get_num_bytes_list_short<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    // A single RLP byte + the encoded length
    1.expr() + get_len_list_short(byte)
}

pub(crate) fn get_num_nibbles<F: FieldExt>(
    _meta: &mut VirtualCells<F>,
    key_len: Expression<F>,
    is_key_odd: Expression<F>,
) -> Expression<F> {
    circuit!([meta, _cb!()], {
        ifx! {is_key_odd => {
            key_len.expr() * 2.expr() - 1.expr()
        } elsex {
            (key_len.expr() - 1.expr()) * 2.expr()
        }}
    })
}

// The key RLC of the drifted leaf needs to be the same as the key RLC of the
// leaf before the drift - the nibbles are the same in both cases, the
// difference is that before the drift some nibbles are stored in the leaf key,
// while after the drift these nibbles are used as position in a branch or/and
// nibbles of the extension node.
pub(crate) fn get_parent_rlc_state<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    ctx: MPTContext<F>,
    is_first_level: Expression<F>,
    rot_parent: i32,
) -> (Expression<F>, Expression<F>) {
    let accs = ctx.accumulators;
    let rot_branch_init = rot_parent + 1 - BRANCH_ROWS_NUM;
    let rot_first_child = rot_branch_init + 1;
    let rot_first_child_prev = rot_first_child - BRANCH_ROWS_NUM;
    circuit!([meta, _cb!()], {
        let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
        ifx! {branch.is_extension() => {
            let key_mult_prev = ifx!{is_first_level => {
                1.expr()
            } elsex {
                a!(accs.key.mult, rot_first_child_prev)
            }};
            (a!(accs.key.rlc, rot_parent), key_mult_prev * a!(accs.mult_diff, rot_first_child))
        } elsex {
            ifx!{is_first_level => {
                (0.expr(), 1.expr())
            } elsex {
                (a!(accs.key.rlc, rot_first_child_prev), a!(accs.key.mult, rot_first_child_prev))
            }}
        }}
    })
}

pub(crate) fn extend_rand<F: FieldExt>(r: &[Expression<F>]) -> Vec<Expression<F>> {
    [
        r.to_vec(),
        r.iter()
            .map(|v| r.last().unwrap().expr() * v.clone())
            .collect::<Vec<_>>(),
    ]
    .concat()
}

pub(crate) fn bytes_into_rlc<F: FieldExt>(expressions: &[u8], r: F) -> F {
    let mut rlc = F::zero();
    let mut mult = F::one();
    for expr in expressions.iter() {
        rlc += F::from(*expr as u64) * mult;
        mult *= r;
    }
    rlc
}

/// MPTConstraintBuilder
pub struct MPTConstraintBuilder<F> {
    pub base: ConstraintBuilder<F>,
    /// Number of non-zero s bytes
    pub length_s: Vec<(Expression<F>, Expression<F>)>,
    /// Number of non-zero s bytes in c bytes (when only using s length)
    pub length_sc: Expression<F>,
    /// Number of non-zero c bytes
    pub length_c: Vec<(Expression<F>, Expression<F>)>,
    /// The range to check in s bytes
    pub range_s: Vec<(Expression<F>, Expression<F>)>,
}

impl<F: FieldExt> MPTConstraintBuilder<F> {
    const DEFAULT_LENGTH_S: usize = 34;
    const DEFAULT_LENGTH_C: usize = 32;
    const NUM_BYTES_SKIP: usize = 2; // RLP bytes never need to be zero checked
    const DEFAULT_RANGE: FixedTableTag = FixedTableTag::RangeKeyLen256;

    pub(crate) fn new(max_degree: usize) -> Self {
        MPTConstraintBuilder {
            base: ConstraintBuilder::new(max_degree),
            length_s: Vec::new(),
            length_sc: 0.expr(),
            length_c: Vec::new(),
            range_s: Vec::new(),
        }
    }

    pub(crate) fn set_length_s(&mut self, length: Expression<F>) {
        self.length_s.push((
            self.base.get_condition_expr(),
            Self::DEFAULT_LENGTH_S.expr() - (length - Self::NUM_BYTES_SKIP.expr()),
        ));
    }

    pub(crate) fn set_length_c(&mut self, length: Expression<F>) {
        self.length_c.push((
            self.base.get_condition_expr(),
            Self::DEFAULT_LENGTH_C.expr() - (length - Self::NUM_BYTES_SKIP.expr()),
        ));
    }

    pub(crate) fn set_length_sc(&mut self, is_s: bool, length: Expression<F>) {
        if is_s {
            self.set_length_s(length);
        } else {
            self.set_length_c(length);
        }
    }

    pub(crate) fn set_length(&mut self, length: Expression<F>) {
        self.set_length_s(length);
        self.length_sc = self.length_sc.expr() + self.base.get_condition_expr();
    }

    pub(crate) fn get_length_s(&self) -> Expression<F> {
        Self::DEFAULT_LENGTH_S.expr() - self.length_s.apply_conditions()
    }

    pub(crate) fn get_length_c(&self) -> Expression<F> {
        Self::DEFAULT_LENGTH_C.expr() - self.length_c.apply_conditions()
    }

    pub(crate) fn set_range_s(&mut self, range: Expression<F>) {
        self.range_s.push((
            self.base.get_condition_expr(),
            Self::DEFAULT_RANGE.expr() - range,
        ));
    }

    pub(crate) fn get_range_s(&self) -> Expression<F> {
        Self::DEFAULT_RANGE.expr() - self.range_s.apply_conditions()
    }
}

use std::{marker::PhantomData, ops::Range};

use crate::{
    _cb, circuit,
    circuit_tools::{Conditionable, ConstraintBuilder, DataTransition, LRCable},
    evm_circuit::util::rlc,
    mpt_circuit::param::{
        KEY_TERMINAL_PREFIX_EVEN, RLP_HASH_VALUE, RLP_LIST_LONG, RLP_LIST_SHORT, RLP_SHORT,
    },
    util::Expr,
};
use gadgets::util::{and, not, or};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};

use super::{
    columns::MainCols,
    param::{
        ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
        ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_0_C_START, BRANCH_0_S_START, BRANCH_ROWS_NUM,
        IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, IS_C_BRANCH_NON_HASHED_POS, IS_C_EXT_LONGER_THAN_55_POS,
        IS_C_EXT_NODE_NON_HASHED_POS, IS_S_BRANCH_NON_HASHED_POS, IS_S_EXT_LONGER_THAN_55_POS,
        IS_S_EXT_NODE_NON_HASHED_POS, KEY_TERMINAL_PREFIX_ODD, NIBBLES_COUNTER_POS,
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
    pub(crate) is_longer_than_55: Expression<F>,
    pub(crate) is_branch_non_hashed: Expression<F>,
    pub(crate) is_ext_non_hashed: Expression<F>,
    pub(crate) is_c1: Expression<F>,
    pub(crate) is_c16: Expression<F>,
    pub(crate) is_branch_s_placeholder: Expression<F>,
    pub(crate) is_branch_c_placeholder: Expression<F>,
    pub(crate) nibbles_counter: DataTransition<F>,
}

// To reduce the expression degree, we pack together multiple information.
// Constraints for the selectors are in `extension_node.rs`.
// Note: even and odd refers to number of nibbles that are compactly encoded.
impl<F: FieldExt> BranchNodeInfo<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        ctx: MPTContext<F>,
        is_s: bool,
        rot_branch_init: i32,
    ) -> Self {
        let s_main = ctx.s_main;
        let rot = Rotation(rot_branch_init);
        let is_short_c16 = meta.query_advice(s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM], rot);
        let is_short_c1 = meta.query_advice(s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM], rot);
        let is_long_even_c16 =
            meta.query_advice(s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM], rot);
        let is_long_even_c1 =
            meta.query_advice(s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM], rot);
        let is_long_odd_c16 =
            meta.query_advice(s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM], rot);
        let is_long_odd_c1 = meta.query_advice(s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM], rot);

        let is_longer_than_55 = meta.query_advice(
            s_main.bytes[if is_s {
                IS_S_EXT_LONGER_THAN_55_POS
            } else {
                IS_C_EXT_LONGER_THAN_55_POS
            } - RLP_NUM],
            rot,
        );
        let is_ext_non_hashed = meta.query_advice(
            s_main.bytes[if is_s {
                IS_S_EXT_NODE_NON_HASHED_POS
            } else {
                IS_C_EXT_NODE_NON_HASHED_POS
            } - RLP_NUM],
            rot,
        );

        let is_branch_non_hashed = meta.query_advice(
            s_main.bytes[if is_s {
                IS_S_BRANCH_NON_HASHED_POS
            } else {
                IS_C_BRANCH_NON_HASHED_POS
            } - RLP_NUM],
            rot,
        );

        let is_c1 = meta.query_advice(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], rot);
        let is_c16 = meta.query_advice(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], rot);

        let is_branch_s_placeholder =
            meta.query_advice(s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM], rot);
        let is_branch_c_placeholder =
            meta.query_advice(s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], rot);

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
            is_longer_than_55,
            is_branch_non_hashed,
            is_ext_non_hashed,
            is_c1,
            is_c16,
            is_branch_s_placeholder,
            is_branch_c_placeholder,
            nibbles_counter,
        }
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

    pub(crate) fn is_extension(&self) -> Expression<F> {
        self.is_even() + self.is_odd()
    }

    // Combinations that make the key even
    pub(crate) fn is_ext_even(&self) -> Expression<F> {
        self.is_short_c16.expr() + self.is_long_even_c1.expr() + self.is_long_odd_c16.expr()
    }

    // Combinations that make the key odd
    pub(crate) fn is_ext_odd(&self) -> Expression<F> {
        self.is_short_c1.expr() + self.is_long_even_c16.expr() + self.is_long_odd_c1.expr()
    }

    pub(crate) fn is_even(&self) -> Expression<F> {
        self.is_long_even_c16.expr() + self.is_long_even_c1.expr()
    }

    pub(crate) fn is_odd(&self) -> Expression<F> {
        self.is_long_odd() + self.is_short()
    }

    pub(crate) fn is_long_odd(&self) -> Expression<F> {
        self.is_long_odd_c16.expr() + self.is_long_odd_c1.expr()
    }

    pub(crate) fn is_long_even(&self) -> Expression<F> {
        self.is_even()
    }

    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short_c16.expr() + self.is_short_c1.expr()
    }

    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long_even() + self.is_long_odd()
    }

    pub(crate) fn is_key_even(&self) -> Expression<F> {
        self.is_c1.expr()
    }

    pub(crate) fn is_key_odd(&self) -> Expression<F> {
        self.is_c16.expr()
    }

    pub(crate) fn is_s_placeholder(&self) -> Expression<F> {
        self.is_branch_s_placeholder.expr()
    }

    pub(crate) fn is_c_placeholder(&self) -> Expression<F> {
        self.is_branch_c_placeholder.expr()
    }

    pub(crate) fn is_placeholder(&self) -> Expression<F> {
        if self.is_s {
            self.is_s_placeholder()
        } else {
            self.is_c_placeholder()
        }
    }

    pub(crate) fn is_s_or_c_placeholder(&self) -> Expression<F> {
        self.is_s_placeholder() + self.is_c_placeholder()
    }

    pub(crate) fn is_branch_non_hashed(&self) -> Expression<F> {
        self.is_branch_non_hashed.expr()
    }

    pub(crate) fn is_ext_non_hashed(&self) -> Expression<F> {
        self.is_ext_non_hashed.expr()
    }

    pub(crate) fn nibbles_counter(&self) -> DataTransition<F> {
        self.nibbles_counter.clone()
    }

    pub(crate) fn set_is_s(&mut self, is_s: bool) {
        self.is_s = is_s;
    }

    pub(crate) fn is_below_account(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        self.ctx.is_account(meta, self.rot_branch_init - 1)
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

    /// Length of the key (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_len(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_short() + self.is_long() => get_len_list_short(a!(self.ctx.s_main.rlp1)),
                self.is_longer_than_55 => get_len_short(a!(self.ctx.s_main.bytes[0])),
            }
        })
    }

    /// Number of RLP bytes for the extension row
    pub(crate) fn ext_num_rlp_bytes(&self, _meta: &mut VirtualCells<F>) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_short() + self.is_long() => 1.expr(),
                self.is_longer_than_55 => 2.expr(),
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
                self.is_longer_than_55 => get_len_short(a!(self.ctx.s_main.bytes[0], rel_rot)),
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
                self.is_longer_than_55 => 2.expr(),
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
    pub(crate) fn num_bytes(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            ifx! {self.is_long() => {
                2.expr() + a!(self.ctx.s_main.rlp2, self.rot_key)
            } elsex {
                get_num_bytes_list_short(a!(self.ctx.s_main.rlp1, self.rot_key))
            }}
        })
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(
        &self,
        _meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            matchx! {
                self.is_very_short() => 1.expr(),
                self.is_short() => 2.expr(),
                self.is_long() => 3.expr(),
            }
        })
    }

    /// Length of the key (excluding RLP bytes)
    pub(crate) fn key_len(
        &self,
        _meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        circuit!([_meta, cb], {
            matchx! {
                self.is_very_short() => 1.expr(), // 1 byte in s_rlp2
                self.is_short() => get_len_short(a!(self.ctx.s_main.rlp2, self.rot_key)),
                self.is_long() => get_len_short(a!(self.ctx.s_main.bytes[0], self.rot_key)),
            }
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        self.num_rlp_bytes(meta, cb) + self.key_len(meta, cb)
    }

    pub(crate) fn num_key_nibbles(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        is_key_odd: Expression<F>,
    ) -> Expression<F> {
        let key_len = self.key_len(meta, cb);
        get_num_nibbles(meta, cb, key_len, is_key_odd)
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
                key_rlc(
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

    pub(crate) fn is_nonce_long(&self) -> Expression<F> {
        self.is_nonce_long.expr()
    }

    pub(crate) fn is_balance_long(&self) -> Expression<F> {
        self.is_balance_long.expr()
    }

    pub(crate) fn nonce_len(
        &self,
        meta: &mut VirtualCells<F>,
        _cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        circuit!([meta, _cb], {
            2.expr() + a!(self.ctx.s_main.rlp2, self.rot_key)
        })
    }

    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(
        &self,
        meta: &mut VirtualCells<F>,
        _cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        circuit!([meta, _cb], {
            2.expr() + a!(self.ctx.s_main.rlp2, self.rot_key)
        })
    }

    /// Returns the length of the key
    pub(crate) fn key_len(
        &self,
        _meta: &mut VirtualCells<F>,
        _cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        circuit!([_meta, _cb], {
            get_len_short(a!(self.ctx.s_main.bytes[0], self.rot_key))
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        self.num_rlp_bytes(meta, cb) + self.key_len(meta, cb)
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(
        &self,
        _meta: &mut VirtualCells<F>,
        _cb: &mut ConstraintBuilder<F>,
    ) -> Expression<F> {
        // 2 RLP bytes + 1 byte that contains the key length.
        3.expr()
    }

    pub(crate) fn nonce_balance_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        _cb: &mut ConstraintBuilder<F>,
        nonce_rlc: Expression<F>,
        balance_rlc: Expression<F>,
        mult_prev: Expression<F>,
        mult_nonce: Expression<F>,
        rot_nonce: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb], {
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
        _cb: &mut ConstraintBuilder<F>,
        storage_rlc: Expression<F>,
        codehash_rlc: Expression<F>,
        mult_prev: Expression<F>,
        rot_storage: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb], {
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
        _cb: &mut ConstraintBuilder<F>,
        main: MainCols<F>,
        value_rlc: Expression<F>,
        is_long: Expression<F>,
        rot_nonce: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb], {
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
}

pub(crate) fn key_rlc<F: FieldExt>(
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
            (get_terminal_odd_nibble(first_byte.expr()) * key_mult_prev.expr(), key_mult_prev.expr() * ctx.r[0].expr())
        } elsex {
            require!(first_byte => KEY_TERMINAL_PREFIX_EVEN);
            (0.expr(), key_mult_prev.expr() * key_mult_first_even.expr())
        }};
        rlc + ctx.rlc_chain(meta, range.start + 1..range.end, 0, mult.expr())
    })
}

pub(crate) fn get_terminal_odd_nibble<F: FieldExt>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_TERMINAL_PREFIX_ODD.expr()
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
    cb: &mut ConstraintBuilder<F>,
    key_len: Expression<F>,
    is_key_odd: Expression<F>,
) -> Expression<F> {
    circuit!([meta, cb], {
        ifx! {is_key_odd => {
            key_len.expr() * 2.expr() - 1.expr()
        } elsex {
            (key_len.expr() - 1.expr()) * 2.expr()
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
            Self::DEFAULT_LENGTH_S.expr() - length,
        ));
    }

    pub(crate) fn set_length_c(&mut self, length: Expression<F>) {
        self.length_c.push((
            self.base.get_condition_expr(),
            Self::DEFAULT_LENGTH_C.expr() - length,
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

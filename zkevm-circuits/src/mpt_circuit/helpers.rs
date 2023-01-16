use std::ops::Range;

use crate::{
    circuit,
    circuit_tools::{Conditionable, ConstraintBuilder, DataTransition},
    mpt_circuit::param::{KEY_TERMINAL_PREFIX_EVEN, RLP_LIST_LONG, RLP_LIST_SHORT, RLP_SHORT},
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
        BRANCH_0_C_START, BRANCH_0_S_START, BRANCH_ROWS_NUM, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
        IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, IS_C_BRANCH_NON_HASHED_POS,
        IS_C_EXT_LONGER_THAN_55_POS, IS_C_EXT_NODE_NON_HASHED_POS, IS_S_BRANCH_NON_HASHED_POS,
        IS_S_EXT_LONGER_THAN_55_POS, IS_S_EXT_NODE_NON_HASHED_POS, KEY_TERMINAL_PREFIX_ODD,
        NIBBLES_COUNTER_POS,
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
    pub(crate) len: (Expression<F>, Expression<F>),
    pub(crate) nibbles_counter: DataTransition<F>,
}

// To reduce the expression degree, we pack together multiple information.
// Constraints for the selectors are in `extension_node.rs`.
// Note: even and odd refers to number of nibbles that are compactly encoded.
impl<F: FieldExt> BranchNodeInfo<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        s_main: MainCols<F>,
        is_s: bool,
        rot_branch_init: i32,
    ) -> BranchNodeInfo<F> {
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

        let len = get_branch_len(meta, s_main, rot, is_s);

        BranchNodeInfo {
            is_s,
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
            len,
            nibbles_counter,
        }
    }

    pub(crate) fn is_extension(&self) -> Expression<F> {
        self.is_even() + self.is_odd()
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

    pub(crate) fn len(&self) -> Expression<F> {
        self.len.0.expr() + self.len.1.expr()
    }

    pub(crate) fn raw_len(&self) -> Expression<F> {
        self.len.1.expr()
    }

    pub(crate) fn nibbles_counter(&self) -> DataTransition<F> {
        self.nibbles_counter.clone()
    }

    pub(crate) fn set_is_s(&mut self, is_s: bool) {
        self.is_s = is_s;
    }
}

#[derive(Clone)]
pub(crate) struct StorageLeafInfo<F> {
    pub(crate) rot_key: i32,
    pub(crate) flag1: Expression<F>,
    pub(crate) flag2: Expression<F>,
}

impl<F: FieldExt> StorageLeafInfo<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        ctx: MPTContext<F>,
        rot_key: i32,
    ) -> StorageLeafInfo<F> {
        let rot = Rotation(rot_key);
        let flag1 = meta.query_advice(ctx.accumulators.s_mod_node_rlc, rot);
        let flag2 = meta.query_advice(ctx.accumulators.c_mod_node_rlc, rot);
        StorageLeafInfo {
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
    pub(crate) fn len(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            ifx! {self.is_long() => {
                2.expr() + a!(ctx.s_main.rlp2, self.rot_key)
            } elsex {
                1.expr() + (a!(ctx.s_main.rlp1, self.rot_key) - RLP_LIST_SHORT.expr())
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
        ctx: MPTContext<F>,
    ) -> Expression<F> {
        circuit!([_meta, cb], {
            matchx! {
                self.is_very_short() => 1.expr(), // 1 byte in s_rlp2
                self.is_short() => a!(ctx.s_main.rlp2, self.rot_key) - RLP_SHORT.expr(),
                self.is_long() => a!(ctx.s_main.bytes[0], self.rot_key) - RLP_SHORT.expr(),
            }
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Expression<F> {
        self.num_rlp_bytes(meta, cb) + self.key_len(meta, cb, ctx)
    }

    pub(crate) fn num_key_nibbles(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_key_odd: Expression<F>,
    ) -> Expression<F> {
        let key_len = self.key_len(meta, cb, ctx);
        get_num_nibbles(meta, cb, key_len, is_key_odd)
    }

    /// Key data is read from the current row, not at rot_key!
    pub(crate) fn key_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        ctx: MPTContext<F>,
        key_mult_prev: Expression<F>,
        is_key_odd: Expression<F>,
        key_mult_first_even: Expression<F>,
        is_longer_than_55: bool,
    ) -> Expression<F> {
        let calc_rlc =
            |meta: &mut VirtualCells<F>, cb: &mut ConstraintBuilder<F>, range: Range<usize>| {
                key_rlc(
                    meta,
                    cb,
                    ctx.clone(),
                    range,
                    key_mult_prev.expr(),
                    is_key_odd.expr(),
                    key_mult_first_even.expr(),
                )
            };
        circuit!([meta, cb], {
            matchx! {
                self.is_short() => {
                    // First key byte is at `s_main.bytes[0]`.
                    calc_rlc(meta, cb, 2..35)
                },
                self.is_long() => {
                    if is_longer_than_55 {
                        // `s_main.rlp1` needs to be 248.
                        require!(a!(ctx.s_main.rlp1) => (RLP_LIST_LONG + 1));
                    }
                    // First key byte is at `s_main.bytes[1]`.
                    calc_rlc(meta, cb, 3..36)
                },
                self.has_no_nibble() => {
                    require!(a!(ctx.s_main.rlp2) => KEY_TERMINAL_PREFIX_EVEN);
                    0.expr()
                },
                self.has_one_nibble() => {
                    get_terminal_odd_nibble(a!(ctx.s_main.rlp2)) * key_mult_prev.expr()
                },
            }
        })
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

pub(crate) fn get_rlp_meta_bytes<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    is_s: bool,
    rot: Rotation,
) -> [Expression<F>; 2] {
    //`s_rlp1, s_rlp2` is used for `S` and `s_main.bytes[0], s_main.bytes[1]` is
    //`s_rlp1, used for `C`
    let (rlp_column_1, rlp_column_2) = if is_s {
        (s_main.rlp1, s_main.rlp2)
    } else {
        (s_main.bytes[0], s_main.bytes[1])
    };
    [
        meta.query_advice(rlp_column_1, rot),
        meta.query_advice(rlp_column_2, rot),
    ]
}

pub(crate) fn get_num_rlp_bytes_selectors<F: FieldExt>(
    rlp_meta_bytes: [Expression<F>; 2],
) -> [Expression<F>; 3] {
    // rlp1, rlp2: 1, 1 means 1 RLP byte
    // rlp1, rlp2: 1, 0 means 2 RLP bytes
    // rlp1, rlp2: 0, 1 means 3 RLP bytes
    let rlp = rlp_meta_bytes;
    let one_rlp_byte = and::expr([rlp[0].expr(), rlp[1].expr()]);
    let two_rlp_bytes = and::expr([rlp[0].expr(), not::expr(rlp[1].expr())]);
    let three_rlp_bytes = and::expr([not::expr(rlp[0].expr()), rlp[1].expr()]);
    [one_rlp_byte, two_rlp_bytes, three_rlp_bytes]
}

pub(crate) fn get_rlp_value_bytes<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    is_s: bool,
    rot: Rotation,
) -> [Expression<F>; 3] {
    let offset = if is_s {
        BRANCH_0_S_START
    } else {
        BRANCH_0_C_START
    } - RLP_NUM;
    s_main.bytes[offset..offset + 3]
        .iter()
        .map(|byte| meta.query_advice(*byte, rot))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

pub(crate) fn get_branch_len<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    rot_into_branch_init: Rotation,
    is_s: bool,
) -> (Expression<F>, Expression<F>) {
    let rlp_meta_bytes = get_rlp_meta_bytes(meta, s_main.clone(), is_s, rot_into_branch_init);
    let num_rlp_byte_selectors = get_num_rlp_bytes_selectors(rlp_meta_bytes);
    let rlp_bytes = get_rlp_value_bytes(meta, s_main.clone(), is_s, rot_into_branch_init);
    let num_rlp_bytes = num_rlp_byte_selectors
        .iter()
        .enumerate()
        .fold(0.expr(), |acc, (idx, sel)| {
            acc.expr() + sel.expr() * (idx + 1).expr()
        });
    (
        num_rlp_bytes,
        num_rlp_byte_selectors[0].expr() * (rlp_bytes[0].expr() - 192.expr())
            + num_rlp_byte_selectors[1].expr() * (rlp_bytes[1].expr())
            + num_rlp_byte_selectors[2].expr()
                * (rlp_bytes[1].expr() * 256.expr() + rlp_bytes[2].expr()),
    )
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

pub(crate) fn accumulate_rand<F: FieldExt>(rs: &[Expression<F>]) -> Vec<Expression<F>> {
    let mut r = Vec::new();
    let mut acc = 1.expr();
    for rs in rs.iter() {
        acc = acc.expr() * rs.expr();
        r.push(acc.expr());
    }
    r
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

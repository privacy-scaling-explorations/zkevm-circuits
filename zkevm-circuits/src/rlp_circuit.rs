//! Circuit implementation for RLP-encoding verification. Please refer: https://hackmd.io/@rohitnarurkar/S1zSz0KM9.

use eth_types::Field;
use gadgets::{
    comparator::{ComparatorChip, ComparatorConfig, ComparatorInstruction},
    less_than::{LtChip, LtConfig, LtInstruction},
};
use halo2_proofs::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, VirtualCells},
    poly::Rotation,
};

use crate::{
    evm_circuit::{
        util::{and, constraint_builder::BaseConstraintBuilder, not, or},
        witness::{
            receipt::{RlpReceiptTag, N_RECEIPT_TAGS},
            rlp_witness::{RlpDataType, RlpWitnessGen},
            tx::{RlpTxTag, N_TX_TAGS},
        },
    },
    util::Expr,
};

#[derive(Clone, Debug)]
#[allow(dead_code)]
/// Config for the RLP circuit.
pub struct Config<F> {
    /// Denotes the randomness.
    r: F,
    /// Denotes the unusable rows from the layout.
    minimum_rows: usize,
    /// Denotes whether or not the row is enabled.
    q_enable: Column<Fixed>,
    /// Denotes whether the row is the first row in the layout.
    q_first: Column<Fixed>,
    /// Denotes whether the row is the last row in the layout.
    q_last: Selector,
    /// Denotes whether the row is the last byte in the RLP-encoded data.
    is_final: Column<Advice>,
    /// Denotes the index of this row, starting from `1` and ending at `n`
    /// where `n` is the byte length of the RLP-encoded data.
    index: Column<Advice>,
    /// Denotes the index of this row, but reversed. It starts from `n` where
    /// `n` is the byte length of the RLP-encoded data and ends at `1`.
    rindex: Column<Advice>,
    /// Denotes the data type, whether this circuit encodes a tx or tx receipt.
    data_type: Column<Advice>,
    /// Denotes the byte value at this row index from the RLP-encoded data.
    value: Column<Advice>,
    /// Denotes the tag assigned to this row.
    tag: Column<Advice>,
    /// List of columns that are assigned:
    /// val := (tag - RlpTxTag::{Variant}).inv()
    tx_tags: [Column<Advice>; N_TX_TAGS],
    /// List of columns that are assigned:
    /// val := (tag - RlpReceiptTag::{Variant}).inv()
    receipt_tags: [Column<Advice>; N_RECEIPT_TAGS],
    /// Denotes a decrementing index specific to the current tag.
    tag_index: Column<Advice>,
    /// Denotes the current tag's span in bytes.
    tag_length: Column<Advice>,
    /// Denotes an accumulator for the length of data, in the case where len >
    /// 55 and the length is represented in its big-endian form.
    length_acc: Column<Advice>,
    /// Denotes an accumulator for the value field over all rows (bytes).
    value_rlc: Column<Advice>,
    /// Denotes the keccak-256 hash of the RLP-encoded data.
    hash: Column<Advice>,
    /// Denotes whether the row appears after `is_final`, hence the purpose is
    /// padding.
    padding: Column<Advice>,

    /// Comparison chip to check: 1 <= tag_index.
    tag_index_cmp_1: ComparatorConfig<F, 1>,
    /// Comparison chip to check: tag_index <= tag_length.
    tag_index_length_cmp: ComparatorConfig<F, 1>,
    /// Comparison chip to check: 1 <= tag_length.
    tag_length_cmp_1: ComparatorConfig<F, 1>,

    /// Lt chip to check: tag_index < 10.
    tag_index_lt_10: LtConfig<F, 1>,
    /// Lt chip to check: tag_index < 34.
    tag_index_lt_34: LtConfig<F, 1>,

    /// Lt chip to check: 127 < value.
    value_gt_127: LtConfig<F, 1>,
    /// Lt chip to check: 183 < value.
    value_gt_183: LtConfig<F, 1>,
    /// Lt chip to check: value < 128.
    value_lt_128: LtConfig<F, 1>,
    /// Lt chip to check: value < 184.
    value_lt_184: LtConfig<F, 1>,
    /// Lt chip to check: value < 192.
    value_lt_192: LtConfig<F, 1>,

    /// Comparison chip to check: 0 <= length_acc.
    length_acc_cmp_0: ComparatorConfig<F, 1>,

    /// Denotes a tuple (value_rlc, n, 1, keccak256(rlp_encode(input))).
    keccak_tuple: [Column<Advice>; 4],
}

impl<F: Field> Config<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_last = meta.selector();
        let is_final = meta.advice_column();
        let index = meta.advice_column();
        let rindex = meta.advice_column();
        let data_type = meta.advice_column();
        let value = meta.advice_column();
        let tag = meta.advice_column();
        let tx_tags = array_init::array_init(|_| meta.advice_column());
        let receipt_tags = array_init::array_init(|_| meta.advice_column());
        let tag_index = meta.advice_column();
        let tag_length = meta.advice_column();
        let length_acc = meta.advice_column();
        let value_rlc = meta.advice_column();
        let hash = meta.advice_column();
        let padding = meta.advice_column();

        // Enable the comparator and lt chips if the current row is enabled and is not a
        // padding row.
        let cmp_lt_enabled = |meta: &mut VirtualCells<F>| {
            and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ])
        };

        let tag_index_cmp_1 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 1.expr(),
            |meta| meta.query_advice(tag_index, Rotation::cur()),
        );
        let tag_index_length_cmp = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |meta| meta.query_advice(tag_length, Rotation::cur()),
        );
        let tag_length_cmp_1 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 1.expr(),
            |meta| meta.query_advice(tag_length, Rotation::cur()),
        );
        let tag_index_lt_10 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |_meta| 10.expr(),
        );
        let tag_index_lt_34 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |_meta| 34.expr(),
        );

        let value_gt_127 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 127.expr(),
            |meta| meta.query_advice(value, Rotation::cur()),
        );
        let value_gt_183 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 183.expr(),
            |meta| meta.query_advice(value, Rotation::cur()),
        );
        let value_lt_128 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(value, Rotation::cur()),
            |_meta| 128.expr(),
        );
        let value_lt_184 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(value, Rotation::cur()),
            |_meta| 184.expr(),
        );
        let value_lt_192 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(value, Rotation::cur()),
            |_meta| 192.expr(),
        );

        let length_acc_cmp_0 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 0.expr(),
            |meta| meta.query_advice(length_acc, Rotation::cur()),
        );

        let keccak_tuple = array_init::array_init(|_| meta.advice_column());

        meta.create_gate("DataType::Transaction", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // Helper macro to declare booleans to check the current row tag.
            macro_rules! is_tx_tag {
                ($var:ident, $tag_variant:ident) => {
                    let $var = |meta: &mut VirtualCells<F>| {
                        1.expr()
                            - meta.query_advice(tag, Rotation::cur())
                                * meta.query_advice(
                                    tx_tags[RlpTxTag::$tag_variant as usize],
                                    Rotation::cur(),
                                )
                    };
                };
            }

            is_tx_tag!(is_prefix, Prefix);
            is_tx_tag!(is_nonce, Nonce);
            is_tx_tag!(is_gas_price, GasPrice);
            is_tx_tag!(is_gas, Gas);
            is_tx_tag!(is_to_prefix, ToPrefix);
            is_tx_tag!(is_to, To);
            is_tx_tag!(is_value, Value);
            is_tx_tag!(is_data_prefix, DataPrefix);
            is_tx_tag!(is_data, Data);

            cb.condition(is_prefix(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
                let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
                let (tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);

                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Prefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Prefix.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Nonce",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Nonce.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                    cb.require_equal(
                        "rindex::next == length_acc",
                        meta.query_advice(rindex, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // if tag_index == tag_length && tag_length > 1
                cb.condition(tindex_eq_tlength.clone() * tlength_lt.clone(), |cb| {
                    cb.require_zero(
                        "183 < value < 192",
                        not::expr(and::expr(vec![
                            value_gt_183.is_lt(meta, None),
                            value_lt_192.is_lt(meta, None),
                        ])),
                    );
                    cb.require_equal(
                        "tag_index == value - 0xb7 + 1",
                        meta.query_advice(tag_index, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 182.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // if tag_index == tag_length && tag_length == 1
                cb.condition(tindex_eq_tlength * tlength_eq, |cb| {
                    cb.require_zero(
                        "127 < value < 184",
                        not::expr(and::expr(vec![
                            value_gt_127.is_lt(meta, None),
                            value_lt_184.is_lt(meta, None),
                        ])),
                    );
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                });

                // if tag_index < tag_length && tag_length > 1
                cb.condition(tindex_lt_tlength * tlength_lt, |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(value, Rotation::cur()),
                    );
                });
            });

            cb.condition(is_nonce(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
                let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
                let (_tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);

                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index == tag_length && tag_length == 1
                cb.condition(tindex_eq_tlength.clone() * tlength_eq, |cb| {
                    cb.require_equal("value < 128", value_lt_128.is_lt(meta, None), 1.expr());
                });

                // if tag_index == tag_length && tag_length > 1
                cb.condition(tindex_eq_tlength * tlength_lt, |cb| {
                    cb.require_equal("127 < value", value_gt_127.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == length_acc",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Nonce",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Nonce.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::GasPrice",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::GasPrice.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                });
            });

            cb.condition(is_gas_price(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
                let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
                let (_tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);

                // tag_index < 34
                cb.require_equal(
                    "tag_index < 34",
                    tag_index_lt_34.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index == tag_length && tag_length == 1
                cb.condition(tindex_eq_tlength.clone() * tlength_eq, |cb| {
                    cb.require_equal("value < 128", value_lt_128.is_lt(meta, None), 1.expr());
                });

                // if tag_index == tag_length && tag_length > 1
                cb.condition(tindex_eq_tlength * tlength_lt, |cb| {
                    cb.require_equal("127 < value", value_gt_127.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == length_acc",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::GasPrice",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::GasPrice.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Gas",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Gas.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                });
            });

            cb.condition(is_gas(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
                let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
                let (_tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);

                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index == tag_length && tag_length == 1
                cb.condition(tindex_eq_tlength.clone() * tlength_eq, |cb| {
                    cb.require_equal("value < 128", value_lt_128.is_lt(meta, None), 1.expr());
                });

                // if tag_index == tag_length && tag_length > 1
                cb.condition(tindex_eq_tlength * tlength_lt, |cb| {
                    cb.require_equal("127 < value", value_gt_127.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == length_acc",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Gas",
                        meta.query_advice(tag, Rotation::cur()),
                        RlpTxTag::Gas.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::ToPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::ToPrefix.expr(),
                    );
                });
            });

            cb.condition(is_to_prefix(meta), |cb| {
                cb.require_equal(
                    "tag_index == 1",
                    meta.query_advice(tag_index, Rotation::cur()),
                    1.expr(),
                );
                cb.require_equal(
                    "tag_length == 1",
                    meta.query_advice(tag_length, Rotation::cur()),
                    1.expr(),
                );
                cb.require_equal(
                    "value == 148",
                    meta.query_advice(value, Rotation::cur()),
                    148.expr(),
                );
                cb.require_equal(
                    "tag::next == RlpTxTag::To",
                    meta.query_advice(tag, Rotation::next()),
                    RlpTxTag::To.expr(),
                );
                cb.require_equal(
                    "tag_index::next == 20",
                    meta.query_advice(tag_index, Rotation::next()),
                    20.expr(),
                );
                cb.require_equal(
                    "tag_length::next == 20",
                    meta.query_advice(tag_length, Rotation::next()),
                    20.expr(),
                );
            });

            cb.condition(is_to(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::To",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::To.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Value",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Value.expr(),
                    );
                    cb.require_equal(
                        "tag_index:next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                });
            });

            cb.condition(is_value(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
                let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
                let (_tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);

                // tag_index < 34
                cb.require_equal(
                    "tag_index < 34",
                    tag_index_lt_34.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index == tag_length && tag_length == 1
                cb.condition(tindex_eq_tlength.clone() * tlength_eq, |cb| {
                    cb.require_equal("value < 128", value_lt_128.is_lt(meta, None), 1.expr());
                });

                // if tag_index == tag_length && tag_length > 1
                cb.condition(tindex_eq_tlength * tlength_lt, |cb| {
                    cb.require_equal("127 < value", value_gt_127.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == length_acc",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Value",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Value.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag:TxDataPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::DataPrefix.expr(),
                    );
                });
            });

            cb.condition(is_data_prefix(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
                let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
                let (tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);
                let (length_acc_gt_0, length_acc_eq_0) = length_acc_cmp_0.expr(meta, None);

                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::DataPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::DataPrefix.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    // if length_acc == 0
                    cb.condition(length_acc_eq_0, |cb| {
                        cb.require_equal(
                            "RlpTxTag::DataPrefix: is_final == 1",
                            meta.query_advice(is_final, Rotation::cur()),
                            1.expr(),
                        );
                    });
                    // if length_acc > 0
                    cb.condition(length_acc_gt_0, |cb| {
                        cb.require_equal(
                            "tag::next == RlpTxTag::Data",
                            meta.query_advice(tag, Rotation::next()),
                            RlpTxTag::Data.expr(),
                        );
                        cb.require_equal(
                            "tag_index::next == tag_length::next",
                            meta.query_advice(tag_index, Rotation::next()),
                            meta.query_advice(tag_length, Rotation::next()),
                        );
                        cb.require_equal(
                            "tag_length::next == length_acc",
                            meta.query_advice(tag_length, Rotation::next()),
                            meta.query_advice(length_acc, Rotation::cur()),
                        );
                    });
                });

                // if tag_index == tag_length && tag_length > 1
                cb.condition(tindex_eq_tlength.clone() * tlength_lt.clone(), |cb| {
                    cb.require_zero("value > 183", value_gt_183.is_lt(meta, None));
                    cb.require_zero("value < 192", value_lt_192.is_lt(meta, None));
                    cb.require_equal(
                        "tag_index == (value - 0xb7) + 1",
                        meta.query_advice(tag_index, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 182.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                });

                // if tag_index < tag_length && tag_length > 1
                cb.condition(tindex_lt_tlength * tlength_lt, |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(value, Rotation::cur()),
                    );
                });

                // if tag_index == tag_length && tag_length == 1
                cb.condition(tindex_eq_tlength * tlength_eq, |cb| {
                    cb.require_zero("127 < value", value_gt_127.is_lt(meta, None));
                    cb.require_zero("value < 184", value_lt_184.is_lt(meta, None));
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                });
            });

            cb.condition(is_data(meta), |cb| {
                let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(tindex_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Data",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::Data.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_index - 1",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_index, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "tag_length::next == tag_length",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::cur()),
                    );
                });

                // if tag_index == 1
                cb.condition(tindex_eq, |cb| {
                    cb.require_equal(
                        "RlpTxTag::Data: is_final == 1",
                        meta.query_advice(is_final, Rotation::cur()),
                        1.expr(),
                    );
                });
            });

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                // Since DataType::Transaction = 0, !data_type = 1.
                not::expr(meta.query_advice(data_type, Rotation::cur())),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ]))
        });

        meta.create_gate("DataType::Receipt", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // Helper macro to declare booleans to check the current row tag.
            macro_rules! is_receipt_tag {
                ($var:ident, $tag_variant:ident) => {
                    let $var = |meta: &mut VirtualCells<F>| {
                        1.expr()
                            - meta.query_advice(tag, Rotation::cur())
                                * meta.query_advice(
                                    receipt_tags[RlpReceiptTag::$tag_variant as usize],
                                    Rotation::cur(),
                                )
                    };
                };
            }

            is_receipt_tag!(is_prefix, Prefix);
            is_receipt_tag!(is_status, Status);

            cb.condition(is_prefix(meta), |_cb| {});

            cb.condition(is_status(meta), |_cb| {});

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                // Since DataType::Receipt = 1, data_type = 1.
                meta.query_advice(data_type, Rotation::cur()),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ]))
        });

        // Constraints that always need to be satisfied.
        meta.create_gate("always", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean(
                "is_final is boolean",
                meta.query_advice(is_final, Rotation::cur()),
            );
            cb.require_boolean(
                "padding is boolean",
                meta.query_advice(padding, Rotation::cur()),
            );

            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        // Constraints for the first row in the layout.
        meta.create_gate("q_first == 1", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "value_rlc == value",
                meta.query_advice(value_rlc, Rotation::cur()),
                meta.query_advice(value, Rotation::cur()),
            );
            cb.require_zero("index == 1", meta.query_advice(index, Rotation::cur()));

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                meta.query_fixed(q_first, Rotation::cur()),
            ]))
        });

        // Constraints for every non-padding row except the first row.
        meta.create_gate("q_first == 0 and padding == 0", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "index == index_prev + 1",
                meta.query_advice(index, Rotation::cur()),
                meta.query_advice(index, Rotation::prev()) + 1.expr(),
            );
            cb.require_equal(
                "rindex == rindex_prev - 1",
                meta.query_advice(rindex, Rotation::cur()),
                meta.query_advice(rindex, Rotation::prev()) - 1.expr(),
            );
            cb.require_equal(
                "hash == hash_prev",
                meta.query_advice(hash, Rotation::cur()),
                meta.query_advice(hash, Rotation::prev()),
            );
            cb.require_equal(
                "value_rlc == (value_rlc_prev * r) + value",
                meta.query_advice(value_rlc, Rotation::cur()),
                meta.query_advice(value_rlc, Rotation::prev()) * r
                    + meta.query_advice(value, Rotation::cur()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_first, Rotation::cur())),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ]))
        });

        // Constraints for the last row of the RLP-encoded data.
        meta.lookup_any("keccak-256 verification for is_final == 1", |meta| {
            let enable = and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                meta.query_advice(is_final, Rotation::cur()),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ]);

            let lookup_columns = vec![value_rlc, index, rindex, hash];
            lookup_columns
                .iter()
                .zip(keccak_tuple.iter())
                .map(|(keccak_field, column)| {
                    (
                        enable.clone() * meta.query_advice(*column, Rotation::cur()),
                        meta.query_advice(*keccak_field, Rotation::cur()),
                    )
                })
                .collect()
        });

        // Constraints for every row except the first row.
        meta.create_gate("q_first == 0", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean(
                "padding can go 0 -> 1 only once",
                meta.query_advice(padding, Rotation::cur())
                    - meta.query_advice(padding, Rotation::prev()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_fixed(q_first, Rotation::cur())),
            ]))
        });

        // Constraints for the last row of the layout.
        meta.create_gate("q_last == 1", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "is_final == 1 or padding == 1",
                or::expr(vec![
                    meta.query_advice(is_final, Rotation::cur()),
                    meta.query_advice(padding, Rotation::cur()),
                ]),
                1.expr(),
            );

            cb.gate(meta.query_selector(q_last))
        });

        Self {
            r,
            minimum_rows: meta.minimum_rows(),
            q_enable,
            q_first,
            q_last,
            is_final,
            index,
            rindex,
            data_type,
            value,
            tag,
            tx_tags,
            receipt_tags,
            tag_index,
            tag_length,
            length_acc,
            value_rlc,
            hash,
            keccak_tuple,
            padding,

            tag_index_cmp_1,
            tag_index_length_cmp,
            tag_length_cmp_1,

            tag_index_lt_10,
            tag_index_lt_34,

            value_gt_127,
            value_gt_183,
            value_lt_128,
            value_lt_184,
            value_lt_192,

            length_acc_cmp_0,
        }
    }

    pub(crate) fn assign<RLP: RlpWitnessGen<F>>(
        &self,
        mut layouter: impl Layouter<F>,
        size: usize,
        witness: RLP,
    ) -> Result<(), Error> {
        let last_row_offset = size - self.minimum_rows + 1;

        let rows = witness.gen_witness(self.r);
        let n_rows = rows.len();

        let tag_index_cmp_1_chip = ComparatorChip::construct(self.tag_index_cmp_1.clone());
        let tag_index_length_cmp_chip =
            ComparatorChip::construct(self.tag_index_length_cmp.clone());
        let tag_length_cmp_1_chip = ComparatorChip::construct(self.tag_length_cmp_1.clone());

        let tag_index_lt_10_chip = LtChip::construct(self.tag_index_lt_10.clone());
        let tag_index_lt_34_chip = LtChip::construct(self.tag_index_lt_34.clone());

        let value_gt_127_chip = LtChip::construct(self.value_gt_127.clone());
        let value_gt_183_chip = LtChip::construct(self.value_gt_183.clone());
        let value_lt_128_chip = LtChip::construct(self.value_lt_128.clone());
        let value_lt_184_chip = LtChip::construct(self.value_lt_184.clone());
        let value_lt_192_chip = LtChip::construct(self.value_lt_192.clone());

        let length_acc_cmp_0_chip = ComparatorChip::construct(self.length_acc_cmp_0.clone());

        let mut value_rlc = F::zero();
        layouter.assign_region(
            || "assign RLP-encoded data",
            |mut region| {
                for (offset, row) in rows.iter().enumerate() {
                    // update value accumulator
                    value_rlc = value_rlc * self.r + F::from(row.value as u64);

                    // q_enable
                    region.assign_fixed(
                        || format!("assign q_enable {}", offset),
                        self.q_enable,
                        offset,
                        || Ok(F::one()),
                    )?;
                    // q_first
                    region.assign_fixed(
                        || format!("assign q_first {}", offset),
                        self.q_first,
                        offset,
                        || Ok(F::from((offset == 0) as u64)),
                    )?;
                    // q_last
                    if offset == last_row_offset {
                        self.q_last.enable(&mut region, offset)?;
                    }
                    // advices
                    for (name, column, value) in [
                        [
                            (
                                "is_final",
                                self.is_final,
                                F::from((row.index == n_rows) as u64),
                            ),
                            ("index", self.index, F::from(row.index as u64)),
                            (
                                "rindex",
                                self.rindex,
                                F::from((n_rows + 1 - row.index) as u64),
                            ),
                            ("data_type", self.data_type, F::from(row.data_type as u64)),
                            ("value", self.value, F::from(row.value as u64)),
                            ("tag", self.tag, F::from(row.tag as u64)),
                        ],
                        [
                            ("tag_index", self.tag_index, F::from(row.tag_index as u64)),
                            (
                                "tag_length",
                                self.tag_length,
                                F::from(row.tag_length as u64),
                            ),
                            ("length_acc", self.length_acc, F::from(row.length_acc)),
                            ("value_rlc", self.value_rlc, value_rlc),
                            ("hash", self.hash, row.hash),
                            ("padding", self.padding, F::zero()),
                        ],
                    ]
                    .join(self.tag_invs(Some(row.data_type), Some(row.tag)).as_slice())
                    {
                        region.assign_advice(
                            || format!("assign {} {}", name, offset),
                            column,
                            offset,
                            || Ok(value),
                        )?;
                    }

                    tag_index_cmp_1_chip.assign(
                        &mut region,
                        offset,
                        F::one(),
                        F::from(row.tag_index as u64),
                    )?;
                    tag_index_length_cmp_chip.assign(
                        &mut region,
                        offset,
                        F::from(row.tag_index as u64),
                        F::from(row.tag_length as u64),
                    )?;
                    tag_length_cmp_1_chip.assign(
                        &mut region,
                        offset,
                        F::one(),
                        F::from(row.tag_length as u64),
                    )?;
                    tag_index_lt_10_chip.assign(
                        &mut region,
                        offset,
                        F::from(row.tag_index as u64),
                        F::from(10u64),
                    )?;
                    tag_index_lt_34_chip.assign(
                        &mut region,
                        offset,
                        F::from(row.tag_index as u64),
                        F::from(34u64),
                    )?;
                    value_gt_127_chip.assign(
                        &mut region,
                        offset,
                        F::from(127u64),
                        F::from(row.value as u64),
                    )?;
                    value_gt_183_chip.assign(
                        &mut region,
                        offset,
                        F::from(183u64),
                        F::from(row.value as u64),
                    )?;
                    value_lt_128_chip.assign(
                        &mut region,
                        offset,
                        F::from(128u64),
                        F::from(row.value as u64),
                    )?;
                    value_lt_184_chip.assign(
                        &mut region,
                        offset,
                        F::from(184u64),
                        F::from(row.value as u64),
                    )?;
                    value_lt_192_chip.assign(
                        &mut region,
                        offset,
                        F::from(192u64),
                        F::from(row.value as u64),
                    )?;
                    length_acc_cmp_0_chip.assign(
                        &mut region,
                        offset,
                        F::zero(),
                        F::from(row.length_acc as u64),
                    )?;
                }

                for offset in n_rows..=last_row_offset {
                    // q_enable
                    region.assign_fixed(
                        || format!("assign q_enable {}", offset),
                        self.q_enable,
                        offset,
                        || Ok(F::one()),
                    )?;
                    // q_first
                    region.assign_fixed(
                        || format!("assign q_first {}", offset),
                        self.q_first,
                        offset,
                        || Ok(F::from((offset == 0) as u64)),
                    )?;
                    // q_last
                    if offset == last_row_offset {
                        self.q_last.enable(&mut region, offset)?;
                    }
                    // advices
                    for (name, column, value) in [
                        [
                            ("is_final", self.is_final, F::zero()),
                            ("index", self.index, F::zero()),
                            ("rindex", self.rindex, F::zero()),
                            ("data_type", self.data_type, F::zero()),
                            ("value", self.value, F::zero()),
                            ("tag", self.tag, F::zero()),
                        ],
                        [
                            ("tag_index", self.tag_index, F::zero()),
                            ("tag_length", self.tag_length, F::zero()),
                            ("length_acc", self.length_acc, F::zero()),
                            ("value_rlc", self.value_rlc, F::zero()),
                            ("hash", self.hash, F::zero()),
                            ("padding", self.padding, F::one()),
                        ],
                    ]
                    .join(self.tag_invs(None, None).as_slice())
                    {
                        region.assign_advice(
                            || format!("assign {} {}", name, offset),
                            column,
                            offset,
                            || Ok(value),
                        )?;
                    }
                }

                Ok(())
            },
        )
    }

    fn tag_invs(
        &self,
        data_type: Option<RlpDataType>,
        tag: Option<u8>,
    ) -> Vec<(&str, Column<Advice>, F)> {
        match data_type {
            Some(RlpDataType::Transaction) => self
                .tx_tag_invs(tag)
                .iter()
                .chain(self.receipt_tag_invs(None).iter())
                .cloned()
                .collect(),
            Some(RlpDataType::Receipt) => self
                .tx_tag_invs(None)
                .iter()
                .chain(self.receipt_tag_invs(tag).iter())
                .cloned()
                .collect(),
            None => self
                .tx_tag_invs(None)
                .iter()
                .chain(self.receipt_tag_invs(None).iter())
                .cloned()
                .collect(),
        }
    }

    fn tx_tag_invs(&self, tag: Option<u8>) -> Vec<(&str, Column<Advice>, F)> {
        macro_rules! tx_tag_inv {
            ($tag:expr, $tag_variant:ident) => {
                (F::from($tag as u64) - F::from(RlpTxTag::$tag_variant as u64))
                    .invert()
                    .unwrap_or(F::zero())
            };
        }

        tag.map_or_else(
            || {
                vec![
                    ("prefix", self.tx_tags[0], F::one()),
                    ("nonce", self.tx_tags[1], F::one()),
                    ("gas_price", self.tx_tags[2], F::one()),
                    ("gas", self.tx_tags[3], F::one()),
                    ("to_prefix", self.tx_tags[4], F::one()),
                    ("to", self.tx_tags[5], F::one()),
                    ("value", self.tx_tags[6], F::one()),
                    ("data_prefix", self.tx_tags[7], F::one()),
                    ("data", self.tx_tags[8], F::one()),
                ]
            },
            |tag| {
                vec![
                    ("prefix", self.tx_tags[0], tx_tag_inv!(tag, Prefix)),
                    ("nonce", self.tx_tags[1], tx_tag_inv!(tag, Nonce)),
                    ("gas_price", self.tx_tags[1], tx_tag_inv!(tag, GasPrice)),
                    ("gas", self.tx_tags[1], tx_tag_inv!(tag, Gas)),
                    ("to_prefix", self.tx_tags[1], tx_tag_inv!(tag, ToPrefix)),
                    ("to", self.tx_tags[1], tx_tag_inv!(tag, To)),
                    ("value", self.tx_tags[1], tx_tag_inv!(tag, Value)),
                    ("data_prefix", self.tx_tags[1], tx_tag_inv!(tag, DataPrefix)),
                    ("data", self.tx_tags[1], tx_tag_inv!(tag, Data)),
                ]
            },
        )
    }

    fn receipt_tag_invs(&self, tag: Option<u8>) -> Vec<(&str, Column<Advice>, F)> {
        macro_rules! receipt_tag_inv {
            ($tag:expr, $tag_variant:ident) => {
                (F::from($tag as u64) - F::from(RlpReceiptTag::$tag_variant as u64))
                    .invert()
                    .unwrap_or(F::zero())
            };
        }

        tag.map_or_else(
            || {
                vec![
                    ("prefix", self.receipt_tags[0], F::one()),
                    ("status", self.receipt_tags[1], F::one()),
                ]
            },
            |tag| {
                vec![
                    (
                        "prefix",
                        self.receipt_tags[0],
                        receipt_tag_inv!(tag, Prefix),
                    ),
                    (
                        "status",
                        self.receipt_tags[1],
                        receipt_tag_inv!(tag, Status),
                    ),
                ]
            },
        )
    }

    pub(crate) fn load<RLP: RlpWitnessGen<F>>(
        &self,
        layouter: &mut impl Layouter<F>,
        witness: RLP,
    ) -> Result<(), Error> {
        let rows = witness.gen_witness(self.r);
        let hash_rlc = witness.hash(self.r);
        let value_rlc = rows.iter().fold(F::zero(), |acc, row| {
            acc * F::from(256u64) + F::from(row.value as u64)
        });

        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let offset = 0;
                for (name, column, value) in &[
                    ("value_rlc", self.keccak_tuple[0], value_rlc),
                    ("index", self.keccak_tuple[1], F::from(rows.len() as u64)),
                    ("rindex", self.keccak_tuple[2], F::one()),
                    ("hash_rlc", self.keccak_tuple[3], hash_rlc),
                ] {
                    region.assign_advice(
                        || format!("keccak table assign {} {}", name, offset),
                        *column,
                        offset,
                        || Ok(*value),
                    )?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

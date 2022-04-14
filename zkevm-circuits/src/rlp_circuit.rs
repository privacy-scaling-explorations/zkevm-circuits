//! Circuit implementation for RLP-encoding verification. Please refer: https://hackmd.io/@rohitnarurkar/S1zSz0KM9.

use eth_types::Field;
use gadgets::{
    comparator::{ComparatorChip, ComparatorConfig},
    less_than::{LtChip, LtConfig},
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};

use crate::{
    evm_circuit::{
        util::{and, constraint_builder::BaseConstraintBuilder, not, or},
        witness::Transaction,
    },
    impl_expr,
    util::Expr,
};

#[derive(Debug)]
/// Inputs to the RLP circuit.
pub enum RlpInput {
    /// Witness to a legacy transaction.
    Transaction(Transaction),
    // TODO: receipt
}

#[derive(Clone, Copy, Debug)]
/// Data types that are supported by the RLP circuit.
pub enum RlpDataType {
    /// Data type for an RLP-encoded legacy transaction.
    Transaction,
    /// Data type for an RLP-encoded transaction receipt.
    Receipt,
}

#[derive(Clone, Copy, Debug)]
/// Tags used to tag rows in the RLP circuit for a transaction.
pub enum RlpTxTag {
    /// Denotes the prefix bytes indicating the “length of length” and/or
    /// “length” of the tx’s RLP-encoding.
    TxPrefix,
    /// Denotes the byte(s) for the tx’s nonce.
    TxNonce,
    /// Denotes the byte(s) for the tx’s gas price.
    TxGasPrice,
    /// Denotes the byte(s) for the tx’s gas.
    TxGas,
    /// Denotes the prefix byte indicating the “length” of the tx’s to.
    TxToPrefix,
    /// Denotes the bytes for the tx’s to.
    TxTo,
    /// Denotes the byte(s) for the tx’s value.
    TxValue,
    /// Denotes the prefix byte(s) indicating the “length of length” and/or
    /// “length” of the tx’s data.
    TxDataPrefix,
    /// Denotes the bytes for the tx’s data.
    TxData,
}

/// Denotes the number of possible tag values for a tx row.
const N_TX_TAGS: usize = 9;

#[derive(Clone, Copy, Debug)]
/// Tags used to tags rows in the RLP circuit for a tx receipt.
pub enum RlpReceiptTag {
    /// Denotes the prefix bytes indicating the "length of length" and/or
    /// "length" of the tx receipt's RLP-encoding.
    ReceiptPrefix,
    /// Denotes the byte for the receipt's status.
    ReceiptStatus,
    // TODO: other receipt tags
}

/// Denotes the number of possible tag values for a tx receipt row.
const N_RECEIPT_TAGS: usize = 2;

impl_expr!(RlpDataType);
impl_expr!(RlpTxTag);
impl_expr!(RlpReceiptTag);

#[derive(Clone, Debug)]
#[allow(dead_code)]
/// Config for the RLP circuit.
pub struct Config<F> {
    /// Denotes the randomness.
    r: F,
    /// Denotes whether or not the row is enabled.
    q_enable: Selector,
    /// Denotes whether the row is the first row in the layout.
    q_first: Column<Fixed>,
    /// Denotes whether the row is the last row in the layout.
    q_last: Selector,
    /// Denotes whether the row is the last byte in the RLP-encoded data.
    is_final: Column<Advice>,
    /// Denotes the index of this row, starting from `0` and ending at `n-1`
    /// where `n` is the byte length of the RLP-encoded data.
    index: Column<Advice>,
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
    /// Denotes a tuple (value_rlc, n, keccak256(rlp_encode(input))).
    keccak_tuple: [Column<Advice>; 3],
    /// Denotes whether the row appears after `is_final`, hence the purpose is
    /// padding.
    padding: Column<Advice>,

    /// Comparison chip to check: 1 <= tag_index.
    tag_index_cmp_1: ComparatorConfig<F, 1>,
    /// Comparison chip to check: tag_index <= tag_length.
    tag_index_length_cmp: ComparatorConfig<F, 1>,
    /// Comparison chip to check: 1 <= tag_length.
    tag_length_cmp_1: ComparatorConfig<F, 1>,

    /// Lt chip to check: tag_index < 9.
    tag_index_lt_9: LtConfig<F, 1>,
    /// Lt chip to check: tag_index < 10.
    tag_index_lt_10: LtConfig<F, 1>,
    /// Lt chip to check: tag_index < 21.
    tag_index_lt_21: LtConfig<F, 1>,
    /// Lt chip to check: tag_index < 33.
    tag_index_lt_33: LtConfig<F, 1>,

    /// Lt chip to check: 127 < value.
    value_gt_127: LtConfig<F, 1>,
    /// Lt chip to check: 183 < value.
    value_gt_183: LtConfig<F, 1>,
    /// Lt chip to check: value < 184.
    value_lt_184: LtConfig<F, 1>,
    /// Lt chip to check: value < 192.
    value_lt_192: LtConfig<F, 1>,
}

impl<F: Field> Config<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_enable = meta.complex_selector();
        let q_first = meta.fixed_column();
        let q_last = meta.selector();
        let is_final = meta.advice_column();
        let index = meta.advice_column();
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
        let keccak_tuple = array_init::array_init(|_| meta.advice_column());
        let padding = meta.advice_column();

        // Enable the comparator and lt chips if the current row is enabled and is not a
        // padding row.
        let cmp_lt_enabled = |meta: &mut VirtualCells<F>| {
            and::expr(vec![
                meta.query_selector(q_enable),
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
        let tag_index_lt_9 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |_meta| 9.expr(),
        );
        let tag_index_lt_10 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |_meta| 10.expr(),
        );
        let tag_index_lt_21 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |_meta| 21.expr(),
        );
        let tag_index_lt_33 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(tag_index, Rotation::cur()),
            |_meta| 33.expr(),
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

            is_tx_tag!(is_prefix, TxPrefix);
            is_tx_tag!(is_nonce, TxNonce);
            is_tx_tag!(is_gas_price, TxGasPrice);
            is_tx_tag!(is_gas, TxGas);
            is_tx_tag!(is_to_prefix, TxToPrefix);
            is_tx_tag!(is_to, TxTo);
            is_tx_tag!(is_value, TxValue);
            is_tx_tag!(is_data_prefix, TxDataPrefix);
            is_tx_tag!(is_data, TxData);

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
                        "tag::next == RlpTxTag::TxPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxPrefix.expr(),
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
                cb.condition(tindex_eq.clone(), |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxNonce",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxNonce.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
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
                        "tag_length::next == value - 0x80",
                        meta.query_advice(tag_length, Rotation::next()),
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
                    cb.condition(tindex_eq, |cb| {
                        cb.require_equal(
                            "tag_length::next == length_acc",
                            meta.query_advice(tag_length, Rotation::next()),
                            meta.query_advice(length_acc, Rotation::cur()),
                        );
                    });
                });
            });

            cb.condition(is_nonce(meta), |cb| {
                let (is_lt, is_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index < 9
                cb.require_equal("tag_index < 9", tag_index_lt_9.is_lt(meta, None), 1.expr());

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([is_lt.clone(), is_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(is_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxNonce",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxNonce.expr(),
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
                cb.condition(is_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxGasPrice",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxGasPrice.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                });
            });

            cb.condition(is_gas_price(meta), |cb| {
                let (is_lt, is_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index < 33
                cb.require_equal(
                    "tag_index < 33",
                    tag_index_lt_33.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([is_lt.clone(), is_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(is_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxGasPrice",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxGasPrice.expr(),
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
                cb.condition(is_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxGas",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxGas.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                });
            });

            cb.condition(is_gas(meta), |cb| {
                let (is_lt, is_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index < 9
                cb.require_equal("tag_index < 9", tag_index_lt_9.is_lt(meta, None), 1.expr());

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([is_lt.clone(), is_eq.clone()])),
                );

                // tag_index > 1
                cb.condition(is_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxGas",
                        meta.query_advice(tag, Rotation::cur()),
                        RlpTxTag::TxGas.expr(),
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
                cb.condition(is_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxToPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxToPrefix.expr(),
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
                    "tag_length",
                    meta.query_advice(tag_length, Rotation::cur()),
                    1.expr(),
                );
                cb.require_equal(
                    "value == 148",
                    meta.query_advice(value, Rotation::cur()),
                    148.expr(),
                );
                cb.require_equal(
                    "tag::next == RlpTxTag::TxTo",
                    meta.query_advice(tag, Rotation::next()),
                    RlpTxTag::TxTo.expr(),
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
                let (is_lt, is_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index < 21
                cb.require_equal(
                    "tag_index < 21",
                    tag_index_lt_21.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([is_lt.clone(), is_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(is_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxTo",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxTo.expr(),
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
                cb.condition(is_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxValue",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxValue.expr(),
                    );
                    cb.require_equal(
                        "tag_index:next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                });
            });

            cb.condition(is_value(meta), |cb| {
                let (is_lt, is_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index < 33
                cb.require_equal(
                    "tag_index < 33",
                    tag_index_lt_33.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([is_lt.clone(), is_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(is_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxValue",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxValue.expr(),
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
                cb.condition(is_eq, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag:TxDataPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxDataPrefix.expr(),
                    );
                });
            });

            cb.condition(is_data_prefix(meta), |cb| {
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
                        "tag::next == RlpTxTag::TxDataPrefix",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxDataPrefix.expr(),
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
                cb.condition(tindex_eq.clone(), |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxData",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxData.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
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
                    cb.condition(tindex_eq, |cb| {
                        cb.require_equal(
                            "tag_length::next == length_acc",
                            meta.query_advice(tag_length, Rotation::next()),
                            meta.query_advice(length_acc, Rotation::cur()),
                        );
                    });
                });

                // if tag_index == tag_legth && tag_length == 1
                cb.condition(tindex_eq_tlength * tlength_eq, |cb| {
                    cb.require_zero(
                        "127 < value < 184",
                        not::expr(and::expr(vec![
                            value_gt_127.is_lt(meta, None),
                            value_lt_184.is_lt(meta, None),
                        ])),
                    );
                    cb.require_equal(
                        "tag_length::next == value - 0x80",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                });
            });

            cb.condition(is_data(meta), |cb| {
                let (is_lt, is_eq) = tag_index_cmp_1.expr(meta, None);

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([is_lt.clone(), is_eq.clone()])),
                );

                // if tag_index > 1
                cb.condition(is_lt, |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::TxData",
                        meta.query_advice(tag, Rotation::next()),
                        RlpTxTag::TxData.expr(),
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
                cb.condition(is_eq, |cb| {
                    cb.require_equal(
                        "is_final == 1",
                        meta.query_advice(is_final, Rotation::cur()),
                        1.expr(),
                    );
                });
            });

            cb.gate(and::expr(vec![
                meta.query_selector(q_enable),
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

            is_receipt_tag!(is_prefix, ReceiptPrefix);
            is_receipt_tag!(is_status, ReceiptStatus);

            cb.condition(is_prefix(meta), |_cb| {});

            cb.condition(is_status(meta), |_cb| {});

            cb.gate(and::expr(vec![
                meta.query_selector(q_enable),
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

            cb.gate(meta.query_selector(q_enable))
        });

        // Constraints for the first row in the layout.
        meta.create_gate("q_first == 1", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "value_rlc == value",
                meta.query_advice(value_rlc, Rotation::cur()),
                meta.query_advice(value, Rotation::cur()),
            );
            cb.require_zero("index == 0", meta.query_advice(index, Rotation::cur()));

            cb.gate(and::expr(vec![
                meta.query_selector(q_enable),
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
                meta.query_selector(q_enable),
                not::expr(meta.query_fixed(q_first, Rotation::cur())),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ]))
        });

        // Constraints for the last row of the RLP-encoded data.
        meta.lookup_any("keccak-256 verification for is_final == 1", |meta| {
            let enable = and::expr(vec![
                meta.query_selector(q_enable),
                meta.query_advice(is_final, Rotation::cur()),
                not::expr(meta.query_advice(padding, Rotation::cur())),
            ]);

            let lookup_columns = vec![value_rlc, index, hash];
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
                meta.query_selector(q_enable),
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
            q_enable,
            q_first,
            q_last,
            is_final,
            index,
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

            tag_index_lt_9,
            tag_index_lt_10,
            tag_index_lt_21,
            tag_index_lt_33,

            value_gt_127,
            value_gt_183,
            value_lt_184,
            value_lt_192,
        }
    }

    pub(crate) fn assign(&self, _layouter: impl Layouter<F>, _size: usize, _witness: RlpInput) {
        unimplemented!();
    }
}

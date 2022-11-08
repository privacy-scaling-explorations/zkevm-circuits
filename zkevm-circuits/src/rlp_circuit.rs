//! Circuit implementation for RLP-encoding verification. Please refer: https://hackmd.io/@rohitnarurkar/S1zSz0KM9.

use eth_types::Field;
use gadgets::{
    comparator::{ComparatorChip, ComparatorConfig, ComparatorInstruction},
    less_than::{LtChip, LtConfig, LtInstruction},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, VirtualCells},
    poly::Rotation,
};

use crate::{
    evm_circuit::{
        util::{and, constraint_builder::BaseConstraintBuilder, not, or},
        witness::{RlpTxTag, RlpWitnessGen, N_TX_TAGS},
    },
    util::{Challenges, Expr},
};

#[derive(Clone, Debug)]
/// Config for the RLP circuit.
pub struct Config<F> {
    /// Denotes the randomness.
    r: F,
    /// Denotes whether or not the row is enabled.
    q_usable: Selector,
    /// Denotes whether the row is the first row in the layout.
    is_first: Column<Advice>,
    /// Denotes whether the row is the last byte in the RLP-encoded data.
    is_last: Column<Advice>,
    /// Transaction ID.
    tx_id: Column<Advice>,
    /// Denotes the index of this row, starting from `1` and ending at `n`
    /// where `n` is the byte length of the RLP-encoded data.
    index: Column<Advice>,
    /// Denotes the index of this row, but reversed. It starts from `n` where
    /// `n` is the byte length of the RLP-encoded data and ends at `1`.
    rindex: Column<Advice>,
    /// Denotes the byte value at this row index from the RLP-encoded data.
    value: Column<Advice>,
    /// Denotes the accumulated value for this span's tag.
    value_acc: Column<Advice>,
    /// Denotes the tag assigned to this row.
    tag: Column<Advice>,
    /// List of columns that are assigned:
    /// val := (tag - RlpTxTag::{Variant}).inv()
    tx_tags: [Column<Advice>; N_TX_TAGS],
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
    /// Lt chip to check: 191 < value.
    value_gt_191: LtConfig<F, 1>,
    /// Lt chip to check: 247 < value.
    value_gt_247: LtConfig<F, 1>,
    /// Lt chip to check: value < 128.
    value_lt_129: LtConfig<F, 1>,
    /// Lt chip to check: value < 184.
    value_lt_184: LtConfig<F, 1>,
    /// Lt chip to check: value < 192.
    value_lt_192: LtConfig<F, 1>,
    /// Lt chip to check: value < 248.
    value_lt_248: LtConfig<F, 1>,
    /// Lt chip to check: value < 256.
    value_lt_256: LtConfig<F, 2>,
    /// Comparison chip to check: 0 <= length_acc.
    length_acc_cmp_0: ComparatorConfig<F, 1>,
    /// Lt chip to check: rindex > 1.
    rindex_gt_1: LtConfig<F, 1>,
}

impl<F: Field> Config<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_usable = meta.complex_selector();
        let is_first = meta.advice_column();
        let is_last = meta.advice_column();
        let tx_id = meta.advice_column();
        let index = meta.advice_column();
        let rindex = meta.advice_column();
        let value = meta.advice_column();
        let value_acc = meta.advice_column();
        let tag = meta.advice_column();
        let tx_tags = array_init::array_init(|_| meta.advice_column());
        let tag_index = meta.advice_column();
        let tag_length = meta.advice_column();
        let length_acc = meta.advice_column();
        let value_rlc = meta.advice_column();
        let hash = meta.advice_column();

        // Enable the comparator and lt chips if the current row is enabled.
        let cmp_lt_enabled = |meta: &mut VirtualCells<F>| meta.query_selector(q_usable);

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
        let value_gt_191 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 191.expr(),
            |meta| meta.query_advice(value, Rotation::cur()),
        );
        let value_gt_247 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 247.expr(),
            |meta| meta.query_advice(value, Rotation::cur()),
        );
        let value_lt_129 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(value, Rotation::cur()),
            |_meta| 129.expr(),
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
        let value_lt_248 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(value, Rotation::cur()),
            |_meta| 248.expr(),
        );
        let value_lt_256 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(value, Rotation::cur()),
            |_meta| 256.expr(),
        );
        let length_acc_cmp_0 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 0.expr(),
            |meta| meta.query_advice(length_acc, Rotation::cur()),
        );
        let rindex_gt_1 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 1.expr(),
            |meta| meta.query_advice(rindex, Rotation::cur()),
        );

        // Helper macro to declare booleans to check the current row tag.
        macro_rules! is_tx_tag {
            ($var:ident, $tag_variant:ident) => {
                let $var = |meta: &mut VirtualCells<F>| {
                    1.expr()
                        - meta.query_advice(tag, Rotation::cur())
                            * meta.query_advice(
                                tx_tags[RlpTxTag::$tag_variant as usize - 1],
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

        meta.create_gate("DataType::Transaction", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
            let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
            let (tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);
            let (length_acc_gt_0, length_acc_eq_0) = length_acc_cmp_0.expr(meta, None);

            //////////////////////////////////////////////////////////////////////////////////////
            ////////////////////////////////// RlpTxTag::Prefix //////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_prefix(meta), |cb| {
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
            });

            // if tag_index > 1
            cb.condition(is_prefix(meta) * tindex_lt.clone(), |cb| {
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
            cb.condition(is_prefix(meta) * tindex_eq.clone(), |cb| {
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
            cb.condition(
                is_prefix(meta) * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("247 < value", value_gt_247.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 256", value_lt_256.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "tag_index::next == value - 0xf7",
                        meta.query_advice(tag_index, Rotation::next()),
                        meta.query_advice(value, Rotation::cur()) - 247.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_prefix(meta) * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("191 < value", value_gt_191.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 248", value_lt_248.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0xc0 (1)",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 192.expr(),
                    );
                },
            );

            // if tag_index < tag_length && tag_length > 1
            cb.condition(
                is_prefix(meta) * tindex_lt_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(value, Rotation::cur()),
                    );
                },
            );

            //////////////////////////////////////////////////////////////////////////////////////
            ////////////////////////////////// RlpTxTag::Nonce ///////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_nonce(meta), |cb| {
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
            });

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_nonce(meta) * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("value < 129", value_lt_129.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "value == value_acc",
                        meta.query_advice(value, Rotation::cur()),
                        meta.query_advice(value_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_nonce(meta) * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
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
                    cb.require_equal(
                        "value_acc::next == value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // if tag_index < tag_length && tag_index > 1
            cb.condition(
                is_nonce(meta) * tindex_lt_tlength.clone() * tindex_lt.clone(),
                |cb| {
                    cb.require_equal(
                        "[nonce] value_acc::next == value_acc::cur * 256 + value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value_acc, Rotation::cur()) * 256.expr() +
                            meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // if tag_index > 1
            cb.condition(is_nonce(meta) * tindex_lt.clone(), |cb| {
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
            cb.condition(is_nonce(meta) * tindex_eq.clone(), |cb| {
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

            //////////////////////////////////////////////////////////////////////////////////////
            ///////////////////////////////// RlpTxTag::GasPrice /////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_gas_price(meta), |cb| {
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
            });

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_gas_price(meta) * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("value < 129", value_lt_129.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "value == value_acc",
                        meta.query_advice(value, Rotation::cur()),
                        meta.query_advice(value_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_gas_price(meta) * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
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
                    cb.require_equal(
                        "value_acc::next == value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // if tag_index < tag_length && tag_index > 1
            cb.condition(
                is_gas_price(meta) * tindex_lt_tlength.clone() * tindex_lt.clone(),
                |cb| {
                    cb.require_equal(
                        "[gas price] value_acc::next == value_acc::cur * randomness + value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value_acc, Rotation::cur()) * r +
                            meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // if tag_index > 1
            cb.condition(is_gas_price(meta) * tindex_lt.clone(), |cb| {
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
            cb.condition(is_gas_price(meta) * tindex_eq.clone(), |cb| {
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

            //////////////////////////////////////////////////////////////////////////////////////
            /////////////////////////////////// RlpTxTag::Gas ////////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_gas(meta), |cb| {
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
            });

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_gas(meta) * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("value < 129", value_lt_129.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "value == value_acc",
                        meta.query_advice(value, Rotation::cur()),
                        meta.query_advice(value_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_gas(meta) * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
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
                },
            );

            // if tag_index < tag_length && tag_index > 1
            cb.condition(
                is_gas(meta) * tindex_lt_tlength.clone() * tindex_lt.clone(),
                |cb| {
                    cb.require_equal(
                        "[gas] value_acc::next == value_acc::cur * 256 + value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value_acc, Rotation::cur()) * 256.expr() +
                            meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // tag_index > 1
            cb.condition(is_gas(meta) * tindex_lt.clone(), |cb| {
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
            cb.condition(is_gas(meta) * tindex_eq.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag::ToPrefix",
                    meta.query_advice(tag, Rotation::next()),
                    RlpTxTag::ToPrefix.expr(),
                );
            });

            //////////////////////////////////////////////////////////////////////////////////////
            ///////////////////////////////// RlpTxTag::ToPrefix /////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
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
                cb.require_equal(
                    "value_acc::next == value::next",
                    meta.query_advice(value_acc, Rotation::next()),
                    meta.query_advice(value, Rotation::next()),
                );
            });

            //////////////////////////////////////////////////////////////////////////////////////
            //////////////////////////////////// RlpTxTag::To ////////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            // if tag_index > 1
            cb.condition(is_to(meta) * tindex_lt.clone(), |cb| {
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
                cb.require_equal(
                    "value_acc::next == value_acc::cur * 256 + value::next",
                    meta.query_advice(value_acc, Rotation::next()),
                    meta.query_advice(value_acc, Rotation::cur()) * 256.expr() +
                        meta.query_advice(value, Rotation::next()),
                );
            });

            // if tag_index == 1
            cb.condition(is_to(meta) * tindex_eq.clone(), |cb| {
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

            //////////////////////////////////////////////////////////////////////////////////////
            /////////////////////////////////// RlpTxTag::Value //////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_value(meta), |cb| {
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
            });

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_value(meta) * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("value < 129", value_lt_129.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "value == value_acc",
                        meta.query_advice(value, Rotation::cur()),
                        meta.query_advice(value_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_value(meta) * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
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
                    cb.require_equal(
                        "value_acc::next == value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // if tag_index < tag_length && tag_index > 1
            cb.condition(
                is_value(meta) * tindex_lt_tlength.clone() * tindex_lt.clone(),
                |cb| {
                    cb.require_equal(
                        "[value] value_acc::next == value_acc::cur * randomness + value::next",
                        meta.query_advice(value_acc, Rotation::next()),
                        meta.query_advice(value_acc, Rotation::cur()) * r +
                            meta.query_advice(value, Rotation::next()),
                    );
                },
            );

            // if tag_index > 1
            cb.condition(is_value(meta) * tindex_lt.clone(), |cb| {
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
            cb.condition(is_value(meta) * tindex_eq.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag:TxDataPrefix",
                    meta.query_advice(tag, Rotation::next()),
                    RlpTxTag::DataPrefix.expr(),
                );
            });

            //////////////////////////////////////////////////////////////////////////////////////
            ///////////////////////////////// RlpTxTag::DataPrefix ///////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_data_prefix(meta), |cb| {
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
            });

            // if tag_index > 1
            cb.condition(is_data_prefix(meta) * tindex_lt.clone(), |cb| {
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

            // if length_acc == 0
            cb.condition(
                is_data_prefix(meta) * tindex_eq.clone() * length_acc_eq_0,
                |cb| {
                    cb.require_equal(
                        "RlpTxTag::DataPrefix: is_last == 1",
                        meta.query_advice(is_last, Rotation::cur()),
                        1.expr(),
                    );
                },
            );

            // if length_acc > 0
            cb.condition(
                is_data_prefix(meta) * tindex_eq.clone() * length_acc_gt_0,
                |cb| {
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
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_data_prefix(meta) * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("value > 183", value_gt_183.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 192", value_lt_192.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "tag_index == (value - 0xb7) + 1",
                        meta.query_advice(tag_index, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 182.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index < tag_length && tag_length > 1
            cb.condition(
                is_data_prefix(meta) * tindex_lt_tlength * tlength_lt,
                |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(value, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_data_prefix(meta) * tindex_eq_tlength * tlength_eq,
                |cb| {
                    cb.require_equal("127 < value", value_gt_127.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(value, Rotation::cur()) - 128.expr(),
                    );
                },
            );

            //////////////////////////////////////////////////////////////////////////////////////
            //////////////////////////////////// RlpTxTag::Data //////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_data(meta), |cb| {
                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );
            });

            // if tag_index > 1
            cb.condition(is_data(meta) * tindex_lt, |cb| {
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
            cb.condition(is_data(meta) * tindex_eq, |cb| {
                cb.require_equal(
                    "RlpTxTag::Data: is_last == 1",
                    meta.query_advice(is_last, Rotation::cur()),
                    1.expr(),
                );
            });

            cb.gate(meta.query_selector(q_usable))
        });

        // Constraints that always need to be satisfied.
        meta.create_gate("always", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean(
                "is_first is boolean",
                meta.query_advice(is_first, Rotation::cur()),
            );
            cb.require_boolean(
                "is_last is boolean",
                meta.query_advice(is_last, Rotation::cur()),
            );

            cb.gate(meta.query_selector(q_usable))
        });

        // Constraints for the first row in the layout.
        meta.create_gate("is_first == 1", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "value_rlc == value",
                meta.query_advice(value_rlc, Rotation::cur()),
                meta.query_advice(value, Rotation::cur()),
            );
            cb.require_equal(
                "index == 1",
                meta.query_advice(index, Rotation::cur()),
                1.expr(),
            );

            cb.gate(and::expr(vec![
                meta.query_selector(q_usable),
                meta.query_advice(is_first, Rotation::cur()),
            ]))
        });

        // Constraints for every row except the first row.
        meta.create_gate("is_first == 0", |meta| {
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
                meta.query_selector(q_usable),
                not::expr(meta.query_advice(is_first, Rotation::cur())),
            ]))
        });

        Self {
            r,
            q_usable,
            is_first,
            is_last,
            tx_id,
            index,
            rindex,
            value,
            value_acc,
            tag,
            tx_tags,
            tag_index,
            tag_length,
            length_acc,
            value_rlc,
            hash,
            tag_index_cmp_1,
            tag_index_length_cmp,
            tag_length_cmp_1,
            tag_index_lt_10,
            tag_index_lt_34,
            value_gt_127,
            value_gt_183,
            value_gt_191,
            value_gt_247,
            value_lt_129,
            value_lt_184,
            value_lt_192,
            value_lt_248,
            value_lt_256,
            length_acc_cmp_0,
            rindex_gt_1,
        }
    }

    pub(crate) fn assign<RLP: RlpWitnessGen<F>>(
        &self,
        mut layouter: impl Layouter<F>,
        witnesses: &[RLP],
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let tag_index_cmp_1_chip = ComparatorChip::construct(self.tag_index_cmp_1.clone());
        let tag_index_length_cmp_chip =
            ComparatorChip::construct(self.tag_index_length_cmp.clone());
        let tag_length_cmp_1_chip = ComparatorChip::construct(self.tag_length_cmp_1.clone());

        let tag_index_lt_10_chip = LtChip::construct(self.tag_index_lt_10);
        let tag_index_lt_34_chip = LtChip::construct(self.tag_index_lt_34);

        let value_gt_127_chip = LtChip::construct(self.value_gt_127);
        let value_gt_183_chip = LtChip::construct(self.value_gt_183);
        let value_gt_191_chip = LtChip::construct(self.value_gt_191);
        let value_gt_247_chip = LtChip::construct(self.value_gt_247);
        let value_lt_129_chip = LtChip::construct(self.value_lt_129);
        let value_lt_184_chip = LtChip::construct(self.value_lt_184);
        let value_lt_192_chip = LtChip::construct(self.value_lt_192);
        let value_lt_248_chip = LtChip::construct(self.value_lt_248);
        let value_lt_256_chip = LtChip::construct(self.value_lt_256);

        let length_acc_cmp_0_chip = ComparatorChip::construct(self.length_acc_cmp_0.clone());

        let rindex_gt_1_chip = LtChip::construct(self.rindex_gt_1);

        layouter.assign_region(
            || "assign RLP-encoded data",
            |mut region| {
                // add a dummy row at offset == 0.
                let mut offset = 0;
                self.assign_padding_rows(&mut region, offset)?;

                for witness in witnesses.iter() {
                    let mut value_rlc = F::zero();
                    let rows = witness.gen_witness(self.r, challenges);
                    let n_rows = rows.len();

                    for (idx, row) in rows.iter().enumerate() {
                        offset += 1;

                        // update value accumulator over the entire RLP encoding.
                        value_rlc = value_rlc * self.r + F::from(row.value as u64);

                        // q_usable
                        self.q_usable.enable(&mut region, offset)?;
                        // is_first
                        region.assign_advice(
                            || format!("assign is_first {}", offset),
                            self.is_first,
                            offset,
                            || Value::known(F::from((idx == 0) as u64)),
                        )?;
                        // advices
                        let rindex = (n_rows + 1 - row.index) as u64;
                        for (name, column, value) in [
                            (
                                "is_last",
                                self.is_last,
                                F::from((row.index == n_rows) as u64),
                            ),
                            ("tx_id", self.tx_id, F::from(row.id as u64)),
                            ("index", self.index, F::from(row.index as u64)),
                            ("rindex", self.rindex, F::from(rindex)),
                            ("value", self.value, F::from(row.value as u64)),
                            ("value_acc", self.value_acc, row.value_acc),
                            ("tag", self.tag, F::from(row.tag as u64)),
                            ("tag_index", self.tag_index, F::from(row.tag_index as u64)),
                            (
                                "tag_length",
                                self.tag_length,
                                F::from(row.tag_length as u64),
                            ),
                            ("length_acc", self.length_acc, F::from(row.length_acc)),
                            ("value_rlc", self.value_rlc, value_rlc),
                        ] {
                            region.assign_advice(
                                || format!("assign {} {}", name, offset),
                                column,
                                offset,
                                || Value::known(value),
                            )?;
                        }
                        region.assign_advice(
                            || format!("assign hash: {}", offset),
                            self.hash,
                            offset,
                            || row.hash,
                        )?;

                        for (name, column, value) in self.tx_tag_invs(Some(row.tag)) {
                            region.assign_advice(
                                || format!("assign {} {}", name, offset),
                                column,
                                offset,
                                || Value::known(value),
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
                        value_gt_191_chip.assign(
                            &mut region,
                            offset,
                            F::from(191u64),
                            F::from(row.value as u64),
                        )?;
                        value_gt_247_chip.assign(
                            &mut region,
                            offset,
                            F::from(247u64),
                            F::from(row.value as u64),
                        )?;
                        value_lt_129_chip.assign(
                            &mut region,
                            offset,
                            F::from(row.value as u64),
                            F::from(129u64),
                        )?;
                        value_lt_184_chip.assign(
                            &mut region,
                            offset,
                            F::from(row.value as u64),
                            F::from(184u64),
                        )?;
                        value_lt_192_chip.assign(
                            &mut region,
                            offset,
                            F::from(row.value as u64),
                            F::from(192u64),
                        )?;
                        value_lt_248_chip.assign(
                            &mut region,
                            offset,
                            F::from(row.value as u64),
                            F::from(248u64),
                        )?;
                        value_lt_256_chip.assign(
                            &mut region,
                            offset,
                            F::from(row.value as u64),
                            F::from(256u64),
                        )?;
                        length_acc_cmp_0_chip.assign(
                            &mut region,
                            offset,
                            F::zero(),
                            F::from(row.length_acc as u64),
                        )?;
                        rindex_gt_1_chip.assign(&mut region, offset, F::one(), F::from(rindex))?;
                    }
                }

                // end with a dummy row.
                offset += 1;
                self.assign_padding_rows(&mut region, offset)?;

                Ok(())
            },
        )
    }

    fn assign_padding_rows(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        for column in [
            self.is_first,
            self.is_last,
            self.tx_id,
            self.index,
            self.tag,
            self.tag_index,
            self.tag_length,
            self.length_acc,
            self.rindex,
            self.value,
            self.value_acc,
            self.value_rlc,
            self.hash,
        ] {
            region.assign_advice(
                || format!("padding row, offset: {}", offset),
                column,
                offset,
                || Value::known(F::zero()),
            )?;
        }

        Ok(())
    }

    fn tx_tag_invs(&self, tag: Option<u8>) -> Vec<(&str, Column<Advice>, F)> {
        macro_rules! tx_tag_inv {
            ($tag:expr, $tag_variant:ident) => {
                if $tag == (RlpTxTag::$tag_variant as u8) {
                    F::zero()
                } else {
                    F::from($tag as u64).invert().unwrap_or(F::zero())
                }
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
                    ("gas_price", self.tx_tags[2], tx_tag_inv!(tag, GasPrice)),
                    ("gas", self.tx_tags[3], tx_tag_inv!(tag, Gas)),
                    ("to_prefix", self.tx_tags[4], tx_tag_inv!(tag, ToPrefix)),
                    ("to", self.tx_tags[5], tx_tag_inv!(tag, To)),
                    ("value", self.tx_tags[6], tx_tag_inv!(tag, Value)),
                    ("data_prefix", self.tx_tags[7], tx_tag_inv!(tag, DataPrefix)),
                    ("data", self.tx_tags[8], tx_tag_inv!(tag, Data)),
                ]
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use eth_types::{Field, U256};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use crate::{evm_circuit::witness::Transaction, util::Challenges};

    use super::Config;

    #[derive(Clone)]
    struct MyConfig<F> {
        rlp_config: Config<F>,
    }

    #[derive(Default)]
    struct MyCircuit<F, RLP> {
        inputs: Vec<RLP>,
        size: usize,
        _marker: PhantomData<F>,
    }

    impl<F: Field, RLP> MyCircuit<F, RLP> {
        fn r() -> F {
            F::from(194881236412749812)
        }
        fn max_txs() -> usize {
            10
        }
    }

    impl<F: Field> Circuit<F> for MyCircuit<F, Transaction> {
        type Config = (MyConfig<F>, Challenges);
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let rlp_config = Config::configure(meta, Self::r());

            (MyConfig { rlp_config }, Challenges::construct(meta))
        }

        fn synthesize(
            &self,
            (config, challenges): Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // assign to the RLP circuit.
            let challenges = challenges.values(&mut layouter);
            config
                .rlp_config
                .assign(layouter, self.inputs.as_slice(), &challenges)
        }
    }

    fn verify_txs<F: Field>(k: u32, inputs: Vec<Transaction>, success: bool) {
        let circuit = MyCircuit::<F, Transaction> {
            inputs,
            size: 2usize.pow(k),
            _marker: PhantomData,
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let err = prover.verify();
        let print_failures = true;
        if err.is_err() && print_failures {
            if let Some(e) = err.err() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }

    fn get_txs() -> [Transaction; 3] {
        [
            Transaction {
                id: 1,
                nonce: 0x123u64,
                gas_price: 100_000_000_000u64.into(),
                gas: 1_000_000u64,
                callee_address: mock::MOCK_ACCOUNTS[0],
                value: U256::from_dec_str("250000000000000000000").unwrap(),
                call_data: vec![1, 2, 3],
                call_data_length: 3,
                ..Default::default()
            },
            Transaction {
                id: 2,
                nonce: 0x00u64,
                gas_price: 100_000_000u64.into(),
                gas: 1_000u64,
                callee_address: mock::MOCK_ACCOUNTS[1],
                value: 0.into(),
                call_data: vec![],
                ..Default::default()
            },
            Transaction {
                id: 3,
                nonce: 0x01u64,
                gas_price: 100_000_000u64.into(),
                gas: 1_000u64,
                callee_address: mock::MOCK_ACCOUNTS[2],
                value: 10u64.into(),
                call_data: vec![
                    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 1, 2, 3,
                    4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6,
                    7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                    10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
                    12, 13, 14, 15, 16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
                    14, 15, 16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                    16, 17, 18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
                    18, 19, 20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                    20, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
                ],
                call_data_length: 200,
                ..Default::default()
            },
        ]
    }

    #[test]
    fn rlp_circuit_tx_1() {
        verify_txs::<Fr>(8, vec![get_txs()[0].clone()], true);
    }

    #[test]
    fn rlp_circuit_tx_2() {
        verify_txs::<Fr>(8, vec![get_txs()[1].clone()], true);
    }

    #[test]
    fn rlp_circuit_tx_3() {
        verify_txs::<Fr>(20, vec![get_txs()[2].clone()], true);
    }

    #[test]
    fn rlp_circuit_multi_txs() {
        let txs = get_txs();
        verify_txs::<Fr>(10, vec![txs[0].clone(), txs[1].clone()], true);
    }
}

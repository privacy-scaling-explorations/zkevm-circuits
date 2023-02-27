use std::any::Any;

use crate::{
    _cb, circuit,
    circuit_tools::{
        cell_manager::{Cell, CellManager, Trackable},
        constraint_builder::{
            Conditionable, ConstraintBuilder, RLCChainable, RLCChainableValue, RLCable,
            RLCableValue,
        },
        gadgets::IsEqualGadget,
        memory::MemoryBank,
    },
    matchr, matchw,
    mpt_circuit::param::{
        EMPTY_TRIE_HASH, KEY_PREFIX_EVEN, KEY_TERMINAL_PREFIX_EVEN, RLP_LIST_LONG,
        RLP_LIST_SHORT, RLP_SHORT,
    },
    util::Expr,
};
use eth_types::Field;
use gadgets::util::{not, or, Scalar};
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    param::{
        KEY_PREFIX_ODD, KEY_TERMINAL_PREFIX_ODD, RLP_LONG,
    },
    witness_row::MptWitnessRow,
    FixedTableTag, MPTConfig, MPTContext, ProofValues,
};

/// Indexable object
pub trait Indexable {
    /// Convert to index
    fn idx(&self) -> usize;
}

impl Indexable for bool {
    fn idx(&self) -> usize {
        if *self {
            0
        } else {
            1
        }
    }
}

pub(crate) trait Gadget<F: Field> {
    /// Constraints
    fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self;

    /// Witness
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        witness: &[MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListGadget<F> {
    pub(crate) is_short: Cell<F>,
    pub(crate) is_long: Cell<F>,
    pub(crate) is_very_long: Cell<F>,
    pub(crate) is_string: Cell<F>,
    pub(crate) bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListWitness {
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) is_very_long: bool,
    pub(crate) is_string: bool,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPListGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        // TODO(Brecht): add lookup
        RLPListGadget {
            is_short: cb.query_cell(),
            is_long: cb.query_cell(),
            is_very_long: cb.query_cell(),
            is_string: cb.query_cell(),
            bytes: bytes.to_vec(),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPListWitness, Error> {
        const RLP_LIST_LONG_1: u8 = RLP_LIST_LONG + 1;
        const RLP_LIST_LONG_2: u8 = RLP_LIST_LONG + 2;

        let mut is_short = false;
        let mut is_long = false;
        let mut is_very_long = false;
        let mut is_string = false;
        match bytes[0] {
            RLP_LIST_SHORT..=RLP_LIST_LONG => is_short = true,
            RLP_LIST_LONG_1 => is_long = true,
            RLP_LIST_LONG_2 => is_very_long = true,
            _ => is_string = true,
        }

        self.is_short.assign(region, offset, F::from(is_short))?;
        self.is_long.assign(region, offset, F::from(is_long))?;
        self.is_very_long.assign(region, offset, F::from(is_very_long))?;
        self.is_string.assign(region, offset, F::from(is_string))?;

        Ok(RLPListWitness {
            is_short,
            is_long,
            is_very_long,
            is_string,
            bytes: bytes.to_vec(),
        })
    }

    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_list(&self) -> Expression<F> {
        not::expr(self.is_string.expr())
    }

    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short.expr()
    }

    // RLP byte followed by the length in 1 byte, followed by the length
    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long.expr()
    }

    // RLP byte followed by the length in 1 byte, followed by the length
    pub(crate) fn is_very_long(&self) -> Expression<F> {
        self.is_very_long.expr()
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => 1.expr(),
                self.is_long() => 2.expr(),
                self.is_very_long() => 3.expr(),
            }
        })
    }

    /// Returns the total length of the list (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        self.num_rlp_bytes() + self.len()
    }

    /// Returns the length of the list (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => get_len_list_short::expr(self.bytes[0].expr()),
                self.is_long() => self.bytes[1].expr(),
                self.is_very_long() => self.bytes[1].expr() * 256.expr() + self.bytes[2].expr(),
            }
        })
    }

    pub(crate) fn rlc(&self, r: &[Expression<F>]) -> (Expression<F>, Expression<F>) {
        circuit!([meta, _cb!()], {
            let value_rlc =
            matchx! {
                self.is_short() => self.bytes[1..].rlc(&r),
                self.is_long() => self.bytes[2..].rlc(&r),
                self.is_very_long() => self.bytes[3..].rlc(&r),
            };
            (value_rlc, self.bytes.rlc(&r))
        })
    }

    /// Returns the rlc of the RLP bytes
    pub(crate) fn rlc_rlp(&self, r: &[Expression<F>]) -> (Expression<F>, Expression<F>) {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => (self.bytes[..1].rlc(&r), r[0].expr()),
                self.is_long() => (self.bytes[..2].rlc(&r), r[1].expr()),
                self.is_very_long() => (self.bytes[..3].rlc(&r), r[2].expr()),
            }
        })
    }
}

impl RLPListWitness {
    pub(crate) fn is_list(&self) -> bool {
        !self.is_string
    }

    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_short(&self) -> bool {
        self.is_short
    }

    // RLP byte followed by the number of bytes in length, followed by the length
    pub(crate) fn is_long(&self) -> bool {
        self.is_long
    }

    // RLP byte followed by the number of bytes in length, followed by the length
    pub(crate) fn is_very_long(&self) -> bool {
        self.is_very_long
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        matchr! {
            self.is_short() => 1,
            self.is_long() => 2,
            self.is_very_long() => 3,
        }
    }

    /// Returns the total length of the list (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchr! {
            self.is_short => get_num_bytes_list_short::value(self.bytes[0]),
            self.is_long => 2 + (self.bytes[1] as usize),
            self.is_very_long => 3 + (self.bytes[1] as usize) * 256 + (self.bytes[2] as usize),
        }
    }

    /// Returns the length of the list (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchr! {
            self.is_short() => get_len_list_short::value(self.bytes[0]),
            self.is_long() => self.bytes[1] as usize,
        }
    }

    /// RLC data
    pub(crate) fn rlc<F: Field>(&self, r: F) -> (F, F) {
        matchr! {
            self.is_short() => {
                (self.bytes.rlc_value(r), self.bytes.rlc_value(r))
            },
            self.is_long() => {
                (self.bytes[1..].rlc_value(r), self.bytes.rlc_value(r))
            },
            _ => {
                unreachable!();
            },
        }
    }

    pub(crate) fn rlc_rlp<F: Field>(&self, r: F) -> F {
        self.rlc(r).1
    }

    pub(crate) fn rlc_value<F: Field>(&self, r: F) -> F {
        self.rlc(r).0
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPValueGadget<F> {
    pub(crate) is_short: Cell<F>,
    pub(crate) is_long: Cell<F>,
    pub(crate) is_very_long: Cell<F>,
    pub(crate) is_list: Cell<F>,
    pub(crate) bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPValueWitness {
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) is_very_long: bool,
    pub(crate) is_list: bool,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPValueGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        // TODO(Brecht): add lookup
        RLPValueGadget {
            is_short: cb.query_cell(),
            is_long: cb.query_cell(),
            is_very_long: cb.query_cell(),
            is_list: cb.query_cell(),
            bytes: bytes.to_vec(),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPValueWitness, Error> {
        const RLP_SHORT_INCLUSIVE: u8 = RLP_SHORT - 1;
        const RLP_LONG_EXCLUSIVE: u8 = RLP_LONG + 1;
        const RLP_VALUE_MAX: u8 = RLP_LIST_SHORT - 1;

        let mut is_short = false;
        let mut is_long = false;
        let mut is_very_long = false;
        let mut is_list = false;
        match bytes[0] {
            0..=RLP_SHORT_INCLUSIVE => is_short = true,
            RLP_SHORT..=RLP_LONG => is_long = true,
            RLP_LONG_EXCLUSIVE..=RLP_VALUE_MAX => is_very_long = true,
            _ => is_list = true,
        }
        /*const RLP_SHORT_INCLUSIVE: u8 = RLP_SHORT + 1;
        const RLP_LONG_INCLUSIVE: u8 = RLP_LONG - 1;
        const RLP_VALUE_MAX: u8 = RLP_LIST_SHORT - 1;

        let mut is_short = false;
        let mut is_long = false;
        let mut is_very_long = false;
        let mut is_list = false;
        match bytes[0] {
            0..=RLP_SHORT => is_short = true,
            RLP_SHORT_INCLUSIVE..=RLP_LONG_INCLUSIVE => is_long = true,
            RLP_LONG..=RLP_VALUE_MAX => is_very_long = true,
            _ => is_list = true,
        }*/

        self.is_short.assign(region, offset, F::from(is_short))?;
        self.is_long.assign(region, offset, F::from(is_long))?;
        self.is_very_long
            .assign(region, offset, F::from(is_very_long))?;
        self.is_list
            .assign(region, offset, F::from(is_list))?;

        Ok(RLPValueWitness {
            is_short,
            is_long,
            is_very_long,
            is_list,
            bytes: bytes.to_vec(),
        })
    }

    // Returns true if this is indeed a string RLP
    pub(crate) fn is_string(&self) -> Expression<F> {
        not::expr(self.is_list.expr())
    }

    // Single RLP byte containing the byte value
    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short.expr()
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long.expr()
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> Expression<F> {
        self.is_very_long.expr()
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => 0.expr(),
                self.is_long() => 1.expr(),
                self.is_very_long() => 2.expr(),
            }
        })
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => 1.expr(),
                self.is_long() => get_num_bytes_short::expr(self.bytes[0].expr()),
                self.is_very_long() => {
                    unreachablex!();
                    0.expr()
                },
            }
        })
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => 1.expr(),
                self.is_long() => get_len_short::expr(self.bytes[0].expr()),
                self.is_very_long() => {
                    unreachablex!();
                    0.expr()
                },
            }
        })
    }

    /// RLC data
    pub(crate) fn rlc(&self, r: &[Expression<F>]) -> (Expression<F>, Expression<F>) {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => {
                    let value_rlc = self.bytes[0].expr();
                    (value_rlc.expr(), value_rlc.expr())
                },
                self.is_long() => {
                    let value_rlc = self.bytes[1..].rlc(&r);
                    (value_rlc, self.bytes.rlc(&r))
                },
                self.is_very_long() => {
                    unreachablex!();
                    (0.expr(), 0.expr())
                },
            }
        })
    }

    pub(crate) fn rlc_rlp(&self, r: &[Expression<F>]) -> Expression<F> {
        self.rlc(r).1
    }

    pub(crate) fn rlc_value(&self, r: &[Expression<F>]) -> Expression<F> {
        self.rlc(r).0
    }
}

impl RLPValueWitness {
    pub(crate) fn is_string(&self) -> bool {
        !self.is_list
    }

    // Single RLP byte containing the byte value
    pub(crate) fn is_short(&self) -> bool {
        self.is_short
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> bool {
        self.is_long
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> bool {
        self.is_very_long
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        matchr! {
            self.is_short() => 0,
            self.is_long() => 1,
            self.is_very_long() => 2,
        }
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchr! {
            self.is_short() => 1,
            self.is_long() => get_num_bytes_short::value(self.bytes[0]),
            self.is_very_long() => unreachable!(),
        }
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchr! {
            self.is_short() => 1,
            self.is_long() => get_len_short::value(self.bytes[0]),
            self.is_very_long() => unreachable!(),
        }
    }

    /// RLC data
    pub(crate) fn rlc<F: Field>(&self, r: F) -> (F, F) {
        matchr! {
            self.is_short() => {
                let value_rlc = self.bytes[0].scalar();
                (value_rlc, value_rlc)
            },
            self.is_long() => {
                let value_rlc = self.bytes[1..].rlc_value(r);
                (value_rlc, self.bytes.rlc_value(r))
            },
            self.is_very_long() => {
                unreachable!();
            },
        }
    }

    pub(crate) fn rlc_rlp<F: Field>(&self, r: F) -> F {
        self.rlc(r).1
    }

    pub(crate) fn rlc_value<F: Field>(&self, r: F) -> F {
        self.rlc(r).0
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyGadget<F> {
    pub(crate) rlp_list: RLPListGadget<F>,
    pub(crate) short_list_value: RLPValueGadget<F>,
    pub(crate) long_list_value: RLPValueGadget<F>,
    short_list_has_no_nibbles: IsEqualGadget<F>,
    long_list_has_no_nibbles: IsEqualGadget<F>,
    bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyWitness {
    pub(crate) rlp_list: RLPListWitness,
    pub(crate) short_list_value: RLPValueWitness,
    pub(crate) long_list_value: RLPValueWitness,
    bytes: Vec<u8>,
}

impl<F: Field> LeafKeyGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        LeafKeyGadget {
            rlp_list: RLPListGadget::construct(cb, bytes),
            short_list_value: RLPValueGadget::construct(cb, &bytes[1..]),
            long_list_value: RLPValueGadget::construct(cb, &bytes[2..]),
            short_list_has_no_nibbles: IsEqualGadget::<F>::construct(
                cb,
                bytes[1].expr(),
                KEY_TERMINAL_PREFIX_EVEN.expr(),
            ),
            long_list_has_no_nibbles: IsEqualGadget::<F>::construct(
                cb,
                bytes[2].expr(),
                KEY_TERMINAL_PREFIX_EVEN.expr(),
            ),
            bytes: bytes.to_vec(),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<LeafKeyWitness, Error> {
        let rlp_list = self.rlp_list.assign(region, offset, bytes)?;
        let short_list_value = self.short_list_value.assign(region, offset, &bytes[1..])?;
        let long_list_value = self.long_list_value.assign(region, offset, &bytes[2..])?;
        self.short_list_has_no_nibbles.assign(
            region,
            offset,
            F::from(bytes[1] as u64),
            F::from(KEY_TERMINAL_PREFIX_EVEN as u64),
        )?;
        self.long_list_has_no_nibbles.assign(
            region,
            offset,
            F::from(bytes[2] as u64),
            F::from(KEY_TERMINAL_PREFIX_EVEN as u64),
        )?;
        Ok(LeafKeyWitness {
            rlp_list,
            short_list_value,
            long_list_value,
            bytes: bytes.to_vec(),
        })
    }

    pub(crate) fn rlc(&self, r: &[Expression<F>]) -> Expression<F> {
        self.bytes.rlc(r)
    }

    pub(crate) fn leaf_key_rlc(
        &self,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
        is_key_odd: Expression<F>,
        key_mult_first_even: Expression<F>,
        requires_longer_than_55: bool,
        r: &[Expression<F>],
    ) -> Expression<F> {
        circuit!([meta, cb], {
            let calc_rlc = |cb: &mut ConstraintBuilder<F>,
                            bytes: &[Expression<F>],
                            is_key_odd: Expression<F>| {
                leaf_key_rlc(
                    cb,
                    bytes,
                    key_mult_prev.expr(),
                    is_key_odd.expr(),
                    key_mult_first_even.expr(),
                    r,
                )
            };
            matchx! {
                self.rlp_list.is_short() => {
                    matchx! {
                        self.short_list_value.is_short() => {
                            // When no nibbles: only terminal prefix at `bytes[1]`.
                            // Else: Terminal prefix + single nibble  at `bytes[1]`
                            let is_odd = not!(self.short_list_has_no_nibbles);
                            calc_rlc(cb, &self.bytes[1..2], is_odd)
                        },
                        self.short_list_value.is_long() => {
                            // First key byte is at `s_main.bytes[0]`.
                            calc_rlc(cb, &self.bytes[2..35], is_key_odd.expr())
                        },
                    }
                },
                self.rlp_list.is_long() => {
                    matchx! {
                        self.long_list_value.is_short() => {
                            // When no nibbles: only terminal prefix at `bytes[2]`.
                            // Else: Terminal prefix + single nibble  at `bytes[2]`
                            let is_odd = not!(self.long_list_has_no_nibbles);
                            calc_rlc(cb, &self.bytes[2..3], is_odd)
                        },
                        self.long_list_value.is_long() => {
                            if requires_longer_than_55 {
                                // rlp1 needs to be 248.
                                require!(self.bytes[0] => (RLP_LIST_LONG + 1));
                            }
                            // First key byte is at `s_main.bytes[1]`.
                            calc_rlc(cb, &self.bytes[3..36], is_key_odd.expr())
                        },
                    }
                },
            }
        })
    }

    pub(crate) fn ext_key_rlc(
        &self,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
        is_key_part_odd: Expression<F>,
        is_key_odd: Expression<F>,
        data: [Vec<Expression<F>>; 2],
        r: &[Expression<F>],
    ) -> Expression<F> {
        circuit!([meta, cb], {
            let (is_short, is_long) = ifx! {self.rlp_list.is_short() => {
                (
                    self.short_list_value.is_short(),
                    self.short_list_value.is_long(),
                )
            } elsex {
                (
                    self.long_list_value.is_short(),
                    self.long_list_value.is_long(),
                )
            }};
            let mult_first_odd = ifx! {is_key_odd => { 1.expr() } elsex { 16.expr() }};
            let calc_rlc = |cb: &mut ConstraintBuilder<F>,
                            bytes: &[Expression<F>],
                            key_mult_first_even: Expression<F>| {
                ext_key_rlc(
                    cb,
                    bytes,
                    key_mult_prev.expr(),
                    is_key_part_odd.expr(),
                    mult_first_odd.expr(),
                    key_mult_first_even,
                    r,
                )
            };
            // TODO(Brecht): somehow the start index doesn't dependend on the list is_short/is_long?
            matchx! {
                and::expr(&[is_long.expr(), not!(is_key_odd)]) => {
                    // Here we need to multiply nibbles over bytes with different r's so we need to rlc over separate nibbles.
                    // Note that there can be at max 31 key bytes because 32 same bytes would mean
                    // the two keys being the same - update operation, not splitting into extension node.
                    // So, we do not need to look further than `s_main.bytes` even if `s_main.bytes[0]`
                    // is not used (when even number of nibbles).
                    let mut key_bytes = vec![data[0][2].expr()];
                    key_bytes.append(&mut data[0][2..].iter().skip(1).zip(data[1][2..].iter()).map(|(byte, nibble_hi)| {
                        let nibble_lo = (byte.expr() - nibble_hi.expr()) * invert!(16);
                        // Check that `nibble_hi` is correct.
                        require!(byte => nibble_lo.expr() * 16.expr() + nibble_hi.expr());
                        // Collect bytes
                        (nibble_hi.expr() * 16.expr() * r[0].expr()) + nibble_lo.expr()
                    }).collect::<Vec<_>>());
                    calc_rlc(cb, &key_bytes, 1.expr())
                },
                and::expr(&[is_long.expr(), is_key_odd.expr()]) => {
                    let additional_mult = ifx! {is_key_part_odd => { r[0].expr() } elsex { 1.expr() }};
                    calc_rlc(cb, &data[0][2..], additional_mult)
                },
                is_short => {
                    calc_rlc(cb, &data[0][1..2], 1.expr())
                },
            }
        })
    }

    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        self.rlp_list.num_bytes()
    }

    /// Length
    pub(crate) fn len(&self) -> Expression<F> {
        self.rlp_list.len()
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            self.rlp_list.num_rlp_bytes()
                + matchx! {
                    self.rlp_list.is_short() => {
                        self.short_list_value.num_rlp_bytes()
                    },
                    self.rlp_list.is_long() => {
                        self.long_list_value.num_rlp_bytes()
                    },
                }
        })
    }

    /// Length of the key (excluding RLP bytes)
    pub(crate) fn key_len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.rlp_list.is_short() => {
                    self.short_list_value.len()
                },
                self.rlp_list.is_long() => {
                    self.long_list_value.len()
                },
            }
        })
    }

    /// Number of bytes of the key (excluding RLP bytes)
    pub(crate) fn key_num_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.rlp_list.is_short() => {
                    self.short_list_value.num_bytes()
                },
                self.rlp_list.is_long() => {
                    self.long_list_value.num_bytes()
                },
            }
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            self.rlp_list.num_rlp_bytes()
                + matchx! {
                    self.rlp_list.is_short() => {
                        self.short_list_value.num_bytes()
                    },
                    self.rlp_list.is_long() => {
                        self.long_list_value.num_bytes()
                    },
                }
        })
    }

    pub(crate) fn num_key_nibbles(&self, is_key_odd: Expression<F>) -> Expression<F> {
        get_num_nibbles(self.key_len(), is_key_odd)
    }
}

pub(crate) fn compute_acc_and_mult<F: Field>(
    row: &[u8],
    acc: &mut F,
    mult: &mut F,
    start: usize,
    len: usize,
    r: F,
) {
    for i in 0..len {
        *acc += F::from(row[start + i] as u64) * *mult;
        *mult *= r;
    }
}

impl LeafKeyWitness {
    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        self.rlp_list.num_bytes()
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes_list(&self) -> usize {
        self.rlp_list.num_rlp_bytes()
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        self.rlp_list.num_rlp_bytes()
            + if self.rlp_list.is_short() {
                self.short_list_value.num_rlp_bytes()
            } else if self.rlp_list.is_long() {
                self.long_list_value.num_rlp_bytes()
            } else {
                unreachable!();
            }
    }

    /// Length of the key (excluding RLP bytes)
    pub(crate) fn key_len(&self) -> usize {
        matchr! {
            self.rlp_list.is_short() => {
                self.short_list_value.len()
            },
            self.rlp_list.is_long() => {
                self.long_list_value.len()
            },
        }
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn num_bytes_on_key_row(&self) -> usize {
        self.rlp_list.num_rlp_bytes()
            + if self.rlp_list.is_short() {
                self.short_list_value.num_bytes()
            } else if self.rlp_list.is_long() {
                self.long_list_value.num_bytes()
            } else {
                unreachable!();
            }
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn rlc_leaf<F: Field>(&self, r: F) -> (F, F) {
        (0.scalar(), 1.scalar())
            .rlc_chain_value(&self.bytes[0..(self.num_bytes_on_key_row() as usize)], r)
    }

    pub(crate) fn leaf_key_rlc<F: Field>(&self, key_rlc: F, key_mult: F, r: F) -> (F, F) {
        if self.key_len() <= 1 {
            return (key_rlc, key_mult);
        }

        let start = self.num_rlp_bytes_list() as usize;
        let len = self.bytes[start] as usize - 128;
        let even_num_of_nibbles = self.bytes[start + 1] == 32;

        let mut key_rlc = key_rlc;
        let mut key_mult = key_mult;
        if !even_num_of_nibbles {
            // If odd number of nibbles, we have nibble+48 in s_advices[0].
            key_rlc += F::from((self.bytes[start + 1] - 48) as u64) * key_mult;
            key_mult *= r;
        }
        (key_rlc, key_mult).rlc_chain_value(&self.bytes[start + 2..start + 2 + len - 1], r)
    }

    pub(crate) fn ext_key_rlc<F: Field>(
        &self,
        key_mult_prev: F,
        is_key_part_odd: bool,
        is_key_odd: bool,
        data: [Vec<u8>; 2],
        r: F,
    ) -> (F, F) {
        let (is_short, is_long) = if self.rlp_list.is_short() {
            (
                self.short_list_value.is_short(),
                self.short_list_value.is_long(),
            )
        } else {
            (
                self.long_list_value.is_short(),
                self.long_list_value.is_long(),
            )
        };
        let mult_first_odd = if is_key_odd  { 1.scalar() } else { 16.scalar() };
        let calc_rlc = |
                        bytes: &[F],
                        key_mult_first_even: F| {
            ext_key_rlc_value(
                bytes,
                key_mult_prev,
                is_key_part_odd,
                mult_first_odd,
                key_mult_first_even,
                r,
            )
        };
        // TODO(Brecht): somehow the start index doesn't dependend on the list is_short/is_long?
        matchr! {
            is_long && !is_key_odd => {
                // Here we need to multiply nibbles over bytes with different r's so we need to rlc over separate nibbles.
                // Note that there can be at max 31 key bytes because 32 same bytes would mean
                // the two keys being the same - update operation, not splitting into extension node.
                // So, we do not need to look further than `s_main.bytes` even if `s_main.bytes[0]`
                // is not used (when even number of nibbles).
                let mut key_bytes = vec![data[0][2].scalar()];
                key_bytes.append(&mut data[0][2..].iter().skip(1).zip(data[1][2..].iter()).map(|(byte, nibble_hi)| {
                    let nibble_lo = (byte - nibble_hi) >> 4;
                    // Check that `nibble_hi` is correct.
                    assert!(*byte == nibble_lo * 16 + nibble_hi);
                    // Collect bytes
                    (F::from(*nibble_hi as u64) * F::from(16 as u64) * r) + F::from(nibble_lo as u64)
                }).collect::<Vec<_>>());
                calc_rlc(&key_bytes, 1.scalar())
            },
            is_long && is_key_odd => {
                let additional_mult = if is_key_part_odd { r } else { 1.scalar() };
                calc_rlc(&data[0][2..].iter().map(|byte| byte.scalar()).collect::<Vec<_>>(), additional_mult)
            },
            is_short => {
                calc_rlc(&data[0][1..2].iter().map(|byte| byte.scalar()).collect::<Vec<_>>(), 1.scalar())
            },
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct KeyData<F> {
    pub(crate) rlc: Cell<F>,
    pub(crate) mult: Cell<F>,
    pub(crate) num_nibbles: Cell<F>,
    pub(crate) is_odd: Cell<F>,
    pub(crate) is_placeholder_leaf_s: Cell<F>,
    pub(crate) is_placeholder_leaf_c: Cell<F>,
    pub(crate) placeholder_nibble: Cell<F>,
    pub(crate) placeholder_is_odd: Cell<F>,
    pub(crate) parent_rlc: Cell<F>,
    pub(crate) parent_mult: Cell<F>,
}

impl<F: Field> Trackable for KeyData<F> {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn clone_box(&self) -> Box<dyn Trackable> {
        Box::new(self.clone())
    }
}

impl<F: Field> KeyData<F> {
    pub(crate) fn load(
        cb: &mut ConstraintBuilder<F>,
        memory: &MemoryBank<F>,
        offset: Expression<F>,
    ) -> Self {
        let key_data = KeyData {
            rlc: cb.query_cell(),
            mult: cb.query_cell(),
            num_nibbles: cb.query_cell(),
            is_odd: cb.query_cell(),
            is_placeholder_leaf_s: cb.query_cell(),
            is_placeholder_leaf_c: cb.query_cell(),
            placeholder_nibble: cb.query_cell(),
            placeholder_is_odd: cb.query_cell(),
            parent_rlc: cb.query_cell(),
            parent_mult: cb.query_cell(),
        };
        circuit!([meta, cb], {
            memory.load(
                "key load",
                cb,
                offset,
                &[
                    key_data.rlc.expr(),
                    key_data.mult.expr(),
                    key_data.num_nibbles.expr(),
                    key_data.is_odd.expr(),
                    key_data.is_placeholder_leaf_s.expr(),
                    key_data.is_placeholder_leaf_c.expr(),
                    key_data.placeholder_nibble.expr(),
                    key_data.placeholder_is_odd.expr(),
                    key_data.parent_rlc.expr(),
                    key_data.parent_mult.expr(),
                ],
            );
        });
        key_data
    }

    pub(crate) fn store(
        cb: &mut ConstraintBuilder<F>,
        memory: &MemoryBank<F>,
        values: [Expression<F>; 10],
    ) {
        memory.store(cb, &values);
    }

    pub(crate) fn store_initial_values(cb: &mut ConstraintBuilder<F>, memory: &MemoryBank<F>) {
        memory.store_with_key(cb, 0.expr(), &Self::default_values());
    }

    pub(crate) fn default_values() -> [Expression<F>; 10] {
        [
            0.expr(),
            1.expr(),
            0.expr(),
            false.expr(),
            false.expr(),
            false.expr(),
            0.expr(),
            false.expr(),
            0.expr(),
            1.expr(),
        ]
    }

    pub(crate) fn witness_store(
        &self,
        _region: &mut Region<'_, F>,
        offset: usize,
        memory: &mut MemoryBank<F>,
        rlc: F,
        mult: F,
        num_nibbles: usize,
        is_placeholder_leaf_s: bool,
        is_placeholder_leaf_c: bool,
        placeholder_nibble: u8,
        placeholder_is_odd: bool,
        parent_rlc: F,
        parent_mult: F,
    ) -> Result<(), Error> {
        //println!("offset: {}", offset);
        //println!("key_rlc_prev: {:?}", pv.key_rlc_prev);
        //println!("key_mult_prev: {:?}", pv.key_rlc_mult_prev);
        //println!("nibbles_num_prev: {:?}", pv.nibbles_num_prev);

        let values = [
            rlc,
            mult,
            num_nibbles.scalar(),
            (num_nibbles % 2 == 1).scalar(),
            is_placeholder_leaf_s.scalar(),
            is_placeholder_leaf_c.scalar(),
            placeholder_nibble.scalar(),
            placeholder_is_odd.scalar(),
            parent_rlc,
            parent_mult,
        ];
        memory.witness_store(offset, &values);

        Ok(())
    }

    pub(crate) fn witness_load(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        memory: &MemoryBank<F>,
        load_offset: usize,
    ) -> Result<Vec<F>, Error> {
        let values = memory.witness_load(load_offset);

        //println!("offset: {}, values: {:?}", offset, values);
        //println!("key_rlc_prev: {:?}", pv.key_rlc_prev);
        //println!("key_mult_prev: {:?}", pv.key_rlc_mult_prev);
        //println!("nibbles_num_prev: {:?}", pv.nibbles_num_prev);

        self.rlc.assign(region, offset, values[0])?;
        self.mult.assign(region, offset, values[1])?;
        self.num_nibbles.assign(region, offset, values[2])?;
        self.is_odd.assign(region, offset, values[3])?;
        self.is_placeholder_leaf_s
            .assign(region, offset, values[4])?;
        self.is_placeholder_leaf_c
            .assign(region, offset, values[5])?;
        self.placeholder_nibble.assign(region, offset, values[6])?;
        self.placeholder_is_odd.assign(region, offset, values[7])?;
        self.parent_rlc.assign(region, offset, values[8])?;
        self.parent_mult.assign(region, offset, values[9])?;

        Ok(values)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ParentData<F> {
    pub(crate) rlc: Cell<F>,
    pub(crate) is_root: Cell<F>,
    pub(crate) is_placeholder: Cell<F>,
    pub(crate) placeholder_rlc: Cell<F>,
}

impl<F: Field> ParentData<F> {
    pub(crate) fn load(
        description: &'static str,
        cb: &mut ConstraintBuilder<F>,
        memory: &MemoryBank<F>,
        offset: Expression<F>,
    ) -> Self {
        let parent_data = ParentData {
            rlc: cb.query_cell(),
            is_root: cb.query_cell(),
            is_placeholder: cb.query_cell(),
            placeholder_rlc: cb.query_cell(),
        };
        circuit!([meta, cb], {
            memory.load(
                description,
                cb,
                offset,
                &[
                    parent_data.rlc.expr(),
                    parent_data.is_root.expr(),
                    parent_data.is_placeholder.expr(),
                    parent_data.placeholder_rlc.expr(),
                ],
            );
        });
        parent_data
    }

    pub(crate) fn store(
        cb: &mut ConstraintBuilder<F>,
        memory: &MemoryBank<F>,
        values: [Expression<F>; 4],
    ) {
        memory.store(cb, &values);
    }

    pub(crate) fn witness_store(
        &self,
        _region: &mut Region<'_, F>,
        offset: usize,
        memory: &mut MemoryBank<F>,
        rlc: F,
        force_hashed: bool,
        is_placeholder: bool,
        placeholder_rlc: F,
    ) -> Result<(), Error> {
        //println!("offset: {}", offset);
        //println!("rlc: {:?}", rlc);
        //println!("is_hashed: {}", is_hashed);

        let values = [
            rlc,
            force_hashed.scalar(),
            is_placeholder.scalar(),
            placeholder_rlc,
        ];
        memory.witness_store(offset, &values);

        Ok(())
    }

    pub(crate) fn witness_load(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        memory: &MemoryBank<F>,
        load_offset: usize,
    ) -> Result<Vec<F>, Error> {
        let values = memory.witness_load(load_offset);

        self.rlc.assign(region, offset, values[0])?;
        self.is_root.assign(region, offset, values[1])?;
        self.is_placeholder.assign(region, offset, values[2])?;
        self.placeholder_rlc.assign(region, offset, values[3])?;

        Ok(values)
    }
}

/// Add the nibble from the drifted branch
pub(crate) fn drifted_nibble_rlc<F: Field>(
    cb: &mut ConstraintBuilder<F>,
    difted_index: Expression<F>,
    key_mult_prev: Expression<F>,
    is_key_odd: Expression<F>,
) -> Expression<F> {
    circuit!([meta, cb], {
        // Add the nibble from the branch (drifted_index is set to the same value for
        // all children)
        let drifted_mult =
            key_mult_prev.expr() * ifx! {is_key_odd => { 16.expr() } elsex { 1.expr() }};
        difted_index * drifted_mult
    })
}

pub(crate) fn leaf_key_rlc<F: Field>(
    cb: &mut ConstraintBuilder<F>,
    bytes: &[Expression<F>],
    key_mult_prev: Expression<F>,
    is_key_odd: Expression<F>,
    key_mult_first_even: Expression<F>,
    r: &[Expression<F>],
) -> Expression<F> {
    circuit!([meta, cb], {
        // Add the odd nibble first if we have one.
        let (rlc, mult) = ifx! {is_key_odd => {
            (get_terminal_odd_nibble(bytes[0].expr()) * key_mult_prev.expr(), r[0].expr())
        } elsex {
            require!(bytes[0] => KEY_TERMINAL_PREFIX_EVEN);
            (0.expr(), key_mult_first_even.expr())
        }};
        (rlc, key_mult_prev * mult).rlc_chain(bytes[1..].rlc(r))
    })
}

pub(crate) fn ext_key_rlc<F: Field>(
    cb: &mut ConstraintBuilder<F>,
    bytes: &[Expression<F>],
    key_mult_prev: Expression<F>,
    is_odd: Expression<F>,
    rlc_mult_first_odd: Expression<F>,
    key_mult_first_odd: Expression<F>,
    r: &[Expression<F>],
) -> Expression<F> {
    circuit!([meta, cb], {
        // Add the odd nibble first if we have one.
        let (rlc, mult) = ifx! {is_odd => {
            (get_ext_odd_nibble(bytes[0].expr()) * key_mult_prev.expr() * rlc_mult_first_odd, key_mult_first_odd.expr())
        } elsex {
            require!(bytes[0] => KEY_PREFIX_EVEN);
            (0.expr(), 1.expr())
        }};
        (rlc, key_mult_prev * mult).rlc_chain(bytes[1..].rlc(r))
    })
}

pub(crate) fn ext_key_rlc_value<F: Field>(
    bytes: &[F],
    key_mult_prev: F,
    is_odd: bool,
    rlc_mult_first_odd: F,
    key_mult_first_odd: F,
    r: F,
) -> (F, F) {
    // Add the odd nibble first if we have one.
    let (rlc, mult) = if is_odd {
        (get_ext_odd_nibble_value(bytes[0]) * key_mult_prev * rlc_mult_first_odd, key_mult_first_odd)
    } else {
        assert!(bytes[0] == KEY_PREFIX_EVEN.scalar());
        (0.scalar(), 1.scalar())
    };
    (rlc, key_mult_prev * mult).rlc_chain_value_f(&bytes[1..], r)
}

pub(crate) fn get_terminal_odd_nibble<F: Field>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_TERMINAL_PREFIX_ODD.expr()
}

pub(crate) fn get_ext_odd_nibble<F: Field>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_PREFIX_ODD.expr()
}

pub(crate) fn get_ext_odd_nibble_value<F: Field>(byte: F) -> F {
    // The odd nible is stored in the same byte as the prefix
    byte - F::from(KEY_PREFIX_ODD as u64)
}

// A single RLP byte
pub(crate) mod get_len_short {
    use crate::mpt_circuit::param::RLP_SHORT;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        byte - RLP_SHORT.expr()
    }
    pub(crate) fn value(byte: u8) -> usize {
        (byte - RLP_SHORT) as usize
    }
}

// A single RLP byte + the encoded length
pub(crate) mod get_num_bytes_short {
    use super::get_len_short;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        1.expr() + get_len_short::expr(byte)
    }
    pub(crate) fn value(byte: u8) -> usize {
        1 + get_len_short::value(byte)
    }
}

pub(crate) mod get_len_list_short {
    use crate::mpt_circuit::param::RLP_LIST_SHORT;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        byte - RLP_LIST_SHORT.expr()
    }
    pub(crate) fn value(byte: u8) -> usize {
        (byte - RLP_LIST_SHORT) as usize
    }
}

// A single RLP byte + the encoded length
pub(crate) mod get_num_bytes_list_short {
    use super::get_len_list_short;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        1.expr() + get_len_list_short::expr(byte)
    }
    pub(crate) fn value(byte: u8) -> usize {
        1 + get_len_list_short::value(byte)
    }
}

pub(crate) fn get_num_nibbles<F: Field>(
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

pub(crate) fn extend_rand<F: Field>(r: &[Expression<F>]) -> Vec<Expression<F>> {
    [
        r.to_vec(),
        r.iter()
            .map(|v| r.last().unwrap().expr() * v.clone())
            .collect::<Vec<_>>(),
    ]
    .concat()
}

pub(crate) fn bytes_into_rlc<F: Field>(expressions: &[u8], r: F) -> F {
    let mut rlc = F::zero();
    let mut mult = F::one();
    for expr in expressions.iter() {
        rlc += F::from(*expr as u64) * mult;
        mult *= r;
    }
    rlc
}

pub(crate) fn parent_memory(is_s: bool) -> String {
    (if is_s { "parent_s" } else { "parent_c" }).to_string()
}

pub(crate) fn key_memory(is_s: bool) -> String {
    (if is_s { "key_s" } else { "key_c" }).to_string()
}

/// MPTConstraintBuilder
#[derive(Clone)]
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

impl<F: Field> MPTConstraintBuilder<F> {
    const DEFAULT_LENGTH_S: usize = 34;
    const DEFAULT_LENGTH_C: usize = 32;
    const NUM_BYTES_SKIP: usize = 2; // RLP bytes never need to be zero checked
    const DEFAULT_RANGE: FixedTableTag = FixedTableTag::RangeKeyLen256;

    pub(crate) fn new(max_degree: usize, cell_manager: Option<CellManager<F>>) -> Self {
        MPTConstraintBuilder {
            base: ConstraintBuilder::new(max_degree, cell_manager),
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

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug, Default)]
pub struct IsEmptyTreeGadget<F> {
    is_in_empty_trie: IsEqualGadget<F>,
    is_in_empty_branch: IsEqualGadget<F>,
}

impl<F: Field> IsEmptyTreeGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        parent_rlc: Expression<F>,
        r: &[Expression<F>],
    ) -> Self {
        circuit!([meta, cb], {
            let empty_root_rlc = EMPTY_TRIE_HASH
                .iter()
                .map(|v| v.expr())
                .collect::<Vec<_>>()
                .rlc(&r);
            let is_in_empty_trie =
                IsEqualGadget::construct(cb, parent_rlc.expr(), empty_root_rlc.expr());
            let is_in_empty_branch = IsEqualGadget::construct(cb, parent_rlc.expr(), 0.expr());

            Self {
                is_in_empty_trie,
                is_in_empty_branch,
            }
        })
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        or::expr(&[self.is_in_empty_trie.expr(), self.is_in_empty_branch.expr()])
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        parent_rlc: F,
        r: F,
    ) -> Result<(), Error> {
        self.is_in_empty_trie.assign(
            region,
            offset,
            parent_rlc,
            bytes_into_rlc(&EMPTY_TRIE_HASH, r),
        )?;
        self.is_in_empty_branch
            .assign(region, offset, parent_rlc, 0.scalar())?;
        Ok(())
    }
}


#[derive(Clone, Debug, Default)]
pub(crate) struct RLPItemGadget<F> {
    pub(crate) value: RLPValueGadget<F>,
    pub(crate) list: RLPListGadget<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPItemWitness {
    pub(crate) value: RLPValueWitness,
    pub(crate) list: RLPListWitness,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPItemGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        RLPItemGadget {
            value: RLPValueGadget::construct(cb, bytes),
            list: RLPListGadget::construct(cb, bytes),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPItemWitness, Error> {
        let value_witness = self.value.assign(region, offset, bytes)?;
        let list_witness = self.list.assign(region, offset, bytes)?;

        if value_witness.is_string() && list_witness.is_list() {
            println!("{:?}", bytes)
        }
        assert!(!(value_witness.is_string() && list_witness.is_list()));

        Ok(RLPItemWitness {
            value: value_witness,
            list: list_witness,
            bytes: bytes.to_vec(),
        })
    }

    // Single RLP byte containing the byte value
    pub(crate) fn is_short(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.is_short(),
                self.list.is_list() => self.list.is_short(),
            }
        })
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.is_long(),
                self.list.is_list() => self.list.is_long(),
            }
        })
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.is_very_long(),
                self.list.is_list() => self.list.is_very_long(),
            }
        })
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.num_rlp_bytes(),
                self.list.is_list() => self.list.num_rlp_bytes(),
            }
        })
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.num_bytes(),
                self.list.is_list() => self.list.num_bytes(),
            }
        })
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.len(),
                self.list.is_list() => self.list.len(),
            }
        })
    }

    /// RLC data
    pub(crate) fn rlc(&self, cb: &mut ConstraintBuilder<F>, r: &[Expression<F>]) -> (Expression<F>, Expression<F>) {
        circuit!([meta, cb], {
            matchx! {
                self.value.is_string() => self.value.rlc(r),
                self.list.is_list() => self.list.rlc(r),
            }
        })
    }

    pub(crate) fn rlc_rlp(&self, cb: &mut ConstraintBuilder<F>, r: &[Expression<F>]) -> Expression<F> {
        self.rlc(cb, r).1
    }

    pub(crate) fn rlc_value(&self, cb: &mut ConstraintBuilder<F>, r: &[Expression<F>]) -> Expression<F> {
        self.rlc(cb, r).0
    }

    pub(crate) fn rlc_branch(&self, r: &[Expression<F>]) -> Expression<F> {
        /*circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.rlc_value(r),
                self.list.is_list() => self.list.rlc(r).1,
            }
        })*/
        circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.rlc(r).0,
                self.list.is_list() => self.list.rlc(r).1,
            }
        })
    }
}

impl RLPItemWitness {
    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchr! {
            self.value.is_string() => self.value.num_bytes(),
            self.list.is_list() => self.list.num_bytes(),
        }
    }

    // Single RLP byte containing the byte value
    /*pub(crate) fn is_short(&self) -> bool {
        matchr! {
            self.value.is_string() => self.value.is_very_long(),
            self.list.is_list() => self.list.is_very_long(),
        }
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> bool {
        self.is_long
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> bool {
        self.is_very_long
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        matchr! {
            self.is_short() => 0,
            self.is_long() => 1,
            self.is_very_long() => 2,
        }
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchr! {
            self.is_short() => 1,
            self.is_long() => get_num_bytes_short::value(self.bytes[0]),
            self.is_very_long() => {
                unreachable!();
            },
        }
    }*/

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchr! {
            self.value.is_string() => self.value.len(),
            self.list.is_list() => self.list.len(),
        }
    }

    /// RLC data
    /*pub(crate) fn rlc<F: Field>(&self, r: F) -> (F, F) {
        matchr! {
            self.is_short() => {
                let value_rlc = self.bytes[0].scalar();
                (value_rlc, value_rlc)
            },
            self.is_long() => {
                let value_rlc = self.bytes[1..].rlc_value(r);
                (value_rlc, self.bytes.rlc_value(r))
            },
            self.is_very_long() => {
                unreachable!();
            },
        }
    }

    pub(crate) fn rlc_rlp<F: Field>(&self, r: F) -> F {
        self.rlc(r).1
    }

    pub(crate) fn rlc_value<F: Field>(&self, r: F) -> F {
        self.rlc(r).0
    }*/

    pub(crate) fn rlc_branch<F: Field>(&self, r: F) -> F {
        /*circuit!([meta, _cb!()], {
            matchx! {
                self.value.is_string() => self.value.rlc_value(r),
                self.list.is_list() => self.list.rlc(r).1,
            }
        })*/
        matchr! {
            self.value.is_string() => self.value.rlc(r).0,
            self.list.is_list() => self.list.rlc(r).1,
        }
    }
}
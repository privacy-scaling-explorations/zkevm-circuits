use std::{any::Any, marker::PhantomData, ops::Range};

use crate::{
    _cb, circuit,
    circuit_tools::{
        cell_manager::{Cell, CellManager, DataTransition, Trackable},
        constraint_builder::{Conditionable, ConstraintBuilder, RLCChainable, RLCable},
        gadgets::IsEqualGadget,
        memory::MemoryBank,
    },
    evm_circuit::util::rlc,
    matchr, matchw,
    mpt_circuit::param::{
        KEY_PREFIX_EVEN, KEY_TERMINAL_PREFIX_EVEN, RLP_HASH_VALUE, RLP_LIST_LONG, RLP_LIST_SHORT,
        RLP_NIL, RLP_SHORT,
    },
    util::Expr,
};
use eth_types::Field;
use gadgets::util::{and, not, Scalar};
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression, VirtualCells},
    poly::Rotation,
};

use super::{
    columns::MainCols,
    param::{
        ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND,
        ACCOUNT_NON_EXISTING_IND, ARITY, BRANCH_0_C_START, BRANCH_0_S_START, BRANCH_ROWS_NUM,
        IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, IS_C_BRANCH_NON_HASHED_POS, IS_C_EXT_LONGER_THAN_55_POS,
        IS_C_EXT_NODE_NON_HASHED_POS, IS_S_BRANCH_NON_HASHED_POS, IS_S_EXT_LONGER_THAN_55_POS,
        IS_S_EXT_NODE_NON_HASHED_POS, KEY_PREFIX_ODD, KEY_TERMINAL_PREFIX_ODD, NIBBLES_COUNTER_POS,
        RLP_LONG,
    },
    witness_row::MptWitnessRow,
    FixedTableTag, MPTConfig, MPTContext, ProofValues,
};
use crate::mpt_circuit::param::{
    IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
    IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, RLP_NUM,
};

/// Indexale object
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
    pub(crate) bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListWitness {
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPListGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        // TODO(Brecht): add lookup
        RLPListGadget {
            is_short: cb.query_cell(),
            is_long: cb.query_cell(),
            bytes: bytes.to_vec(),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPListWitness, Error> {
        const RLP_LIST_LONG_INCLUSIVE: u8 = RLP_LIST_LONG - 1;
        const RLP_LIST_VALUE_MAX: u8 = 255;

        let mut is_short = false;
        let mut is_long = false;
        match bytes[0] {
            RLP_LIST_SHORT..=RLP_LIST_LONG_INCLUSIVE => is_short = true,
            RLP_LIST_LONG..=RLP_LIST_VALUE_MAX => is_long = true,
            _ => {
                println!("bytes: {:?}", bytes);
                unreachable!();
            }
        }

        self.is_short.assign(region, offset, F::from(is_short))?;
        self.is_long.assign(region, offset, F::from(is_long))?;

        Ok(RLPListWitness {
            is_short,
            is_long,
            bytes: bytes.to_vec(),
        })
    }

    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short.expr()
    }

    // RLP byte followed by the number of bytes in length, followed by the length
    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long.expr()
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => 1.expr(),
                self.is_long() => 2.expr(),
            }
        })
    }

    /// Returns the total length of the list (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => get_num_bytes_list_short::expr(self.bytes[0].expr()),
                self.is_long() => 2.expr() + self.bytes[1].expr(),
            }
        })
    }

    /// Returns the length of the list (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {
                self.is_short() => get_len_list_short::expr(self.bytes[0].expr()),
                self.is_long() => self.bytes[1].expr(),
            }
        })
    }
}

impl RLPListWitness {
    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_short(&self) -> bool {
        self.is_short
    }

    // RLP byte followed by the number of bytes in length, followed by the length
    pub(crate) fn is_long(&self) -> bool {
        self.is_long
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> u64 {
        matchr! {
            self.is_short() => 1,
            self.is_long() => 2,
        }
    }

    /// Returns the total length of the list (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> u64 {
        matchr! {
            self.is_short() => get_num_bytes_list_short::value(self.bytes[0]),
            self.is_long() => 2 + (self.bytes[1] as u64),
        }
    }

    /// Returns the length of the list (excluding RLP bytes)
    pub(crate) fn len(&self) -> u64 {
        matchr! {
            self.is_short() => get_len_list_short::value(self.bytes[0]),
            self.is_long() => self.bytes[1] as u64,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPValueGadget<F> {
    pub(crate) is_short: Cell<F>,
    pub(crate) is_long: Cell<F>,
    pub(crate) is_very_long: Cell<F>,
    pub(crate) bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPValueWitness {
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) is_very_long: bool,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPValueGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        // TODO(Brecht): add lookup
        RLPValueGadget {
            is_short: cb.query_cell(),
            is_long: cb.query_cell(),
            is_very_long: cb.query_cell(),
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
        const RLP_LONG_INCLUSIVE: u8 = RLP_LONG - 1;
        const RLP_VALUE_MAX: u8 = RLP_LIST_SHORT - 1;

        let mut is_short = false;
        let mut is_long = false;
        let mut is_very_long = false;
        match bytes[0] {
            0..=RLP_SHORT_INCLUSIVE => is_short = true,
            RLP_SHORT..=RLP_LONG_INCLUSIVE => is_long = true,
            RLP_LONG..=RLP_VALUE_MAX => is_very_long = true,
            _ => unreachable!(),
        }

        self.is_short.assign(region, offset, F::from(is_short))?;
        self.is_long.assign(region, offset, F::from(is_long))?;
        self.is_very_long
            .assign(region, offset, F::from(is_very_long))?;

        Ok(RLPValueWitness {
            is_short,
            is_long,
            is_very_long,
            bytes: bytes.to_vec(),
        })
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
}

impl RLPValueWitness {
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
    pub(crate) fn num_rlp_bytes(&self) -> u64 {
        matchr! {
            self.is_short() => 0,
            self.is_long() => 1,
            self.is_very_long() => 2,
        }
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> u64 {
        matchr! {
            self.is_short() => 1,
            self.is_long() => get_num_bytes_short::value(self.bytes[0]),
            self.is_very_long() => {
                unreachable!();
            },
        }
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> u64 {
        matchr! {
            self.is_short() => 1,
            self.is_long() => get_len_short::value(self.bytes[0]),
            self.is_very_long() => {
                unreachable!();
            },
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyGadget<F> {
    rlp_list: RLPListGadget<F>,
    short_list_value: RLPValueGadget<F>,
    long_list_value: RLPValueGadget<F>,
    short_list_has_no_nibbles: IsEqualGadget<F>,
    long_list_has_no_nibbles: IsEqualGadget<F>,
    bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyWitness {
    rlp_list: RLPListWitness,
    short_list_value: RLPValueWitness,
    long_list_value: RLPValueWitness,
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

    pub(crate) fn key_rlc(
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

    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        self.rlp_list.num_bytes()
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

impl LeafKeyWitness {
    /// Returns the total length of the leaf (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> u64 {
        self.rlp_list.num_bytes()
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes_list(&self) -> u64 {
        self.rlp_list.num_rlp_bytes()
    }

    /// Number of RLP bytes for leaf and key
    pub(crate) fn num_rlp_bytes(&self) -> u64 {
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
    pub(crate) fn key_len(&self) -> u64 {
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
    pub(crate) fn num_bytes_on_key_row(&self) -> u64 {
        self.rlp_list.num_rlp_bytes()
            + if self.rlp_list.is_short() {
                self.short_list_value.num_bytes()
            } else if self.rlp_list.is_long() {
                self.long_list_value.num_bytes()
            } else {
                unreachable!();
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

impl<F: Field> BranchNodeInfo<F> {
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

    pub(crate) fn ext_is_not_hashed(&self) -> Expression<F> {
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
                self.is_branch_short(meta) => get_len_list_short::expr(rlp_bytes[0].expr()),
                self.is_branch_long(meta) => rlp_bytes[1].expr(),
                self.is_branch_very_long(meta) => rlp_bytes[1].expr() * 256.expr() + rlp_bytes[2].expr(),
            }
        })
    }

    /// Number of bytes in the extension node
    pub(crate) fn ext_num_bytes(&self, meta: &mut VirtualCells<F>, rot_c: i32) -> Expression<F> {
        self.ext_num_rlp_bytes(meta) + self.ext_len(meta, rot_c)
    }

    /// Length of the extension node (excluding RLP bytes)
    pub(crate) fn ext_len(&self, _meta: &mut VirtualCells<F>, rot_c: i32) -> Expression<F> {
        circuit!([_meta, _cb!()], {
            matchx! {
                self.is_short() + self.is_long() => get_len_list_short::expr(a!(self.ctx.s_main.rlp1, rot_c)),
                self.is_longer_than_55_s => get_len_short::expr(a!(self.ctx.s_main.bytes[0], rot_c)),
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
                self.is_long() => get_len_short::expr(a!(self.ctx.s_main.rlp2, rel_rot)),
                self.is_longer_than_55_s => get_len_short::expr(a!(self.ctx.s_main.bytes[0], rel_rot)),
            }
        })
    }

    /// Number of bytes of the key (including RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_key_num_bytes(
        &self,
        meta: &mut VirtualCells<F>,
        rel_rot: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! (
                self.is_short() => 0.expr(),
                self.is_long() => 1.expr(),
                self.is_longer_than_55_s => 2.expr(),
            ) + self.ext_key_len(meta, rel_rot)
        })
    }

    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn ext_num_bytes_on_key_row(
        &self,
        meta: &mut VirtualCells<F>,
        rel_rot: i32,
    ) -> Expression<F> {
        self.ext_num_rlp_bytes(meta) + self.ext_key_num_bytes(meta, rel_rot)
    }

    /// Length of the included branch (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_branch_len(
        &self,
        meta: &mut VirtualCells<F>,
        rot_ext_s: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx! {self.contains_hashed_branch(meta, rot_ext_s) => {
                32.expr()
            } elsex {
                get_len_list_short::expr(a!(self.ctx.c_main.bytes[0], rot_ext_s))
            }}
        })
    }

    /// Length of the included branch (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn ext_branch_num_bytes(
        &self,
        meta: &mut VirtualCells<F>,
        rot_ext_s: i32,
    ) -> Expression<F> {
        1.expr() + self.ext_branch_len(meta, rot_ext_s)
    }

    /// Length of the key (excluding RLP bytes)
    /// Uses data on the current row!
    pub(crate) fn contains_hashed_branch(
        &self,
        meta: &mut VirtualCells<F>,
        rot_ext_s: i32,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            a!(self.ctx.c_main.rlp2, rot_ext_s) * invert!(RLP_HASH_VALUE)
        })
    }

    /// Key data is read from the current row, not at rot_key!
    pub(crate) fn ext_key_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
        rot_ext_c: i32,
    ) -> Expression<F> {
        circuit!([meta, cb], {
            let mult_first_odd = ifx! {self.is_key_odd() => { 1.expr() } elsex { 16.expr() }};
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
                    let mut key_bytes = vec![a!(self.ctx.s_main.bytes[0], rot_ext_c - 1)];
                    key_bytes.append(&mut self.ctx.s_main.bytes.iter().skip(1).zip(self.ctx.s_main.bytes.iter()).map(|(byte, byte_hi)| {
                        let byte = a!(byte, rot_ext_c - 1);
                        let nibble_hi = a!(byte_hi, rot_ext_c);
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
                    let key_bytes = self.ctx.s_main.bytes(meta, rot_ext_c - 1);
                    calc_rlc(meta, cb, &key_bytes, additional_mult)
                },
                self.is_short() => {
                    let key_bytes = vec![a!(self.ctx.s_main.rlp2, rot_ext_c - 1)];
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

#[derive(Clone)]
pub(crate) struct BranchChildInfo<F> {
    pub(crate) is_s: bool,
    pub(crate) ctx: MPTContext<F>,
    pub(crate) rot_branch: i32,
}

impl<F: Field> BranchChildInfo<F> {
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
                a!(self.ctx.main(self.is_s).rlp2, self.rot_branch) * invert!(RLP_HASH_VALUE) * 32.expr() + 1.expr()
            } elsex {
                get_num_bytes_list_short::expr(a!(self.ctx.main(self.is_s).bytes[0], self.rot_branch))
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
                    require!(a!(main.bytes[0], self.rot_branch) => RLP_NIL);
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
}

impl<F: Field> StorageLeafInfo<F> {
    pub(crate) fn new(ctx: MPTContext<F>, is_s: bool, rot_key: i32) -> Self {
        StorageLeafInfo {
            is_s,
            ctx: ctx.clone(),
            rot_key,
        }
    }

    pub(crate) fn set_is_s(&mut self, is_s: bool) {
        self.is_s = is_s;
    }

    pub(crate) fn is_below_account(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        let rot_parent = if self.is_s { -1 } else { -3 };
        self.ctx.is_account(meta, self.rot_key + rot_parent)
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

impl<F: Field> AccountLeafInfo<F> {
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
            get_len_short::expr(a!(self.ctx.s_main.bytes[0], self.rot_key))
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

    pub(crate) fn key_rlc(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        key_mult_prev: Expression<F>,
        is_key_odd: Expression<F>,
        key_mult_first_even: Expression<F>,
        rot: i32,
    ) -> Expression<F> {
        leaf_key_rlc(
            cb,
            &self.ctx.expr(meta, self.rot_key + rot)[3..36],
            key_mult_prev.expr(),
            is_key_odd,
            key_mult_first_even,
            &self.ctx.r,
        )
    }
}

pub(crate) fn contains_placeholder_leaf<F: Field>(
    meta: &mut VirtualCells<F>,
    ctx: MPTContext<F>,
    is_s: bool,
    rot_branch_child: i32,
) -> Expression<F> {
    meta.query_advice(ctx.denoter.sel(is_s), Rotation(rot_branch_child))
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

pub(crate) fn get_terminal_odd_nibble<F: Field>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_TERMINAL_PREFIX_ODD.expr()
}

pub(crate) fn get_ext_odd_nibble<F: Field>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_PREFIX_ODD.expr()
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
    pub(crate) fn value(byte: u8) -> u64 {
        (byte - RLP_SHORT) as u64
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
    pub(crate) fn value(byte: u8) -> u64 {
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
    pub(crate) fn value(byte: u8) -> u64 {
        (byte - RLP_LIST_SHORT) as u64
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
    pub(crate) fn value(byte: u8) -> u64 {
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

// Returns the RLC values stored in the parent of the current node.
pub(crate) fn get_parent_rlc_state<F: Field>(
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

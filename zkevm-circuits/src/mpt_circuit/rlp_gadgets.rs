use crate::{
    _cb, circuit,
    circuit_tools::{
        cell_manager::Cell,
        constraint_builder::{ConstraintBuilder, RLCable, RLCableValue},
    },
    matchr, matchw,
    mpt_circuit::param::{RLP_LIST_LONG, RLP_LIST_SHORT, RLP_SHORT},
    util::Expr,
};
use eth_types::Field;
use gadgets::util::{not, Scalar};
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression},
};

use super::param::{KEY_PREFIX_ODD, KEY_TERMINAL_PREFIX_ODD, RLP_LONG};

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
        // TODO(Brecht): add lookup/LtGadget
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
        self.is_very_long
            .assign(region, offset, F::from(is_very_long))?;
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
            let value_rlc = matchx! {
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

    pub(crate) fn rlc_rlp_dummy<F: Field>(&self, r: F) -> F {
        self.rlc(r).1
    }

    pub(crate) fn rlc_value<F: Field>(&self, r: F) -> F {
        self.rlc(r).0
    }

    /// Returns the rlc of the RLP bytes
    pub(crate) fn rlc_rlp2<F: Field>(&self, r: F) -> (F, F) {
        matchr! {
            self.is_short() => (self.bytes[..1].rlc_value(r), r),
            self.is_long() => (self.bytes[..2].rlc_value(r), r*r),
            self.is_very_long() => (self.bytes[..3].rlc_value(r), r*r*r),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListDataGadget<F> {
    pub(crate) rlp_list_bytes: [Cell<F>; 3],
    pub(crate) rlp_list: RLPListGadget<F>,
}

impl<F: Field> RLPListDataGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>) -> Self {
        let rlp_list_bytes = cb.query_bytes();
        let rlp_list_bytes_expr = rlp_list_bytes.iter().map(|c| c.expr()).collect::<Vec<_>>();
        RLPListDataGadget {
            rlp_list: RLPListGadget::construct(cb, &rlp_list_bytes_expr),
            rlp_list_bytes,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        list_bytes: &[u8],
    ) -> Result<RLPListWitness, Error> {
        for (cell, byte) in self.rlp_list_bytes.iter().zip(list_bytes.iter()) {
            cell.assign(region, offset, byte.scalar())?;
        }
        let rlp_list = self.rlp_list.assign(region, offset, list_bytes)?;

        Ok(rlp_list)
    }

    pub(crate) fn rlc(&self, r: &[Expression<F>]) -> (Expression<F>, Expression<F>) {
        self.rlp_list.rlc_rlp(&r)
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

        self.is_short.assign(region, offset, F::from(is_short))?;
        self.is_long.assign(region, offset, F::from(is_long))?;
        self.is_very_long
            .assign(region, offset, F::from(is_very_long))?;
        self.is_list.assign(region, offset, F::from(is_list))?;

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
    pub(crate) fn rlc(
        &self,
        cb: &mut ConstraintBuilder<F>,
        r: &[Expression<F>],
    ) -> (Expression<F>, Expression<F>) {
        circuit!([meta, cb], {
            matchx! {
                self.value.is_string() => self.value.rlc(r),
                self.list.is_list() => self.list.rlc(r),
            }
        })
    }

    pub(crate) fn rlc_rlp(
        &self,
        cb: &mut ConstraintBuilder<F>,
        r: &[Expression<F>],
    ) -> Expression<F> {
        self.rlc(cb, r).1
    }

    pub(crate) fn rlc_value(
        &self,
        cb: &mut ConstraintBuilder<F>,
        r: &[Expression<F>],
    ) -> Expression<F> {
        self.rlc(cb, r).0
    }

    pub(crate) fn rlc_branch(&self, r: &[Expression<F>]) -> Expression<F> {
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

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchr! {
            self.value.is_string() => self.value.len(),
            self.list.is_list() => self.list.len(),
        }
    }

    pub(crate) fn rlc_branch<F: Field>(&self, r: F) -> F {
        matchr! {
            self.value.is_string() => self.value.rlc(r).0,
            self.list.is_list() => self.list.rlc(r).1,
        }
    }
}

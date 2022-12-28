use crate::evm_circuit::param::N_BYTES_U64;
use crate::evm_circuit::table::{FixedTableTag, Lookup};
use crate::evm_circuit::util::constraint_builder::ConstraintBuilder;
use crate::evm_circuit::util::math_gadget::{IsEqualGadget, IsZeroGadget, LtGadget};
use crate::evm_circuit::util::{self, from_bytes, sum, CachedRegion, Cell};
use crate::util::Expr;
use array_init::array_init;
use eth_types::{Field, ToLittleEndian, Word, U256};
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Error;

/// Construction of word shift right for `signed(a) >> shift == signed(b)`.
#[derive(Clone, Debug)]
pub(crate) struct SarWordsGadget<F> {
    a: util::Word<F>,
    shift: util::Word<F>,
    b: util::Word<F>,
    // four 64-bit limbs of word `a`
    a64s: [Cell<F>; 4],
    // four 64-bit limbs of word `b`
    b64s: [Cell<F>; 4],
    // Each of the four `a64s` limbs is split into two parts (`a64s_lo` and `a64s_hi`) at
    // position `shf_mod64`. `a64s_lo` is the lower `shf_mod64` bits.
    a64s_lo: [Cell<F>; 4],
    // `a64s_hi` is the higher `64 - shf_mod64` bits.
    a64s_hi: [Cell<F>; 4],
    // shift[0] / 64
    shf_div64: Cell<F>,
    // shift[0] % 64
    shf_mod64: Cell<F>,
    // 1 << shf_mod64
    p_lo: Cell<F>,
    // 1 << (64 - shf_mod64)
    p_hi: Cell<F>,
    // p_top = is_neg * (0xFFFFFFFFFFFFFFFF - p_hi + 1))
    p_top: Cell<F>,
    // is_neg = is_neg(a)
    is_neg: LtGadget<F, 1>,
    // shift < 256
    shf_lt256: IsZeroGadget<F>,
    // shf_div64 == 0
    shf_div64_eq0: IsZeroGadget<F>,
    // shf_div64 == 1
    shf_div64_eq1: IsEqualGadget<F>,
    // shf_div64 == 2
    shf_div64_eq2: IsEqualGadget<F>,
    // shf_div64 == 3
    shf_div64_eq3: IsEqualGadget<F>,
    // a64s_lo[idx] < p_lo
    a64s_lo_lt_p_lo: [LtGadget<F, 16>; 4],
    // a64s_hi[idx] < p_hi
    a64s_hi_lt_p_hi: [LtGadget<F, 16>; 4],
}

impl<F: Field> SarWordsGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        a: util::Word<F>,
        shift: util::Word<F>,
    ) -> Self {
        let b = cb.query_word();
        let a64s = array_init(|_| cb.query_cell());
        let b64s = array_init(|_| cb.query_cell());
        let a64s_lo = array_init(|_| cb.query_cell());
        let a64s_hi = array_init(|_| cb.query_cell());
        let shf_div64 = cb.query_cell();
        let shf_mod64 = cb.query_cell();
        let p_lo = cb.query_cell();
        let p_hi = cb.query_cell();
        let p_top = cb.query_cell();
        let is_neg = LtGadget::construct(cb, 127.expr(), a.cells[31].expr());
        let shf_lt256 = IsZeroGadget::construct(cb, sum::expr(&shift.cells[1..32]));
        let max_u64 = 0xFFFFFFFFFFFFFFFF_u64;
        for idx in 0..4 {
            let offset = idx * N_BYTES_U64;

            // a64s constraint
            cb.require_equal(
                "a64s[idx] == from_bytes(a[8 * idx..8 * (idx + 1)])",
                a64s[idx].expr(),
                from_bytes::expr(&a.cells[offset..offset + N_BYTES_U64]),
            );

            // b64s constraint
            cb.require_equal(
                 "b64s[idx] * shf_lt256 + is_neg * (1 - shf_lt256) * 0xFFFFFFFFFFFFFFFF == from_bytes(b[8 * idx..8 * (idx + 1)])",
                 b64s[idx].expr() * shf_lt256.expr() + is_neg.expr() * (1.expr() - shf_lt256.expr()) * max_u64.expr(),
                 from_bytes::expr(&b.cells[offset..offset + N_BYTES_U64]),
             );
            cb.require_equal(
                "a64s[idx] == a64s_lo[idx] + a64s_hi[idx] * p_lo",
                a64s[idx].expr(),
                a64s_lo[idx].expr() + a64s_hi[idx].expr() * p_lo.expr(),
            );
        }

        // a64s_lo[idx] < p_lo
        let a64s_lo_lt_p_lo = array_init(|idx| {
            let lt = LtGadget::construct(cb, a64s_lo[idx].expr(), p_lo.expr());
            cb.require_equal("a64s_lo[idx] < p_lo", lt.expr(), 1.expr());
            lt
        });

        // a64s_hi[idx] < p_hi
        let a64s_hi_lt_p_hi = array_init(|idx| {
            let lt = LtGadget::construct(cb, a64s_hi[idx].expr(), p_hi.expr());
            cb.require_equal("a64s_hi[idx] < p_hi", lt.expr(), 1.expr());
            lt
        });

        // merge contraints
        let shf_div64_eq0 = IsZeroGadget::construct(cb, shf_div64.expr());
        let shf_div64_eq1 = IsEqualGadget::construct(cb, shf_div64.expr(), 1.expr());
        let shf_div64_eq2 = IsEqualGadget::construct(cb, shf_div64.expr(), 2.expr());
        let shf_div64_eq3 = IsEqualGadget::construct(cb, shf_div64.expr(), 3.expr());

        cb.require_equal(
            "Constrain b64s[0]",
            b64s[0].expr(),
            (a64s_hi[0].expr() + a64s_lo[1].expr() * p_hi.expr()) * shf_div64_eq0.expr()
                + (a64s_hi[1].expr() + a64s_lo[2].expr() * p_hi.expr()) * shf_div64_eq1.expr()
                + (a64s_hi[2].expr() + a64s_lo[3].expr() * p_hi.expr()) * shf_div64_eq2.expr()
                + (a64s_hi[3].expr() + p_top.expr()) * shf_div64_eq3.expr()
                + is_neg.expr()
                    * max_u64.expr()
                    * (1.expr()
                        - shf_div64_eq0.expr()
                        - shf_div64_eq1.expr()
                        - shf_div64_eq2.expr()
                        - shf_div64_eq3.expr()),
        );
        cb.require_equal(
            "Constrain b64s[1]",
            b64s[1].expr(),
            (a64s_hi[1].expr() + a64s_lo[2].expr() * p_hi.expr()) * shf_div64_eq0.expr()
                + (a64s_hi[2].expr() + a64s_lo[3].expr() * p_hi.expr()) * shf_div64_eq1.expr()
                + (a64s_hi[3].expr() + p_top.expr()) * shf_div64_eq2.expr()
                + is_neg.expr()
                    * max_u64.expr()
                    * (1.expr()
                        - shf_div64_eq0.expr()
                        - shf_div64_eq1.expr()
                        - shf_div64_eq2.expr()),
        );
        cb.require_equal(
            "Constrain b64s[2]",
            b64s[2].expr(),
            (a64s_hi[2].expr() + a64s_lo[3].expr() * p_hi.expr()) * shf_div64_eq0.expr()
                + (a64s_hi[3].expr() + p_top.expr()) * shf_div64_eq1.expr()
                + is_neg.expr()
                    * max_u64.expr()
                    * (1.expr() - shf_div64_eq0.expr() - shf_div64_eq1.expr()),
        );
        cb.require_equal(
            "Constrain b64s[3]",
            b64s[3].expr(),
            (a64s_hi[3].expr() + p_top.expr()) * shf_div64_eq0.expr()
                + is_neg.expr() * max_u64.expr() * (1.expr() - shf_div64_eq0.expr()),
        );

        // shift constraint
        cb.require_equal(
            "shift[0] == shf_mod64 + shf_div64 * 64",
            shift.cells[0].expr(),
            shf_mod64.expr() + shf_div64.expr() * 64.expr(),
        );

        // p_lo == pow(2, shf_mod64)
        cb.add_lookup(
            "Pow2 lookup",
            Lookup::Fixed {
                tag: FixedTableTag::Pow2.expr(),
                values: [shf_mod64.expr(), p_lo.expr(), 0.expr()],
            },
        );

        // p_hi == pow(2, 64 - shf_mod64)
        cb.add_lookup(
            "Pow2 lookup",
            Lookup::Fixed {
                tag: FixedTableTag::Pow2.expr(),
                values: [64.expr() - shf_mod64.expr(), p_hi.expr(), 0.expr()],
            },
        );

        Self {
            a,
            shift,
            b,
            a64s,
            b64s,
            a64s_lo,
            a64s_hi,
            shf_div64,
            shf_mod64,
            p_lo,
            p_hi,
            p_top,
            is_neg,
            shf_lt256,
            shf_div64_eq0,
            shf_div64_eq1,
            shf_div64_eq2,
            shf_div64_eq3,
            a64s_lo_lt_p_lo,
            a64s_hi_lt_p_hi,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        a: Word,
        shift: Word,
        b: Word,
    ) -> Result<(), Error> {
        self.assign_witness(region, offset, &a, &shift)?;
        self.a.assign(region, offset, Some(a.to_le_bytes()))?;
        self.shift
            .assign(region, offset, Some(shift.to_le_bytes()))?;
        self.b.assign(region, offset, Some(b.to_le_bytes()))?;
        Ok(())
    }

    pub(crate) fn b(&self) -> &util::Word<F> {
        &self.b
    }

    fn assign_witness(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        a: &Word,
        shift: &Word,
    ) -> Result<(), Error> {
        let is_neg = is_neg(a);
        let shf0 = shift.to_le_bytes()[0] as usize;
        let shf_div64 = shf0 / 64;
        let shf_mod64 = shf0 % 64;
        let p_lo: u128 = 1 << shf_mod64;
        let p_hi: u128 = 1 << (64 - shf_mod64);
        let p_top: u128 = if is_neg {
            0xFFFFFFFFFFFFFFFF_u128 - p_hi + 1
        } else {
            0
        };
        let shf_lt256 = shift
            .to_le_bytes()
            .iter()
            .fold(0, |acc, val| acc + *val as u128)
            - shf0 as u128;
        let a64s = a.0;
        let mut a64s_lo = [0_u128; 4];
        let mut a64s_hi = [0_u128; 4];
        for idx in 0..4 {
            a64s_lo[idx] = u128::from(a64s[idx]) % p_lo;
            a64s_hi[idx] = u128::from(a64s[idx]) / p_lo;
        }
        let mut b64s = if is_neg {
            [0xFFFFFFFFFFFFFFFF_u128; 4]
        } else {
            [0_u128; 4]
        };
        b64s[3 - shf_div64 as usize] = a64s_hi[3] + p_top;
        for k in 0..3 - shf_div64 {
            b64s[k] = a64s_hi[k + shf_div64] + a64s_lo[k + shf_div64 + 1] * p_hi;
        }
        self.a64s
            .iter()
            .zip(a64s.iter())
            .map(|(cell, val)| cell.assign(region, offset, Value::known(F::from(*val))))
            .collect::<Result<Vec<_>, _>>()?;
        self.b64s
            .iter()
            .zip(b64s.iter())
            .map(|(cell, val)| cell.assign(region, offset, Value::known(F::from_u128(*val))))
            .collect::<Result<Vec<_>, _>>()?;
        self.a64s_lo
            .iter()
            .zip(a64s_lo.iter())
            .map(|(cell, val)| cell.assign(region, offset, Value::known(F::from_u128(*val))))
            .collect::<Result<Vec<_>, _>>()?;
        self.a64s_hi
            .iter()
            .zip(a64s_hi.iter())
            .map(|(cell, val)| cell.assign(region, offset, Value::known(F::from_u128(*val))))
            .collect::<Result<Vec<_>, _>>()?;
        self.shf_div64
            .assign(region, offset, Value::known(F::from(shf_div64 as u64)))?;
        self.shf_mod64
            .assign(region, offset, Value::known(F::from(shf_mod64 as u64)))?;
        self.p_lo
            .assign(region, offset, Value::known(F::from_u128(p_lo)))?;
        self.p_hi
            .assign(region, offset, Value::known(F::from_u128(p_hi)))?;
        self.p_top
            .assign(region, offset, Value::known(F::from_u128(p_top)))?;
        self.is_neg.assign(
            region,
            offset,
            127.into(),
            u64::from(a.to_le_bytes()[31]).into(),
        )?;
        self.shf_lt256
            .assign(region, offset, F::from_u128(shf_lt256))?;
        self.shf_div64_eq0
            .assign(region, offset, F::from(shf_div64 as u64))?;
        self.shf_div64_eq1
            .assign(region, offset, F::from(shf_div64 as u64), F::from(1))?;
        self.shf_div64_eq2
            .assign(region, offset, F::from(shf_div64 as u64), F::from(2))?;
        self.shf_div64_eq3
            .assign(region, offset, F::from(shf_div64 as u64), F::from(3))?;
        self.a64s_lo_lt_p_lo
            .iter()
            .zip(a64s_lo.iter())
            .map(|(lt, val)| lt.assign(region, offset, F::from_u128(*val), F::from_u128(p_lo)))
            .collect::<Result<Vec<_>, _>>()?;
        self.a64s_hi_lt_p_hi
            .iter()
            .zip(a64s_hi.iter())
            .map(|(lt, val)| lt.assign(region, offset, F::from_u128(*val), F::from_u128(p_hi)))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }
}

#[inline]
fn is_neg(x: &U256) -> bool {
    127 < x.to_le_bytes()[31]
}

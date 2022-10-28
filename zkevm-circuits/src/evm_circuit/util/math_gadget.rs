use super::CachedRegion;
use crate::{
    evm_circuit::util::{
        self, constraint_builder::ConstraintBuilder, from_bytes, pow_of_two, pow_of_two_expr,
        select, split_u256, split_u256_limb64, sum, Cell,
    },
    util::Expr,
};
use eth_types::{Field, ToLittleEndian, ToScalar, Word};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
    inverse: Cell<F>,
    is_zero: Expression<F>,
}

impl<F: Field> IsZeroGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, value: Expression<F>) -> Self {
        let inverse = cb.query_cell();

        let is_zero = 1.expr() - (value.clone() * inverse.expr());
        // when `value != 0` check `inverse = a.invert()`: value * (1 - value *
        // inverse)
        cb.add_constraint("value ⋅ (1 - value ⋅ value_inv)", value * is_zero.clone());
        // when `value == 0` check `inverse = 0`: `inverse ⋅ (1 - value *
        // inverse)`
        cb.add_constraint(
            "value_inv ⋅ (1 - value ⋅ value_inv)",
            inverse.expr() * is_zero.clone(),
        );

        Self { inverse, is_zero }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: F,
    ) -> Result<F, Error> {
        let inverse = value.invert().unwrap_or(F::zero());
        self.inverse.assign(region, offset, Value::known(inverse))?;
        Ok(if value.is_zero().into() {
            F::one()
        } else {
            F::zero()
        })
    }
}

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualGadget<F> {
    is_zero: IsZeroGadget<F>,
}

impl<F: Field> IsEqualGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let is_zero = IsZeroGadget::construct(cb, lhs - rhs);

        Self { is_zero }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<F, Error> {
        self.is_zero.assign(region, offset, lhs - rhs)
    }
}

#[derive(Clone, Debug)]
pub struct BatchedIsZeroGadget<F, const N: usize> {
    is_zero: Cell<F>,
    nonempty_witness: Cell<F>,
}

impl<F: Field, const N: usize> BatchedIsZeroGadget<F, N> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, values: [Expression<F>; N]) -> Self {
        let is_zero = cb.query_bool();
        let nonempty_witness = cb.query_cell();

        for value in values.iter() {
            cb.require_zero(
                "is_zero is 0 if there is any non-zero value",
                is_zero.expr() * value.clone(),
            );
        }

        cb.require_zero(
            "is_zero is 1 if values are all zero",
            values.iter().fold(1.expr() - is_zero.expr(), |acc, value| {
                acc * (1.expr() - value.expr() * nonempty_witness.clone().expr())
            }),
        );

        Self {
            is_zero,
            nonempty_witness,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        values: [F; N],
    ) -> Result<F, Error> {
        let is_zero =
            if let Some(inverse) = values.iter().find_map(|value| Option::from(value.invert())) {
                self.nonempty_witness
                    .assign(region, offset, Value::known(inverse))?;
                F::zero()
            } else {
                F::one()
            };
        self.is_zero.assign(region, offset, Value::known(is_zero))?;

        Ok(is_zero)
    }
}

/// Construction of 2 256-bit words addition and result, which is useful for
/// opcode ADD, SUB and balance operation
#[derive(Clone, Debug)]
pub(crate) struct AddWordsGadget<F, const N_ADDENDS: usize, const CHECK_OVREFLOW: bool> {
    addends: [util::Word<F>; N_ADDENDS],
    sum: util::Word<F>,
    carry_lo: Cell<F>,
    carry_hi: Option<Cell<F>>,
}

impl<F: Field, const N_ADDENDS: usize, const CHECK_OVREFLOW: bool>
    AddWordsGadget<F, N_ADDENDS, CHECK_OVREFLOW>
{
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        addends: [util::Word<F>; N_ADDENDS],
        sum: util::Word<F>,
    ) -> Self {
        let carry_lo = cb.query_cell();
        let carry_hi = if CHECK_OVREFLOW {
            None
        } else {
            Some(cb.query_cell())
        };

        let addends_lo = &addends
            .iter()
            .map(|addend| from_bytes::expr(&addend.cells[..16]))
            .collect::<Vec<_>>();
        let addends_hi = &addends
            .iter()
            .map(|addend| from_bytes::expr(&addend.cells[16..]))
            .collect::<Vec<_>>();
        let sum_lo = from_bytes::expr(&sum.cells[..16]);
        let sum_hi = from_bytes::expr(&sum.cells[16..]);

        cb.require_equal(
            "sum(addends_lo) == sum_lo + carry_lo ⋅ 2^128",
            sum::expr(addends_lo),
            sum_lo + carry_lo.expr() * pow_of_two_expr(128),
        );
        cb.require_equal(
            if CHECK_OVREFLOW {
                "sum(addends_hi) + carry_lo == sum_hi"
            } else {
                "sum(addends_hi) + carry_lo == sum_hi + carry_hi ⋅ 2^128"
            },
            sum::expr(addends_hi) + carry_lo.expr(),
            if CHECK_OVREFLOW {
                sum_hi
            } else {
                sum_hi + carry_hi.as_ref().unwrap().expr() * pow_of_two_expr(128)
            },
        );

        for carry in if CHECK_OVREFLOW {
            vec![&carry_lo]
        } else {
            vec![&carry_lo, carry_hi.as_ref().unwrap()]
        } {
            cb.require_in_set(
                "carry_lo in 0..N_ADDENDS",
                carry.expr(),
                (0..N_ADDENDS).map(|idx| idx.expr()).collect(),
            );
        }

        Self {
            addends,
            sum,
            carry_lo,
            carry_hi,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        addends: [Word; N_ADDENDS],
        sum: Word,
    ) -> Result<(), Error> {
        for (word, value) in self.addends.iter().zip(addends.iter()) {
            word.assign(region, offset, Some(value.to_le_bytes()))?;
        }
        self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;

        let (addends_lo, addends_hi): (Vec<_>, Vec<_>) = addends.iter().map(split_u256).unzip();
        let (sum_lo, sum_hi) = split_u256(&sum);

        let sum_of_addends_lo = addends_lo
            .into_iter()
            .fold(Word::zero(), |acc, addend_lo| acc + addend_lo);
        let sum_of_addends_hi = addends_hi
            .into_iter()
            .fold(Word::zero(), |acc, addend_hi| acc + addend_hi);

        let carry_lo = (sum_of_addends_lo - sum_lo) >> 128;
        self.carry_lo.assign(
            region,
            offset,
            Value::known(
                carry_lo
                    .to_scalar()
                    .expect("unexpected U256 -> Scalar conversion failure"),
            ),
        )?;

        if !CHECK_OVREFLOW {
            let carry_hi = (sum_of_addends_hi + carry_lo - sum_hi) >> 128;
            self.carry_hi.as_ref().unwrap().assign(
                region,
                offset,
                Value::known(
                    carry_hi
                        .to_scalar()
                        .expect("unexpected U256 -> Scalar conversion failure"),
                ),
            )?;
        }

        Ok(())
    }

    pub(crate) fn addends(&self) -> &[util::Word<F>] {
        &self.addends
    }

    pub(crate) fn sum(&self) -> &util::Word<F> {
        &self.sum
    }

    pub(crate) fn carry(&self) -> &Option<util::Cell<F>> {
        &self.carry_hi
    }
}

/// Construction of 256-bit product by 256-bit multiplicand * 64-bit multiplier,
/// which disallows overflow.
#[derive(Clone, Debug)]
pub(crate) struct MulWordByU64Gadget<F> {
    multiplicand: util::Word<F>,
    product: util::Word<F>,
    carry_lo: [util::Cell<F>; 8],
}

impl<F: Field> MulWordByU64Gadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        multiplicand: util::Word<F>,
        multiplier: Expression<F>,
    ) -> Self {
        let gadget = Self {
            multiplicand,
            product: cb.query_word(),
            carry_lo: cb.query_bytes(),
        };

        let multiplicand_lo = from_bytes::expr(&gadget.multiplicand.cells[..16]);
        let multiplicand_hi = from_bytes::expr(&gadget.multiplicand.cells[16..]);

        let product_lo = from_bytes::expr(&gadget.product.cells[..16]);
        let product_hi = from_bytes::expr(&gadget.product.cells[16..]);

        let carry_lo = from_bytes::expr(&gadget.carry_lo[..8]);

        cb.require_equal(
            "multiplicand_lo ⋅ multiplier == carry_lo ⋅ 2^128 + product_lo",
            multiplicand_lo * multiplier.expr(),
            carry_lo.clone() * pow_of_two_expr(128) + product_lo,
        );

        cb.require_equal(
            "multiplicand_hi ⋅ multiplier + carry_lo == product_hi",
            multiplicand_hi * multiplier.expr() + carry_lo,
            product_hi,
        );

        gadget
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        multiplicand: Word,
        multiplier: u64,
        product: Word,
    ) -> Result<(), Error> {
        self.multiplicand
            .assign(region, offset, Some(multiplicand.to_le_bytes()))?;
        self.product
            .assign(region, offset, Some(product.to_le_bytes()))?;

        let (multiplicand_lo, _) = split_u256(&multiplicand);
        let (product_lo, _) = split_u256(&product);

        let carry_lo = (multiplicand_lo * multiplier - product_lo) >> 128;
        for (cell, byte) in self.carry_lo.iter().zip(
            u64::try_from(carry_lo)
                .map_err(|_| Error::Synthesis)?
                .to_le_bytes()
                .iter(),
        ) {
            cell.assign(region, offset, Value::known(F::from(*byte as u64)))?;
        }

        Ok(())
    }

    pub(crate) fn product(&self) -> &util::Word<F> {
        &self.product
    }
}

/// Requires that the passed in value is within the specified range.
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER`.
#[derive(Clone, Debug)]
pub struct RangeCheckGadget<F, const N_BYTES: usize> {
    parts: [Cell<F>; N_BYTES],
}

impl<F: Field, const N_BYTES: usize> RangeCheckGadget<F, N_BYTES> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, value: Expression<F>) -> Self {
        let parts = cb.query_bytes();

        // Require that the reconstructed value from the parts equals the
        // original value
        cb.require_equal(
            "Constrain bytes recomposited to value",
            value,
            from_bytes::expr(&parts),
        );

        Self { parts }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: F,
    ) -> Result<(), Error> {
        let bytes = value.to_repr();
        for (idx, part) in self.parts.iter().enumerate() {
            part.assign(region, offset, Value::known(F::from(bytes[idx] as u64)))?;
        }
        Ok(())
    }
}

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs `< 256**N_BYTES`
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER` to prevent overflow:
/// values are stored in a single field element and two of these are added
/// together.
/// The equation that is enforced is `lhs - rhs == diff - (lt * range)`.
/// Because all values are `<= 256**N_BYTES` and `lt` is boolean, `lt` can only
/// be `1` when `lhs < rhs`.
#[derive(Clone, Debug)]
pub struct LtGadget<F, const N_BYTES: usize> {
    lt: Cell<F>, // `1` when `lhs < rhs`, `0` otherwise.
    diff: [Cell<F>; N_BYTES], /* The byte values of `diff`.
                  * `diff` equals `lhs - rhs` if `lhs >= rhs`,
                  * `lhs - rhs + range` otherwise. */
    range: F, // The range of the inputs, `256**N_BYTES`
}

impl<F: Field, const N_BYTES: usize> LtGadget<F, N_BYTES> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let lt = cb.query_bool();
        let diff = cb.query_bytes();
        let range = pow_of_two(N_BYTES * 8);

        // The equation we require to hold: `lhs - rhs == diff - (lt * range)`.
        cb.require_equal(
            "lhs - rhs == diff - (lt ⋅ range)",
            lhs - rhs,
            from_bytes::expr(&diff) - (lt.expr() * range),
        );

        Self { lt, diff, range }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.lt.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(F, Vec<u8>), Error> {
        // Set `lt`
        let lt = lhs < rhs;
        self.lt.assign(
            region,
            offset,
            Value::known(if lt { F::one() } else { F::zero() }),
        )?;

        // Set the bytes of diff
        let diff = (lhs - rhs) + (if lt { self.range } else { F::zero() });
        let diff_bytes = diff.to_repr();
        for (idx, diff) in self.diff.iter().enumerate() {
            diff.assign(
                region,
                offset,
                Value::known(F::from(diff_bytes[idx] as u64)),
            )?;
        }

        Ok((if lt { F::one() } else { F::zero() }, diff_bytes.to_vec()))
    }

    pub(crate) fn diff_bytes(&self) -> Vec<Cell<F>> {
        self.diff.to_vec()
    }
}

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs are both 256-bit word.
#[derive(Clone, Debug)]
pub struct LtWordGadget<F> {
    comparison_hi: ComparisonGadget<F, 16>,
    lt_lo: LtGadget<F, 16>,
}

impl<F: Field> LtWordGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: &util::Word<F>,
        rhs: &util::Word<F>,
    ) -> Self {
        let comparison_hi = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&lhs.cells[16..]),
            from_bytes::expr(&rhs.cells[16..]),
        );
        let lt_lo = LtGadget::construct(
            cb,
            from_bytes::expr(&lhs.cells[..16]),
            from_bytes::expr(&rhs.cells[..16]),
        );
        Self {
            comparison_hi,
            lt_lo,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        let (hi_lt, hi_eq) = self.comparison_hi.expr();
        hi_lt + hi_eq * self.lt_lo.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Word,
        rhs: Word,
    ) -> Result<(), Error> {
        let (lhs_lo, lhs_hi) = split_u256(&lhs);
        let (rhs_lo, rhs_hi) = split_u256(&rhs);
        self.comparison_hi.assign(
            region,
            offset,
            F::from_u128(lhs_hi.as_u128()),
            F::from_u128(rhs_hi.as_u128()),
        )?;
        self.lt_lo.assign(
            region,
            offset,
            F::from_u128(lhs_lo.as_u128()),
            F::from_u128(rhs_lo.as_u128()),
        )?;
        Ok(())
    }
}

/// Returns (lt, eq):
/// - `lt` is `1` when `lhs < rhs`, `0` otherwise.
/// - `eq` is `1` when `lhs == rhs`, `0` otherwise.
/// lhs and rhs `< 256**N_BYTES`
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER`.
#[derive(Clone, Debug)]
pub struct ComparisonGadget<F, const N_BYTES: usize> {
    lt: LtGadget<F, N_BYTES>,
    eq: IsZeroGadget<F>,
}

impl<F: Field, const N_BYTES: usize> ComparisonGadget<F, N_BYTES> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let lt = LtGadget::<F, N_BYTES>::construct(cb, lhs, rhs);
        let eq = IsZeroGadget::<F>::construct(cb, sum::expr(&lt.diff_bytes()));

        Self { lt, eq }
    }

    pub(crate) fn expr(&self) -> (Expression<F>, Expression<F>) {
        (self.lt.expr(), self.eq.expr())
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(F, F), Error> {
        // lt
        let (lt, diff) = self.lt.assign(region, offset, lhs, rhs)?;

        // eq
        let eq = self.eq.assign(region, offset, sum::value(&diff))?;

        Ok((lt, eq))
    }
}

/// Returns (is_a, is_b):
/// - `is_a` is `1` when `value == a`, else `0`
/// - `is_b` is `1` when `value == b`, else `0`
/// `value` is required to be either `a` or `b`.
/// The benefit of this gadget over `IsEqualGadget` is that the
/// expression returned is a single value which will make
/// future expressions depending on this result more efficient.
#[derive(Clone, Debug)]
pub struct PairSelectGadget<F> {
    is_a: Cell<F>,
    is_b: Expression<F>,
}

impl<F: Field> PairSelectGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        value: Expression<F>,
        a: Expression<F>,
        b: Expression<F>,
    ) -> Self {
        let is_a = cb.query_bool();
        let is_b = 1.expr() - is_a.expr();

        // Force `is_a` to be `0` when `value != a`
        cb.add_constraint("is_a ⋅ (value - a)", is_a.expr() * (value.clone() - a));
        // Force `1 - is_a` to be `0` when `value != b`
        cb.add_constraint("(1 - is_a) ⋅ (value - b)", is_b.clone() * (value - b));

        Self { is_a, is_b }
    }

    pub(crate) fn expr(&self) -> (Expression<F>, Expression<F>) {
        (self.is_a.expr(), self.is_b.clone())
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: F,
        a: F,
        _b: F,
    ) -> Result<(F, F), Error> {
        let is_a = if value == a { F::one() } else { F::zero() };
        self.is_a.assign(region, offset, Value::known(is_a))?;

        Ok((is_a, F::one() - is_a))
    }
}

/// Returns (quotient: numerator/denominator, remainder: numerator%denominator),
/// with `numerator` an expression and `denominator` a constant.
/// Input requirements:
/// - `quotient < 256**N_BYTES`
/// - `quotient * denominator < field size`
/// - `remainder < denominator` requires a range lookup table for `denominator`
#[derive(Clone, Debug)]
pub struct ConstantDivisionGadget<F, const N_BYTES: usize> {
    quotient: Cell<F>,
    remainder: Cell<F>,
    denominator: u64,
    quotient_range_check: RangeCheckGadget<F, N_BYTES>,
}

impl<F: Field, const N_BYTES: usize> ConstantDivisionGadget<F, N_BYTES> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        numerator: Expression<F>,
        denominator: u64,
    ) -> Self {
        let quotient = cb.query_cell();
        let remainder = cb.query_cell();

        // Require that remainder < denominator
        cb.range_lookup(remainder.expr(), denominator);

        // Require that quotient < 2**N_BYTES
        // so we can't have any overflow when doing `quotient * denominator`.
        let quotient_range_check = RangeCheckGadget::construct(cb, quotient.expr());

        // Check if the division was done correctly
        cb.require_equal(
            "numerator - remainder == quotient ⋅ denominator",
            numerator - remainder.expr(),
            quotient.expr() * denominator.expr(),
        );

        Self {
            quotient,
            remainder,
            denominator,
            quotient_range_check,
        }
    }

    pub(crate) fn quotient(&self) -> Expression<F> {
        self.quotient.expr()
    }

    pub(crate) fn remainder(&self) -> Expression<F> {
        self.remainder.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        numerator: u128,
    ) -> Result<(u128, u128), Error> {
        let denominator = self.denominator as u128;
        let quotient = numerator / denominator;
        let remainder = numerator % denominator;

        self.quotient
            .assign(region, offset, Value::known(F::from_u128(quotient)))?;
        self.remainder
            .assign(region, offset, Value::known(F::from_u128(remainder)))?;

        self.quotient_range_check
            .assign(region, offset, F::from_u128(quotient))?;

        Ok((quotient, remainder))
    }
}

/// Returns `rhs` when `lhs < rhs`, and returns `lhs` otherwise.
/// lhs and rhs `< 256**N_BYTES`
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER`.
#[derive(Clone, Debug)]
pub struct MinMaxGadget<F, const N_BYTES: usize> {
    lt: LtGadget<F, N_BYTES>,
    min: Expression<F>,
    max: Expression<F>,
}

impl<F: Field, const N_BYTES: usize> MinMaxGadget<F, N_BYTES> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let lt = LtGadget::construct(cb, lhs.clone(), rhs.clone());
        let max = select::expr(lt.expr(), rhs.clone(), lhs.clone());
        let min = select::expr(lt.expr(), lhs, rhs);

        Self { lt, min, max }
    }

    pub(crate) fn min(&self) -> Expression<F> {
        self.min.clone()
    }

    pub(crate) fn max(&self) -> Expression<F> {
        self.max.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(F, F), Error> {
        let (lt, _) = self.lt.assign(region, offset, lhs, rhs)?;
        Ok(if lt.is_zero_vartime() {
            (rhs, lhs)
        } else {
            (lhs, rhs)
        })
    }
}

// This function generates a Lagrange polynomial in the range [start, end) which
// will be evaluated to 1 when `exp == value`, otherwise 0
pub(crate) fn generate_lagrange_base_polynomial<
    F: Field,
    Exp: Expr<F>,
    R: Iterator<Item = usize>,
>(
    exp: Exp,
    val: usize,
    range: R,
) -> Expression<F> {
    let mut numerator = 1u64.expr();
    let mut denominator = F::from(1);
    for x in range {
        if x != val {
            numerator = numerator * (exp.expr() - x.expr());
            denominator *= F::from(val as u64) - F::from(x as u64);
        }
    }
    numerator * denominator.invert().unwrap()
}

/// Construct the gadget that checks a * b + c == d (modulo 2**256),
/// where a, b, c, d are 256-bit words. This can be used by opcode MUL, DIV,
/// and MOD. For opcode MUL, set c to 0. For opcode DIV and MOD, treat c as
/// residue and d as dividend.
///
/// We execute a multi-limb multiplication as follows:
/// a and b is divided into 4 64-bit limbs, denoted as a0~a3 and b0~b3
/// defined t0, t1, t2, t3
///   t0 = a0 * b0, contribute to 0 ~ 128 bit
///   t1 = a0 * b1 + a1 * b0, contribute to 64 ~ 193 bit (include the carry)
///   t2 = a0 * b2 + a2 * b0 + a1 * b1, contribute to above 128 bit
///   t3 = a0 * b3 + a3 * b0 + a2 * b1 + a1 * b2, contribute to above 192 bit
///
/// so t0 ~ t1 include all contributions to the low 256-bit of product, with
/// a maximum 68-bit radix (the part higher than 256-bit), denoted as carry_hi
/// Similarly, we define carry_lo as the radix of contributions to the low
/// 128-bit of the product.
/// We can slightly relax the constraint of carry_lo/carry_hi to 72-bit and
/// allocate 9 bytes for them each
///
/// Finally we just prove:
///   t0 + t1 * 2^64 = <low 128 bit of product> + carry_lo
///   t2 + t3 * 2^64 + carry_lo = <high 128 bit of product> + carry_hi
///
/// Last, we sum the parts that are higher than 256-bit in the multiplication
/// into overflow
///   overflow = carry_hi + a1 * b3 + a2 * b2 + a3 * b1 + a2 * b3 + a3 * b2
///              + a3 * b3
/// In the cases of DIV and MOD, we need to constrain overflow == 0 outside the
/// MulAddWordsGadget.
#[derive(Clone, Debug)]
pub(crate) struct MulAddWordsGadget<F> {
    carry_lo: [Cell<F>; 9],
    carry_hi: [Cell<F>; 9],
    overflow: Expression<F>,
}

impl<F: Field> MulAddWordsGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, words: [&util::Word<F>; 4]) -> Self {
        let (a, b, c, d) = (words[0], words[1], words[2], words[3]);
        let carry_lo = cb.query_bytes();
        let carry_hi = cb.query_bytes();
        let carry_lo_expr = from_bytes::expr(&carry_lo);
        let carry_hi_expr = from_bytes::expr(&carry_hi);

        let mut a_limbs = vec![];
        let mut b_limbs = vec![];
        for trunk in 0..4 {
            let idx = (trunk * 8) as usize;
            a_limbs.push(from_bytes::expr(&a.cells[idx..idx + 8]));
            b_limbs.push(from_bytes::expr(&b.cells[idx..idx + 8]));
        }
        let c_lo = from_bytes::expr(&c.cells[0..16]);
        let c_hi = from_bytes::expr(&c.cells[16..32]);
        let d_lo = from_bytes::expr(&d.cells[0..16]);
        let d_hi = from_bytes::expr(&d.cells[16..32]);

        let t0 = a_limbs[0].clone() * b_limbs[0].clone();
        let t1 = a_limbs[0].clone() * b_limbs[1].clone() + a_limbs[1].clone() * b_limbs[0].clone();
        let t2 = a_limbs[0].clone() * b_limbs[2].clone()
            + a_limbs[1].clone() * b_limbs[1].clone()
            + a_limbs[2].clone() * b_limbs[0].clone();
        let t3 = a_limbs[0].clone() * b_limbs[3].clone()
            + a_limbs[1].clone() * b_limbs[2].clone()
            + a_limbs[2].clone() * b_limbs[1].clone()
            + a_limbs[3].clone() * b_limbs[0].clone();
        let overflow = carry_hi_expr.clone()
            + a_limbs[1].clone() * b_limbs[3].clone()
            + a_limbs[2].clone() * b_limbs[2].clone()
            + a_limbs[3].clone() * b_limbs[2].clone()
            + a_limbs[2].clone() * b_limbs[3].clone()
            + a_limbs[3].clone() * b_limbs[2].clone()
            + a_limbs[3].clone() * b_limbs[3].clone();

        cb.require_equal(
            "(a * b)_lo + c_lo == d_lo + carry_lo ⋅ 2^128",
            t0.expr() + t1.expr() * pow_of_two_expr(64) + c_lo,
            d_lo + carry_lo_expr.clone() * pow_of_two_expr(128),
        );
        cb.require_equal(
            "(a * b)_hi + c_hi + carry_lo == d_hi + carry_hi ⋅ 2^128",
            t2.expr() + t3.expr() * pow_of_two_expr(64) + c_hi + carry_lo_expr,
            d_hi + carry_hi_expr * pow_of_two_expr(128),
        );

        Self {
            carry_lo,
            carry_hi,
            overflow,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        words: [Word; 4],
    ) -> Result<(), Error> {
        let (a, b, c, d) = (words[0], words[1], words[2], words[3]);

        let a_limbs = split_u256_limb64(&a);
        let b_limbs = split_u256_limb64(&b);
        let (c_lo, c_hi) = split_u256(&c);
        let (d_lo, d_hi) = split_u256(&d);

        let t0 = a_limbs[0] * b_limbs[0];
        let t1 = a_limbs[0] * b_limbs[1] + a_limbs[1] * b_limbs[0];
        let t2 = a_limbs[0] * b_limbs[2] + a_limbs[1] * b_limbs[1] + a_limbs[2] * b_limbs[0];
        let t3 = a_limbs[0] * b_limbs[3]
            + a_limbs[1] * b_limbs[2]
            + a_limbs[2] * b_limbs[1]
            + a_limbs[3] * b_limbs[0];

        let carry_lo = (t0 + (t1 << 64) + c_lo - d_lo) >> 128;
        let carry_hi = (t2 + (t3 << 64) + c_hi + carry_lo - d_hi) >> 128;

        self.carry_lo
            .iter()
            .zip(carry_lo.to_le_bytes().iter())
            .map(|(cell, byte)| cell.assign(region, offset, Value::known(F::from(*byte as u64))))
            .collect::<Result<Vec<_>, _>>()?;

        self.carry_hi
            .iter()
            .zip(carry_hi.to_le_bytes().iter())
            .map(|(cell, byte)| cell.assign(region, offset, Value::known(F::from(*byte as u64))))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(())
    }

    pub(crate) fn overflow(&self) -> Expression<F> {
        self.overflow.clone()
    }
}

#[derive(Clone, Debug)]
/// CmpWordsGadget compares two words, exposing `eq`  and `lt`
pub(crate) struct CmpWordsGadget<F> {
    comparison_lo: ComparisonGadget<F, 16>,
    comparison_hi: ComparisonGadget<F, 16>,
    pub eq: Expression<F>,
    pub lt: Expression<F>,
}

impl<F: Field> CmpWordsGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        a: &util::Word<F>,
        b: &util::Word<F>,
    ) -> Self {
        // `a[0..16] <= b[0..16]`
        let comparison_lo = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&a.cells[0..16]),
            from_bytes::expr(&b.cells[0..16]),
        );

        let (lt_lo, eq_lo) = comparison_lo.expr();

        // `a[16..32] <= b[16..32]`
        let comparison_hi = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&a.cells[16..32]),
            from_bytes::expr(&b.cells[16..32]),
        );
        let (lt_hi, eq_hi) = comparison_hi.expr();

        // `a < b` when:
        // - `a[16..32] < b[16..32]` OR
        // - `a[16..32] == b[16..32]` AND `a[0..16] < b[0..16]`
        let lt = select::expr(lt_hi, 1.expr(), eq_hi.clone() * lt_lo);

        // `a == b` when both parts are equal
        let eq = eq_hi * eq_lo;

        Self {
            comparison_lo,
            comparison_hi,
            lt,
            eq,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        a: Word,
        b: Word,
    ) -> Result<(), Error> {
        // `a[0..1] <= b[0..16]`
        self.comparison_lo.assign(
            region,
            offset,
            from_bytes::value(&a.to_le_bytes()[0..16]),
            from_bytes::value(&b.to_le_bytes()[0..16]),
        )?;

        // `a[16..32] <= b[16..32]`
        self.comparison_hi.assign(
            region,
            offset,
            from_bytes::value(&a.to_le_bytes()[16..32]),
            from_bytes::value(&b.to_le_bytes()[16..32]),
        )?;

        Ok(())
    }
}

/// Construct the gadget that checks a * b + c == d * 2**256 + e
/// where a, b, c, d, e are 256-bit words.
///
/// We execute a multi-limb multiplication as follows:
/// a and b is divided into 4 64-bit limbs, denoted as a0~a3 and b0~b3
/// defined t0, t1, t2, t3, t4, t5, t6:
///   t0 = a0 * b0,
///   t1 = a0 * b1 + a1 * b0,
///   t2 = a0 * b2 + a2 * b0 + a1 * b1,
///   t3 = a0 * b3 + a3 * b0 + a2 * b1 + a1 * b2,
///   t4 = a1 * b3 + a2 * b2 + a3 * b1,
///   t5 = a2 * b3 + a3 * b2,
///   t6 = a3 * b3,
///
/// The addend c as well as the the words that form the result d, e are divided
/// in 2 128-bit limbs each: c_lo, c_hi, d_lo, d_hi, e_lo, e_hi.
///
/// so t0 ~ t1 include all contributions to the low 128-bit of product (e_lo),
/// with a maximum 65-bit carry (the part higher than 128-bit), denoted as
/// carry_0. Similarly, we define carry_1 as the carry of contributions to the
/// next 128-bit of the product (e_hi) with a maximum val of 66 bits. Finally,
/// we define carry_2 as the carry for the next 128 bits of the product (d_lo).
///
/// We can slightly relax the constraint of carry_0/carry_1, carry_2 to 72-bit
/// and allocate 9 bytes for them each
///
/// Finally we just prove:
///   t0 + t1 * 2^64 + c_lo = e_lo + carry_0 * 2^128
///   t2 + t3 * 2^64 + c_hi + carry_0 = e_hi + carry_1 * 2^128
///   t4 + t5 * 2^64 + carry_1 = d_lo + carry_2 * 2^128
///   t6 + carry_2 = d_hi
#[derive(Clone, Debug)]
pub(crate) struct MulAddWords512Gadget<F> {
    carry_0: [Cell<F>; 9],
    carry_1: [Cell<F>; 9],
    carry_2: [Cell<F>; 9],
}

impl<F: Field> MulAddWords512Gadget<F> {
    /// words argument is: a, b, d, e
    /// Addend is the optional c.
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        words: [&util::Word<F>; 4],
        addend: Option<&util::Word<F>>,
    ) -> Self {
        let carry_0 = cb.query_bytes();
        let carry_1 = cb.query_bytes();
        let carry_2 = cb.query_bytes();
        let carry_0_expr = from_bytes::expr(&carry_0);
        let carry_1_expr = from_bytes::expr(&carry_1);
        let carry_2_expr = from_bytes::expr(&carry_2);

        // Split input words in limbs
        let mut a_limbs = vec![];
        let mut b_limbs = vec![];
        for trunk in 0..4 {
            let idx = (trunk * 8) as usize;
            a_limbs.push(from_bytes::expr(&words[0].cells[idx..idx + 8]));
            b_limbs.push(from_bytes::expr(&words[1].cells[idx..idx + 8]));
        }

        let d_lo = from_bytes::expr(&words[2].cells[0..16]);
        let d_hi = from_bytes::expr(&words[2].cells[16..32]);
        let e_lo = from_bytes::expr(&words[3].cells[0..16]);
        let e_hi = from_bytes::expr(&words[3].cells[16..32]);

        // Limb multiplication
        let t0 = a_limbs[0].clone() * b_limbs[0].clone();
        let t1 = a_limbs[0].clone() * b_limbs[1].clone() + a_limbs[1].clone() * b_limbs[0].clone();
        let t2 = a_limbs[0].clone() * b_limbs[2].clone()
            + a_limbs[1].clone() * b_limbs[1].clone()
            + a_limbs[2].clone() * b_limbs[0].clone();
        let t3 = a_limbs[0].clone() * b_limbs[3].clone()
            + a_limbs[1].clone() * b_limbs[2].clone()
            + a_limbs[2].clone() * b_limbs[1].clone()
            + a_limbs[3].clone() * b_limbs[0].clone();
        let t4 = a_limbs[1].clone() * b_limbs[3].clone()
            + a_limbs[2].clone() * b_limbs[2].clone()
            + a_limbs[3].clone() * b_limbs[1].clone();
        let t5 = a_limbs[2].clone() * b_limbs[3].clone() + a_limbs[3].clone() * b_limbs[2].clone();
        let t6 = a_limbs[3].clone() * b_limbs[3].clone();

        if let Some(c) = addend {
            let c_lo = from_bytes::expr(&c.cells[0..16]);
            let c_hi = from_bytes::expr(&c.cells[16..32]);
            cb.require_equal(
                "(t0 + t1 ⋅ 2^64) + c_lo == e_lo + carry_0 ⋅ 2^128",
                t0.expr() + t1.expr() * pow_of_two_expr(64) + c_lo,
                e_lo + carry_0_expr.clone() * pow_of_two_expr(128),
            );

            cb.require_equal(
                "(t2 + t3 ⋅ 2^64) + c_hi + carry_0 == e_hi + carry_1 ⋅ 2^128",
                t2.expr() + t3.expr() * pow_of_two_expr(64) + c_hi + carry_0_expr,
                e_hi + carry_1_expr.clone() * pow_of_two_expr(128),
            );
        } else {
            cb.require_equal(
                "(t0 + t1 ⋅ 2^64) == e_lo + carry_0 ⋅ 2^128",
                t0.expr() + t1.expr() * pow_of_two_expr(64),
                e_lo + carry_0_expr.clone() * pow_of_two_expr(128),
            );

            cb.require_equal(
                "(t2 + t3 ⋅ 2^64) + carry_0 == e_hi + carry_1 ⋅ 2^128",
                t2.expr() + t3.expr() * pow_of_two_expr(64) + carry_0_expr,
                e_hi + carry_1_expr.clone() * pow_of_two_expr(128),
            );
        }

        cb.require_equal(
            "(t4 + t5 ⋅ 2^64) + carry_1 == d_lo + carry_2 ⋅ 2^128",
            t4.expr() + t5.expr() * pow_of_two_expr(64) + carry_1_expr,
            d_lo + carry_2_expr.clone() * pow_of_two_expr(128),
        );

        cb.require_equal("t6 + carry_2 == d_hi", t6.expr() + carry_2_expr, d_hi);

        Self {
            carry_0,
            carry_1,
            carry_2,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        words: [Word; 4],
        addend: Option<Word>,
    ) -> Result<(), Error> {
        let (a, b, d, e) = (words[0], words[1], words[2], words[3]);

        let a_limbs = split_u256_limb64(&a);
        let b_limbs = split_u256_limb64(&b);
        let (d_lo, _d_hi) = split_u256(&d);
        let (e_lo, e_hi) = split_u256(&e);

        let t0 = a_limbs[0] * b_limbs[0];
        let t1 = a_limbs[0] * b_limbs[1] + a_limbs[1] * b_limbs[0];
        let t2 = a_limbs[0] * b_limbs[2] + a_limbs[1] * b_limbs[1] + a_limbs[2] * b_limbs[0];
        let t3 = a_limbs[0] * b_limbs[3]
            + a_limbs[1] * b_limbs[2]
            + a_limbs[2] * b_limbs[1]
            + a_limbs[3] * b_limbs[0];

        let t4 = a_limbs[1] * b_limbs[3] + a_limbs[2] * b_limbs[2] + a_limbs[3] * b_limbs[1];
        let t5 = a_limbs[2] * b_limbs[3] + a_limbs[3] * b_limbs[2];

        let (carry_0, carry_1) = if let Some(c) = addend {
            let (c_lo, c_hi) = split_u256(&c);
            let carry_0 = ((t0 + (t1 << 64) + c_lo).saturating_sub(e_lo)) >> 128;
            let carry_1 = ((t2 + (t3 << 64) + c_hi + carry_0).saturating_sub(e_hi)) >> 128;
            (carry_0, carry_1)
        } else {
            let carry_0 = ((t0 + (t1 << 64)).saturating_sub(e_lo)) >> 128;
            let carry_1 = ((t2 + (t3 << 64) + carry_0).saturating_sub(e_hi)) >> 128;
            (carry_0, carry_1)
        };
        let carry_2 = ((t4 + (t5 << 64) + carry_1).saturating_sub(d_lo)) >> 128;

        self.carry_0
            .iter()
            .zip(carry_0.to_le_bytes().iter())
            .map(|(cell, byte)| cell.assign(region, offset, Value::known(F::from(*byte as u64))))
            .collect::<Result<Vec<_>, _>>()?;

        self.carry_1
            .iter()
            .zip(carry_1.to_le_bytes().iter())
            .map(|(cell, byte)| cell.assign(region, offset, Value::known(F::from(*byte as u64))))
            .collect::<Result<Vec<_>, _>>()?;

        self.carry_2
            .iter()
            .zip(carry_2.to_le_bytes().iter())
            .map(|(cell, byte)| cell.assign(region, offset, Value::known(F::from(*byte as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }
}

/// Constraints the words a, n, r such that:
/// a mod n = r, if n!=0
/// r = 0,       if n==0
///
/// We use the auxiliary a_or_zero word, whose value is constrained to be: a if
/// n!=0, 0 if n==0. This allows to use the equation k * n + r = a_or_zero to
/// verify the modulus, which holds with r=0 in the case of n=0. Unlike the
/// usual k * n + r = a, which forces r = a when n=0, this equation assures that
/// r<n or r=n=0.
#[derive(Clone, Debug)]
pub(crate) struct ModGadget<F> {
    k: util::Word<F>,
    a_or_zero: util::Word<F>,
    mul: MulAddWordsGadget<F>,
    n_is_zero: IsZeroGadget<F>,
    a_or_is_zero: IsZeroGadget<F>,
    eq: IsEqualGadget<F>,
    lt: LtWordGadget<F>,
}
impl<F: Field> ModGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, words: [&util::Word<F>; 3]) -> Self {
        let (a, n, r) = (words[0], words[1], words[2]);
        let k = cb.query_word();
        let a_or_zero = cb.query_word();
        let n_is_zero = IsZeroGadget::construct(cb, sum::expr(&n.cells));
        let a_or_is_zero = IsZeroGadget::construct(cb, sum::expr(&a_or_zero.cells));
        let mul = MulAddWordsGadget::construct(cb, [&k, n, r, &a_or_zero]);
        let eq = IsEqualGadget::construct(cb, a.expr(), a_or_zero.expr());
        let lt = LtWordGadget::construct(cb, r, n);
        // Constraint the aux variable a_or_zero to be =a or =0 if n==0:
        // (a == a_zero) ^ (n == 0 & a_or_zero == 0)
        cb.add_constraint(
            " (1 - (a == a_or_zero)) * ( 1 - (n == 0) * (a_or_zero == 0)",
            (1.expr() - eq.expr()) * (1.expr() - n_is_zero.expr() * a_or_is_zero.expr()),
        );

        // Constrain the result r to be valid: (r<n) ^ n==0
        cb.add_constraint(
            " (1 - (r<n) - (n==0) ",
            1.expr() - lt.expr() - n_is_zero.expr(),
        );

        Self {
            k,
            a_or_zero,
            mul,
            n_is_zero,
            a_or_is_zero,
            eq,
            lt,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        a: Word,
        n: Word,
        r: Word,
        randomness: F,
    ) -> Result<(), Error> {
        let k = if n.is_zero() { Word::zero() } else { a / n };
        let a_or_zero = if n.is_zero() { Word::zero() } else { a };

        self.k.assign(region, offset, Some(k.to_le_bytes()))?;
        self.a_or_zero
            .assign(region, offset, Some(a_or_zero.to_le_bytes()))?;
        let n_sum = (0..32).fold(0, |acc, idx| acc + n.byte(idx) as u64);
        let a_or_zero_sum = (0..32).fold(0, |acc, idx| acc + a_or_zero.byte(idx) as u64);
        self.n_is_zero.assign(region, offset, F::from(n_sum))?;
        self.a_or_is_zero
            .assign(region, offset, F::from(a_or_zero_sum))?;
        self.mul.assign(region, offset, [k, n, r, a_or_zero])?;
        self.lt.assign(region, offset, r, n)?;
        self.eq.assign(
            region,
            offset,
            util::Word::random_linear_combine(a.to_le_bytes(), randomness),
            util::Word::random_linear_combine(a_or_zero.to_le_bytes(), randomness),
        )?;

        Ok(())
    }
}

/// Construction of 256-bit word original and absolute values, which is useful
/// for opcodes operated on signed values.
#[derive(Clone, Debug)]
pub(crate) struct AbsWordGadget<F> {
    x: util::Word<F>,
    x_abs: util::Word<F>,
    sum: util::Word<F>,
    is_neg: LtGadget<F, 1>,
    add_words: AddWordsGadget<F, 2, false>,
}

impl<F: Field> AbsWordGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>) -> Self {
        let x = cb.query_word();
        let x_abs = cb.query_word();
        let sum = cb.query_word();
        let x_lo = from_bytes::expr(&x.cells[0..16]);
        let x_hi = from_bytes::expr(&x.cells[16..32]);
        let x_abs_lo = from_bytes::expr(&x_abs.cells[0..16]);
        let x_abs_hi = from_bytes::expr(&x_abs.cells[16..32]);
        let is_neg = LtGadget::construct(cb, 127.expr(), x.cells[31].expr());

        cb.add_constraint(
            "x_abs_lo == x_lo when x >= 0",
            (1.expr() - is_neg.expr()) * (x_abs_lo.expr() - x_lo.expr()),
        );
        cb.add_constraint(
            "x_abs_hi == x_hi when x >= 0",
            (1.expr() - is_neg.expr()) * (x_abs_hi.expr() - x_hi.expr()),
        );

        // When `is_neg`, constrain `sum == 0` and `carry == 1`. Since the final
        // result is `1 << 256`.
        let add_words = AddWordsGadget::construct(cb, [x.clone(), x_abs.clone()], sum.clone());
        cb.add_constraint(
            "sum == 0 when x < 0",
            is_neg.expr() * add_words.sum().expr(),
        );
        cb.add_constraint(
            "carry_hi == 1 when x < 0",
            is_neg.expr() * (1.expr() - add_words.carry().as_ref().unwrap().expr()),
        );

        Self {
            x,
            x_abs,
            sum,
            is_neg,
            add_words,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        x: Word,
        x_abs: Word,
    ) -> Result<(), Error> {
        self.x.assign(region, offset, Some(x.to_le_bytes()))?;
        self.x_abs
            .assign(region, offset, Some(x_abs.to_le_bytes()))?;
        self.is_neg.assign(
            region,
            offset,
            127.into(),
            u64::from(x.to_le_bytes()[31]).into(),
        )?;
        let sum = x.overflowing_add(x_abs).0;
        self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;
        self.add_words.assign(region, offset, [x, x_abs], sum)
    }

    pub(crate) fn x(&self) -> &util::Word<F> {
        &self.x
    }

    pub(crate) fn x_abs(&self) -> &util::Word<F> {
        &self.x_abs
    }

    pub(crate) fn is_neg(&self) -> &LtGadget<F, 1> {
        &self.is_neg
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use std::marker::PhantomData;
    use strum::IntoEnumIterator;

    use super::util::StoredExpression;
    use super::*;
    use crate::evm_circuit::param::{MAX_STEP_HEIGHT, STEP_WIDTH};
    use crate::evm_circuit::step::Step;
    use crate::evm_circuit::table::{FixedTableTag, Table};
    use crate::evm_circuit::util::{rlc, CellType};
    use crate::evm_circuit::{Advice, Column, Fixed};
    use crate::table::LookupTable;
    use crate::{evm_circuit::step::ExecutionState, util::power_of_randomness_from_instance};
    use eth_types::Word;
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::{ConstraintSystem, Selector};
    use halo2_proofs::plonk::{Error, Expression};
    use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};

    trait MathGadgetContainer<F: Field>: Clone {
        const NAME: &'static str;

        fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self
        where
            Self: Sized;

        fn assign_gadget_container(
            &self,
            input_words: &[Word],
            region: &mut CachedRegion<'_, '_, F>,
        ) -> Result<(), Error>;
    }

    #[derive(Debug, Clone)]
    struct UnitTestMathGadgetBaseCircuitConfig<F: Field, G>
    where
        G: MathGadgetContainer<F>,
    {
        q_usable: Selector,
        fixed_table: [Column<Fixed>; 4],
        advices: [Column<Advice>; STEP_WIDTH],
        step: Step<F>,
        stored_expressions: Vec<StoredExpression<F>>,
        math_gadget_container: G,
        _marker: PhantomData<F>,
        power_of_randomness: [Expression<F>; 31],
    }

    struct UnitTestMathGadgetBaseCircuit<F, G> {
        size: usize,
        input_words: Vec<Word>,
        randomness: F,
        _marker: PhantomData<G>,
    }

    impl<F: Field, G> UnitTestMathGadgetBaseCircuit<F, G> {
        fn new(size: usize, input_words: Vec<Word>, randomness: F) -> Self {
            UnitTestMathGadgetBaseCircuit {
                size,
                input_words,
                randomness,
                _marker: PhantomData,
            }
        }
    }

    impl<F: Field, G: MathGadgetContainer<F>> Circuit<F> for UnitTestMathGadgetBaseCircuit<F, G> {
        type Config = UnitTestMathGadgetBaseCircuitConfig<F, G>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            UnitTestMathGadgetBaseCircuit {
                size: 0,
                input_words: vec![],
                randomness: F::from(123456u64),
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let q_usable = meta.selector();
            let fixed_table = [(); 4].map(|_| meta.fixed_column());
            let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());
            let step_curr = Step::new(meta, advices, 0);
            let step_next = Step::new(meta, advices, MAX_STEP_HEIGHT);
            let power_of_randomness = power_of_randomness_from_instance(meta);

            let mut cb = ConstraintBuilder::new(
                step_curr.clone(),
                step_next,
                &power_of_randomness,
                ExecutionState::STOP,
            );
            let math_gadget_container = G::configure_gadget_container(&mut cb);
            let (constraints, _, stored_expressions, _) = cb.build();

            if !constraints.is_empty() {
                meta.create_gate(G::NAME, |meta| {
                    let q_usable = meta.query_selector(q_usable);
                    constraints
                        .into_iter()
                        .map(move |(name, constraint)| (name, q_usable.clone() * constraint))
                });
            }

            let cell_manager = step_curr.cell_manager.clone();
            for column in cell_manager.columns().iter() {
                if let CellType::Lookup(table) = column.cell_type {
                    match table {
                        Table::Fixed => {
                            let name = format!("{:?}", table);
                            meta.lookup_any(Box::leak(name.into_boxed_str()), |meta| {
                                let table_expressions = fixed_table.table_exprs(meta);
                                vec![(
                                    column.expr(),
                                    rlc::expr(&table_expressions, &power_of_randomness),
                                )]
                            });
                        }
                        _ => (),
                    }
                }
            }

            UnitTestMathGadgetBaseCircuitConfig::<F, G> {
                q_usable,
                fixed_table,
                advices,
                step: step_curr,
                stored_expressions,
                math_gadget_container,
                _marker: PhantomData,
                power_of_randomness,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "assign test container",
                |mut region| {
                    let offset = 0;
                    config.q_usable.enable(&mut region, offset)?;
                    let power_of_randomness = [(); 31].map(|_| self.randomness);
                    let cached_region = &mut CachedRegion::<'_, '_, F>::new(
                        &mut region,
                        power_of_randomness,
                        STEP_WIDTH,
                        MAX_STEP_HEIGHT * 3,
                        config.advices[0].index(), // TODO
                        offset,
                    );
                    config.step.state.execution_state.assign(
                        cached_region,
                        offset,
                        ExecutionState::STOP as usize,
                    )?;
                    config
                        .math_gadget_container
                        .assign_gadget_container(&self.input_words, cached_region)?;
                    for stored_expr in &config.stored_expressions {
                        stored_expr.assign(cached_region, offset)?;
                    }
                    Ok(())
                },
            )?;

            // assign fixed range tables only as they are the only tables referred by a
            // specfic math gadget -- ConstantDivisionGadget.
            layouter.assign_region(
                || "fixed table",
                |mut region| {
                    for (offset, row) in std::iter::once([F::zero(); 4])
                        .chain(
                            FixedTableTag::iter()
                                .filter(|t| {
                                    matches!(
                                        t,
                                        FixedTableTag::Range5
                                            | FixedTableTag::Range16
                                            | FixedTableTag::Range32
                                            | FixedTableTag::Range64
                                            | FixedTableTag::Range256
                                            | FixedTableTag::Range512
                                            | FixedTableTag::Range1024
                                    )
                                })
                                .flat_map(|tag| tag.build()),
                        )
                        .enumerate()
                    {
                        for (column, value) in config.fixed_table.iter().zip_eq(row) {
                            region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
                        }
                    }

                    Ok(())
                },
            )
        }
    }

    fn test_math_gadget_container<F: Field, G: MathGadgetContainer<F>>(
        input_words: Vec<Word>,
        expected_success: bool,
    ) {
        const K: usize = 12;
        let randomness = F::from(123456u64);
        let power_of_randomness: Vec<Vec<F>> = (1..32)
            .map(|exp| vec![randomness.pow(&[exp, 0, 0, 0]); (1 << K) - 64])
            .collect();
        let circuit = UnitTestMathGadgetBaseCircuit::<F, G>::new(K, input_words, randomness);

        let prover = MockProver::<F>::run(K as u32, &circuit, power_of_randomness).unwrap();
        if expected_success {
            assert_eq!(prover.verify(), Ok(()));
        } else {
            assert_ne!(prover.verify(), Ok(()));
        }
    }

    #[test]
    fn test_iszero() {
        #[derive(Clone)]
        /// n != 0
        struct IsZeroGadgetTestContainer<F> {
            z_gadget: IsZeroGadget<F>,
            n: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for IsZeroGadgetTestContainer<F> {
            const NAME: &'static str = "IsZeroGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let n = cb.query_word();
                let z_gadget = IsZeroGadget::<F>::construct(cb, sum::expr(&n.cells));
                cb.require_equal("Input must not be 0", z_gadget.expr(), 0.expr());
                IsZeroGadgetTestContainer { z_gadget, n }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let n = input_words[0];
                let offset = 0;

                self.n.assign(region, offset, Some(n.to_le_bytes()))?;
                self.z_gadget
                    .assign(region, 0, sum::value(&n.to_le_bytes()))?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(0)], false);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(1)], true);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(
            vec![Word::from(1000)],
            true,
        );

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::MAX], true);
    }

    #[test]
    fn test_batched_iszero() {
        const N: usize = 32;
        #[derive(Clone)]
        /// all(n.cells) == 0
        struct IsZeroGadgetTestContainer<F> {
            z_gadget: BatchedIsZeroGadget<F, N>,
            n: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for IsZeroGadgetTestContainer<F> {
            const NAME: &'static str = "BatchedIsZeroGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let n = cb.query_word();
                let z_gadget = BatchedIsZeroGadget::<F, N>::construct(
                    cb,
                    n.cells
                        .iter()
                        .map(|cell| cell.expr())
                        .collect::<Vec<Expression<F>>>()
                        .try_into()
                        .unwrap(),
                );
                cb.require_equal("Input must be all 0", z_gadget.expr(), 1.expr());
                IsZeroGadgetTestContainer { z_gadget, n }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let n = input_words[0];
                let offset = 0;

                self.n.assign(region, offset, Some(n.to_le_bytes()))?;
                self.z_gadget.assign(
                    region,
                    0,
                    n.to_le_bytes().map(|byte| F::from(byte as u64)),
                )?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(0)], true);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(1)], false);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(
            vec![Word::from(1u64 << 32)],
            false,
        );

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::MAX], false);
    }

    #[test]
    fn test_isequal() {
        #[derive(Clone)]
        /// a == b
        struct IsEqualGadgetTestContainer<F> {
            eq_gadget: IsEqualGadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for IsEqualGadgetTestContainer<F> {
            const NAME: &'static str = "IsEqualGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_rlc();
                let b = cb.query_rlc();
                let eq_gadget =
                    IsEqualGadget::<F>::construct(cb, sum::expr(&a.cells), sum::expr(&b.cells));
                cb.require_equal("Inputs must equal", eq_gadget.expr(), 1.expr());
                IsEqualGadgetTestContainer {
                    eq_gadget: eq_gadget,
                    a,
                    b,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.eq_gadget.assign(
                    region,
                    0,
                    sum::value(&a.to_le_bytes()),
                    sum::value(&b.to_le_bytes()),
                )?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(1000), Word::from(1000)],
            true,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1)],
            false,
        );
    }

    #[test]
    fn test_addwords() {
        #[derive(Clone)]
        /// sum = a + b
        struct AddWordsTestContainer<F> {
            addwords_gadget: AddWordsGadget<F, 2, true>,
            a: util::Word<F>,
            b: util::Word<F>,
            sum: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for AddWordsTestContainer<F> {
            const NAME: &'static str = "AddWordsGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let sum = cb.query_word();
                let addwords_gadget = AddWordsGadget::<F, 2, true>::construct(
                    cb,
                    [a.clone(), b.clone()],
                    sum.clone(),
                );
                AddWordsTestContainer {
                    addwords_gadget,
                    a,
                    b,
                    sum,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let sum = input_words[2];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;
                self.addwords_gadget.assign(region, 0, [a, b], sum)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(2)],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(1000), Word::from(1000), Word::from(2000)],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::MAX - 1, Word::from(1), Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::MAX, Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1), Word::from(0)],
            false,
        );
    }

    #[test]
    fn test_mul_word_u64() {
        #[derive(Clone)]
        /// product = a*(b as u64)
        struct MulWordByU64TestContainer<F> {
            mulwords_u64_gadget: MulWordByU64Gadget<F>,
            a: util::Word<F>,
            b: Cell<F>,
            product: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for MulWordByU64TestContainer<F> {
            const NAME: &'static str = "MulWordByU64Gadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_cell();
                let product = cb.query_word();
                let mulwords_u64_gadget =
                    MulWordByU64Gadget::<F>::construct(cb, a.clone(), b.expr());
                MulWordByU64TestContainer {
                    mulwords_u64_gadget,
                    a,
                    b,
                    product,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = u64::from_le_bytes(input_words[1].to_le_bytes()[..8].try_into().unwrap());
                let product = input_words[2];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Value::known(F::from(b)))?;
                self.product
                    .assign(region, offset, Some(product.to_le_bytes()))?;
                self.mulwords_u64_gadget.assign(region, 0, a, b, product)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, MulWordByU64TestContainer<Fr>>(
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, MulWordByU64TestContainer<Fr>>(
            vec![Word::MAX, Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, MulWordByU64TestContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, MulWordByU64TestContainer<Fr>>(
            vec![Word::MAX, Word::from(1), Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, MulWordByU64TestContainer<Fr>>(
            vec![Word::MAX, Word::from(1), Word::from(1)],
            false,
        );
    }

    #[test]
    fn test_range_check() {
        #[derive(Clone)]
        /// a in [0..1<<32]
        struct RangeCheckTestContainer<F> {
            range_check_gadget: RangeCheckGadget<F, 4>,
            a: Cell<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for RangeCheckTestContainer<F> {
            const NAME: &'static str = "RangeCheckGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let range_check_gadget = RangeCheckGadget::<F, 4>::construct(cb, a.expr());
                RangeCheckTestContainer {
                    range_check_gadget,
                    a,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0].to_scalar().unwrap();
                let offset = 0;

                self.a.assign(region, offset, Value::known(F::from(a)))?;
                self.range_check_gadget.assign(region, 0, a)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, RangeCheckTestContainer<Fr>>(vec![Word::from(0)], true);

        test_math_gadget_container::<Fr, RangeCheckTestContainer<Fr>>(vec![Word::from(1)], true);

        test_math_gadget_container::<Fr, RangeCheckTestContainer<Fr>>(
            vec![Word::from((1u64 << 32) - 1)],
            true,
        );

        test_math_gadget_container::<Fr, RangeCheckTestContainer<Fr>>(
            vec![Word::from(1u64 << 32)],
            false,
        );
    }

    #[test]
    fn test_lt() {
        const N: usize = 3;
        #[derive(Clone)]
        /// a < b
        struct LtGadgetTestContainer<F> {
            lt_gadget: LtGadget<F, N>,
            a: Cell<F>,
            b: Cell<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for LtGadgetTestContainer<F> {
            const NAME: &'static str = "LtGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let b = cb.query_cell();
                let lt_gadget = LtGadget::<F, N>::construct(cb, a.expr(), b.expr());
                cb.require_equal("a < b", lt_gadget.expr(), 1.expr());
                LtGadgetTestContainer { lt_gadget, a, b }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = F::from(u64::from_le_bytes(
                    input_words[0].to_le_bytes()[..8].try_into().unwrap(),
                ));
                let b = F::from(u64::from_le_bytes(
                    input_words[1].to_le_bytes()[..8].try_into().unwrap(),
                ));
                let offset = 0;

                self.a.assign(region, offset, Value::known(a))?;
                self.b.assign(region, offset, Value::known(b))?;
                self.lt_gadget.assign(region, offset, a, b)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, LtGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, LtGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from((1u64 << N * 8) - 1)],
            true,
        );

        test_math_gadget_container::<Fr, LtGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(0)],
            false,
        );

        // out of range check
        test_math_gadget_container::<Fr, LtGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(2 << N * 8)],
            false,
        );
    }

    #[test]
    fn test_ltword() {
        #[derive(Clone)]
        /// a < b
        struct LtWordTestContainer<F> {
            ltword_gadget: LtWordGadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for LtWordTestContainer<F> {
            const NAME: &'static str = "LtWordGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let ltword_gadget = LtWordGadget::<F>::construct(cb, &a, &b);
                cb.require_equal("a < b", ltword_gadget.expr(), 1.expr());
                LtWordTestContainer {
                    ltword_gadget,
                    a,
                    b,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.ltword_gadget.assign(region, 0, a, b)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::from(1), Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::MAX, Word::MAX],
            false,
        );
    }

    #[test]
    fn test_comparison() {
        const N: usize = 4;
        #[derive(Clone)]
        /// a < b
        struct ComparisonTestContainer<F, const CHECK_EQ: bool> {
            cmp_gadget: ComparisonGadget<F, N>,
            a: Cell<F>,
            b: Cell<F>,
        }

        impl<F: Field, const CHECK_EQ: bool> MathGadgetContainer<F>
            for ComparisonTestContainer<F, CHECK_EQ>
        {
            const NAME: &'static str = "ComparisonGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let b = cb.query_cell();
                let cmp_gadget = ComparisonGadget::<F, N>::construct(cb, a.expr(), b.expr());
                cb.require_equal(
                    "(a < b) * (a == b) == 0",
                    cmp_gadget.expr().0 * cmp_gadget.expr().1,
                    0.expr(),
                );

                if CHECK_EQ {
                    cb.require_equal("a == b", cmp_gadget.expr().1, 1.expr());
                } else {
                    cb.require_equal("a < b", cmp_gadget.expr().0, 1.expr());
                }

                ComparisonTestContainer { cmp_gadget, a, b }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0].to_scalar().unwrap();
                let b = input_words[1].to_scalar().unwrap();
                let offset = 0;

                self.a.assign(region, offset, Value::known(a))?;
                self.b.assign(region, offset, Value::known(b))?;
                self.cmp_gadget.assign(region, offset, a, b)?;

                Ok(())
            }
        }

        // a == b check
        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(1 << N), Word::from(1 << N)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(1 << N)],
            false,
        );

        // a < b check
        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(1), Word::from(1 << N)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(10000), Word::from(2 << N)],
            false,
        );
    }

    #[test]
    fn test_pairselection() {
        #[derive(Clone)]
        /// a < b
        struct PairSelectionTestContainer<F, const SELECT_A: bool> {
            select_gadget: PairSelectGadget<F>,
            a: Cell<F>,
            b: Cell<F>,
            v: Cell<F>,
        }

        impl<F: Field, const SELECT_A: bool> MathGadgetContainer<F>
            for PairSelectionTestContainer<F, SELECT_A>
        {
            const NAME: &'static str = "PairSelectGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let v = cb.query_cell();
                let a = cb.query_cell();
                let b = cb.query_cell();
                let select_gadget =
                    PairSelectGadget::<F>::construct(cb, v.expr(), a.expr(), b.expr());
                cb.require_equal(
                    "is_a * is_b == 0",
                    select_gadget.expr().0 * select_gadget.expr().1,
                    0.expr(),
                );

                if SELECT_A {
                    cb.require_equal("is_a == 1", select_gadget.expr().0, 1.expr());
                } else {
                    cb.require_equal("is_b == 1", select_gadget.expr().1, 1.expr());
                }

                PairSelectionTestContainer {
                    select_gadget,
                    v,
                    a,
                    b,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let v = input_words[0].to_scalar().unwrap();
                let a = input_words[1].to_scalar().unwrap();
                let b = input_words[2].to_scalar().unwrap();
                let offset = 0;

                self.v.assign(region, offset, Value::known(v))?;
                self.a.assign(region, offset, Value::known(a))?;
                self.b.assign(region, offset, Value::known(b))?;
                self.select_gadget.assign(region, offset, v, a, b)?;

                Ok(())
            }
        }

        // choose a check
        test_math_gadget_container::<Fr, PairSelectionTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, PairSelectionTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, PairSelectionTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(1), Word::from(0)],
            false,
        );

        // choose b check
        test_math_gadget_container::<Fr, PairSelectionTestContainer<Fr, false>>(
            vec![Word::from(0), Word::from(1), Word::from(0)],
            true,
        );
    }

    #[test]
    fn test_constantdivisiongadget() {
        const N: usize = 4;
        #[derive(Clone)]
        /// a < b
        struct ConstantDivisionTestContainer<F, const DENOMINATOR: u64, const REMINDER: u64> {
            constdiv_gadget: ConstantDivisionGadget<F, N>,
            a: Cell<F>,
        }

        impl<F: Field, const DENOMINATOR: u64, const REMAINDER: u64> MathGadgetContainer<F>
            for ConstantDivisionTestContainer<F, DENOMINATOR, REMAINDER>
        {
            const NAME: &'static str = "ConstantDivisionGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let constdiv_gadget =
                    ConstantDivisionGadget::<F, N>::construct(cb, a.expr(), DENOMINATOR);

                cb.require_equal(
                    "a == n * denom",
                    constdiv_gadget.remainder(),
                    REMAINDER.expr(),
                );

                ConstantDivisionTestContainer { constdiv_gadget, a }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = u64::from_le_bytes(input_words[0].to_le_bytes()[..8].try_into().unwrap());
                let offset = 0;

                self.a.assign(region, offset, Value::known(F::from(a)))?;
                self.constdiv_gadget.assign(region, offset, a as u128)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 0>>(
            vec![Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 0>>(
            vec![Word::from(5)],
            true,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 1>>(
            vec![Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 4>>(
            vec![Word::from(1)],
            false,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 16, 0>>(
            vec![Word::from(1 << N)],
            true,
        );
    }

    #[test]
    fn test_minmax() {
        const N: usize = 4;
        #[derive(Clone)]

        struct MinMaxTestContainer<F, const MIN_A: bool> {
            minmax_gadget: MinMaxGadget<F, N>,
            a: Cell<F>,
            b: Cell<F>,
        }

        impl<F: Field, const MIN_A: bool> MathGadgetContainer<F> for MinMaxTestContainer<F, MIN_A> {
            const NAME: &'static str = "MinMaxGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let b = cb.query_cell();
                let minmax_gadget = MinMaxGadget::<F, N>::construct(cb, a.expr(), b.expr());

                if MIN_A {
                    cb.require_equal("min == a", minmax_gadget.min(), a.expr());
                    cb.require_equal("max == b", minmax_gadget.max(), b.expr());
                } else {
                    cb.require_equal("min == b", minmax_gadget.min(), b.expr());
                    cb.require_equal("max == a", minmax_gadget.max(), a.expr());
                }

                MinMaxTestContainer {
                    minmax_gadget,
                    a,
                    b,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0].to_scalar().unwrap();
                let b = input_words[1].to_scalar().unwrap();
                let offset = 0;

                self.a.assign(region, offset, Value::known(a))?;
                self.b.assign(region, offset, Value::known(b))?;
                self.minmax_gadget.assign(region, offset, a, b)?;

                Ok(())
            }
        }

        // min == a
        test_math_gadget_container::<Fr, MinMaxTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, MinMaxTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, MinMaxTestContainer<Fr, true>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        // min == b
        test_math_gadget_container::<Fr, MinMaxTestContainer<Fr, false>>(
            vec![Word::from(1), Word::from(0)],
            true,
        );
    }

    #[test]
    fn test_mod() {
        #[derive(Clone)]
        /// a % n == r
        struct ModGadgetTestContainer<F> {
            mod_gadget: ModGadget<F>,
            a: util::Word<F>,
            n: util::Word<F>,
            r: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for ModGadgetTestContainer<F> {
            const NAME: &'static str = "ModGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let n = cb.query_word();
                let r = cb.query_word();
                let mod_gadget = ModGadget::<F>::construct(cb, [&a, &n, &r]);
                ModGadgetTestContainer {
                    mod_gadget,
                    a,
                    n,
                    r,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let n = input_words[1];
                let a_reduced = input_words[2];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.n.assign(region, offset, Some(n.to_le_bytes()))?;
                self.r
                    .assign(region, offset, Some(a_reduced.to_le_bytes()))?;
                self.mod_gadget.assign(region, 0, a, n, a_reduced, F::one())
            }
        }

        test_math_gadget_container::<Fr, ModGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ModGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ModGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ModGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(1)],
            false,
        );
    }

    #[test]
    fn test_cmpword() {
        #[derive(Clone)]
        /// a < b
        struct CmpWordGadgetTestContainer<F, const CHECK_EQ: bool> {
            cmp_gadget: CmpWordsGadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
        }

        impl<F: Field, const CHECK_EQ: bool> MathGadgetContainer<F>
            for CmpWordGadgetTestContainer<F, CHECK_EQ>
        {
            const NAME: &'static str = "CmpWordsGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let cmp_gadget = CmpWordsGadget::<F>::construct(cb, &a, &b);
                cb.require_equal(
                    "(a < b) * (a == b) == 0",
                    cmp_gadget.eq.clone() * cmp_gadget.lt.clone(),
                    0.expr(),
                );

                if CHECK_EQ {
                    cb.require_equal("a == b", cmp_gadget.eq.clone(), 1.expr());
                } else {
                    cb.require_equal("a < b", cmp_gadget.lt.clone(), 1.expr());
                }

                CmpWordGadgetTestContainer { cmp_gadget, a, b }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.cmp_gadget.assign(region, offset, a, b)?;
                Ok(())
            }
        }

        // a == b check
        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, true>>(
            vec![Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, true>>(
            vec![Word::MAX, Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, true>>(
            vec![Word::from(0), Word::MAX],
            false,
        );

        // a < b check
        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, false>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, false>>(
            vec![Word::from(1), Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, CmpWordGadgetTestContainer<Fr, false>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );
    }

    #[test]
    fn test_muladd() {
        #[derive(Clone)]
        /// a*b + c == d
        struct MulAddGadgetContainer<F> {
            math_gadget: MulAddWordsGadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
            c: util::Word<F>,
            d: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for MulAddGadgetContainer<F> {
            const NAME: &'static str = "MulAddGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let c = cb.query_word();
                let d = cb.query_word();
                let math_gadget = MulAddWordsGadget::<F>::construct(cb, [&a, &b, &c, &d]);
                MulAddGadgetContainer {
                    math_gadget,
                    a,
                    b,
                    c,
                    d,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let offset = 0;
                self.a
                    .assign(region, offset, Some(input_words[0].to_le_bytes()))?;
                self.b
                    .assign(region, offset, Some(input_words[1].to_le_bytes()))?;
                self.c
                    .assign(region, offset, Some(input_words[2].to_le_bytes()))?;
                self.d
                    .assign(region, offset, Some(input_words[3].to_le_bytes()))?;
                self.math_gadget
                    .assign(region, offset, input_words.try_into().unwrap())
            }
        }

        test_math_gadget_container::<Fr, MulAddGadgetContainer<Fr>>(
            vec![Word::from(0), Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, MulAddGadgetContainer<Fr>>(
            vec![Word::from(1), Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, MulAddGadgetContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, MulAddGadgetContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(1), Word::from(2)],
            true,
        );

        test_math_gadget_container::<Fr, MulAddGadgetContainer<Fr>>(
            vec![Word::from(10), Word::from(1), Word::from(1), Word::from(3)],
            false,
        );
    }

    #[test]
    fn test_muladd512() {
        #[derive(Clone)]
        /// a * b + c == d * 2**256 + e
        struct MulAddWords512GadgetContainer<F> {
            math_gadget: MulAddWords512Gadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
            d: util::Word<F>,
            e: util::Word<F>,
            addend: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for MulAddWords512GadgetContainer<F> {
            const NAME: &'static str = "MulAddWords512Gadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let d = cb.query_word();
                let e = cb.query_word();
                let addend = cb.query_word();
                let math_gadget =
                    MulAddWords512Gadget::<F>::construct(cb, [&a, &b, &d, &e], Some(&addend));
                MulAddWords512GadgetContainer {
                    math_gadget,
                    a,
                    b,
                    d,
                    e,
                    addend,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let offset = 0;
                self.a
                    .assign(region, offset, Some(input_words[0].to_le_bytes()))?;
                self.b
                    .assign(region, offset, Some(input_words[1].to_le_bytes()))?;
                self.d
                    .assign(region, offset, Some(input_words[2].to_le_bytes()))?;
                self.e
                    .assign(region, offset, Some(input_words[3].to_le_bytes()))?;
                self.addend
                    .assign(region, offset, Some(input_words[4].to_le_bytes()))?;
                self.math_gadget.assign(
                    region,
                    offset,
                    [
                        input_words[0],
                        input_words[1],
                        input_words[2],
                        input_words[3],
                    ],
                    Some(input_words[4]),
                )
            }
        }

        test_math_gadget_container::<Fr, MulAddWords512GadgetContainer<Fr>>(
            vec![
                Word::from(0),
                Word::from(0),
                Word::from(0),
                Word::from(0),
                Word::from(0),
            ],
            true,
        );

        test_math_gadget_container::<Fr, MulAddWords512GadgetContainer<Fr>>(
            vec![
                Word::from(1),
                Word::from(0),
                Word::from(0),
                Word::from(0),
                Word::from(0),
            ],
            true,
        );

        test_math_gadget_container::<Fr, MulAddWords512GadgetContainer<Fr>>(
            vec![
                Word::from(1),
                Word::from(1),
                Word::from(0),
                Word::from(1),
                Word::from(0),
            ],
            true,
        );

        // test_math_gadget_container::<Fr, MulAddWords512GadgetContainer<Fr>>(
        //     vec![Word::from(1), Word::from(1), Word::from(1), Word::from(2),
        // Word::from(2**256)],     true,
        // );

        test_math_gadget_container::<Fr, MulAddWords512GadgetContainer<Fr>>(
            vec![
                Word::from(10),
                Word::from(1),
                Word::from(1),
                Word::from(3),
                Word::from(0),
            ],
            false,
        );
    }

    #[test]
    fn test_absword() {
        #[derive(Clone)]
        struct AbsWordGadgetContainer<F> {
            absword_gadget: AbsWordGadget<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for AbsWordGadgetContainer<F> {
            const NAME: &'static str = "AbsWordGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let absword_gadget = AbsWordGadget::<F>::construct(cb);
                AbsWordGadgetContainer { absword_gadget }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let offset = 0;
                let x = input_words[0];
                let x_abs = input_words[1];
                self.absword_gadget.assign(region, offset, x, x_abs)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, AbsWordGadgetContainer<Fr>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, AbsWordGadgetContainer<Fr>>(
            vec![Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, AbsWordGadgetContainer<Fr>>(
            vec![Word::from(1), Word::from(2)],
            false,
        );
    }
}

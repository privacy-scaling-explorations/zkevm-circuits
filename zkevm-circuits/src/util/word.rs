#![allow(missing_docs)]
//! Define generic Word type with utility functions
// Naming Convesion
// - Limbs: An EVN word is 256 bits. Limbs N means split 256 into N limb. For example, N = 4, each
//   limb is 256/4 = 64 bits

use eth_types::{Field, ToLittleEndian, U256};
use gadgets::util::{not, or, Expr};
use halo2_proofs::{
    circuit::{AssignedCell, Value, Region},
    plonk::{Error, Expression, Column, Advice, Assigned},
};
use itertools::Itertools;

use crate::evm_circuit::util::{from_bytes, CachedRegion, Cell};

#[derive(Clone, Debug, Copy)]
pub  struct WordLimbs<T, const N: usize> {
    pub limbs: [T; N],
}

pub  type Word2<T> = WordLimbs<T, 2>;

pub  type Word4<T> = WordLimbs<T, 4>;

pub  type Word16<T> = WordLimbs<T, 16>;

pub  type Word32<T> = WordLimbs<T, 32>;

pub(crate)  type WordCell<F> = Word<Cell<F>>;

pub(crate)  type Word32Cell<F> = Word32<Cell<F>>;

impl<T, const N: usize> WordLimbs<T, N> {
    pub fn new(limbs: [T; N]) -> Self {
        Self { limbs }
    }

    pub fn n() -> usize {
        N
    }
}

impl<T: Default, const N: usize> Default for WordLimbs<T, N> {
    fn default() -> Self {
        Self {
            limbs: [(); N].map(|_| T::default()),
        }
    }
}

pub  trait WordExpr<F> {
    fn to_word(&self) -> Word<Expression<F>>;
}

impl<F: Field, const N: usize> WordLimbs<Cell<F>, N> {
    pub fn assign<const N1: usize>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: Option<[u8; N1]>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        assert_eq!(N1 % N, 0); // TODO assure N|N1, find way to use static_assertion instead
        bytes.map_or(Err(Error::Synthesis), |bytes| {
            bytes
                .chunks(N1 / N) // chunk in little endian
                .map(|chunk| from_bytes::value(chunk))
                .zip(self.limbs.iter())
                .map(|(value, cell)| cell.assign(region, offset, Value::known(value)))
                .collect()
        })
    }

    pub fn word_expr(&self) -> WordLimbs<Expression<F>, N> {
        return WordLimbs::new(self.limbs.clone().map(|cell| cell.expr()))
    }
}

impl<F: Field, const N: usize> WordExpr<F> for WordLimbs<Cell<F>, N> {
    fn to_word(&self) -> Word<Expression<F>> {
        Word(self.word_expr().to_word_n())
    }
}

impl<F: Field, const N: usize>  WordLimbs<F, N> {
    pub fn is_zero_vartime(&self) -> bool {
        self.limbs.iter().all(|limb| limb.is_zero_vartime())
    }
}

// `Word`, special alias for Word2.
#[derive(Clone, Debug, Copy, Default)]
pub struct Word<T>(Word2<T>);

impl<T: Clone> Word<T> {
    pub fn new(limbs: [T; 2]) -> Self {
        Self(WordLimbs::<T, 2>::new(limbs))
    }
    pub fn hi(&self) -> &T {
        &self.0.limbs[1]
    }
    pub fn lo(&self) -> &T {
        &self.0.limbs[0]
    }

    pub fn n() -> usize {
        2
    }

    pub fn to_lo_hi(&self) -> (&T, &T) {
        (&self.0.limbs[0], &self.0.limbs[1])
    }

    pub fn into_lo_hi(self) -> (T, T) {
        let [lo, hi] = self.0.limbs;
        (lo,hi)
    }

    pub fn into_value(self) -> Word<Value<T>> {
        let [lo, hi] = self.0.limbs;
        Word::new([Value::known(lo), Value::known(hi)])
    }

}

impl<T> std::ops::Deref for Word<T> {
    type Target = WordLimbs<T, 2>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Field> Word<F> {

    pub fn from_u256(value: eth_types::Word) -> Word<F> {
        let bytes = value.to_le_bytes();
        Word::new([
            from_bytes::value(&bytes[..16]),
            from_bytes::value(&bytes[16..]),
        ])
    }

    pub fn from_u64(value: u64) -> Word<F> {
        let bytes = value.to_le_bytes();
        Word::new([from_bytes::value(&bytes), F::from(0)])
    }
}

impl<F: Field> Into<Word<F>> for eth_types::Word {
    fn into(self) -> Word<F> { Word::<F>::from_u256(self) }
}

impl<F: Field> Word<Cell<F>> {
    pub fn assign_lo(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        Ok(vec![
            self.limbs[0].assign(region, offset, value)?,
            self.limbs[1].assign(region, offset, Value::known(F::from(0)))?,
        ])
    }
}

impl<F: Field> Word<Value<F>> {
   pub fn assign_advice<A, AR>(
        &self,
        region: &mut Region<'_, F>,
        annotation: A,
        column: Word<Column<Advice>>,
        offset: usize,
    ) -> Result<Word<AssignedCell<F, F>>, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>
    {
        let annotation : String = annotation().into();
        let lo = region.assign_advice(|| &annotation, *column.lo(), offset, || *self.lo())?;
        let hi = region.assign_advice(|| &annotation, *column.hi(), offset, || *self.hi())?;

        Ok(Word::new([lo,hi]))
    }
}


impl<F: Field> WordExpr<F> for Word<Cell<F>> {
    fn to_word(&self) -> Word<Expression<F>> {
        self.word_expr().to_word()
    }
}

impl<F: Field> Word<Expression<F>> {
    // create word from lo limb with hi limb as 0. caller need to guaranteed to be 128 bits.
    pub fn from_lo_unchecked(lo: Expression<F>) -> Self {
        Self(WordLimbs::<Expression<F>, 2>::new([lo, 0.expr()]))
    }

    pub fn zero() -> Self {
        Self(WordLimbs::<Expression<F>, 2>::new([0.expr(), 0.expr()]))
    }

    // select based on selector. Here assume selector is 1/0 therefore no overflow check
    pub fn select<T: WordExpr<F>>(
        selector: Expression<F>,
        when_true: T,
        when_false: T,
    ) -> Word<Expression<F>> {
        let when_true_sel = 
        when_true
            .to_word()
            .mul_selector(selector.clone());
            let (true_lo, true_hi) =  when_true_sel    .to_lo_hi();
        let when_false_sel =     when_false
        .to_word()
        .mul_selector(1.expr() - selector);
        let (false_lo, false_hi) = when_false_sel.to_lo_hi();
        Word::new([
            true_lo.clone() + false_lo.clone(),
            true_hi.clone() + false_hi.clone(),
        ])
    }

    // Assume selector is 1/0 therefore no overflow check
    pub fn mul_selector(&self, selector: Expression<F>) -> Self {
        Word::new([self.lo().clone() * selector.clone(), self.hi().clone() * selector])
    }

    // No overflow check on lo/hi limbs
    pub fn add_unchecked(self, rhs: Self) -> Self {
        Word::new([
            self.lo().clone() + rhs.lo().clone(),
            self.hi().clone() + rhs.hi().clone(),
        ])
    }

    // No underflow check on lo/hi limbs
    pub fn sub_unchecked(self, rhs: Self) -> Self {
        Word::new([
            self.lo().clone() - rhs.lo().clone(),
            self.hi().clone() - rhs.hi().clone(),
        ])
    }
}

impl<F: Field> WordExpr<F> for Word<Expression<F>> {
    fn to_word(&self) -> Word<Expression<F>> {
        self.clone()
    }
}

impl<F: Field, const N1: usize> WordLimbs<Expression<F>, N1> {
    /// to_wordlimbs will aggregate nested expressions, which implies during expression evaluation
    /// it need more recursive call. if the converted limbs word will be used in many place,
    /// consider create new low limbs word, have equality constrain, then finally use low limbs
    /// elsewhere.
    // TODO static assertion. wordaround https://github.com/nvzqz/static-assertions-rs/issues/40
    pub fn to_word_n<const N2: usize>(&self) -> WordLimbs<Expression<F>, N2> {
        assert_eq!(N1 % N2, 0);
        let limbs = self
            .limbs
            .chunks(N1 / N2)
            .map(|chunk| from_bytes::expr(chunk))
            .collect_vec()
            .try_into()
            .unwrap();
        WordLimbs::<Expression<F>, N2>::new(limbs)
    }

    // TODO static assertion. wordaround https://github.com/nvzqz/static-assertions-rs/issues/40
    pub fn eq<const N2: usize>(&self, others: &WordLimbs<Expression<F>, N2>) -> Expression<F> {
        assert_eq!(N1 % N2, 0);
        not::expr(or::expr(
            self.limbs
                .chunks(N1 / N2)
                .map(|chunk| from_bytes::expr(chunk))
                .zip(others.limbs.clone())
                .map(|(expr1, expr2)| expr1 - expr2)
                .collect_vec(),
        ))
    }
}

impl<F: Field, const N1: usize> WordExpr<F> for WordLimbs<Expression<F>, N1> {
    fn to_word(&self) -> Word<Expression<F>> {
        Word(self.to_word_n())
    }
}

// TODO unittest

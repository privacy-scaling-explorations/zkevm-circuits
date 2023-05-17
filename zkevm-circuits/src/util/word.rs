//! Define generic Word type with utility functions
// Naming Convesion
// - Limbs: An EVN word is 256 bits. Limbs N means split 256 into N limb. For example, N = 4, each
//   limb is 256/4 = 64 bits

use eth_types::{Field, ToLittleEndian};
use gadgets::util::{not, or, Expr};
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Error, Expression},
};
use itertools::Itertools;

use crate::evm_circuit::util::{from_bytes, CachedRegion, Cell};

#[derive(Clone, Debug, Copy)]
pub(crate) struct WordLimbs<T, const N: usize> {
    pub limbs: [T; N],
}

pub(crate) type Word2<T> = WordLimbs<T, 2>;

pub(crate) type Word4<T> = WordLimbs<T, 4>;

pub(crate) type Word16<T> = WordLimbs<T, 16>;

pub(crate) type Word32<T> = WordLimbs<T, 32>;

pub(crate) type WordCell<F> = Word<Cell<F>>;

pub(crate) type Word32Cell<F> = Word32<Cell<F>>;

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

pub(crate) trait WordExpr<F> {
    fn to_word(&self) -> Word<Expression<F>>;
}

impl<F: Field, const N: usize> WordLimbs<Cell<F>, N> {
    // N1 is number of bytes to assign, while N is number of limbs.
    // N1 % N = 0 (also implies N1 >= N)
    // If N1 > N, then N1 will be chunk into N1 / N size then aggregate to single expression
    // then assign to N limbs respectively.
    // e.g. N1 = 4 bytes, [b1, b2, b3, b4], and N = 2 limbs [l1, l2]
    // It equivalent `l1.assign(b1.expr() + b2.expr * F(256))`, `l2.assign(b3.expr() + b4.expr *
    // F(256))`
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

    // N_LO, N_HI are number of bytes to assign to first half and second half of size N limbs,
    // respectively N_LO and N_HI can be different size, the only requirement is N_LO % (N/2)
    // and N_HI % (N/2) [N/2] limbs will be assigned separately.
    // E.g. N_LO = 4 => [nl1, nl2, nl3, nl4]
    // N_HI = 2 => [nh1, nh2]
    // N = 2 => [l1, l2]
    // it equivalent l1.assign(nl1.expr() + nl2.expr() * 256 + nl3.expr() * 256^2 +  nl3.expr() *
    // 256^3) and l2.assign(nh1.expr() + nh2.expr() * 256)
    pub fn assign_lo_hi<const N_LO: usize, const N_HI: usize>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes_lo: Option<[u8; N_LO]>,
        bytes_hi: Option<[u8; N_HI]>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        assert_eq!(N % 2, 0); // TODO use static_assertion instead
        assert_eq!(N_LO % (N / 2), 0);
        assert_eq!(N_HI % (N / 2), 0);
        // assign lo
        let bytes_lo_assigned: Result<Vec<AssignedCell<F, F>>, Error> =
            bytes_lo.map_or(Err(Error::Synthesis), |bytes| {
                bytes
                    .chunks(N_LO / (N / 2)) // chunk in little endian
                    .map(|chunk| from_bytes::value(chunk))
                    .zip(self.limbs[0..(N / 2)].iter())
                    .map(|(value, cell)| cell.assign(region, offset, Value::known(value)))
                    .collect()
            });

        // assign hi
        let bytes_hi_assigned: Result<Vec<AssignedCell<F, F>>, Error> =
            bytes_hi.map_or(Err(Error::Synthesis), |bytes| {
                bytes
                    .chunks(N_HI / (N / 2)) // chunk in little endian
                    .map(|chunk| from_bytes::value(chunk))
                    .zip(self.limbs[N / 2..].iter())
                    .map(|(value, cell)| cell.assign(region, offset, Value::known(value)))
                    .collect()
            });

        match (bytes_lo_assigned, bytes_hi_assigned) {
            (Ok(bytes_lo_assignedcells), Ok(bytes_hi_assignedcells)) => Ok([
                bytes_lo_assignedcells.to_vec(),
                bytes_hi_assignedcells.to_vec(),
            ]
            .concat()),
            _ => Err(Error::Synthesis),
        }
    }

    pub fn word_expr(&self) -> WordLimbs<Expression<F>, N> {
        return WordLimbs::new(self.limbs.map(|cell| cell.expr()));
    }
}

impl<F: Field, const N: usize> WordExpr<F> for WordLimbs<Cell<F>, N> {
    fn to_word(&self) -> Word<Expression<F>> {
        Word(self.word_expr().to_word_n())
    }
}

// `Word`, special alias for Word2.
#[derive(Clone, Debug, Copy, Default)]
pub(crate) struct Word<T>(Word2<T>);

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
        let (true_lo, true_hi) = when_true
            .to_word()
            .mul_selector(selector.clone())
            .to_lo_hi();
        let (false_lo, false_hi) = when_false
            .to_word()
            .mul_selector(1.expr() - selector)
            .to_lo_hi();
        Word::new([
            true_lo.clone() + false_lo.clone(),
            true_hi.clone() + false_hi.clone(),
        ])
    }

    // Assume selector is 1/0 therefore no overflow check
    pub fn mul_selector(&self, selector: Expression<F>) -> Self {
        Word::new([self.lo().clone() * selector, self.hi().clone() * selector])
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
                .zip(others.limbs)
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

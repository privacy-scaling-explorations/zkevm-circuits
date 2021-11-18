use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::ops::{Index, IndexMut};

pub const B13: u64 = 13;
pub const B9: u64 = 9;

/// Base 9 coef mapper scalers
/// f_logic(x1, x2, x3, x4) = x1 ^ (!x2 & x3) ^ x4
/// f_arith(x1, x2, x3, x4) = 2*x1 + x2 + 3*x3 + 2*x4
/// where x1, x2, x3, x4 are binary.
/// We have the property that `0 <= f_arith(...) < 9` and
/// the map from `f_arith(...)` to `f_logic(...)` is injective.
pub const A1: u64 = 2u64;
pub const A2: u64 = 1u64;
pub const A3: u64 = 3u64;
pub const A4: u64 = 2u64;

pub type Lane13 = BigUint;
pub type Lane9 = BigUint;

pub struct StateBigInt {
    xy: Vec<BigUint>,
}
impl Default for StateBigInt {
    fn default() -> Self {
        let mut xy: Vec<BigUint> = Vec::with_capacity(25);
        for _ in 0..25 {
            xy.push(Zero::zero());
        }
        Self { xy }
    }
}

impl StateBigInt {
    pub fn from_state_big_int<F>(a: &StateBigInt, lane_transform: F) -> Self
    where
        F: Fn(BigUint) -> BigUint,
    {
        let mut out = StateBigInt::default();
        for (x, y) in (0..5).cartesian_product(0..5) {
            out[(x, y)] = lane_transform(a[(x, y)].clone());
        }
        out
    }
}

impl Index<(usize, usize)> for StateBigInt {
    type Output = BigUint;
    fn index(&self, xy: (usize, usize)) -> &Self::Output {
        assert!(xy.0 < 5);
        assert!(xy.1 < 5);

        &self.xy[xy.0 * 5 + xy.1]
    }
}

impl IndexMut<(usize, usize)> for StateBigInt {
    fn index_mut(&mut self, xy: (usize, usize)) -> &mut Self::Output {
        assert!(xy.0 < 5);
        assert!(xy.1 < 5);

        &mut self.xy[xy.0 * 5 + xy.1]
    }
}

impl Clone for StateBigInt {
    fn clone(&self) -> StateBigInt {
        let xy = self.xy.clone();
        StateBigInt { xy }
    }
}

pub fn mod_u64(a: &BigUint, b: u64) -> u64 {
    (a % b).iter_u64_digits().take(1).next().unwrap_or(0)
}

pub fn convert_b2_to_b13(a: u64) -> Lane13 {
    let mut lane13: BigUint = Zero::zero();
    for i in 0..64 {
        let bit = (a >> i) & 1;
        lane13 += bit * BigUint::from(B13).pow(i);
    }
    lane13
}

pub fn convert_b2_to_b9(a: u64) -> Lane9 {
    let mut lane9: BigUint = Zero::zero();
    for i in 0..64 {
        let bit = (a >> i) & 1;
        lane9 += bit * BigUint::from(B9).pow(i);
    }
    lane9
}

/// Maps a sum of 12 bits to the XOR result of 12 bits.
///
/// The input `x` is a chunk of a base 13 number and it represents the
/// arithmatic sum of 12 bits. Asking the result of the 12 bits XORed together
/// is equivalent of asking if `x` being an odd number.
///
/// For example, if we have 5 bits set and 7 bits unset, then we have `x` as 5
/// and the xor result to be 1.
pub fn convert_b13_coef(x: u64) -> u64 {
    assert!(x < 13);
    x & 1
}

/// Maps the arithmatic result `2*a + b + 3*c + 2*d` to the bit operation result
/// `a ^ (~b & c) ^ d`
///
/// The input `x` is a chunk of a base 9 number and it represents the arithmatic
/// result of `2*a + b + 3*c + 2*d`, where `a`, `b`, `c`, and `d` each is a bit.
pub fn convert_b9_coef(x: u64) -> u64 {
    assert!(x < 9);
    let bit_table: [u64; 9] = [0, 0, 1, 1, 0, 0, 1, 1, 0];
    bit_table[x as usize]
}

pub fn convert_b13_lane_to_b9(x: Lane13, rot: u32) -> Lane9 {
    let mut base = BigUint::from(B9).pow(rot);
    let mut special_chunk = Zero::zero();
    let mut raw = x;
    let mut acc: Lane9 = Zero::zero();

    for i in 0..65 {
        let remainder: u64 = mod_u64(&raw, B13);
        if i == 0 || i == 64 {
            special_chunk += remainder;
        } else {
            acc += convert_b13_coef(remainder) * base.clone();
        }
        raw /= B13;
        base *= B9;
        if i == 63 - rot {
            base = One::one();
        }
    }
    acc += convert_b13_coef(special_chunk) * BigUint::from(B9).pow(rot);
    acc
}

pub fn convert_lane<F>(
    lane: BigUint,
    from_base: u64,
    to_base: u64,
    coef_transform: F,
) -> BigUint
where
    F: Fn(u64) -> u64,
{
    let mut base: BigUint = One::one();
    let mut raw = lane;
    let mut acc: BigUint = Zero::zero();

    for _ in 0..64 {
        let remainder: u64 = mod_u64(&raw, B9);
        acc += coef_transform(remainder) * base.clone();
        raw /= from_base;
        base *= to_base;
    }
    acc
}

pub fn convert_b9_lane_to_b13(x: Lane9) -> Lane13 {
    convert_lane(x, B9, B13, convert_b9_coef)
}

pub fn convert_b9_lane_to_b2(x: Lane9) -> u64 {
    convert_lane(x, B9, 2, convert_b9_coef)
        .iter_u64_digits()
        .take(1)
        .next()
        .unwrap_or(0)
}

pub fn convert_b9_lane_to_b2_normal(x: Lane9) -> u64 {
    convert_lane(x, B9, 2, |y| y)
        .iter_u64_digits()
        .take(1)
        .next()
        .unwrap_or(0)
}

/// This function allows us to inpect coefficients of big-numbers in different
/// bases.
pub fn inspect(x: BigUint, name: &str, base: u64) {
    let mut raw = x.clone();
    let mut info: Vec<(u32, u64)> = vec![];

    for i in 0..65 {
        let remainder: u64 = mod_u64(&raw, base);
        raw /= base;
        if remainder != 0 {
            info.push((i, remainder));
        }
    }
    println!("inspect {} {} info {:?}", name, x, info);
}

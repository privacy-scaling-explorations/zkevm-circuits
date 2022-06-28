#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]

use crate::{
    circuit::{StateTag, NEXT_INPUTS_BYTES, STATE_WORDS},
    common::State,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{layouter, AssignedCell, Layouter},
    plonk::Error,
};
use itertools::Itertools;
use std::{convert::TryInto, ops::Div};

pub(crate) mod absorb;
pub(crate) mod base_conversion;
pub mod circuit;
pub(crate) mod generic;
pub(crate) mod iota;
pub(crate) mod mixing;
pub(crate) mod pi;
pub(crate) mod rho;
pub(crate) mod rho_checks;
pub(crate) mod rho_helpers;
pub(crate) mod tables;
pub(crate) mod theta;
pub(crate) mod xi;

use crate::circuit::KeccakConfig;

#[repr(transparent)]
#[derive(Debug, Clone)]
pub(crate) struct PermutationInputs<F>(pub(crate) Vec<NextInput<F>>);

impl<F: Field> PermutationInputs<F> {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn from_bytes(mut bytes: &[u8]) -> Self {
        let permutations = (bytes.len() as f64).div(NEXT_INPUTS_BYTES as f64).ceil() as usize;
        let mut idx = 1;
        let mut perm_inputs = Self::new();
        let bytes = &mut bytes;
        let state_tag = |idx| match permutations - idx > 0 {
            true => StateTag::Continue,
            false => StateTag::Finalize,
            _ => unreachable!(),
        };

        // Add the Continue and Finalize permutations
        while bytes.len() > 0 {
            perm_inputs
                .0
                .push(NextInput::from_bytes(bytes, idx, state_tag(idx)));
            idx += 1;
        }

        perm_inputs
    }
}

#[derive(Debug, Clone)]
pub(crate) struct NextInput<F> {
    pub(crate) unpadded_bytes: [F; NEXT_INPUTS_BYTES],
    padded_bytes: [F; NEXT_INPUTS_BYTES],
    pub(crate) og_len: usize,
    pub(crate) state_tag: StateTag,
    pub(crate) perm_count: usize,
}

impl<F: Field> NextInput<F> {
    pub fn new() -> Self {
        Self {
            unpadded_bytes: [F::zero(); NEXT_INPUTS_BYTES],
            padded_bytes: [F::zero(); NEXT_INPUTS_BYTES],
            og_len: 0,
            state_tag: StateTag::Start,
            perm_count: 0,
        }
    }

    pub fn with_og_len(bytes: &[u8], len: usize) -> Self {
        let bytes: [F; NEXT_INPUTS_BYTES] = bytes
            .iter()
            .map(|&byte| F::from(byte as u64))
            .chain(vec![F::zero(); NEXT_INPUTS_BYTES - len])
            .collect_vec()
            .try_into()
            .unwrap();
        Self {
            unpadded_bytes: bytes.clone(),
            padded_bytes: bytes,
            og_len: len,
            state_tag: StateTag::Start,
            perm_count: 0,
        }
    }

    fn pad(&mut self) {
        match (
            self.og_len == NEXT_INPUTS_BYTES,
            self.og_len == NEXT_INPUTS_BYTES - 1,
        ) {
            (true, false) => (),
            (false, true) => {
                if let Some(last) = self.padded_bytes.last_mut() {
                    *last = F::from(0x81u64);
                }
            }
            (false, false) => {
                self.padded_bytes[self.og_len] = F::from(0x80u64);
                self.padded_bytes[NEXT_INPUTS_BYTES - 1] = F::one();
            }
            _ => unreachable!(),
        }
    }

    pub fn from_bytes(byte_slice: &mut &[u8], perm_count: usize, state_tag: StateTag) -> Self {
        let len = if byte_slice.len() < NEXT_INPUTS_BYTES {
            byte_slice.len()
        } else {
            NEXT_INPUTS_BYTES
        };

        let mut bytes = vec![0u8; len];
        bytes[0..len].copy_from_slice(&byte_slice[0..len]);
        *byte_slice = &byte_slice[len..];

        let mut next_inp = Self::with_og_len(&bytes, len);
        next_inp.pad();
        next_inp.perm_count = perm_count;
        next_inp.state_tag = state_tag;
        next_inp
    }
}

#[cfg(test)]
mod next_inputs {
    use super::*;
    use halo2_proofs::pairing::bn256::Fr as Fp;
    use pretty_assertions::assert_eq;

    #[test]
    fn correct_padding() {
        let input = [
            65, 108, 105, 99, 101, 32, 119, 97, 115, 32, 98, 101, 103, 105, 110, 110, 105, 110,
            103, 32, 116, 111, 32, 103, 101, 116, 32, 118, 101, 114, 121, 32, 116, 105, 114, 101,
            100, 32, 111, 102, 32, 115, 105, 116, 116, 105, 110, 103, 32, 98, 121, 32, 104, 101,
            114, 32, 115, 105, 115, 116, 101, 114, 32, 111, 110, 32, 116, 104, 101, 32, 98, 97,
            110, 107, 44, 32, 97, 110, 100, 32, 111, 102, 32, 104, 97, 118, 105, 110, 103, 32, 110,
            111, 116, 104, 105, 110, 103, 32, 116, 111, 32, 100, 111, 58, 32, 111, 110, 99, 101,
            32, 111, 114, 32, 116, 119, 105, 99, 101, 32, 115, 104, 101, 32, 104, 97, 100, 32, 112,
            101, 101, 112, 101, 100, 32, 105, 110, 116, 111, 32, 116, 104, 101, 32, 98, 111, 111,
            107, 32, 104, 101, 114, 32, 115, 105, 115, 116, 101, 114, 32, 119, 97, 115, 32, 114,
            101, 97, 100, 105, 110, 103, 44, 32, 98, 117, 116, 32, 105, 116, 32, 104, 97, 100, 32,
            110, 111, 32, 112, 105, 99, 116, 117, 114, 101, 115, 32, 111, 114, 32, 99, 111, 110,
            118, 101, 114, 115, 97, 116, 105, 111, 110, 115, 32, 105, 110, 32, 105, 116, 44, 32,
            97, 110, 100, 32, 119, 104, 97, 116, 32, 105, 115, 32, 116, 104, 101, 32, 117, 115,
            101, 32, 111, 102, 32, 97, 32, 98, 111, 111, 107, 44, 32, 116, 104, 111, 117, 103, 104,
            116, 32, 65, 108, 105, 99, 101, 32, 119, 105, 116, 104, 111, 117, 116, 32, 112, 105,
            99, 116, 117, 114, 101, 115, 32, 111, 114, 32, 99, 111, 110, 118, 101, 114, 115, 97,
            116, 105, 111, 110, 115, 63,
        ];

        let perm_inputs = PermutationInputs::<Fp>::from_bytes(&input);

        let first_perm = input[0..NEXT_INPUTS_BYTES]
            .iter()
            .map(|&byte| Fp::from(byte as u64))
            .collect_vec();

        assert_eq!(perm_inputs.0[0].padded_bytes, first_perm[..]);
        assert!(perm_inputs.0[0].state_tag.is_continue());

        let second_perm = input[NEXT_INPUTS_BYTES..2 * NEXT_INPUTS_BYTES]
            .iter()
            .map(|&byte| Fp::from(byte as u64))
            .collect_vec();

        assert_eq!(perm_inputs.0[1].padded_bytes, second_perm[..]);
        assert!(perm_inputs.0[1].state_tag.is_continue());

        let mut last_perm_expected = input[NEXT_INPUTS_BYTES * 2..]
            .iter()
            .map(|&byte| Fp::from(byte as u64))
            .collect_vec();

        last_perm_expected.extend_from_slice(&[Fp::from(0x80u64)]);
        last_perm_expected.extend_from_slice(&vec![Fp::zero(); 136 - 28]);
        last_perm_expected.extend_from_slice(&[Fp::one()]);

        assert_eq!(
            perm_inputs.0.last().unwrap().padded_bytes,
            last_perm_expected[..]
        );
        assert!(perm_inputs.0.last().unwrap().state_tag.is_finalize());
    }
}

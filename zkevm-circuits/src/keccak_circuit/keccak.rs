use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, not, xor},
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, TableColumn},
    poly::Rotation,
};
use std::{marker::PhantomData, vec};

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const C_WIDTH: usize = 5 * 64;
const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
const IOTA_ROUND_CST: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
// Bit positions that have a non-zero value in `IOTA_ROUND_CST`.
const IOTA_ROUND_BIT_POS: [usize; 7] = [0, 1, 3, 7, 15, 31, 63];
const NUM_BITS_PER_LOOKUP: usize = 2;

/// Public data for the bytecode
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct KeccakRow {
    s_bits: [u8; KECCAK_WIDTH],
    c_bits: [u8; C_WIDTH],
}

/// KeccakConfig
#[derive(Clone, Debug)]
pub struct KeccakConfig<F> {
    q_enable: Column<Fixed>,
    s_bits: [Column<Advice>; KECCAK_WIDTH],
    c_bits: [Column<Advice>; C_WIDTH],
    iota_bits: [Column<Fixed>; IOTA_ROUND_BIT_POS.len()],
    c_table: TableColumn,
    _marker: PhantomData<F>,
}

/// KeccakCircuit
#[derive(Default)]
pub struct KeccakCircuit<F: Field> {
    inputs: Vec<KeccakRow>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakCircuit<F> {
    type Config = KeccakConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;
        config.assign(layouter, self.size, &self.inputs)?;
        Ok(())
    }
}

impl<F: Field> KeccakConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.fixed_column();
        let s_bits = array_init::array_init(|_| meta.advice_column());
        let c_bits = array_init::array_init(|_| meta.advice_column());
        let iota_bits = array_init::array_init(|_| meta.fixed_column());
        let c_table = meta.lookup_table_column();

        let mut b = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        let mut b_next = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        meta.create_gate("Query state bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        b[i][j][k] = meta.query_advice(s_bits[counter], Rotation::cur());
                        b_next[i][j][k] = meta.query_advice(s_bits[counter], Rotation::next());
                        counter += 1;
                    }
                }
            }
            vec![0u64.expr()]
        });
        let mut c = vec![vec![0u64.expr(); 64]; 5];
        meta.create_gate("Query Theta c bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for k in 0..64 {
                    c[i][k] = meta.query_advice(c_bits[counter], Rotation::cur());
                    counter += 1;
                }
            }
            vec![0u64.expr()]
        });

        // TODO: pack 4 (or even more) of these in a single lookup
        // => Total number of lookups: 5*64/4 = 80
        for i in 0..5 {
            let pi = (5 + i - 1) % 5;
            let ni = (i + 1) % 5;
            for s in (0..64).step_by(NUM_BITS_PER_LOOKUP) {
                meta.lookup("Theta c", |_| {
                    let mut input = 0u64.expr();
                    let mut bits = 0u64.expr();
                    for k in s..s + NUM_BITS_PER_LOOKUP {
                        let pk = (64 + k - 1) % 64;
                        input = input * 10u64.expr()
                            + (b[pi][0][k].clone()
                                + b[pi][1][k].clone()
                                + b[pi][2][k].clone()
                                + b[pi][3][k].clone()
                                + b[pi][4][k].clone()
                                + b[ni][0][pk].clone()
                                + b[ni][1][pk].clone()
                                + b[ni][2][pk].clone()
                                + b[ni][3][pk].clone()
                                + b[ni][4][pk].clone());
                        bits = bits * 2u64.expr() + c[i][k].clone();
                    }
                    vec![(input * (NUM_BITS_PER_LOOKUP * 2).expr() + bits, c_table)]
                });
            }
        }

        meta.create_gate("Constrain round bits", |meta| {
            // Theta
            let mut ob = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        ob[i][j][k] = xor::expr(b[i][j][k].clone(), c[i][k].clone());
                    }
                }
            }
            b = ob.clone();

            // Rho/Pi
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        ob[j][(2 * i + 3 * j) % 5][k] = b[i][j][(64 + k - RHOM[i][j]) % 64].clone();
                    }
                }
            }
            b = ob.clone();

            // Chi
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        ob[i][j][k] = xor::expr(
                            b[i][j][k].clone(),
                            not::expr(b[(i + 1) % 5][j][k].clone()) * b[(i + 2) % 5][j][k].clone(),
                        );
                    }
                }
            }
            // Iota
            for (idx, iota_bit) in iota_bits.iter().enumerate() {
                let k = IOTA_ROUND_BIT_POS[idx];
                ob[0][0][k] = xor::expr(
                    meta.query_fixed(*iota_bit, Rotation::cur()),
                    ob[0][0][k].clone(),
                );
            }
            b = ob.clone();

            let mut max_degree = 0;
            let mut cb = BaseConstraintBuilder::new(9);
            // TODO: just use lookup columns to enforce this?
            for i in 0..5 {
                for k in 0..64 {
                    cb.require_boolean("c bit boolean", c[i][k].clone());
                }
            }
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        if b[i][j][k].degree() > max_degree {
                            max_degree = b[i][j][k].degree();
                        }
                        cb.require_equal("state bit", b[i][j][k].clone(), b_next[i][j][k].clone());
                    }
                }
            }
            println!("max expression degree: {}", max_degree);
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        KeccakConfig {
            q_enable,
            s_bits,
            c_bits,
            iota_bits,
            c_table,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        witness: &[KeccakRow],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                let mut offset = 0;
                for keccak_row in witness.iter() {
                    self.set_row(&mut region, offset, keccak_row.s_bits, keccak_row.c_bits)?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        s_bits: [u8; KECCAK_WIDTH],
        c_bits: [u8; C_WIDTH],
    ) -> Result<(), Error> {
        let round = offset % 25;

        // q_enable
        region.assign_fixed(
            || format!("assign q_enable {}", offset),
            self.q_enable,
            offset,
            || Ok(F::from(round != 24)),
        )?;

        // State bits
        for (idx, (bit, column)) in s_bits.iter().zip(self.s_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Theta c bits
        for (idx, (bit, column)) in c_bits.iter().zip(self.c_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign theta c bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Iota bit columns
        if round < 24 {
            for (pos, column) in IOTA_ROUND_BIT_POS.iter().zip(self.iota_bits.iter()) {
                region.assign_fixed(
                    || format!("assign iota bit {} {}", *pos, offset),
                    *column,
                    offset,
                    || Ok(F::from(((IOTA_ROUND_CST[round] >> *pos) & 1) as u64)),
                )?;
            }
        }

        Ok(())
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "c table",
            |mut table| {
                if NUM_BITS_PER_LOOKUP == 1 {
                    for idx in 0u64..=10 {
                        table.assign_cell(
                            || "range",
                            self.c_table,
                            idx as usize,
                            || Ok(F::from(idx * 2 + (idx & 1))),
                        )?;
                    }
                } else if NUM_BITS_PER_LOOKUP == 2 {
                    let mut offset = 0;
                    for a in 0u64..=10 {
                        for b in 0u64..=10 {
                            table.assign_cell(
                                || "range",
                                self.c_table,
                                offset,
                                || Ok(F::from(((a * 10) + b) * 4 + ((a & 1) * 2) + (b & 1))),
                            )?;
                            offset += 1;
                        }
                    }
                } else {
                    unimplemented!();
                }
                Ok(())
            },
        )
    }
}

fn keccak(bytes: Vec<u8>) -> Vec<KeccakRow> {
    let mut rows: Vec<KeccakRow> = Vec::new();

    let bits = into_bits(&bytes);

    let mut counter = 0;
    let mut b = [[[0u8; 64]; 5]; 5];
    for i in 0..5 {
        for j in 0..5 {
            for k in 0..64 {
                b[i][j][k] = bits[counter];
                counter += 1;
            }
        }
    }

    for round in 0..25 {
        let mut c = [[0u8; 64]; 5];
        for i in 0..5 {
            let pi = (5 + i - 1) % 5;
            let ni = (i + 1) % 5;
            for k in 0..64 {
                let pk = (64 + k - 1) % 64;
                c[i][k] = (b[pi][0][k]
                    + b[pi][1][k]
                    + b[pi][2][k]
                    + b[pi][3][k]
                    + b[pi][4][k]
                    + b[ni][1][pk]
                    + b[ni][0][pk]
                    + b[ni][2][pk]
                    + b[ni][3][pk]
                    + b[ni][4][pk])
                    & 1;
            }
        }

        // Flatten bits
        let mut counter = 0;
        let mut s_bits = [0u8; KECCAK_WIDTH];
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..64 {
                    s_bits[counter] = b[i][j][k];
                    counter += 1;
                }
            }
        }

        // Flatten bits
        let mut counter = 0;
        let mut c_bits = [0u8; C_WIDTH];
        for i in 0..5 {
            for k in 0..64 {
                c_bits[counter] = c[i][k];
                counter += 1;
            }
        }

        rows.push(KeccakRow { s_bits, c_bits });

        // Theta
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..64 {
                    b[i][j][k] ^= c[i][k];
                }
            }
        }

        // Rho/Pi
        let mut ob = b.clone();
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..64 {
                    ob[j][(2 * i + 3 * j) % 5][k] = b[i][j][(64 + k - RHOM[i][j]) % 64]
                }
            }
        }
        b = ob;

        // Chi
        let mut ob = b.clone();
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..64 {
                    ob[i][j][k] = b[i][j][k] ^ ((1 - b[(i + 1) % 5][j][k]) * b[(i + 2) % 5][j][k]);
                }
            }
        }
        b = ob;

        // Iota
        if round < 24 {
            for k in IOTA_ROUND_BIT_POS {
                b[0][0][k] ^= ((IOTA_ROUND_CST[round] >> k) & 1) as u8;
            }
        }
    }

    rows
}

fn into_bits(bytes: &[u8]) -> Vec<u8> {
    let num_bits = bytes.len() * 8;
    let mut bits: Vec<u8> = vec![0; num_bits];

    let mut counter = 0;
    for byte in bytes {
        for idx in 0u64..8 {
            bits[counter] = (*byte >> idx) & 1;
            counter += 1;
        }
    }

    bits
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakRow>, success: bool) {
        let circuit = KeccakCircuit::<F> {
            inputs,
            size: 2usize.pow(k),
            _marker: PhantomData,
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let err = prover.verify();
        let print_failures = true;
        if err.is_err() && print_failures {
            for e in err.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }

    #[test]
    fn new_keccak_simple() {
        let k = 8;
        let inputs = keccak(vec![1u8; 1600]);
        verify::<Fr>(k, inputs, true);
    }
}

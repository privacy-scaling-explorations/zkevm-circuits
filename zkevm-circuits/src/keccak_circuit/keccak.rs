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
use itertools::Itertools;
use std::{env::var, marker::PhantomData, vec};

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
//const NUM_BITS_PER_THETA_LOOKUP: usize = 3;
const MAX_INPUT_THETA_LOOKUP: u64 = 5;
//const NUM_BITS_PER_CHI_LOOKUP: usize = 4;
//const NUM_CHI_LOOKUP_VALUES: usize = KECCAK_WIDTH / NUM_BITS_PER_CHI_LOOKUP;

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

fn get_num_bits_per_theta_lookup() -> usize {
    let degree = get_degree() as u32;
    let mut num_bits = 1;
    while (MAX_INPUT_THETA_LOOKUP + 1).pow(num_bits + 1) <= 2u64.pow(degree) {
        num_bits += 1;
    }
    num_bits as usize
}

/// Public data for the bytecode
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct KeccakRow {
    s_bits: [u8; KECCAK_WIDTH],
    c_bits: [u8; C_WIDTH],
    //chi_lookup_values: [u64; NUM_CHI_LOOKUP_VALUES],
}

/// KeccakConfig
#[derive(Clone, Debug)]
pub struct KeccakConfig<F> {
    q_enable: Column<Fixed>,
    s_bits: [Column<Advice>; KECCAK_WIDTH],
    c_bits: [Column<Advice>; C_WIDTH],
    //chi_lookup_values: [Column<Advice>; KECCAK_WIDTH / NUM_BITS_PER_CHI_LOOKUP],
    iota_bits: [Column<Fixed>; IOTA_ROUND_BIT_POS.len()],
    c_table: Vec<TableColumn>,
    //chi_table: [TableColumn; 1 + NUM_BITS_PER_CHI_LOOKUP],
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
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        println!("num_bits_per_theta_lookup: {}", num_bits_per_theta_lookup);

        let q_enable = meta.fixed_column();
        let s_bits = array_init::array_init(|_| meta.advice_column());
        let c_bits = array_init::array_init(|_| meta.advice_column());
        //let chi_lookup_values = array_init::array_init(|_| meta.advice_column());
        let iota_bits = array_init::array_init(|_| meta.fixed_column());
        //let mut c_table = array_init::array_init(|_| meta.lookup_table_column());
        // vec![meta.lookup_table_column(); 1 + num_bits_per_theta_lookup];

        let mut c_table = Vec::new();
        for idx in 0..1 + num_bits_per_theta_lookup {
            c_table.push(meta.lookup_table_column());
        }

        //let chi_table = array_init::array_init(|_| meta.lookup_table_column());

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
        /*let mut chi_lookup_inputs = vec![0u64.expr(); chi_lookup_values.len()];
        meta.create_gate("Query Chi lookup values", |meta| {
            for idx in 0..chi_lookup_values.len() {
                chi_lookup_inputs[idx] = meta.query_advice(chi_lookup_values[idx], Rotation::cur());
            }
            vec![0u64.expr()]
        });*/

        // Theta lookups
        // TODO: pack 4 (or even more) of these in a single lookup
        // => Total number of lookups: 5*64/4 = 80
        let mut theta = Vec::new();
        for i in 0..5 {
            let pi = (5 + i - 1) % 5;
            let ni = (i + 1) % 5;
            for k in 0..64 {
                let pk = (64 + k - 1) % 64;
                /*input = input * 10u64.expr()
                + (b[pi][0][k].clone()
                    + b[pi][1][k].clone()
                    + b[pi][2][k].clone()
                    + b[pi][3][k].clone()
                    + b[pi][4][k].clone()
                    + b[ni][0][pk].clone()
                    + b[ni][1][pk].clone()
                    + b[ni][2][pk].clone()
                    + b[ni][3][pk].clone()
                    + b[ni][4][pk].clone());*/
                let bit = xor::expr(b[pi][0][k].clone(), b[pi][1][k].clone())
                    + xor::expr(b[pi][2][k].clone(), b[pi][3][k].clone())
                    + xor::expr(b[pi][4][k].clone(), b[ni][0][pk].clone())
                    + xor::expr(b[ni][1][pk].clone(), b[ni][2][pk].clone())
                    + xor::expr(b[ni][3][pk].clone(), b[ni][4][pk].clone());
                /*input = input * MAX_INPUT_THETA_LOOKUP.expr()
                + xor::expr(
                    xor::expr(b[pi][0][k].clone(), b[pi][1][k].clone()),
                    xor::expr(b[pi][2][k].clone(), b[pi][3][k].clone()),
                )
                + xor::expr(
                    xor::expr(b[pi][4][k].clone(), b[ni][0][pk].clone()),
                    xor::expr(b[ni][1][pk].clone(), b[ni][2][pk].clone()),
                )
                + xor::expr(b[ni][3][pk].clone(), b[ni][4][pk].clone());*/
                theta.push((c[i][k].clone(), bit));
            }
        }

        let mut lookup_counter = 0;
        for chunk in theta.chunks(num_bits_per_theta_lookup) {
            meta.lookup("Theta c", |_| {
                let mut factor = 1u64;
                let mut input = 0u64.expr();
                let mut tables = Vec::new();
                for (idx, (bit, expr)) in chunk.iter().enumerate() {
                    //input = input * MAX_INPUT_THETA_LOOKUP.expr() + expr.clone();
                    input = input + expr.clone() * factor.expr();
                    factor *= MAX_INPUT_THETA_LOOKUP;
                    tables.push((bit.clone(), c_table[1 + idx]));
                }
                tables.push((input, c_table[0]));
                tables
            });
            lookup_counter += 1;
        }
        println!("Lookups: {}", lookup_counter);

        // Chi lookups
        // TODO: pack 8 (or even more) of these in a single lookup
        // => Total number of lookups: 5*5*64/8 = 200
        /*let mut counter = 0;
        for i in 0..5 {
            for j in 0..5 {
                for s in (0..64).step_by(NUM_BITS_PER_CHI_LOOKUP) {
                    meta.lookup("Chi lookups", |meta| {
                        let selector = meta.query_fixed(q_enable, Rotation::cur());
                        let mut tables = Vec::new();
                        for (idx, k) in (s..s + NUM_BITS_PER_CHI_LOOKUP).enumerate() {
                            tables.push((
                                selector.clone() * b_next[i][j][k].clone(),
                                chi_table[1 + idx],
                            ));
                        }
                        tables.push((
                            selector.clone() * chi_lookup_inputs[counter].clone(),
                            chi_table[0],
                        ));
                        counter += 1;
                        tables
                    });
                }
            }
        }*/

        meta.create_gate("Constrain round bits", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            /*for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        cb.require_boolean("boolean state bit", b[i][j][k].clone());
                    }
                }
            }*/

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
            /*let mut count = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for l in (0..64).step_by(NUM_BITS_PER_CHI_LOOKUP) {
                        let mut offset = 1u64;
                        let mut compressed_value = 0u64.expr();
                        for k in l..l + NUM_BITS_PER_CHI_LOOKUP {
                            compressed_value = compressed_value
                                + (b[i][j][k].clone()
                                    + (not::expr(b[(i + 1) % 5][j][k].clone())
                                        * b[(i + 2) % 5][j][k].clone()))
                                    * offset.clone().expr();
                            offset *= 3;
                        }
                        cb.require_equal(
                            "chi lookup table value",
                            compressed_value,
                            chi_lookup_inputs[count].clone(),
                        );
                        count += 1;
                    }
                }
            }
            b = ob.clone();
            */

            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        cb.require_equal(
                            "state transition",
                            not::expr(b[(i + 1) % 5][j][k].clone()) * b[(i + 2) % 5][j][k].clone(),
                            xor::expr(b[i][j][k].clone(), b_next[i][j][k].clone()),
                            /* xor::expr(xor::expr(b[i][j][k].clone(), b_next[i][j][k].clone()),
                             * b_next[i][j][k].clone()), */
                        );
                    }
                }
            }

            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        println!("degree: {}", meta.degree());

        KeccakConfig {
            q_enable,
            s_bits,
            c_bits,
            //chi_lookup_values,
            iota_bits,
            c_table,
            //chi_table,
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
                    self.set_row(
                        &mut region,
                        offset,
                        keccak_row.s_bits,
                        keccak_row.c_bits,
                        //keccak_row.chi_lookup_values,
                    )?;
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
        //chi_lookup_values: [u64; NUM_CHI_LOOKUP_VALUES],
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

        // Chi lookup values
        /*for (idx, (value, column)) in chi_lookup_values
            .iter()
            .zip(self.chi_lookup_values.iter())
            .enumerate()
        {
            region.assign_advice(
                || format!("assign chi lookup value {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*value as u64)),
            )?;
        }*/

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
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        layouter.assign_table(
            || "c table",
            |mut table| {
                for (offset, perm) in (0..num_bits_per_theta_lookup)
                    .map(|_| 0..=MAX_INPUT_THETA_LOOKUP)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut compressed_value = 0u64;
                    let mut factor = 1u64;
                    for (idx, input) in perm.iter().enumerate() {
                        compressed_value += input * factor;
                        factor *= MAX_INPUT_THETA_LOOKUP;

                        table.assign_cell(
                            || "theta c output",
                            self.c_table[idx + 1],
                            offset,
                            || Ok(F::from(*input & 1)),
                        )?;
                    }

                    table.assign_cell(
                        || "theta c input",
                        self.c_table[0],
                        offset,
                        || Ok(F::from(compressed_value)),
                    )?;
                }
                Ok(())
            },
        )?;

        /*layouter.assign_table(
            || "chi table",
            |mut table| {
                for (offset, perm) in (0..NUM_BITS_PER_CHI_LOOKUP)
                    .map(|_| 0..=2)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut factor = 1u64;
                    let mut compressed_value = 0u64;
                    for (idx, input) in perm.iter().enumerate() {
                        compressed_value = compressed_value + input * factor;
                        factor *= 3;

                        table.assign_cell(
                            || "chi output",
                            self.chi_table[idx + 1],
                            offset,
                            || Ok(F::from(*input & 1)),
                        )?;
                    }

                    table.assign_cell(
                        || "chi input",
                        self.chi_table[0],
                        offset,
                        || Ok(F::from(compressed_value)),
                    )?;
                }
                Ok(())
            },
        )?;*/

        Ok(())
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

        /*let mut chi_lookup_values = [0u64; NUM_CHI_LOOKUP_VALUES];
        let mut count = 0;
        for i in 0..5 {
            for j in 0..5 {
                for l in (0..64).step_by(NUM_BITS_PER_CHI_LOOKUP) {
                    let mut offset = 1u64;
                    let mut compressed_value = 0u64;
                    for k in l..l + NUM_BITS_PER_CHI_LOOKUP {
                        compressed_value = compressed_value
                            + ((b[i][j][k] + ((1 - b[(i + 1) % 5][j][k]) * b[(i + 2) % 5][j][k]))
                                as u64)
                                * offset;
                        offset *= 3;
                    }
                    chi_lookup_values[count] = compressed_value;
                    count += 1;
                }
            }
        }*/

        rows.push(KeccakRow {
            s_bits,
            c_bits,
            //chi_lookup_values,
        });

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
        /*if round < 24 {
            for k in IOTA_ROUND_BIT_POS {
                b[0][0][k] ^= ((IOTA_ROUND_CST[round] >> k) & 1) as u8;
            }
        }*/
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

#![allow(clippy::needless_range_loop)]

use std::collections::HashMap;

use eth_types::Field;
use eyre::Result;
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    util::{not, or, Expr},
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase, Selector},
    poly::Rotation,
};

use super::{countdown::Countdown, xnif};

/// *
///  This circuit takes a list of values and their lengths
///  and returns
///     - an AssignedCell with the rlc of the first `values_to_accumulate` values
///     - an AssignedCell for each value
///
///  Some restrictions
///     - the length of the values must be fixed per circuit
///
/// *

#[derive(Clone)]
pub struct FixedRlcConfig<F: Field> {
    q_enable: Selector,

    // encoding
    is_lens_config: HashMap<usize, IsZeroConfig<F>>,
    eq_values_config: HashMap<usize, IsZeroConfig<F>>,
    value_col: Column<Advice>,
    len_col: Column<Fixed>,
    bytes_cols: Vec<Column<Advice>>,

    // rlc
    rlc_acc: Column<Advice>,
    rlc_acc_propagate: IsZeroConfig<F>,
    rlc_check_config: HashMap<usize, IsZeroConfig<F>>,

    // count
    countdown: Countdown<F>,
}

impl<F: Field> FixedRlcConfig<F> {
    // **note**, allowed_lens must be fixed per circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        allowed_lens: &[usize],
        rlc_r: Expression<F>,
    ) -> Self {
        let rlc_acc = meta.advice_column_in(SecondPhase);
        let largest = *allowed_lens.iter().max().unwrap();
        let value_col = meta.advice_column();
        let len_col = meta.fixed_column();
        let bytes_cols: Vec<_> = (0..largest).map(|_| meta.advice_column()).collect();
        let q_enable = meta.complex_selector();
        let countdown = Countdown::configure(meta, q_enable);

        meta.enable_equality(value_col);
        meta.enable_equality(rlc_acc);

        // byte encoding constraints

        let is_lens_config: HashMap<_, _> = allowed_lens
            .iter()
            .map(|len| {
                let inv = meta.advice_column();
                let is_zero = IsZeroChip::configure(
                    meta,
                    |meta| meta.query_selector(q_enable),
                    |meta| meta.query_fixed(len_col, Rotation::cur()) - len.expr(),
                    inv,
                );
                (*len, is_zero)
            })
            .collect();

        let eq_values_config: HashMap<_, _> = allowed_lens
            .iter()
            .map(|len| {
                let inv = meta.advice_column();
                let is_zero = IsZeroChip::configure(
                    meta,
                    |meta| meta.query_selector(q_enable) * is_lens_config.get(len).unwrap().expr(),
                    |meta| {
                        let value = meta.query_advice(value_col, Rotation::cur());
                        let mut sum = 0.expr();
                        for i in 0..*len {
                            sum = sum
                                + meta.query_advice(bytes_cols[i], Rotation::cur())
                                    * F::from(256).pow([i as u64]);
                        }
                        value - sum
                    },
                    inv,
                );
                (*len, is_zero)
            })
            .collect();

        meta.create_gate("check that bytes correctly encodes the value", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let switch = eq_values_config
                .values()
                .map(|v| v.expr())
                .collect::<Vec<_>>();
            [q_enable * not::expr(or::expr(switch))]
        });

        // rlc encoding constraints

        let rlc_acc_propagate_inv = meta.advice_column_in(SecondPhase);
        let rlc_acc_propagate = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(rlc_acc, Rotation::cur())
                    - meta.query_advice(rlc_acc, Rotation::next())
            },
            rlc_acc_propagate_inv,
        );

        let rlc_check_config: HashMap<_, _> = allowed_lens
            .iter()
            .map(|len| {
                let inv = meta.advice_column_in(SecondPhase);
                let is_zero = IsZeroChip::configure(
                    meta,
                    |meta| {
                        meta.query_selector(q_enable)
                            * is_lens_config.get(len).unwrap().expr()
                            * not::expr(countdown.is_zero())
                    },
                    |meta| {
                        let mut rlc_acc_cur = meta.query_advice(rlc_acc, Rotation::cur());
                        let rlc_acc_next = meta.query_advice(rlc_acc, Rotation::next());
                        for byte in bytes_cols.iter().take(*len) {
                            rlc_acc_cur = rlc_acc_cur * rlc_r.clone()
                                + meta.query_advice(*byte, Rotation::cur());
                        }
                        rlc_acc_cur - rlc_acc_next
                    },
                    inv,
                );
                (*len, is_zero)
            })
            .collect();

        meta.create_gate("compute next rlc_acc if count > 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let switch = rlc_check_config
                .values()
                .map(|v| v.expr())
                .collect::<Vec<_>>();

            [q_enable * xnif(not::expr(countdown.is_zero()), or::expr(switch))]
        });

        meta.create_gate("propagate rlc_acc if count == 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            [q_enable * xnif(countdown.is_zero(), rlc_acc_propagate.expr())]
        });
        Self {
            eq_values_config,
            rlc_check_config,
            rlc_acc_propagate,
            countdown,
            rlc_acc,
            q_enable,
            value_col,
            len_col,
            bytes_cols,
            is_lens_config,
        }
    }

    #[allow(clippy::type_complexity)]
    // **note**, values.len() and values.x.1 should be fixed per circuit
    // returns the final rlc_acc value
    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        values: Vec<(F, usize)>,
        length: usize, // we only accoumulate the row values
        rlc_r: Value<F>,
    ) -> Result<(AssignedCell<F, F>, Vec<AssignedCell<F, F>>), Error> {
        let ret = layouter.assign_region(
            || "rlc checker",
            |mut region| {
                // name columns

                self.countdown
                    .annotate_columns_in_region(&mut region, "rlc");

                region.name_column(|| "RLC_len", self.len_col);
                region.name_column(|| "RLC_value", self.value_col);
                region.name_column(|| "RLC_acc", self.rlc_acc);
                for (i, col) in self.bytes_cols.iter().enumerate() {
                    region.name_column(|| format!("RLC_byte_{}", i), *col);
                }
                for (len, is_len) in self.is_lens_config.iter() {
                    region.name_column(|| format!("RLC_islen_{}_inv", len), is_len.value_inv);
                }

                let mut value_cells = Vec::new();

                let mut count = F::from(length as u64);
                let mut rlc_acc = Value::known(F::ZERO);
                let mut last_rlc_acc_cell = None;
                let rlc_acc_propagate = IsZeroChip::construct(self.rlc_acc_propagate.clone());

                for (offset, (value, len)) in values.iter().enumerate() {
                    self.q_enable.enable(&mut region, offset)?;

                    for (is_len, is_len_config) in &self.is_lens_config {
                        let is_zero = IsZeroChip::construct(is_len_config.clone());
                        is_zero.assign(
                            &mut region,
                            offset,
                            Value::known(F::from(*len as u64) - F::from(*is_len as u64)),
                        )?;
                    }

                    region.assign_fixed(
                        || "len",
                        self.len_col,
                        offset,
                        || Value::known(F::from(*len as u64)),
                    )?;

                    value_cells.push(region.assign_advice(
                        || "value",
                        self.value_col,
                        offset,
                        || Value::known(*value),
                    )?);

                    // bytes encoding

                    assert!(value.to_repr().iter().skip(*len).all(|b| *b == 0));

                    let bytes = &(&value.to_repr())[0..self.bytes_cols.len()];

                    for (i, b) in bytes.iter().enumerate() {
                        region.assign_advice(
                            || format!("byte {}", i),
                            self.bytes_cols[i],
                            offset,
                            || Value::known(F::from(*b as u64)),
                        )?;
                    }

                    // rlc encoding

                    if offset == 0 {
                        region.assign_advice(
                            || format!("byte {}", 0),
                            self.rlc_acc,
                            offset,
                            || Value::known(F::ZERO),
                        )?;
                    }

                    for (len, rlc_check) in &self.rlc_check_config {
                        let mut rlc_acc_next = rlc_acc;
                        for b in bytes.iter().take(*len) {
                            rlc_acc_next = rlc_acc_next * rlc_r + Value::known(F::from(*b as u64));
                        }
                        IsZeroChip::construct(rlc_check.clone()).assign(
                            &mut region,
                            offset,
                            rlc_acc - rlc_acc_next,
                        )?;
                    }

                    for (len, eq_value) in &self.eq_values_config {
                        let sum = bytes
                            .iter()
                            .take(*len)
                            .fold(F::ZERO, |acc, v| acc + F::from(256) * F::from(*v as u64));
                        IsZeroChip::construct(eq_value.clone()).assign(
                            &mut region,
                            offset,
                            Value::known(*value - sum),
                        )?;
                    }

                    let count_prev = count;
                    let rlc_acc_prev = rlc_acc;
                    if count > F::ZERO {
                        for b in bytes.iter().take(*len) {
                            rlc_acc = rlc_acc * rlc_r + Value::known(F::from(*b as u64));
                        }
                        count -= F::ONE;
                    }
                    self.countdown.assign(
                        &mut region,
                        offset,
                        count_prev,
                        count,
                        offset == values.len() - 1,
                    )?;

                    rlc_acc_propagate.assign(&mut region, offset, rlc_acc_prev - rlc_acc)?;

                    last_rlc_acc_cell = Some(region.assign_advice(
                        || "rlc_acc",
                        self.rlc_acc,
                        offset + 1,
                        || rlc_acc,
                    )?);
                }

                Ok((last_rlc_acc_cell.unwrap(), value_cells))
            },
        )?;

        Ok(ret)
    }
}

#[cfg(test)]
mod test {

    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::SimpleFloorPlanner, dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit,
    };
    use zkevm_circuits::util::Challenges;

    use super::*;

    #[derive(Clone)]
    struct TestCircuitConfig<F: Field> {
        fixed_rlc: FixedRlcConfig<F>,
        challenges: Challenges,
    }

    impl<F: Field> TestCircuitConfig<F> {
        pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
            let challenges = Challenges::construct(meta);
            let rlc_r = challenges.exprs(meta).keccak_input();
            let fixed_rlc = FixedRlcConfig::configure(meta, &[1, 16, 20], rlc_r);
            Self {
                challenges,
                fixed_rlc,
            }
        }
    }

    #[derive(Default)]
    struct TestCircuit<F: Field> {
        _marker: PhantomData<F>,
    }

    impl<F: Field> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
            unreachable!()
        }

        fn params(&self) -> Self::Params {}

        fn configure_with_params(
            meta: &mut ConstraintSystem<F>,
            _params: Self::Params,
        ) -> Self::Config {
            TestCircuitConfig::new(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let challenges = config.challenges.values(&mut layouter);

            let address =
                F::from_str_vartime("1378211552805413204046691570283904042755861616012").unwrap();
            let word_hi = F::from_str_vartime("161608102011034763426291125516264774166").unwrap();
            let byte = F::from_str_vartime("7").unwrap();

            let values = vec![
                (byte, 1),
                (word_hi, 16),
                (address, 20),
                (address, 20),
                (word_hi, 16),
            ];
            let length = 3;

            let (rlc_acc_cell, _) = config.fixed_rlc.assign(
                &mut layouter,
                values.clone(),
                length,
                challenges.keccak_input(),
            )?;

            // check rlc is correct

            let expected_rlc_acc_value = values
                .iter()
                .take(length)
                .flat_map(|(f, n)| f.to_repr()[0..*n].to_vec())
                .fold(Value::known(F::ZERO), |acc, b| {
                    acc * challenges.keccak_input() + Value::known(F::from(b as u64))
                });

            let _ = rlc_acc_cell.value().zip(expected_rlc_acc_value).and_then(
                |(rlc_acc_cell, expected_rlc_acc_value)| {
                    assert_eq!(*rlc_acc_cell, expected_rlc_acc_value);
                    Value::known(F::ZERO)
                },
            );

            Ok(())
        }
    }

    #[test]
    fn test_fixed_rlc_success() {
        let circuit = TestCircuit::default();
        let k = 4;
        let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied_par()
    }
}

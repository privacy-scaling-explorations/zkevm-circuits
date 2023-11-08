use std::collections::HashMap;

use eth_types::{keccak256, Field, H256};
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

use super::xnif;

type Offset = usize;

#[derive(Clone)]
pub enum AlterWitness {
    Rlc(Offset),
    ByteEncoding(Offset),
}

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
    count: Column<Advice>,
    count_is_zero: IsZeroConfig<F>,
    count_propagate: IsZeroConfig<F>,
    count_decrement: IsZeroConfig<F>,

    // for tests
    alter: Option<AlterWitness>,
}

impl<F: Field> FixedRlcConfig<F> {
    // **note**, allowed_lens must be fixed per circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        allowed_lens: &[usize],
        rlc_r: Expression<F>,
        alter: Option<AlterWitness>,
    ) -> Self {
        let rlc_acc = meta.advice_column_in(SecondPhase);
        let largest = *allowed_lens.iter().max().unwrap();
        let count = meta.advice_column();
        let value_col = meta.advice_column();
        let len_col = meta.fixed_column();
        let bytes_cols: Vec<_> = (0..largest).map(|_| meta.advice_column()).collect();
        let q_enable = meta.complex_selector();

        meta.enable_equality(value_col);

        // count constraints

        let count_is_zero_inv = meta.advice_column();
        let count_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(count, Rotation::cur()),
            count_is_zero_inv,
        );

        let count_propagate_inv = meta.advice_column();
        let count_propagate = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(count, Rotation::cur())
                    - meta.query_advice(count, Rotation::next())
            },
            count_propagate_inv,
        );

        let count_decrement_inv = meta.advice_column();
        let count_decrement = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(count, Rotation::cur())
                    - meta.query_advice(count, Rotation::next())
                    - 1.expr()
            },
            count_decrement_inv,
        );

        meta.create_gate("count decrements if > 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            [q_enable * xnif(not::expr(count_is_zero.expr()), count_decrement.expr())]
        });

        meta.create_gate("count propagates if == 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            [q_enable * xnif(count_is_zero.expr(), count_propagate.expr())]
        });

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
                    |meta| meta.query_selector(q_enable) * is_lens_config.get(len).unwrap().expr(),
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

            [q_enable * xnif(not::expr(count_is_zero.expr()), or::expr(switch))]
        });

        meta.create_gate("propagate rlc_acc if count == 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            [q_enable * xnif(count_is_zero.expr(), rlc_acc_propagate.expr())]
        });
        Self {
            alter,
            eq_values_config,
            rlc_check_config,
            rlc_acc_propagate,
            count_propagate,
            count_decrement,
            count_is_zero,
            count,
            rlc_acc,
            q_enable,
            value_col,
            len_col,
            bytes_cols,
            is_lens_config,
        }
    }

    pub fn hash(values: Vec<(F, usize)>) -> H256 {
        // TODO: update digest incrementally
        let mut bytes = Vec::new();
        for (value, len) in values {
            let mut value = value.to_repr()[0..len].to_vec();
            bytes.append(&mut value);
        }
        H256::from(keccak256(&bytes))
    }

    #[allow(clippy::type_complexity)]
    // **note**, values.len() and values.x.1 should be fixed per circuit
    // returns the final rlc_acc value
    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        values: Vec<(F, usize)>,
        values_to_accumulate: usize, // we only accoumulate the first values
        rlc_r: Value<F>,
    ) -> Result<(AssignedCell<F, F>, Vec<AssignedCell<F, F>>), Error> {
        let ret = layouter.assign_region(
            || "rlc checker",
            |mut region| {
                let mut value_cells = Vec::new();

                region.name_column(|| "RLC_len", self.len_col);
                region.name_column(|| "RLC_value", self.value_col);
                region.name_column(|| "RLC_acc", self.rlc_acc);
                for (i, col) in self.bytes_cols.iter().enumerate() {
                    region.name_column(|| format!("RLC_byte_{}", i), *col);
                }
                for (len, is_len) in self.is_lens_config.iter() {
                    region.name_column(|| format!("RLC_islen_{}_inv", len), is_len.value_inv);
                }
                region.name_column(|| "RLC_count", self.count);

                region.name_column(|| "RLC_count_is_zero_inv", self.count_is_zero.value_inv);
                region.name_column(|| "RLC_count_propagate_inv", self.count_propagate.value_inv);
                region.name_column(|| "RLC_count_decrement_inv", self.count_decrement.value_inv);

                let mut count = F::from(values_to_accumulate as u64 + 1);
                let mut rlc_acc = Value::known(F::ZERO);
                let mut last_rlc_acc_cell = None;

                let count_is_zero = IsZeroChip::construct(self.count_is_zero.clone());
                let rlc_acc_propagate = IsZeroChip::construct(self.rlc_acc_propagate.clone());
                let count_propagate = IsZeroChip::construct(self.count_propagate.clone());
                let count_decrement = IsZeroChip::construct(self.count_decrement.clone());

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

                    region.assign_advice(|| "count", self.count, offset, || Value::known(count))?;
                    count_is_zero.assign(&mut region, offset, Value::known(count))?;

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
                        let mut b = *b;
                        if let Some(AlterWitness::ByteEncoding(alter_offset)) = self.alter {
                            if offset == alter_offset {
                                let (b_1, _) = b.overflowing_add(1);
                                b = b_1;
                            }
                        }
                        region.assign_advice(
                            || format!("byte {}", i),
                            self.bytes_cols[i],
                            offset,
                            || Value::known(F::from(b as u64)),
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
                        let mut sum = F::ZERO;
                        for i in 0..*len {
                            sum = sum * F::from(256) + F::from(bytes[i] as u64);
                        }
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
                        if let Some(AlterWitness::Rlc(alter_offset)) = self.alter {
                            if offset == alter_offset {
                                rlc_acc = rlc_acc + Value::known(F::ONE);
                            }
                        }
                        count -= F::ONE;
                    }

                    count_propagate.assign(
                        &mut region,
                        offset,
                        Value::known(count_prev - count),
                    )?;
                    count_decrement.assign(
                        &mut region,
                        offset,
                        Value::known(count_prev - count - F::ONE),
                    )?;

                    rlc_acc_propagate.assign(&mut region, offset, rlc_acc_prev - rlc_acc)?;

                    last_rlc_acc_cell = Some(region.assign_advice(
                        || "rlc_acc",
                        self.rlc_acc,
                        offset + 1,
                        || rlc_acc,
                    )?);
                }

                region.assign_advice(
                    || "count",
                    self.count,
                    values.len(),
                    || Value::known(count),
                )?;

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
        pub(crate) fn new(meta: &mut ConstraintSystem<F>, alter: Option<AlterWitness>) -> Self {
            let challenges = Challenges::construct(meta);
            let rlc_r = challenges.exprs(meta).keccak_input();
            let fixed_rlc = FixedRlcConfig::configure(meta, &[1, 16, 20], rlc_r, alter);
            Self {
                challenges,
                fixed_rlc,
            }
        }
    }

    #[derive(Default)]
    struct TestCircuit<F: Field> {
        alter: Option<AlterWitness>,
        _marker: PhantomData<F>,
    }

    impl<F: Field> TestCircuit<F> {
        pub(crate) fn alter(alter: AlterWitness) -> Self {
            Self {
                alter: Some(alter),
                _marker: PhantomData,
            }
        }
    }

    impl<F: Field> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = Option<AlterWitness>;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
            unreachable!()
        }

        fn params(&self) -> Self::Params {
            self.alter.clone()
        }

        fn configure_with_params(
            meta: &mut ConstraintSystem<F>,
            params: Self::Params,
        ) -> Self::Config {
            TestCircuitConfig::new(meta, params)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let challenges = config.challenges.values(&mut layouter);

            config.fixed_rlc.assign(
                &mut layouter,
                vec![(F::from(7), 1), (F::from(0xF1F2), 16), (F::from(0xF1F2), 16)],
                2,
                challenges.keccak_input(),
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_fixed_rlc() {
        let circuit = TestCircuit::default();
        let k = 4;
        let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied_par()
    }

    #[test]
    fn test_fixed_rlc_bad_byte_encoding() {
        let circuit = TestCircuit::alter(AlterWitness::ByteEncoding(0));
        let k = 4;
        let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify_par().is_err());
    }

    #[test]
    fn test_fixed_rlc_bad_rlc() {
        let circuit = TestCircuit::alter(AlterWitness::Rlc(0));
        let k = 4;
        let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify_par().is_err());
    }

}

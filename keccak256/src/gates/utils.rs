use crate::gates::gate_helpers::CellF;
use pairing::arithmetic::FieldExt;

use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct RunningSum<F> {
    q_enable: Selector,
    x: Column<Advice>,
    acc: Column<Advice>,
    _marker: PhantomData<F>,
}

/// Perform Running Sum
///
/// Copy cells from an input column
/// Enforce a cell in an output column to be the sum of the input cells.
///
/// |offset | x |  acc|
/// |-------|---|-----|
/// |0      | _ |  0  |
/// |1      | 3 |  3  |
/// |2      | 5 |  8  |
/// |3      | 1 |  9  |
impl<F: FieldExt> RunningSum<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        input: Column<Advice>,
        output: Column<Advice>,
    ) -> Self {
        let q_enable = meta.selector();
        let x = meta.advice_column();
        let acc = meta.advice_column();
        meta.enable_equality(input.into());
        meta.enable_equality(output.into());
        meta.enable_equality(x.into());
        meta.enable_equality(acc.into());

        meta.create_gate("Running sum", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let x = meta.query_advice(x, Rotation::cur());
            let acc_prev = meta.query_advice(acc, Rotation::prev());
            let acc = meta.query_advice(acc, Rotation::cur());

            vec![("running sum", q_enable * (acc - acc_prev - x))]
        });

        Self {
            q_enable,
            x,
            acc,
            _marker: PhantomData,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        initial: Option<CellF<F>>,
        cells: Vec<CellF<F>>,
    ) -> Result<(CellF<F>, CellF<F>), Error> {
        let (initial, sum) = layouter.assign_region(
            || "running sum",
            |mut region| {
                let mut offset = 0;
                let value = match initial.clone() {
                    Some(cell_f) => cell_f.value,
                    None => F::zero(),
                };
                let cell = region.assign_advice(
                    || "initial",
                    self.acc,
                    offset,
                    || Ok(value),
                )?;
                match &initial {
                    Some(cell_f) => {
                        region.constrain_equal(cell_f.cell, cell)?;
                    }
                    None => {}
                };
                offset += 1;
                let initial = CellF { cell, value };

                let sum: Result<CellF<F>, Error> =
                    cells.iter().try_fold(initial.clone(), |acc_cell, x| {
                        let x_cell = region.assign_advice(
                            || "x",
                            self.x,
                            offset,
                            || Ok(x.value),
                        )?;
                        region.constrain_equal(x.cell, x_cell)?;
                        self.q_enable.enable(&mut region, offset)?;

                        let value = acc_cell.value + x.value;
                        let cell = region.assign_advice(
                            || "acc",
                            self.acc,
                            offset,
                            || Ok(value),
                        )?;
                        offset += 1;

                        Ok(CellF { cell, value })
                    });
                let sum = sum?;
                Ok((initial, sum))
            },
        )?;
        Ok((initial, sum))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use pairing::arithmetic::FieldExt;
    use pairing::bn256::Fr as Fp;
    use pretty_assertions::assert_eq;
    #[test]
    fn test_running_sum() {
        #[derive(Debug, Clone)]
        struct MyAppConfig<F> {
            input: Column<Advice>,
            output: Column<Advice>,
            running_sum: RunningSum<F>,
        }

        impl<F: FieldExt> MyAppConfig<F> {
            fn configure(
                meta: &mut ConstraintSystem<F>,
                input: Column<Advice>,
                output: Column<Advice>,
            ) -> Self {
                let running_sum = RunningSum::configure(meta, input, output);
                Self {
                    input,
                    output,
                    running_sum,
                }
            }
            fn assign_region(
                &self,
                layouter: &mut impl Layouter<F>,
                values: Vec<F>,
            ) -> Result<(F, F), Error> {
                let cells = layouter.assign_region(
                    || "assign input",
                    |mut region| {
                        let cells: Vec<CellF<F>> = values
                            .iter()
                            .enumerate()
                            .map(|(offset, &value)| {
                                let cell = region
                                    .assign_advice(
                                        || "input",
                                        self.input,
                                        offset,
                                        || Ok(value),
                                    )
                                    .unwrap();

                                CellF { cell, value }
                            })
                            .collect::<Vec<CellF<F>>>();
                        Ok(cells)
                    },
                )?;
                let (initial, sum) =
                    self.running_sum.assign_region(layouter, None, cells)?;
                layouter.assign_region(
                    || "assign output",
                    |mut region| {
                        let offset = 0;
                        let cell = region.assign_advice(
                            || "output",
                            self.output,
                            offset,
                            || {
                                Ok(values
                                    .iter()
                                    .fold(F::zero(), |acc, &x| acc + x))
                            },
                        )?;
                        region.constrain_equal(cell, sum.cell)?;
                        Ok(())
                    },
                )?;
                Ok((initial.value, sum.value))
            }
        }

        #[derive(Default)]
        struct MyCircuit<F> {
            values: Vec<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = MyAppConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let input = meta.advice_column();
                let output = meta.advice_column();
                Self::Config::configure(meta, input, output)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.assign_region(&mut layouter, self.values.clone())?;
                Ok(())
            }
        }

        let circuit = MyCircuit::<Fp> {
            values: vec![
                Fp::from(1),
                Fp::from(2),
                Fp::from(3),
                Fp::from(4),
                Fp::from(5),
            ],
        };
        let prover = MockProver::<Fp>::run(5, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}

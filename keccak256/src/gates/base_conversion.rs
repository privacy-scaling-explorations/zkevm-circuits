use halo2::{
    circuit::{Cell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

use crate::gates::base_eval::BaseEvaluationConfig;
use crate::gates::tables::BaseInfo;
use pairing::arithmetic::FieldExt;

#[derive(Clone, Debug)]
pub struct BaseConversionConfig<F> {
    q_enable: Selector,
    bi: BaseInfo<F>,
    lane: Column<Advice>,
    input_eval: BaseEvaluationConfig<F>,
    output_eval: BaseEvaluationConfig<F>,
}

impl<F: FieldExt> BaseConversionConfig<F> {
    /// Side effect: lane is equality enabled
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        bi: BaseInfo<F>,
        lane: Column<Advice>,
    ) -> Self {
        let q_enable = meta.complex_selector();

        let input_eval =
            BaseEvaluationConfig::configure(meta, bi.input_pob(), lane);
        let output_eval =
            BaseEvaluationConfig::configure(meta, bi.output_pob(), lane);

        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let input_slices =
                meta.query_advice(input_eval.coef, Rotation::cur());
            let output_slices =
                meta.query_advice(output_eval.coef, Rotation::cur());
            vec![
                (q_enable.clone() * input_slices, bi.input_tc),
                (q_enable * output_slices, bi.output_tc),
            ]
        });

        Self {
            q_enable,
            bi,
            lane,
            input_eval,
            output_eval,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input: (Cell, F),
    ) -> Result<(Cell, F), Error> {
        let (input_coefs, output_coefs, output) =
            self.bi.compute_coefs(input.1)?;

        let output_cell = layouter.assign_region(
            || "lane",
            |mut region| {
                let output_cell = region.assign_advice(
                    || "lane output",
                    self.lane,
                    0,
                    || Ok(output),
                )?;

                Ok(output_cell)
            },
        )?;

        layouter.assign_region(
            || "Base conversion",
            |mut region| {
                for (offset, _) in input_coefs.iter().enumerate() {
                    self.q_enable.enable(&mut region, offset)?;
                }
                self.input_eval.assign_region(
                    &mut region,
                    input.0,
                    &input_coefs,
                )?;

                self.output_eval.assign_region(
                    &mut region,
                    output_cell,
                    &output_coefs,
                )?;
                Ok(())
            },
        )?;

        Ok((output_cell, output))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::convert_b2_to_b13;
    use crate::gates::{
        gate_helpers::biguint_to_f, tables::FromBinaryTableConfig,
    };
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use pairing::arithmetic::FieldExt;
    use pairing::bn256::Fr as Fp;
    use pretty_assertions::assert_eq;
    #[test]
    fn test_base_conversion() {
        // We have to use a MyConfig because:
        // We need to load the table
        #[derive(Debug, Clone)]
        struct MyConfig<F> {
            lane: Column<Advice>,
            table: FromBinaryTableConfig<F>,
            conversion: BaseConversionConfig<F>,
        }
        impl<F: FieldExt> MyConfig<F> {
            pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
                let table = FromBinaryTableConfig::configure(meta);
                let lane = meta.advice_column();
                let bi = table.get_base_info(false);
                let conversion =
                    BaseConversionConfig::configure(meta, bi, lane);
                Self {
                    lane,
                    table,
                    conversion,
                }
            }

            pub fn load(
                &self,
                layouter: &mut impl Layouter<F>,
            ) -> Result<(), Error> {
                self.table.load(layouter)
            }

            pub fn assign_region(
                &self,
                layouter: &mut impl Layouter<F>,
                input: F,
            ) -> Result<F, Error> {
                let cell = layouter.assign_region(
                    || "Input lane",
                    |mut region| {
                        region.assign_advice(
                            || "Input lane",
                            self.lane,
                            0,
                            || Ok(input),
                        )
                    },
                )?;
                let output =
                    self.conversion.assign_region(layouter, (cell, input))?;
                Ok(output.1)
            }
        }

        #[derive(Default)]
        struct MyCircuit<F> {
            input_b2_lane: F,
            output_b13_lane: F,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Self::Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;
                let output =
                    config.assign_region(&mut layouter, self.input_b2_lane)?;
                assert_eq!(output, self.output_b13_lane);
                Ok(())
            }
        }
        let input = 12345678u64;
        let circuit = MyCircuit::<Fp> {
            input_b2_lane: Fp::from(input),
            output_b13_lane: biguint_to_f::<Fp>(&convert_b2_to_b13(input))
                .unwrap(),
        };
        let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}

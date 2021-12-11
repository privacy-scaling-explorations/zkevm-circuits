use halo2::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};

use crate::arith_helpers::{convert_b2_to_b13, mod_u64};
use crate::gates::base_eval::BaseEvaluationConfig;
use crate::gates::gate_helpers::f_to_biguint;
use crate::gates::gate_helpers::CellF;
use pairing::arithmetic::FieldExt;

#[derive(Clone, Debug)]
struct BaseConversionConfig<F> {
    q_enable: Selector,
    num_chunks: usize,
    input_base: u64,
    output_base: u64,
    input_table_col: TableColumn,
    output_table_col: TableColumn,
    input_eval: BaseEvaluationConfig<F>,
    output_eval: BaseEvaluationConfig<F>,
}

impl<F: FieldExt> BaseConversionConfig<F> {
    /// Side effect: input_lane and output_lane are equality enabled
    fn configure(
        meta: &mut ConstraintSystem<F>,
        num_chunks: usize,
        input_base: u64,
        output_base: u64,
        input_table_col: TableColumn,
        output_table_col: TableColumn,
        input_lane: Column<Advice>,
        output_lane: Column<Advice>,
    ) -> Self {
        let q_enable = meta.complex_selector();
        let input_pob = F::from(input_base.pow(num_chunks as u32));
        let output_pob = F::from(output_base.pow(num_chunks as u32));

        let input_eval =
            BaseEvaluationConfig::configure(meta, input_pob, input_lane);
        let output_eval =
            BaseEvaluationConfig::configure(meta, output_pob, output_lane);

        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let input_slices =
                meta.query_advice(input_eval.coef, Rotation::cur());
            let output_slices =
                meta.query_advice(output_eval.coef, Rotation::cur());
            vec![
                (q_enable.clone() * input_slices, input_table_col),
                (q_enable * output_slices, output_table_col),
            ]
        });

        Self {
            q_enable,
            num_chunks,
            input_base,
            output_base,
            input_table_col,
            output_table_col,
            input_eval,
            output_eval,
        }
    }

    fn compute_coefs(&self, input: F) -> Result<(Vec<F>, Vec<F>), Error> {
        // big-endian
        let input_chunks: Vec<u64> = {
            let mut raw = f_to_biguint(input).ok_or(Error::Synthesis)?;
            // little endian
            let mut input_chunks: Vec<u64> = (0..64)
                .map(|_| {
                    let remainder: u64 = mod_u64(&raw, self.input_base);
                    raw /= self.input_base;
                    remainder
                })
                .collect();
            // big endian
            input_chunks.reverse();
            input_chunks
        };
        let input_coefs: Vec<F> = input_chunks
            .chunks(self.num_chunks)
            .map(|chunks| {
                let coef = chunks
                    .iter()
                    // big endian
                    .fold(0, |acc, &x| acc * self.input_base + x);
                F::from(coef)
            })
            .collect();

        let output_coefs: Vec<F> = input_chunks
            .chunks(self.num_chunks)
            .map(|chunks| {
                let coef =
                    chunks.iter().fold(0, |acc, &x| acc * self.output_base + x);
                F::from(coef)
            })
            .collect();
        Ok((input_coefs, output_coefs))
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input_lane: CellF<F>,
        output_lane: CellF<F>,
    ) -> Result<(), Error> {
        let (input_coefs, output_coefs) =
            self.compute_coefs(input_lane.value)?;
        self.input_eval
            .assign_region(layouter, input_lane, &input_coefs)?;
        self.output_eval
            .assign_region(layouter, output_lane, &output_coefs)?;
        Ok(())
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
        const INPUT_BASE: u64 = 2;
        const OUTPUT_BASE: u64 = 13;

        #[derive(Debug, Clone)]
        struct MyConfig<F> {
            input_lane: Column<Advice>,
            output_lane: Column<Advice>,
            table: FromBinaryTableConfig<F>,
            conversion: BaseConversionConfig<F>,
        }
        impl<F: FieldExt> MyConfig<F> {
            pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
                let table = FromBinaryTableConfig::configure(meta);
                let input_lane = meta.advice_column();
                let output_lane = meta.advice_column();
                let conversion = BaseConversionConfig::configure(
                    meta,
                    table.num_chunks(),
                    INPUT_BASE,
                    OUTPUT_BASE,
                    table.base2,
                    table.base13,
                    input_lane,
                    output_lane,
                );
                Self {
                    input_lane,
                    output_lane,
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
                input_value: F,
                output_value: F,
            ) -> Result<(), Error> {
                let (input_lane, output_lane) = layouter.assign_region(
                    || "I/O values",
                    |mut region| {
                        let input_lane = region.assign_advice(
                            || "input lane",
                            self.input_lane,
                            0,
                            || Ok(input_value),
                        )?;
                        let output_lane = region.assign_advice(
                            || "output lane",
                            self.output_lane,
                            0,
                            || Ok(output_value),
                        )?;

                        Ok((
                            CellF {
                                cell: input_lane,
                                value: input_value,
                            },
                            CellF {
                                cell: output_lane,
                                value: output_value,
                            },
                        ))
                    },
                )?;
                self.conversion.assign_region(
                    layouter,
                    input_lane,
                    output_lane,
                )?;
                Ok(())
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
                config.assign_region(
                    &mut layouter,
                    self.input_b2_lane,
                    self.output_b13_lane,
                )?;
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

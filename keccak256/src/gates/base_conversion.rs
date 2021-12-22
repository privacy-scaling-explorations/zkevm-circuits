use halo2::{
    circuit::{Cell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

use crate::gates::tables::BaseInfo;
use pairing::arithmetic::FieldExt;

#[derive(Clone, Debug)]
pub struct BaseConversionConfig<F> {
    q_running_sum: Selector,
    q_lookup: Selector,
    bi: BaseInfo<F>,
    input_lane: Column<Advice>,
    input_coef: Column<Advice>,
    input_acc: Column<Advice>,
    output_coef: Column<Advice>,
    output_acc: Column<Advice>,
}

impl<F: FieldExt> BaseConversionConfig<F> {
    /// Side effect: lane is equality enabled
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        bi: BaseInfo<F>,
        input_lane: Column<Advice>,
    ) -> Self {
        let q_running_sum = meta.selector();
        let q_lookup = meta.complex_selector();
        let input_coef = meta.advice_column();
        let input_acc = meta.advice_column();
        let output_coef = meta.advice_column();
        let output_acc = meta.advice_column();

        meta.enable_equality(input_coef.into());
        meta.enable_equality(input_acc.into());
        meta.enable_equality(output_coef.into());
        meta.enable_equality(output_acc.into());
        meta.enable_equality(input_lane.into());

        meta.create_gate("input running sum", |meta| {
            let q_enable = meta.query_selector(q_running_sum);
            let coef = meta.query_advice(input_coef, Rotation::cur());
            let acc_prev = meta.query_advice(input_acc, Rotation::prev());
            let acc = meta.query_advice(input_acc, Rotation::cur());
            let power_of_base = bi.input_pob();
            vec![q_enable * (acc - acc_prev * power_of_base - coef)]
        });
        meta.create_gate("output running sum", |meta| {
            let q_enable = meta.query_selector(q_running_sum);
            let coef = meta.query_advice(output_coef, Rotation::cur());
            let acc_prev = meta.query_advice(output_acc, Rotation::prev());
            let acc = meta.query_advice(output_acc, Rotation::cur());
            let power_of_base = bi.output_pob();
            vec![q_enable * (acc - acc_prev * power_of_base - coef)]
        });
        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_lookup);
            let input_slices = meta.query_advice(input_coef, Rotation::cur());
            let output_slices = meta.query_advice(output_coef, Rotation::cur());
            vec![
                (q_enable.clone() * input_slices, bi.input_tc),
                (q_enable * output_slices, bi.output_tc),
            ]
        });

        Self {
            q_running_sum,
            q_lookup,
            bi,
            input_lane,
            input_coef,
            input_acc,
            output_coef,
            output_acc,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input: (Cell, F),
    ) -> Result<(Cell, F), Error> {
        let (input_coefs, output_coefs, _) = self.bi.compute_coefs(input.1)?;

        let (out_cell, out_value) = layouter.assign_region(
            || "Base conversion",
            |mut region| {
                let mut input_acc = F::zero();
                let input_pob = self.bi.input_pob();
                let mut output_acc = F::zero();
                let output_pob = self.bi.output_pob();
                for (offset, (&input_coef, &output_coef)) in
                    input_coefs.iter().zip(output_coefs.iter()).enumerate()
                {
                    self.q_lookup.enable(&mut region, offset)?;
                    if offset != 0 {
                        self.q_running_sum.enable(&mut region, offset)?;
                    }
                    let input_coef_cell = region.assign_advice(
                        || "Input Coef",
                        self.input_coef,
                        offset,
                        || Ok(input_coef),
                    )?;
                    input_acc = input_acc * input_pob + input_coef;
                    let input_acc_cell = region.assign_advice(
                        || "Input Acc",
                        self.input_acc,
                        offset,
                        || Ok(input_acc),
                    )?;
                    let output_coef_cell = region.assign_advice(
                        || "Output Coef",
                        self.output_coef,
                        offset,
                        || Ok(output_coef),
                    )?;
                    output_acc = output_acc * output_pob + output_coef;
                    let output_acc_cell = region.assign_advice(
                        || "Output Acc",
                        self.output_acc,
                        offset,
                        || Ok(output_acc),
                    )?;

                    if offset == 0 {
                        // bind first acc to first coef
                        region
                            .constrain_equal(input_acc_cell, input_coef_cell)?;
                        region.constrain_equal(
                            output_acc_cell,
                            output_coef_cell,
                        )?;
                    } else if offset == input_coefs.len() - 1 {
                        region.constrain_equal(input_acc_cell, input.0)?;
                        return Ok((output_acc_cell, output_acc));
                    }
                }
                unreachable!();
            },
        )?;

        Ok((out_cell, out_value))
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
                layouter.assign_region(
                    || "Input lane",
                    |mut region| {
                        let cell = region.assign_advice(
                            || "Output lane",
                            self.lane,
                            0,
                            || Ok(output.1),
                        )?;
                        region.constrain_equal(cell, output.0)?;
                        Ok(())
                    },
                )?;
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
        let k = 17;

        #[cfg(feature = "dev-graph")]
        {
            use plotters::prelude::*;
            let root = BitMapBackend::new("base-conversion.png", (1024, 32768))
                .into_drawing_area();
            root.fill(&WHITE).unwrap();
            let root =
                root.titled("Base conversion", ("sans-serif", 60)).unwrap();
            halo2::dev::CircuitLayout::default()
                .mark_equality_cells(true)
                .render(k, &circuit, &root)
                .unwrap();
        }
        let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}

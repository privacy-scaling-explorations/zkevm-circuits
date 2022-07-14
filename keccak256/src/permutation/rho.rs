use crate::common::ROTATION_CONSTANTS;
use crate::gate_helpers::{biguint_to_f, f_to_biguint};
use crate::permutation::{
    generic::GenericConfig,
    rho_helpers::{slice_lane, RhoLane},
    tables::{Base13toBase9TableConfig, StackableTable},
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use itertools::Itertools;
use std::{convert::TryInto, vec};

pub fn assign_rho<F: Field>(
    layouter: &mut impl Layouter<F>,
    base13to9_config: &Base13toBase9TableConfig<F>,
    generic: &GenericConfig<F>,
    stackable: &StackableTable<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let mut next_state = vec![];
    let mut step2_od_join = vec![];
    let mut step3_od_join = vec![];
    for (lane_idx, lane) in state.iter().enumerate() {
        let rotation = {
            let x = lane_idx / 5;
            let y = lane_idx % 5;
            ROTATION_CONSTANTS[x][y]
        };
        let (conversions, special) =
            RhoLane::new(f_to_biguint(*lane.value().unwrap_or(&F::zero())), rotation)
                .get_full_witness();
        let slices = slice_lane(rotation);

        let (input_coefs, mut output_coefs, step2_od, step3_od) =
            base13to9_config.assign_region(layouter, &slices, &conversions)?;

        let input_pobs = conversions
            .iter()
            .map(|c| biguint_to_f::<F>(&c.input.power_of_base))
            .collect_vec();

        let mut output_pobs = conversions
            .iter()
            .map(|c| biguint_to_f::<F>(&c.output.power_of_base))
            .collect_vec();
        // Final output power of base
        output_pobs.push(biguint_to_f::<F>(&special.output_pob));

        let input_from_chunks =
            generic.linear_combine_consts(layouter, input_coefs, input_pobs, None)?;
        let last_chunk = generic.sub_advice(layouter, lane.clone(), input_from_chunks)?;

        let final_output_coef = stackable.lookup_special_chunks(layouter, &last_chunk)?;
        output_coefs.push(final_output_coef);

        let output_lane =
            generic.linear_combine_consts(layouter, output_coefs, output_pobs, None)?;
        next_state.push(output_lane);
        step2_od_join.extend(step2_od);
        step3_od_join.extend(step3_od);
    }
    let step2_sum = generic.running_sum(layouter, step2_od_join, None)?;
    let step3_sum = generic.running_sum(layouter, step3_od_join, None)?;
    stackable.lookup_range_12(layouter, &[step2_sum])?;
    stackable.lookup_range_169(layouter, &[step3_sum])?;
    Ok(next_state.try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::{convert_b2_to_b13, StateBigInt};
    use crate::common::*;
    use crate::gate_helpers::biguint_to_f;
    use crate::keccak_arith::*;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pairing::bn256::Fr as Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, TableColumn},
    };
    use itertools::Itertools;
    use pretty_assertions::assert_eq;
    use std::convert::TryInto;

    #[test]
    fn test_rho_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
        }

        #[derive(Clone)]
        struct MyConfig<F> {
            advice: Column<Advice>,
            generic: GenericConfig<F>,
            stackable: StackableTable<F>,
            base13to9_config: Base13toBase9TableConfig<F>,
        }
        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let advices: [Column<Advice>; 3] = (0..3)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let fixed = meta.fixed_column();
                let stackable_cols: [TableColumn; 3] = (0..3)
                    .map(|_| meta.lookup_table_column())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let base13to9_cols: [TableColumn; 3] = (0..3)
                    .map(|_| meta.lookup_table_column())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let stackable = StackableTable::configure(meta, advices, stackable_cols);
                let generic = GenericConfig::configure(meta, advices, fixed);
                let base13to9_config =
                    Base13toBase9TableConfig::configure(meta, advices, base13to9_cols);

                Self::Config {
                    advice: advices[0],
                    generic,
                    stackable,
                    base13to9_config,
                }
            }

            fn synthesize(
                &self,
                mut config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.base13to9_config.load(&mut layouter)?;
                config.stackable.load(&mut layouter)?;
                let state = layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let state = self
                            .in_state
                            .iter()
                            .enumerate()
                            .map(|(offset, &value)| {
                                region.assign_advice(|| "lane", config.advice, offset, || Ok(value))
                            })
                            .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;

                        Ok(state.try_into().unwrap())
                    },
                )?;
                let out_state = assign_rho(
                    &mut layouter,
                    &config.base13to9_config,
                    &config.generic,
                    &config.stackable,
                    &state,
                )?;
                layouter.assign_region(
                    || "check final states",
                    |mut region| {
                        for (assigned, value) in out_state.iter().zip(self.out_state.iter()) {
                            region.constrain_constant(assigned.cell(), value)?;
                        }
                        Ok(())
                    },
                )?;

                Ok(())
            }
        }

        let input1: State = [
            [102, 111, 111, 98, 97],
            [114, 0, 5, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 5, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
        }
        let s0_arith = KeccakFArith::theta(&in_biguint);
        for (x, y) in (0..5).cartesian_product(0..5) {
            in_state[5 * x + y] = biguint_to_f(&s0_arith[(x, y)]);
        }
        let s1_arith = KeccakFArith::rho(&s0_arith);
        let mut out_state: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = biguint_to_f(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<Fp> {
            in_state,
            out_state,
        };
        let k = 15;
        #[cfg(feature = "dev-graph")]
        {
            use plotters::prelude::*;
            let root =
                BitMapBackend::new("rho-test-circuit.png", (1024, 16384)).into_drawing_area();
            root.fill(&WHITE).unwrap();
            let root = root.titled("Rho", ("sans-serif", 60)).unwrap();
            halo2_proofs::dev::CircuitLayout::default()
                .render(k, &circuit, &root)
                .unwrap();
        }
        // Test without public inputs
        let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}

use itertools::Itertools;
use std::marker::PhantomData;
use strum::IntoEnumIterator;

use super::util::StoredExpression;
use super::*;
use crate::evm_circuit::param::{MAX_STEP_HEIGHT, STEP_WIDTH};
use crate::evm_circuit::step::Step;
use crate::evm_circuit::table::{FixedTableTag, Table};
use crate::evm_circuit::util::{rlc, CellType};
use crate::evm_circuit::{Advice, Column, Fixed};
use crate::table::LookupTable;
use crate::{evm_circuit::step::ExecutionState, util::power_of_randomness_from_instance};
use eth_types::{Word, U256};
use halo2_proofs::circuit::Layouter;
use halo2_proofs::plonk::{ConstraintSystem, Selector};
use halo2_proofs::plonk::{Error, Expression};
use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};

pub(crate) const WORD_LOW_MAX: Word = U256([u64::MAX, u64::MAX, 0, 0]);
pub(crate) const WORD_HIGH_MAX: Word = U256([0, 0, u64::MAX, u64::MAX]);

pub(crate) trait MathGadgetContainer<F: Field>: Clone {
    const NAME: &'static str;

    fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self
    where
        Self: Sized;

    fn assign_gadget_container(
        &self,
        input_words: &[Word],
        region: &mut CachedRegion<'_, '_, F>,
    ) -> Result<(), Error>;
}

#[derive(Debug, Clone)]
pub(crate) struct UnitTestMathGadgetBaseCircuitConfig<F: Field, G>
where
    G: MathGadgetContainer<F>,
{
    q_usable: Selector,
    fixed_table: [Column<Fixed>; 4],
    advices: [Column<Advice>; STEP_WIDTH],
    step: Step<F>,
    stored_expressions: Vec<StoredExpression<F>>,
    math_gadget_container: G,
    _marker: PhantomData<F>,
    power_of_randomness: [Expression<F>; 31],
}

pub(crate) struct UnitTestMathGadgetBaseCircuit<F, G> {
    size: usize,
    input_words: Vec<Word>,
    randomness: F,
    _marker: PhantomData<G>,
}

impl<F: Field, G> UnitTestMathGadgetBaseCircuit<F, G> {
    fn new(size: usize, input_words: Vec<Word>, randomness: F) -> Self {
        UnitTestMathGadgetBaseCircuit {
            size,
            input_words,
            randomness,
            _marker: PhantomData,
        }
    }
}

impl<F: Field, G: MathGadgetContainer<F>> Circuit<F> for UnitTestMathGadgetBaseCircuit<F, G> {
    type Config = UnitTestMathGadgetBaseCircuitConfig<F, G>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        UnitTestMathGadgetBaseCircuit {
            size: 0,
            input_words: vec![],
            randomness: F::from(123456u64),
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_usable = meta.selector();
        let fixed_table = [(); 4].map(|_| meta.fixed_column());
        let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());
        let step_curr = Step::new(meta, advices, 0, false);
        let step_next = Step::new(meta, advices, MAX_STEP_HEIGHT, true);
        let power_of_randomness = power_of_randomness_from_instance(meta);

        let mut cb = ConstraintBuilder::new(
            step_curr.clone(),
            step_next,
            &power_of_randomness,
            ExecutionState::STOP,
        );
        let math_gadget_container = G::configure_gadget_container(&mut cb);
        let (constraints, stored_expressions, _) = cb.build();

        if !constraints.step.is_empty() {
            let step_constraints = constraints.step;
            meta.create_gate(G::NAME, |meta| {
                let q_usable = meta.query_selector(q_usable);
                step_constraints
                    .into_iter()
                    .map(move |(name, constraint)| (name, q_usable.clone() * constraint))
            });
        }

        let cell_manager = step_curr.cell_manager.clone();
        for column in cell_manager.columns().iter() {
            if let CellType::Lookup(table) = column.cell_type {
                if table == Table::Fixed {
                    let name = format!("{:?}", table);
                    meta.lookup_any(Box::leak(name.into_boxed_str()), |meta| {
                        let table_expressions = fixed_table.table_exprs(meta);
                        vec![(
                            column.expr(),
                            rlc::expr(&table_expressions, &power_of_randomness),
                        )]
                    });
                }
            }
        }

        UnitTestMathGadgetBaseCircuitConfig::<F, G> {
            q_usable,
            fixed_table,
            advices,
            step: step_curr,
            stored_expressions,
            math_gadget_container,
            _marker: PhantomData,
            power_of_randomness,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign test container",
            |mut region| {
                let offset = 0;
                config.q_usable.enable(&mut region, offset)?;
                let power_of_randomness = [(); 31].map(|_| self.randomness);
                let cached_region = &mut CachedRegion::<'_, '_, F>::new(
                    &mut region,
                    power_of_randomness,
                    STEP_WIDTH,
                    MAX_STEP_HEIGHT * 3,
                    config.advices[0].index(), // TODO
                    offset,
                );
                config.step.state.execution_state.assign(
                    cached_region,
                    offset,
                    ExecutionState::STOP as usize,
                )?;
                config
                    .math_gadget_container
                    .assign_gadget_container(&self.input_words, cached_region)?;
                for stored_expr in &config.stored_expressions {
                    stored_expr.assign(cached_region, offset)?;
                }
                Ok(())
            },
        )?;

        // assign fixed range tables only as they are the only tables referred by a
        // specfic math gadget -- ConstantDivisionGadget.
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for (offset, row) in std::iter::once([F::zero(); 4])
                    .chain(
                        FixedTableTag::iter()
                            .filter(|t| {
                                matches!(
                                    t,
                                    FixedTableTag::Range5
                                        | FixedTableTag::Range16
                                        | FixedTableTag::Range32
                                        | FixedTableTag::Range64
                                        | FixedTableTag::Range256
                                        | FixedTableTag::Range512
                                        | FixedTableTag::Range1024
                                )
                            })
                            .flat_map(|tag| tag.build()),
                    )
                    .enumerate()
                {
                    for (column, value) in config.fixed_table.iter().zip_eq(row) {
                        region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
                    }
                }

                Ok(())
            },
        )
    }
}

pub(crate) fn test_math_gadget_container<F: Field, G: MathGadgetContainer<F>>(
    input_words: Vec<Word>,
    expected_success: bool,
) {
    const K: usize = 12;
    let randomness = F::from(123456u64);
    let power_of_randomness: Vec<Vec<F>> = (1..32)
        .map(|exp| vec![randomness.pow(&[exp, 0, 0, 0]); (1 << K) - 64])
        .collect();
    let circuit = UnitTestMathGadgetBaseCircuit::<F, G>::new(K, input_words, randomness);

    let prover = MockProver::<F>::run(K as u32, &circuit, power_of_randomness).unwrap();
    if expected_success {
        assert_eq!(prover.verify(), Ok(()));
    } else {
        assert_ne!(prover.verify(), Ok(()));
    }
}

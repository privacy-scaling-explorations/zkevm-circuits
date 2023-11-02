use std::marker::PhantomData;

use crate::{
    evm_circuit::{
        param::{MAX_STEP_HEIGHT, N_PHASE2_COLUMNS, STEP_WIDTH},
        step::{ExecutionState, Step},
        util::{
            constraint_builder::EVMConstraintBuilder, CachedRegion, StoredExpression, LOOKUP_CONFIG,
        },
        Advice, Column,
    },
    util::Challenges,
};
use eth_types::{Field, Word};
pub(crate) use halo2_proofs::circuit::Layouter;
use halo2_proofs::{
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error, FirstPhase, SecondPhase, Selector, ThirdPhase},
};

pub(crate) trait MemoryGadgetContainer<F: Field>: Clone {
    fn configure_gadget_container(cb: &mut EVMConstraintBuilder<F>) -> Self
    where
        Self: Sized;

    fn assign_gadget_container(
        &self,
        witnesses: &[Word],
        region: &mut CachedRegion<'_, '_, F>,
    ) -> Result<(), Error>;
}

#[derive(Debug, Clone)]
pub(crate) struct UnitTestMemoryGadgetBaseCircuitConfig<F: Field, G>
where
    G: MemoryGadgetContainer<F>,
{
    q_usable: Selector,
    advices: [Column<Advice>; STEP_WIDTH],
    step: Step<F>,
    stored_expressions: Vec<StoredExpression<F>>,
    memory_gadget_container: G,
    _marker: PhantomData<F>,
}

pub(crate) struct UnitTestMemoryGadgetBaseCircuit<G> {
    witnesses: Vec<Word>,
    _marker: PhantomData<G>,
}

impl<G> UnitTestMemoryGadgetBaseCircuit<G> {
    fn new(witnesses: Vec<Word>) -> Self {
        UnitTestMemoryGadgetBaseCircuit {
            witnesses,
            _marker: PhantomData,
        }
    }
}

impl<F: Field, G: MemoryGadgetContainer<F>> Circuit<F> for UnitTestMemoryGadgetBaseCircuit<G> {
    type Config = (UnitTestMemoryGadgetBaseCircuitConfig<F, G>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        UnitTestMemoryGadgetBaseCircuit {
            witnesses: vec![],
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenges_exprs = challenges.exprs(meta);

        let q_usable = meta.selector();

        let lookup_column_count: usize = LOOKUP_CONFIG.iter().map(|(_, count)| *count).sum();
        let advices = [(); STEP_WIDTH]
            .iter()
            .enumerate()
            .map(|(n, _)| {
                if n < lookup_column_count {
                    meta.advice_column_in(ThirdPhase)
                } else if n < lookup_column_count + N_PHASE2_COLUMNS {
                    meta.advice_column_in(SecondPhase)
                } else {
                    meta.advice_column_in(FirstPhase)
                }
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let step_curr = Step::new(meta, advices, 0);
        let step_next = Step::new(meta, advices, MAX_STEP_HEIGHT);
        let mut cb = EVMConstraintBuilder::new(
            meta,
            step_curr.clone(),
            step_next,
            &challenges_exprs,
            ExecutionState::STOP,
        );
        let memory_gadget_container = G::configure_gadget_container(&mut cb);
        let (constraints, stored_expressions, _, _) = cb.build();

        if !constraints.step.is_empty() {
            let step_constraints = constraints.step;
            meta.create_gate("MemoryGadgetTestContainer", |meta| {
                let q_usable = meta.query_selector(q_usable);
                step_constraints
                    .into_iter()
                    .map(move |(name, constraint)| (name, q_usable.clone() * constraint))
            });
        }

        (
            UnitTestMemoryGadgetBaseCircuitConfig::<F, G> {
                q_usable,
                advices,
                step: step_curr,
                stored_expressions,
                memory_gadget_container,
                _marker: PhantomData,
            },
            challenges,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let (config, challenges) = config;
        let challenge_values = challenges.values(&mut layouter);
        layouter.assign_region(
            || "assign test container",
            |mut region| {
                let offset = 0;
                config.q_usable.enable(&mut region, offset)?;
                let cached_region = &mut CachedRegion::<'_, '_, F>::new(
                    &mut region,
                    &challenge_values,
                    config.advices.to_vec(),
                    MAX_STEP_HEIGHT * 3,
                    offset,
                );
                config.step.state.execution_state.assign(
                    cached_region,
                    offset,
                    ExecutionState::STOP as usize,
                )?;
                config
                    .memory_gadget_container
                    .assign_gadget_container(&self.witnesses, cached_region)?;
                for stored_expr in &config.stored_expressions {
                    stored_expr.assign(cached_region, offset)?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

/// This fn test_math_gadget_container takes math gadget container and run a
/// container based circuit. All test logic should be included in the container,
/// and witness words are used for both input & output data. How to deal with
/// the witness words is left to each container.
pub(crate) fn test_memory_gadget_container<F: Field, G: MemoryGadgetContainer<F>>(
    witnesses: Vec<Word>,
    expected_success: bool,
) {
    const K: usize = 12;
    let circuit = UnitTestMemoryGadgetBaseCircuit::<G>::new(witnesses);

    let prover = MockProver::<F>::run(K as u32, &circuit, vec![]).unwrap();
    if expected_success {
        assert_eq!(prover.verify(), Ok(()));
    } else {
        assert_ne!(prover.verify(), Ok(()));
    }
}

/// A simple macro for less code & better readability
macro_rules! try_test {
    ($base_class:ty, $witnesses:expr, $expect_success:expr $(,)?) => {{
        test_memory_gadget_container::<Fr, $base_class>($witnesses.to_vec(), $expect_success)
    }};
}

#[cfg(test)]
pub(crate) use try_test;

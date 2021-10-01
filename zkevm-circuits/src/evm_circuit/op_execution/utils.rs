//! Reusable utilities for the op code implementations.

use super::super::Constraint;
use super::utils::constraint_builder::ConstraintBuilder;
use super::OpExecutionState;
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

pub(crate) mod common_cases;
pub(crate) mod constraint_builder;
pub(crate) mod math_gadgets;

// Makes sure all state transition variables are always constrained.
// This makes it impossible for opcodes to forget to constrain
// any state variables. If no update is specified it is assumed
// that the state variable needs to remain the same (which may not
// be correct, but this will easily be detected while testing).
#[derive(Clone, Debug, Default)]
pub(crate) struct StateTransitions<F> {
    pub gc_delta: Option<Expression<F>>,
    pub sp_delta: Option<Expression<F>>,
    pub pc_delta: Option<Expression<F>>,
    pub gas_delta: Option<Expression<F>>,
}

impl<F: FieldExt> StateTransitions<F> {
    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
    ) {
        // Global Counter
        cb.add_expression(
            state_next.global_counter.expr()
                - (state_curr.global_counter.expr()
                    + self.gc_delta.clone().unwrap_or(0.expr())),
        );
        // Stack Pointer
        cb.add_expression(
            state_next.stack_pointer.expr()
                - (state_curr.stack_pointer.expr()
                    + self.sp_delta.clone().unwrap_or(0.expr())),
        );
        // Program Counter
        cb.add_expression(
            state_next.program_counter.expr()
                - (state_curr.program_counter.expr()
                    + self.pc_delta.clone().unwrap_or(0.expr())),
        );
        // Gas Counter
        cb.add_expression(
            state_next.gas_counter.expr()
                - (state_curr.gas_counter.expr()
                    + self.gas_delta.clone().unwrap_or(0.expr())),
        );
    }
}

pub(crate) fn batch_add_expressions<F: FieldExt>(
    constraints: Vec<Constraint<F>>,
    expressions: Vec<Expression<F>>,
) -> Vec<Constraint<F>> {
    constraints
        .into_iter()
        .map(|mut constraint| {
            constraint.polys =
                [constraint.polys.clone(), expressions.clone().to_vec()]
                    .concat();
            constraint
        })
        .collect()
}

pub(crate) mod sum {
    use super::super::Cell;
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(cells: &[Cell<F>]) -> Expression<F> {
        cells.iter().fold(0.expr(), |acc, cell| acc + cell.expr())
    }

    pub(crate) fn value<F: FieldExt>(values: &[u8]) -> F {
        values
            .iter()
            .fold(F::zero(), |acc, value| acc + F::from_u64(*value as u64))
    }
}

/// Counts the number of repetitions
#[macro_export]
macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + crate::count!($($xs)*));
}

/// Common OpGadget implementer
#[macro_export]
macro_rules! impl_op_gadget {
    ([$($op:ident),*], $name:ident { $($case:ident ($($args:expr),*) ),* $(,)? }) => {

        paste::paste! {
            #[derive(Clone, Debug)]
            pub struct $name<F> {
                $(
                    [<$case:snake>]: $case<F>,
                )*
            }
        }

        impl<F: FieldExt> OpGadget<F> for $name<F> {
            const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[$(OpcodeId::$op),*];

            const CASE_CONFIGS: &'static [CaseConfig] = &[
                $(
                    *$case::<F>::CASE_CONFIG,
                )*
            ];

            fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
                paste::paste! {
                    let [
                        $(
                            mut [<$case:snake>],
                        )*
                    ]: [CaseAllocation<F>; crate::count!($($case)*)] =
                        case_allocations.try_into().unwrap();
                    Self {
                        $(
                            [<$case:snake>]: $case::construct(
                                &mut [<$case:snake>],
                                $(
                                    $args,
                                )*
                            ),
                        )*
                    }
                }
            }

            fn constraints(
                &self,
                state_curr: &OpExecutionState<F>,
                state_next: &OpExecutionState<F>,
            ) -> Vec<Constraint<F>> {
                paste::paste! {
                    $(
                        let [<$case:snake>] = self.[<$case:snake>].constraint(
                            state_curr,
                            state_next,
                            concat!(stringify!($name), " ", stringify!([<$case:snake>])),
                        );
                    )*
                    let cases = vec![
                        $(
                            [<$case:snake>],
                        )*
                    ];
                }
                // Add common expressions to all cases
                let mut cb = ConstraintBuilder::default();
                cb.require_in_set(
                    state_curr.opcode.expr(),
                    vec![$(OpcodeId::$op.expr()),*],
                );
                utils::batch_add_expressions(
                    cases,
                    cb.expressions,
                )
            }

            paste::paste! {
                fn assign(
                    &self,
                    region: &mut Region<'_, F>,
                    offset: usize,
                    op_execution_state: &mut CoreStateInstance,
                    execution_step: &ExecutionStep,
                ) -> Result<(), Error> {
                    $(
                        if execution_step.case == $case::<F>::CASE_CONFIG.case {
                            return self.[<$case:snake>].assign(
                                region,
                                offset,
                                op_execution_state,
                                execution_step,
                            );
                        }
                    )*
                    else {
                        unreachable!();
                    }
                }
            }
        }
    };
}

//! The EVM circuit implementation.

use halo2::{
    arithmetic::FieldExt,
    circuit::{self, Layouter, Region},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector,
    },
    poly::Rotation,
};
use std::convert::TryInto;

mod op_execution;
mod param;
use self::{
    op_execution::{OpExecutionGadget, OpExecutionState},
    param::{CIRCUIT_HEIGHT, CIRCUIT_WIDTH, NUM_CELL_OP_EXECTION_STATE},
};

#[derive(Clone, Debug)]
pub(crate) enum CallField {
    // Transaction id.
    TxId,
    // Global counter at the begin of call.
    GlobalCounterBegin,
    // Global counter at the end of call, used for locating reverting section.
    GlobalCounterEnd,
    // Caller’s unique identifier.
    CallerID,
    // Offset of calldata.
    CalldataOffset,
    // Size of calldata.
    CalldataSize,
    // Depth of call, should be expected in range 0..=1024.
    Depth,
    // Address of caller.
    CallerAddress,
    // Address of code which interpreter is executing, could differ from
    // `ReceiverAddress` when delegate call.
    CodeAddress,
    // Address of receiver.
    ReceiverAddress,
    // Gas given of call.
    GasAvailable,
    // Value in wei of call.
    Value,
    // If call succeeds or not in the future.
    IsPersistant,
    // If call is within a static call.
    IsStatic,
    // If call is `CREATE*`. We lookup op from calldata when is create,
    // otherwise we lookup code under address.
    IsCreate,
}

#[derive(Clone, Debug)]
pub(crate) enum CallStateField {
    // Program counter.
    ProgramCounter,
    // Stack pointer.
    StackPointer,
    // Memory size.
    MemeorySize,
    // Gas counter.
    GasCounter,
    // State trie write counter.
    StateWriteCounter,
    // Last callee's unique identifier.
    CalleeID,
    // Offset of returndata.
    ReturndataOffset,
    // Size of returndata.
    ReturndataSize,
}

#[derive(Clone, Debug)]
pub(crate) enum BusMappingLookup<F> {
    // Read-Write
    OpExecutionState {
        field: CallStateField,
        value: Expression<F>,
        is_write: bool,
    },
    Stack {
        // One can only access its own stack, so id is no needed to be
        // specified.
        // Stack index is always deterministic respect to stack pointer, so an
        // index offset is enough.
        index_offset: i32,
        value: Expression<F>,
        is_write: bool,
    },
    Memory {
        // Some ops like CALLDATALOAD can peek caller's memeory as calldata, so
        // we allow it to specify the id.
        id: Expression<F>,
        index: Expression<F>,
        value: Expression<F>,
        is_write: bool,
    },
    AccountStorage {
        address: Expression<F>,
        location: Expression<F>,
        value: Expression<F>,
        is_write: bool,
    },
    // TODO: AccountNonce,
    // TODO: AccountBalance,
    // TODO: AccountCodeHash,

    // Read-Only
    Call {
        field: CallField,
        value: Expression<F>,
    },
    Bytecode {
        hash: Expression<F>,
        index: Expression<F>,
        value: Expression<F>,
    },
    // TODO: Block,
    // TODO: Bytecode,
    // TODO: Tx,
    // TODO: TxCalldata,
}

#[derive(Clone, Copy, Debug, PartialOrd, PartialEq, Eq, Ord)]
pub(crate) enum FixedLookup {
    // Noop provides [0, 0, 0, 0] row
    Noop,
    // meaningful tags start with 1
    Range256,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(Clone, Debug)]
pub(crate) enum Lookup<F> {
    FixedLookup(FixedLookup, [Expression<F>; 3]),
    BusMappingLookup(BusMappingLookup<F>),
}

#[derive(Clone, Debug)]
struct Constraint<F> {
    name: &'static str,
    selector: Expression<F>,
    linear_combinations: Vec<Expression<F>>,
    lookups: Vec<Lookup<F>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Cell<F> {
    // expression for constraint
    expression: Expression<F>,
    // relative position to selector for synthesis
    column: Column<Advice>,
    rotation: usize,
}

impl<F: FieldExt> Cell<F> {
    fn exp(&self) -> Expression<F> {
        self.expression.clone()
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<circuit::Cell, Error> {
        region.assign_advice(
            || {
                format!(
                    "Cell column: {:?} and rotation: {}",
                    self.column, self.rotation
                )
            },
            self.column,
            offset + self.rotation,
            || value.ok_or(Error::SynthesisError),
        )
    }
}

// TODO: Integrate with evm_word
#[derive(Clone, Debug)]
struct Word<F> {
    // random linear combination expression of cells
    expression: Expression<F>,
    // inner cells for syntesis
    cells: [Cell<F>; 32],
}

impl<F: FieldExt> Word<F> {
    fn new(cells: &[Cell<F>], r: F) -> Self {
        let r = Expression::Constant(r);
        Self {
            expression: cells
                .iter()
                .rev()
                .fold(Expression::Constant(F::zero()), |acc, byte| {
                    acc * r.clone() + byte.exp()
                }),
            cells: cells.to_owned().try_into().unwrap(),
        }
    }

    fn exp(&self) -> Expression<F> {
        self.expression.clone()
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        word: Option<[u8; 32]>,
    ) -> Result<Vec<circuit::Cell>, Error> {
        word.map_or(Err(Error::SynthesisError), |word| {
            self.cells
                .iter()
                .zip(word.iter())
                .map(|(cell, byte)| {
                    cell.assign(region, offset, Some(F::from_u64(*byte as u64)))
                })
                .collect()
        })
    }
}

// TODO: Should we maintain these state in circuit or we prepare all of them
// when parsing debug trace?
#[derive(Debug)]
pub(crate) struct CoreStateInstance {
    is_executing: bool,
    global_counter: usize,
    call_id: usize,
    program_counter: usize,
    stack_pointer: usize,
    gas_counter: usize,
}

impl CoreStateInstance {
    fn new(call_id: usize) -> Self {
        Self {
            is_executing: false,
            global_counter: 0,
            call_id,
            program_counter: 0,
            stack_pointer: 1024,
            gas_counter: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Case {
    Success,
    // out of gas
    OutOfGas,
    // call depth exceeded 1024
    DepthOverflow,
    // insufficient balance for transfer
    InsufficientBalance,
    // contract address collision
    ContractAddressCollision,
    // execution reverted
    Reverted,
    // max code size exceeded
    MaxCodeSizeExceeded,
    // invalid jump destination
    InvalidJump,
    // static call protection
    WriteProtection,
    // return data out of bound
    ReturnDataOutOfBounds,
    // contract must not begin with 0xef due to EIP #3541 EVM Object Format (EOF)
    InvalidBeginningCode,
    // stack underflow
    StackUnderflow,
    // stack overflow
    StackOverflow,
    // invalid opcode
    InvalidCode,
}

// TODO: use ExecutionStep from bus_mapping
pub(crate) struct ExecutionStep {
    opcode: u8,
    case: Case,
    values: Vec<[u8; 32]>,
}

#[derive(Clone)]
struct EvmCircuit<F> {
    q_step: Selector,
    qs_byte_lookup: Column<Advice>,
    fixed_table: [Column<Fixed>; 4],
    op_execution_gadget: OpExecutionGadget<F>,
}

impl<F: FieldExt> EvmCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_step = meta.selector();
        let qs_byte_lookup = meta.advice_column();
        let advices = (0..CIRCUIT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // fixed_table contains pre-built tables identified by tag including:
        // - different size range tables
        // - bitwise table
        // - comparator table
        // - ...
        let fixed_table = [
            meta.fixed_column(), // tag
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];

        let (
            qs_op_execution,
            qs_byte_lookups,
            op_execution_state_curr,
            op_execution_state_next,
            op_execution_free_cells,
        ) = Self::configure_allocations(meta, q_step, qs_byte_lookup, advices);

        // independent_lookups collect lookups by independent selectors, which
        // means we can sum some of them together to save lookups.
        let mut independent_lookups =
            Vec::<(Expression<F>, Vec<Lookup<F>>)>::new();

        let op_execution_gadget = OpExecutionGadget::configure(
            meta,
            r,
            qs_op_execution,
            qs_byte_lookups,
            op_execution_state_curr,
            op_execution_state_next,
            op_execution_free_cells,
            &mut independent_lookups,
        );

        // TODO: call_initialization_gadget

        Self::configure_lookups(
            meta,
            qs_byte_lookup,
            advices,
            fixed_table,
            independent_lookups,
        );

        EvmCircuit {
            q_step,
            qs_byte_lookup,
            fixed_table,
            op_execution_gadget,
        }
    }

    // TODO: refactor return type
    #[allow(clippy::type_complexity)]
    fn configure_allocations(
        meta: &mut ConstraintSystem<F>,
        q_step: Selector,
        qs_byte_lookup: Column<Advice>,
        advices: [Column<Advice>; CIRCUIT_WIDTH],
    ) -> (
        Expression<F>,
        Vec<Cell<F>>,
        OpExecutionState<F>,
        OpExecutionState<F>,
        Vec<Cell<F>>,
    ) {
        let mut qs_byte_lookups = Vec::with_capacity(CIRCUIT_HEIGHT);
        meta.create_gate("Query byte lookup as a synthetic selector", |meta| {
            for h in 0..CIRCUIT_HEIGHT as i32 {
                qs_byte_lookups.push(Cell {
                    expression: meta.query_advice(qs_byte_lookup, Rotation(h)),
                    column: qs_byte_lookup,
                    rotation: h as usize,
                });
            }

            vec![Expression::Constant(F::zero())]
        });

        // TODO: Enable this when switch to kzg branch and remove the failure
        //       VerifyFailure::ConstraintPoison
        // meta.create_gate("Query byte lookup as a synthetic selector", |meta| {
        //     let exp = meta.query_advice(qs_byte_lookup, Rotation::cur());

        //     vec![exp.clone() * (Expression::Constant(F::one()) - exp)]
        // });

        let mut cells_curr = Vec::with_capacity(CIRCUIT_WIDTH * CIRCUIT_HEIGHT);
        meta.create_gate("Query cells for current step", |meta| {
            for h in 0..CIRCUIT_HEIGHT as i32 {
                for &column in advices.iter() {
                    cells_curr.push(Cell {
                        expression: meta.query_advice(column, Rotation(h)),
                        column,
                        rotation: h as usize,
                    });
                }
            }

            vec![Expression::Constant(F::zero())]
        });

        let num_cells_next_asseccible = NUM_CELL_OP_EXECTION_STATE;

        let cells_next =
            &mut cells_curr[..num_cells_next_asseccible].to_vec()[..];
        meta.create_gate("Query cells for next step", |meta| {
            for cell in cells_next.iter_mut() {
                cell.expression = meta.query_advice(
                    cell.column,
                    Rotation((cell.rotation + CIRCUIT_HEIGHT) as i32),
                );
            }

            vec![Expression::Constant(F::zero())]
        });

        let op_execution_state_curr =
            OpExecutionState::new(&cells_curr[..NUM_CELL_OP_EXECTION_STATE]);
        let op_execution_state_next =
            OpExecutionState::new(&cells_next[..NUM_CELL_OP_EXECTION_STATE]);
        let op_execution_free_cells =
            cells_curr[NUM_CELL_OP_EXECTION_STATE..].to_vec();

        let mut qs_op_execution = Expression::Constant(F::zero());
        meta.create_gate(
            "Query synthetic selector for OpExecutionGadget",
            |meta| {
                qs_op_execution = meta.query_selector(q_step)
                    * op_execution_state_curr.is_executing.exp();

                vec![Expression::Constant(F::zero())]
            },
        );

        (
            qs_op_execution,
            qs_byte_lookups,
            op_execution_state_curr,
            op_execution_state_next,
            op_execution_free_cells,
        )
    }

    fn configure_lookups(
        meta: &mut ConstraintSystem<F>,
        qs_byte_lookup: Column<Advice>,
        advices: [Column<Advice>; CIRCUIT_WIDTH],
        fixed_table: [Column<Fixed>; 4],
        independent_lookups: Vec<(Expression<F>, Vec<Lookup<F>>)>,
    ) {
        // TODO: call_lookups
        // TODO: bytecode_lookups
        // TODO: rw_lookups

        let mut fixed_lookups = Vec::<[Expression<F>; 4]>::new();

        for (qs_lookup, lookups) in independent_lookups {
            let mut fixed_lookup_count = 0;

            for lookup in lookups {
                match lookup {
                    Lookup::FixedLookup(tag, exps) => {
                        let tag_exp =
                            Expression::Constant(F::from_u64(tag as u64));

                        if fixed_lookups.len() == fixed_lookup_count {
                            fixed_lookups.push(
                                [tag_exp]
                                    .iter()
                                    .chain(exps.iter())
                                    .map(|exp| qs_lookup.clone() * exp.clone())
                                    .collect::<Vec<_>>()
                                    .try_into()
                                    .unwrap(),
                            );
                        } else {
                            for (acc, exp) in fixed_lookups[fixed_lookup_count]
                                .iter_mut()
                                .zip([tag_exp].iter().chain(exps.iter()))
                            {
                                *acc = acc.clone()
                                    + qs_lookup.clone() * exp.clone();
                            }
                        }
                        fixed_lookup_count += 1;
                    }
                    Lookup::BusMappingLookup(_) => {
                        // TODO:
                        unimplemented!()
                    }
                }
            }
        }

        // Configure whole row lookups by qs_byte_lookup
        let zero = Expression::Constant(F::zero());
        for column in advices {
            meta.lookup(|meta| {
                let tag = Expression::Constant(F::from_u64(
                    FixedLookup::Range256 as u64,
                ));
                let qs_byte_lookup =
                    meta.query_advice(qs_byte_lookup, Rotation::cur());
                [
                    qs_byte_lookup.clone() * tag,
                    qs_byte_lookup * meta.query_advice(column, Rotation::cur()),
                    zero.clone(),
                    zero.clone(),
                ]
                .iter()
                .zip(fixed_table.iter())
                .map(|(exp, column)| {
                    (exp.clone(), meta.query_fixed(*column, Rotation::cur()))
                })
                .collect::<Vec<_>>()
            });
        }

        for fixed_lookup in fixed_lookups.iter() {
            meta.lookup(|meta| {
                fixed_lookup
                    .iter()
                    .zip(fixed_table.iter())
                    .map(|(exp, column)| {
                        (
                            exp.clone(),
                            meta.query_fixed(*column, Rotation::cur()),
                        )
                    })
                    .collect::<Vec<_>>()
            });
        }
    }

    fn load_fixed_tables(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                let mut offest = 0;

                // Noop
                for (idx, column) in self.fixed_table.iter().enumerate() {
                    region.assign_fixed(
                        || format!("Noop: {}", idx),
                        *column,
                        offest,
                        || Ok(F::zero()),
                    )?;
                }
                offest += 1;

                // Range256
                for idx in 0..256 {
                    region.assign_fixed(
                        || "Range256: tag",
                        self.fixed_table[0],
                        offest,
                        || Ok(F::from_u64(FixedLookup::Range256 as u64)),
                    )?;
                    region.assign_fixed(
                        || "Range256: value",
                        self.fixed_table[1],
                        offest,
                        || Ok(F::from_u64(idx as u64)),
                    )?;
                    for (idx, column) in
                        self.fixed_table[2..].iter().enumerate()
                    {
                        region.assign_fixed(
                            || format!("Range256: padding {}", idx),
                            *column,
                            offest,
                            || Ok(F::zero()),
                        )?;
                    }
                    offest += 1;
                }

                // TODO: BitwiseAnd
                // TODO: BitwiseOr
                // TODO: BitwiseXor

                Ok(())
            },
        )
    }

    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        execution_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "evm circuit",
            |mut region| {
                let mut core_state = CoreStateInstance::new(0);

                // TODO: call_initialization should maintain this
                core_state.is_executing = true;

                for (idx, execution_step) in execution_steps.iter().enumerate()
                {
                    let offset = idx * CIRCUIT_HEIGHT;

                    self.q_step.enable(&mut region, offset)?;

                    self.op_execution_gadget.assign_execution_step(
                        &mut region,
                        offset,
                        &mut core_state,
                        Some(execution_step),
                    )?;
                }

                self.op_execution_gadget.assign_execution_step(
                    &mut region,
                    execution_steps.len() * CIRCUIT_HEIGHT,
                    &mut core_state,
                    None,
                )?;

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod test {
    use super::{EvmCircuit, ExecutionStep};
    use halo2::{
        arithmetic::FieldExt,
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use std::marker::PhantomData;

    #[derive(Clone)]
    pub(crate) struct TestCircuitConfig<F> {
        evm_circuit: EvmCircuit<F>,
    }

    #[derive(Default)]
    pub(crate) struct TestCircuit<F> {
        execution_steps: Vec<ExecutionStep>,
        _marker: PhantomData<F>,
    }

    impl<F> TestCircuit<F> {
        pub(crate) fn new(execution_steps: Vec<ExecutionStep>) -> Self {
            Self {
                execution_steps,
                _marker: PhantomData,
            }
        }
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Self::Config {
                evm_circuit: EvmCircuit::configure(meta, F::one()),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.evm_circuit.load_fixed_tables(&mut layouter)?;
            config
                .evm_circuit
                .assign(&mut layouter, &self.execution_steps)
        }
    }
}

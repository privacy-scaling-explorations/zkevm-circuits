//! The EVM circuit implementation.

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};
use std::{collections::HashSet, convert::TryInto, iter::FromIterator};

// immutable
enum InterpreterContextKey {
    // global counter at the end of call, used for locating reverting section
    GlobalCounterEnd,
    // caller’s unique identifier
    CallerID,
    // offset of calldata
    CalldataOffset,
    // size of calldata
    CalldataSize,
    // address of tx sender (EOA address)
    TxOrigin,
    // gas price of tx
    GasPrice,
    // depth of call, should ∈ [0,1024]
    Depth,
    // address of caller
    CallerAddress,
    // address of code which interpreter is executing, could differ from `address` when delegate call
    CodeAddress,
    // address of receiver
    Address,
    // gas given of call
    GasAvailable,
    // value in wei of call
    Value,
    // if call succeeds or not in the future
    IsPersistant,
    // if call is within a static call
    IsStatic,
    // more would be needed like:
    // GasBaseFee,
}

// mutable
enum InterpreterStateKey {
    // global counter
    GlobalCounter,
    // program counter
    ProgramCounter,
    // stack pointer
    StackPointer,
    // memory size
    MemeorySize,
    // if call is `CREATE*`, if true we lookup op from calldata, otherwise we lookup code under address
    IsCreate,
    // gas counter
    GasCounter,
    // state trie write counter
    StateWriteCounter,
    // number of slot to continue the same op for
    SlotTodo,
    // last callee's unique identifier
    CalleeID,
    // offset of returndata
    ReturndataOffset,
    // size of returndata
    ReturndataSize,
}

enum BusMappingLookup<F> {
    InterpreterContext {
        key: InterpreterContextKey,
        value: Expression<F>,
    },
    InterpreterState {
        key: InterpreterStateKey,
        value: Expression<F>,
        is_write: bool,
    },
    Stack {
        // one can access its own stack, so id is no needed to be specify
        // stack index is always deterministic respect to stack pointer, so an
        // index offset is enough
        index_offset: i32,
        value: Expression<F>,
        is_write: bool,
    },
    Memory {
        // some op like CALLDATALOAD can peek caller's memeory, so we allow it
        // to specify the id.
        id: Expression<F>,
        index: Expression<F>,
        value: Expression<F>,
        is_write: bool,
    },
    Storage {
        address: Expression<F>,
        location: Expression<F>,
        value: Expression<F>,
        is_write: bool,
    },
    // more would be needed like:
    // Code,
    // Block,
    // Tx,
    // TxCalldata,
    // AccountNonce,
    // AccountBalance,
    // AccountCodeHash,
    // AccountStorageRoot,
}

enum Lookup<F> {
    RangeLookup(/* usize, Expression<F> */),
    BusMappingLookup(BusMappingLookup<F>),
}

#[derive(Debug, PartialEq, Eq, Hash)]
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
    // is_write protection
    WriteProtection,
    // return data out of bound
    ReturnDataOutOfBounds,
    // contract must not begin with 0xef due to EOF
    InvalidBeginningCode,
    // stack underflow
    StackUnderflow(usize),
    // stack overflow
    StackOverflow(usize),
    // invalid opcode
    InvalidCode,
}

struct ExecutionResult<F> {
    case: Case,
    linear_constraints: Vec<Expression<F>>,
    lookups: Vec<Lookup<F>>,
}

#[derive(Clone, Debug)]
struct Allocation<F> {
    // expression for configuration
    exp: Expression<F>,
    // relative position to selector for synthesis
    column: Column<Advice>,
    offset: usize,
}

impl<F: FieldExt> Allocation<F> {
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<Cell, Error> {
        region.assign_advice(
            || format!("assign allocation {:?}", self.column),
            self.column,
            offset + self.offset,
            || value.ok_or(Error::SynthesisError),
        )
    }
}

// TODO: Integrate with evm_word
#[derive(Clone, Debug)]
struct Word<F> {
    // random linear combination exp for configuration
    exp: Expression<F>,
    // inner allocations for syntesis
    allocs: [Allocation<F>; 32],
}

impl<F: FieldExt> Word<F> {
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        /* value: [Option<u8>; 32] or U256 */
    ) -> Result<Cell, Error> {
        Err(Error::SynthesisError)
    }
}

struct InterpreterState<F> {
    // unique id for each interpreter, could be the global counter of the call beginning
    id: Expression<F>,
    global_counter: Expression<F>,
    program_counter: Expression<F>,
    stack_pointer: Expression<F>,
    gas_counter: Expression<F>,
    memory_size: Expression<F>,
}

struct InterpreterStateInstance {
    id: usize,
    global_counter: usize,
    program_counter: usize,
    stack_pointer: usize,
    gas_counter: u64,
    memory_size: usize,
}

trait OpGadget<F: FieldExt> {
    fn cases() -> HashSet<Case>;

    fn construct(words: &[Word<F>], all: &[Allocation<F>]) -> Self;

    fn constraints(
        &self,
        interpreter_state_curr: &InterpreterState<F>,
        interpreter_state_next: &InterpreterState<F>,
    ) -> Vec<ExecutionResult<F>>;

    fn transit(&self, interpreter_state: &mut InterpreterStateInstance);

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        /* TODO: execution_result: ExecutionResultInstance */
    );

    // TODO: figure out how the parsing api would be like
}

struct AddGadget<F> {
    success: (Word<F>, Word<F>, Word<F>, [Allocation<F>; 32]),
    out_of_gas: (Allocation<F>, Allocation<F>),
}

impl<F: FieldExt> OpGadget<F> for AddGadget<F> {
    fn cases() -> HashSet<Case> {
        HashSet::from_iter([Case::Success, Case::OutOfGas, Case::StackUnderflow(2)])
    }

    fn construct(words: &[Word<F>], all: &[Allocation<F>]) -> Self {
        Self {
            success: (
                words[0].clone(),
                words[1].clone(),
                words[2].clone(),
                all[96..128].to_owned().try_into().unwrap(),
            ),
            out_of_gas: (all[0].clone(), all[1].clone()),
        }
    }

    fn constraints(
        &self,
        interpreter_state_curr: &InterpreterState<F>,
        interpreter_state_next: &InterpreterState<F>,
    ) -> Vec<ExecutionResult<F>> {
        let success = {
            let exp_256 = Expression::Constant(F::from_u64(1 << 8));

            // interpreter state transition constraints
            let interpreter_state_transition_constraints = vec![
                interpreter_state_next.global_counter.clone()
                    - (interpreter_state_curr.global_counter.clone()
                        + Expression::Constant(F::from_u64(3))),
                interpreter_state_next.stack_pointer.clone()
                    - (interpreter_state_curr.stack_pointer.clone()
                        + Expression::Constant(F::from_u64(1))),
                interpreter_state_next.program_counter.clone()
                    - (interpreter_state_curr.program_counter.clone()
                        + Expression::Constant(F::from_u64(1))),
                interpreter_state_next.gas_counter.clone()
                    - (interpreter_state_curr.gas_counter.clone()
                        + Expression::Constant(F::from_u64(3))),
            ];

            let (a, b, c, carry) = &self.success;
            // add constraints
            let mut add_constraints = vec![
                (carry[0].exp.clone() * exp_256.clone() + c.exp.clone())
                    - (a.allocs[0].exp.clone() + b.allocs[0].exp.clone()),
            ];
            for idx in 1..32 {
                add_constraints.push(
                    (carry[idx].exp.clone() * exp_256.clone() + c.exp.clone())
                        - (a.allocs[idx].exp.clone()
                            + b.allocs[idx].exp.clone()
                            + carry[idx - 1].exp.clone()),
                )
            }

            ExecutionResult {
                case: Case::Success,
                linear_constraints: [interpreter_state_transition_constraints, add_constraints]
                    .concat(),
                lookups: vec![
                    Lookup::BusMappingLookup(BusMappingLookup::Stack {
                        index_offset: 1,
                        value: a.exp.clone(),
                        is_write: false,
                    }),
                    Lookup::BusMappingLookup(BusMappingLookup::Stack {
                        index_offset: 2,
                        value: b.exp.clone(),
                        is_write: false,
                    }),
                    Lookup::BusMappingLookup(BusMappingLookup::Stack {
                        index_offset: 1,
                        value: c.exp.clone(),
                        is_write: true,
                    }),
                ],
            }
        };

        let out_of_gas = {
            let (one, two, three) = (
                Expression::Constant(F::from_u64(1)),
                Expression::Constant(F::from_u64(2)),
                Expression::Constant(F::from_u64(3)),
            );
            let (gas_available, gas_overdemand) = &self.out_of_gas;
            ExecutionResult {
                case: Case::OutOfGas,
                linear_constraints: vec![
                    interpreter_state_curr.gas_counter.clone() + three.clone()
                        - (gas_available.exp.clone() + gas_overdemand.exp.clone()),
                    (gas_overdemand.exp.clone() - one)
                        * (gas_overdemand.exp.clone() - two)
                        * (gas_overdemand.exp.clone() - three),
                ],
                lookups: vec![Lookup::BusMappingLookup(
                    BusMappingLookup::InterpreterContext {
                        key: InterpreterContextKey::GasAvailable,
                        value: gas_available.exp.clone(),
                    },
                )],
            }
        };

        vec![success, out_of_gas]
    }

    fn transit(&self, interpreter_state: &mut InterpreterStateInstance) {
        interpreter_state.global_counter += 3;
        interpreter_state.program_counter += 1;
        interpreter_state.stack_pointer += 1;
        interpreter_state.gas_counter += 3;
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        /* TODO: execution_result: ExecutionResultInstance */
    ) {
    }
}

struct EvmCircuit<F> {
    add_gadget: AddGadget<F>,
}

impl<F: FieldExt> EvmCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        // TODO: figure out how many min cells required
        let min_cells_required = 320;
        let width = 32;
        let height = min_cells_required / width + (min_cells_required % width != 0) as usize;

        let columns = (0..width).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let mut allocations = Vec::with_capacity(width * height);
        meta.create_gate("allocations", |meta| {
            for w in 0..width {
                for h in 0..height as i32 {
                    allocations.push(meta.query_advice(columns[w], Rotation(h)));
                }
            }
            vec![Expression::Constant(F::zero())]
        });

        // TODO: allocate op switch
        // TODO: allocate case switch
        // TODO: allocate ? word
        // TODO: handle common error like StackUnderflow or StackOverflow

        let add_gadget = AddGadget::construct(&[], &[]);

        EvmCircuit { add_gadget }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        /* TODO: execution_results: Vec<ExecutionResultInstance> */
    ) -> Result<(), Error> {
        // for execution_result in execution_results {
        //     self.opcode_gadgets[0]
        // }
        Ok(())
    }
}

// DISCUSSION:
// 1. How would ExecutionResultInstance be like? (it should be parse from the output of zkevm-test-vector)
// enum BusMappingInstance {
//     InterpreterContext {
//         key: InterpreterContextKey,
//         value: [u8; 32], /* U256 or Word */
//     },
//     InterpreterState {
//         key: InterpreterStateKey,
//         value: [u8; 32], /* U256 or Word */
//         is_write: bool,
//     },
//     Stack {
//         index: usize,
//         value: [u8; 32], /* U256 or Word */
//         is_write: bool,
//     },
//     MemoryWord {
//         id: usize,
//         index: usize,
//         value: Vec<u8>,
//         is_write: bool,
//     },
//     MemoryByte {
//         id: usize,
//         index: usize,
//         value: u8,
//         is_write: bool,
//     },
//     Storage {
//         address: [u8; 20],  /* U160 or Address */
//         location: [u8; 32], /* U160 or Address */
//         value: [u8; 32],    /* U256 or Word */
//         is_write: bool,
//     },
//     // Code,
//     // Block,
//     // Tx,
//     // TxCalldata,
//     // AccountNonce,
//     // AccountBalance,
//     // AccountCodeHash,
//     // AccountStorageRoot,
// }

// struct ExecutionResultInstance {
//     opcode: u8,
//     case: Case,
//     bas_mappings: Vec<BusMappingInstance>,
// }

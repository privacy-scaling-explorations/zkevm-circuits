use crate::{
    evm_circuit::{
        param::{STEP_HEIGHT, STEP_WIDTH},
        step::{ExecutionState, Preset, Step},
        table::{FixedTableTag, Lookup, LookupTable, Table},
        util::constraint_builder::ConstraintBuilder,
    },
    util::Expr,
};
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::{
        Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};
use std::collections::HashMap;

mod add;
mod bitwise;
mod byte;
mod comparator;
mod dup;
mod error_oog_pure_memory;
mod jump;
mod jumpdest;
mod jumpi;
mod memory;
mod pc;
mod pop;
mod push;
mod signextend;
mod stop;
mod swap;
use add::AddGadget;
use bitwise::BitwiseGadget;
use byte::ByteGadget;
use comparator::ComparatorGadget;
use dup::DupGadget;
use error_oog_pure_memory::ErrorOOGPureMemoryGadget;
use jump::JumpGadget;
use jumpdest::JumpdestGadget;
use jumpi::JumpiGadget;
use memory::MemoryGadget;
use pc::PcGadget;
use pop::PopGadget;
use push::PushGadget;
use signextend::SignextendGadget;
use stop::StopGadget;
use swap::SwapGadget;

#[allow(missing_docs)]
pub mod bus_mapping_tmp {
    use crate::evm_circuit::{
        step::ExecutionState,
        table::{RwTableTag, TxContextFieldTag},
        util::RandomLinearCombination,
    };
    use bus_mapping::{
        eth_types::{Address, ToLittleEndian, ToScalar, Word},
        evm::OpcodeId,
    };
    use halo2::arithmetic::FieldExt;
    use sha3::{Digest, Keccak256};

    #[derive(Debug, Default)]
    pub struct Block<F> {
        // randomness for random linear combination
        pub randomness: F,
        pub txs: Vec<Transaction<F>>,
        pub rws: Vec<Rw>,
        pub bytecodes: Vec<Bytecode>,
    }

    #[derive(Debug, Default)]
    pub struct Transaction<F> {
        // Context
        pub id: usize,
        pub nonce: u64,
        pub gas: u64,
        pub gas_tip_cap: Word,
        pub gas_fee_cap: Word,
        pub caller_address: Address,
        pub callee_address: Address,
        pub is_create: bool,
        pub value: Word,
        pub call_data_length: usize,
        pub call_data: Vec<u8>,

        pub calls: Vec<Call<F>>,
        pub steps: Vec<ExecStep>,
    }

    impl<F: FieldExt> Transaction<F> {
        pub fn table_assignments(&self, randomness: F) -> Vec<[F; 4]> {
            [
                vec![
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::Nonce as u64),
                        F::zero(),
                        F::from(self.nonce),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::Gas as u64),
                        F::zero(),
                        F::from(self.gas),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::GasTipCap as u64),
                        F::zero(),
                        RandomLinearCombination::random_linear_combine(
                            self.gas_tip_cap.to_le_bytes(),
                            randomness,
                        ),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::GasFeeCap as u64),
                        F::zero(),
                        RandomLinearCombination::random_linear_combine(
                            self.gas_fee_cap.to_le_bytes(),
                            randomness,
                        ),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::CallerAddress as u64),
                        F::zero(),
                        self.caller_address.to_scalar().unwrap(),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::CalleeAddress as u64),
                        F::zero(),
                        self.callee_address.to_scalar().unwrap(),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::IsCreate as u64),
                        F::zero(),
                        F::from(self.is_create as u64),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::Value as u64),
                        F::zero(),
                        RandomLinearCombination::random_linear_combine(
                            self.value.to_le_bytes(),
                            randomness,
                        ),
                    ],
                    [
                        F::from(self.id as u64),
                        F::from(TxContextFieldTag::CallDataLength as u64),
                        F::zero(),
                        F::from(self.call_data_length as u64),
                    ],
                ],
                self.call_data
                    .iter()
                    .enumerate()
                    .map(|(idx, byte)| {
                        [
                            F::from(self.id as u64),
                            F::from(TxContextFieldTag::CallData as u64),
                            F::from(idx as u64),
                            F::from(*byte as u64),
                        ]
                    })
                    .collect(),
            ]
            .concat()
        }
    }

    #[derive(Debug, Default)]
    pub struct Call<F> {
        pub id: usize,
        pub is_root: bool,
        pub is_create: bool,
        pub opcode_source: F,
    }

    #[derive(Clone, Debug, Default)]
    pub struct ExecStep {
        pub call_idx: usize,
        pub rw_indices: Vec<usize>,
        pub execution_state: ExecutionState,
        pub rw_counter: usize,
        pub program_counter: u64,
        pub stack_pointer: usize,
        pub gas_left: u64,
        pub gas_cost: u64,
        pub memory_size: u64,
        pub state_write_counter: usize,
        pub opcode: Option<OpcodeId>,
    }

    #[derive(Debug)]
    pub struct Bytecode {
        pub hash: Word,
        pub bytes: Vec<u8>,
    }

    impl Bytecode {
        pub fn new(bytes: Vec<u8>) -> Self {
            Self {
                hash: Word::from_big_endian(
                    Keccak256::digest(&bytes).as_slice(),
                ),
                bytes,
            }
        }

        pub fn table_assignments<'a, F: FieldExt>(
            &'a self,
            randomness: F,
        ) -> impl Iterator<Item = [F; 4]> + '_ {
            struct BytecodeIterator<'a, F> {
                idx: usize,
                push_data_left: usize,
                hash: F,
                bytes: &'a [u8],
            }

            impl<'a, F: FieldExt> Iterator for BytecodeIterator<'a, F> {
                type Item = [F; 4];

                fn next(&mut self) -> Option<Self::Item> {
                    if self.idx == self.bytes.len() {
                        return None;
                    }

                    let idx = self.idx;
                    let byte = self.bytes[self.idx];
                    let mut is_code = true;

                    if self.push_data_left > 0 {
                        is_code = false;
                        self.push_data_left -= 1;
                    } else if (OpcodeId::PUSH1.as_u8()
                        ..=OpcodeId::PUSH32.as_u8())
                        .contains(&byte)
                    {
                        self.push_data_left = byte as usize
                            - (OpcodeId::PUSH1.as_u8() - 1) as usize;
                    }

                    self.idx += 1;

                    Some([
                        self.hash,
                        F::from(idx as u64),
                        F::from(byte as u64),
                        F::from(is_code as u64),
                    ])
                }
            }

            BytecodeIterator {
                idx: 0,
                push_data_left: 0,
                hash: RandomLinearCombination::random_linear_combine(
                    self.hash.to_le_bytes(),
                    randomness,
                ),
                bytes: &self.bytes,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub enum Rw {
        TxAccessListAccount {
            rw_counter: usize,
            is_write: bool,
        },
        TxAccessListStorageSlot {
            rw_counter: usize,
            is_write: bool,
        },
        TxRefund {
            rw_counter: usize,
            is_write: bool,
        },
        Account {
            rw_counter: usize,
            is_write: bool,
        },
        AccountStorage {
            rw_counter: usize,
            is_write: bool,
        },
        AccountDestructed {
            rw_counter: usize,
            is_write: bool,
        },
        CallContext {
            rw_counter: usize,
            is_write: bool,
        },
        Stack {
            rw_counter: usize,
            is_write: bool,
            call_id: usize,
            stack_pointer: usize,
            value: Word,
        },
        Memory {
            rw_counter: usize,
            is_write: bool,
            call_id: usize,
            memory_address: u64,
            byte: u8,
        },
    }

    impl Rw {
        pub fn stack_value(&self) -> Word {
            match self {
                Self::Stack { value, .. } => *value,
                _ => unreachable!(),
            }
        }

        pub fn table_assignment<F: FieldExt>(&self, randomness: F) -> [F; 8] {
            match self {
                Self::Stack {
                    rw_counter,
                    is_write,
                    call_id,
                    stack_pointer,
                    value,
                } => [
                    F::from(*rw_counter as u64),
                    F::from(*is_write as u64),
                    F::from(RwTableTag::Stack as u64),
                    F::from(*call_id as u64),
                    F::from(*stack_pointer as u64),
                    RandomLinearCombination::random_linear_combine(
                        value.to_le_bytes(),
                        randomness,
                    ),
                    F::zero(),
                    F::zero(),
                ],
                Self::Memory {
                    rw_counter,
                    is_write,
                    call_id,
                    memory_address,
                    byte,
                } => [
                    F::from(*rw_counter as u64),
                    F::from(*is_write as u64),
                    F::from(RwTableTag::Memory as u64),
                    F::from(*call_id as u64),
                    F::from(*memory_address),
                    F::from(*byte as u64),
                    F::zero(),
                    F::zero(),
                ],
                _ => unimplemented!(),
            }
        }
    }
}
use bus_mapping_tmp::{Block, Call, ExecStep, Transaction};

pub(crate) trait ExecutionGadget<F: FieldExt> {
    const NAME: &'static str;

    const EXECUTION_STATE: ExecutionState;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self;

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction<F>,
        call: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug)]
pub(crate) struct ExecutionConfig<F> {
    q_step: Selector,
    step: Step<F>,
    presets_map: HashMap<ExecutionState, Vec<Preset<F>>>,
    add_gadget: AddGadget<F>,
    bitwise_gadget: BitwiseGadget<F>,
    byte_gadget: ByteGadget<F>,
    comparator_gadget: ComparatorGadget<F>,
    dup_gadget: DupGadget<F>,
    error_oog_pure_memory_gadget: ErrorOOGPureMemoryGadget<F>,
    jump_gadget: JumpGadget<F>,
    jumpdest_gadget: JumpdestGadget<F>,
    jumpi_gadget: JumpiGadget<F>,
    memory_gadget: MemoryGadget<F>,
    pc_gadget: PcGadget<F>,
    pop_gadget: PopGadget<F>,
    push_gadget: PushGadget<F>,
    signextend_gadget: SignextendGadget<F>,
    stop_gadget: StopGadget<F>,
    swap_gadget: SwapGadget<F>,
}

impl<F: FieldExt> ExecutionConfig<F> {
    pub(crate) fn configure<TxTable, RwTable, BytecodeTable>(
        meta: &mut ConstraintSystem<F>,
        randomness: Column<Instance>,
        fixed_table: [Column<Fixed>; 4],
        tx_table: TxTable,
        rw_table: RwTable,
        bytecode_table: BytecodeTable,
    ) -> Self
    where
        TxTable: LookupTable<F, 4>,
        RwTable: LookupTable<F, 8>,
        BytecodeTable: LookupTable<F, 4>,
    {
        let q_step = meta.complex_selector();
        let qs_byte_lookup = meta.advice_column();
        let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());

        let randomness = {
            let mut expr = None;
            meta.create_gate("Query randomness", |meta| {
                expr = Some(meta.query_instance(randomness, Rotation::cur()));
                vec![0.expr()]
            });
            expr.unwrap()
        };

        let step_curr = Step::new(meta, qs_byte_lookup, advices, false);
        let step_next = Step::new(meta, qs_byte_lookup, advices, true);
        let mut independent_lookups = Vec::new();
        let mut presets_map = HashMap::new();

        meta.create_gate("Constrain execution state", |meta| {
            let q_step = meta.query_selector(q_step);

            // Only one of execution_state should be enabled
            let sum_to_one = step_curr
                .state
                .execution_state
                .iter()
                .fold(1.expr(), |acc, cell| acc - cell.expr());

            // Cells representation for execution_state should be bool.
            let bool_checks = step_curr
                .state
                .execution_state
                .iter()
                .map(|cell| cell.expr() * (1.expr() - cell.expr()));

            std::iter::once(sum_to_one)
                .chain(bool_checks)
                .map(move |poly| q_step.clone() * poly)
        });

        // TODO: ExecutionState transition needs to be constraint to avoid
        // transition from non-terminator to BeginTx.

        // Use qs_byte_lookup as selector to do byte range lookup on each advice
        // column. In this way, ExecutionGadget could enable the byte range
        // lookup by enable qs_byte_lookup.
        for advice in advices {
            meta.lookup_any(|meta| {
                let advice = meta.query_advice(advice, Rotation::cur());
                let qs_byte_lookup =
                    meta.query_advice(qs_byte_lookup, Rotation::cur());

                vec![
                    qs_byte_lookup.clone() * FixedTableTag::Range256.expr(),
                    qs_byte_lookup * advice,
                    0.expr(),
                    0.expr(),
                ]
                .into_iter()
                .zip(fixed_table.table_exprs(meta).to_vec().into_iter())
                .collect::<Vec<_>>()
            });
        }

        macro_rules! configure_gadget {
            () => {
                Self::configure_gadget(
                    meta,
                    q_step,
                    &randomness,
                    &step_curr,
                    &step_next,
                    &mut independent_lookups,
                    &mut presets_map,
                )
            };
        }

        let config = Self {
            q_step,
            add_gadget: configure_gadget!(),
            bitwise_gadget: configure_gadget!(),
            byte_gadget: configure_gadget!(),
            comparator_gadget: configure_gadget!(),
            dup_gadget: configure_gadget!(),
            error_oog_pure_memory_gadget: configure_gadget!(),
            jump_gadget: configure_gadget!(),
            jumpdest_gadget: configure_gadget!(),
            jumpi_gadget: configure_gadget!(),
            memory_gadget: configure_gadget!(),
            pc_gadget: configure_gadget!(),
            pop_gadget: configure_gadget!(),
            push_gadget: configure_gadget!(),
            signextend_gadget: configure_gadget!(),
            stop_gadget: configure_gadget!(),
            swap_gadget: configure_gadget!(),
            step: step_curr,
            presets_map,
        };

        Self::configure_lookup(
            meta,
            q_step,
            fixed_table,
            tx_table,
            rw_table,
            bytecode_table,
            independent_lookups,
        );

        config
    }

    fn configure_gadget<G: ExecutionGadget<F>>(
        meta: &mut ConstraintSystem<F>,
        q_step: Selector,
        randomness: &Expression<F>,
        step_curr: &Step<F>,
        step_next: &Step<F>,
        independent_lookups: &mut Vec<Vec<Lookup<F>>>,
        presets_map: &mut HashMap<ExecutionState, Vec<Preset<F>>>,
    ) -> G {
        let mut cb = ConstraintBuilder::new(
            step_curr,
            step_next,
            randomness.clone(),
            G::EXECUTION_STATE,
        );

        let gadget = G::configure(&mut cb);

        let (constraints, lookups, presets) = cb.build();
        assert!(
            presets_map.insert(G::EXECUTION_STATE, presets).is_none(),
            "execution state already configured"
        );

        if !constraints.is_empty() {
            meta.create_gate(G::NAME, |meta| {
                let q_step = meta.query_selector(q_step);

                constraints.into_iter().map(move |(name, constraint)| {
                    (name, q_step.clone() * constraint)
                })
            });
        }

        // Push lookups of this ExecutionState to independent_lookups for
        // further configuration in configure_lookup.
        independent_lookups.push(lookups);

        gadget
    }

    fn configure_lookup<TxTable, RwTable, BytecodeTable>(
        meta: &mut ConstraintSystem<F>,
        q_step: Selector,
        fixed_table: [Column<Fixed>; 4],
        tx_table: TxTable,
        rw_table: RwTable,
        bytecode_table: BytecodeTable,
        independent_lookups: Vec<Vec<Lookup<F>>>,
    ) where
        TxTable: LookupTable<F, 4>,
        RwTable: LookupTable<F, 8>,
        BytecodeTable: LookupTable<F, 4>,
    {
        // Because one and only one ExecutionState is enabled at a step, we then
        // know only one of independent_lookups will be enabled at a step, so we
        // can add up them together to reduce the amount of lookup arguments.
        // This map holds all added up independent lookups as accumulated
        // lookups, and will be used in configuring lookup arguments later.
        let mut acc_lookups_of_table = HashMap::new();

        for lookups in independent_lookups {
            let mut index_of_table = HashMap::new();

            for lookup in lookups {
                let table = lookup.table();
                let acc_lookups =
                    acc_lookups_of_table.entry(table).or_insert_with(Vec::new);
                let index = index_of_table.entry(table).or_insert(0);

                if *index == acc_lookups.len() {
                    acc_lookups.push(lookup.input_exprs());
                } else {
                    // Add up independent lookup together
                    for (acc, expr) in acc_lookups[*index]
                        .iter_mut()
                        .zip(lookup.input_exprs().into_iter())
                    {
                        *acc = acc.clone() + expr;
                    }
                }
                *index += 1;
            }
        }

        macro_rules! lookup {
            ($id:path, $table:ident) => {
                if let Some(acc_lookups) = acc_lookups_of_table.remove(&$id) {
                    for input_exprs in acc_lookups {
                        meta.lookup_any(|meta| {
                            let q_step = meta.query_selector(q_step);
                            input_exprs
                                .into_iter()
                                .zip(
                                    $table
                                        .table_exprs(meta)
                                        .to_vec()
                                        .into_iter(),
                                )
                                .map(|(input, table)| {
                                    (q_step.clone() * input, table)
                                })
                                .collect::<Vec<_>>()
                        });
                    }
                }
            };
        }

        lookup!(Table::Fixed, fixed_table);
        lookup!(Table::Tx, tx_table);
        lookup!(Table::Rw, rw_table);
        lookup!(Table::Bytecode, bytecode_table);
    }

    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Execution step",
            |mut region| {
                let mut offset = 0;
                for transaction in &block.txs {
                    for step in &transaction.steps {
                        let call = &transaction.calls[step.call_idx];

                        self.q_step.enable(&mut region, offset)?;
                        self.assign_exec_step(
                            &mut region,
                            offset,
                            block,
                            transaction,
                            call,
                            step,
                        )?;

                        offset += STEP_HEIGHT;
                    }
                }
                Ok(())
            },
        )
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction<F>,
        call: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.step.assign_exec_step(region, offset, call, step)?;

        for (cell, value) in self
            .presets_map
            .get(&step.execution_state)
            .expect("not implemented")
        {
            cell.assign(region, offset, Some(*value))?;
        }

        macro_rules! assign_exec_step {
            ($gadget:expr) => {
                $gadget.assign_exec_step(
                    region,
                    offset,
                    block,
                    transaction,
                    call,
                    step,
                )?
            };
        }

        match step.execution_state {
            ExecutionState::STOP => assign_exec_step!(self.stop_gadget),
            ExecutionState::ADD => assign_exec_step!(self.add_gadget),
            ExecutionState::BITWISE => assign_exec_step!(self.bitwise_gadget),
            ExecutionState::SIGNEXTEND => {
                assign_exec_step!(self.signextend_gadget)
            }
            ExecutionState::CMP => assign_exec_step!(self.comparator_gadget),
            ExecutionState::BYTE => assign_exec_step!(self.byte_gadget),
            ExecutionState::POP => assign_exec_step!(self.pop_gadget),
            ExecutionState::MEMORY => assign_exec_step!(self.memory_gadget),
            ExecutionState::PC => assign_exec_step!(self.pc_gadget),
            ExecutionState::JUMP => assign_exec_step!(self.jump_gadget),
            ExecutionState::JUMPI => assign_exec_step!(self.jumpi_gadget),
            ExecutionState::JUMPDEST => {
                assign_exec_step!(self.jumpdest_gadget)
            }
            ExecutionState::PUSH => assign_exec_step!(self.push_gadget),
            ExecutionState::DUP => assign_exec_step!(self.dup_gadget),
            ExecutionState::SWAP => assign_exec_step!(self.swap_gadget),
            ExecutionState::ErrorOutOfGasPureMemory => {
                assign_exec_step!(self.error_oog_pure_memory_gadget)
            }
            _ => unimplemented!(),
        }

        Ok(())
    }
}

use super::util::{CachedRegion, StoredExpression};
use crate::{
    evm_circuit::{
        param::{MAX_STEP_HEIGHT, STEP_WIDTH},
        step::{ExecutionState, Preset, Step},
        table::{FixedTableTag, Lookup, LookupTable, Table},
        util::constraint_builder::{BaseConstraintBuilder, ConstraintBuilder},
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use std::{collections::HashMap, convert::TryInto, iter};

mod add;
mod begin_tx;
mod bitwise;
mod byte;
mod calldatacopy;
mod calldataload;
mod calldatasize;
mod caller;
mod callvalue;
mod coinbase;
mod comparator;
mod dup;
mod end_block;
mod end_tx;
mod error_oog_static_memory;
mod extcodehash;
mod gas;
mod is_zero;
mod jump;
mod jumpdest;
mod jumpi;
mod memory;
mod memory_copy;
mod msize;
mod mul;
mod number;
mod pc;
mod pop;
mod push;
mod selfbalance;
mod signed_comparator;
mod signextend;
mod sload;
mod sstore;
mod stop;
mod swap;
mod timestamp;

use add::AddGadget;
use begin_tx::BeginTxGadget;
use bitwise::BitwiseGadget;
use byte::ByteGadget;
use calldatacopy::CallDataCopyGadget;
use calldataload::CallDataLoadGadget;
use calldatasize::CallDataSizeGadget;
use caller::CallerGadget;
use callvalue::CallValueGadget;
use coinbase::CoinbaseGadget;
use comparator::ComparatorGadget;
use dup::DupGadget;
use end_block::EndBlockGadget;
use end_tx::EndTxGadget;
use error_oog_static_memory::ErrorOOGStaticMemoryGadget;
use extcodehash::ExtcodehashGadget;
use gas::GasGadget;
use is_zero::IsZeroGadget;
use jump::JumpGadget;
use jumpdest::JumpdestGadget;
use jumpi::JumpiGadget;
use memory::MemoryGadget;
use memory_copy::CopyToMemoryGadget;
use msize::MsizeGadget;
use mul::MulGadget;
use number::NumberGadget;
use pc::PcGadget;
use pop::PopGadget;
use push::PushGadget;
use selfbalance::SelfbalanceGadget;
use signed_comparator::SignedComparatorGadget;
use signextend::SignextendGadget;
use sload::SloadGadget;
use sstore::SstoreGadget;
use stop::StopGadget;
use swap::SwapGadget;
use timestamp::TimestampGadget;

pub(crate) trait ExecutionGadget<F: FieldExt> {
    const NAME: &'static str;

    const EXECUTION_STATE: ExecutionState;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self;

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug)]
pub(crate) struct ExecutionConfig<F> {
    q_usable: Selector,
    q_step: Column<Advice>,
    num_rows_until_next_step: Column<Advice>,
    num_rows_inv: Column<Advice>,
    q_step_first: Selector,
    q_step_last: Selector,
    advices: [Column<Advice>; STEP_WIDTH],
    step: Step<F>,
    presets_map: HashMap<ExecutionState, Vec<Preset<F>>>,
    height_map: HashMap<ExecutionState, usize>,
    stored_expressions_map: HashMap<ExecutionState, Vec<StoredExpression<F>>>,
    add_gadget: AddGadget<F>,
    mul_gadget: MulGadget<F>,
    bitwise_gadget: BitwiseGadget<F>,
    begin_tx_gadget: BeginTxGadget<F>,
    byte_gadget: ByteGadget<F>,
    calldatacopy_gadget: CallDataCopyGadget<F>,
    calldataload_gadget: CallDataLoadGadget<F>,
    calldatasize_gadget: CallDataSizeGadget<F>,
    caller_gadget: CallerGadget<F>,
    call_value_gadget: CallValueGadget<F>,
    comparator_gadget: ComparatorGadget<F>,
    dup_gadget: DupGadget<F>,
    end_block_gadget: EndBlockGadget<F>,
    end_tx_gadget: EndTxGadget<F>,
    error_oog_static_memory_gadget: ErrorOOGStaticMemoryGadget<F>,
    jump_gadget: JumpGadget<F>,
    jumpdest_gadget: JumpdestGadget<F>,
    jumpi_gadget: JumpiGadget<F>,
    gas_gadget: GasGadget<F>,
    memory_gadget: MemoryGadget<F>,
    copy_to_memory_gadget: CopyToMemoryGadget<F>,
    pc_gadget: PcGadget<F>,
    pop_gadget: PopGadget<F>,
    push_gadget: PushGadget<F>,
    signed_comparator_gadget: SignedComparatorGadget<F>,
    signextend_gadget: SignextendGadget<F>,
    stop_gadget: StopGadget<F>,
    swap_gadget: SwapGadget<F>,
    msize_gadget: MsizeGadget<F>,
    coinbase_gadget: CoinbaseGadget<F>,
    timestamp_gadget: TimestampGadget<F>,
    selfbalance_gadget: SelfbalanceGadget<F>,
    number_gadget: NumberGadget<F>,
    sload_gadget: SloadGadget<F>,
    sstore_gadget: SstoreGadget<F>,
    extcodehash_gadget: ExtcodehashGadget<F>,
    iszero_gadget: IsZeroGadget<F>,
}

impl<F: Field> ExecutionConfig<F> {
    pub(crate) fn configure<TxTable, RwTable, BytecodeTable, BlockTable>(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; 31],
        fixed_table: [Column<Fixed>; 4],
        tx_table: TxTable,
        rw_table: RwTable,
        bytecode_table: BytecodeTable,
        block_table: BlockTable,
    ) -> Self
    where
        TxTable: LookupTable<F, 4>,
        RwTable: LookupTable<F, 11>,
        BytecodeTable: LookupTable<F, 4>,
        BlockTable: LookupTable<F, 3>,
    {
        let q_usable = meta.complex_selector();
        let q_step = meta.advice_column();
        let num_rows_until_next_step = meta.advice_column();
        let num_rows_inv = meta.advice_column();
        let q_step_first = meta.complex_selector();
        let q_step_last = meta.complex_selector();
        let qs_byte_lookup = meta.advice_column();
        let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());

        let step_curr = Step::new(meta, qs_byte_lookup, advices, 0);
        let mut independent_lookups = Vec::new();
        let mut presets_map = HashMap::new();
        let mut height_map = HashMap::new();

        meta.create_gate("Constrain execution state", |meta| {
            let q_usable = meta.query_selector(q_usable);
            let q_step = meta.query_advice(q_step, Rotation::cur());
            let q_step_first = meta.query_selector(q_step_first);
            let q_step_last = meta.query_selector(q_step_last);

            // Only one of execution_state should be enabled
            let sum_to_one = (
                "Only one of execution_state should be enabled",
                step_curr
                    .state
                    .execution_state
                    .iter()
                    .fold(1u64.expr(), |acc, cell| acc - cell.expr()),
            );

            // Cells representation for execution_state should be bool.
            let bool_checks = step_curr.state.execution_state.iter().map(|cell| {
                (
                    "Representation for execution_state should be bool",
                    cell.expr() * (1u64.expr() - cell.expr()),
                )
            });

            let _first_step_check = {
                let begin_tx_selector =
                    step_curr.execution_state_selector([ExecutionState::BeginTx]);
                iter::once((
                    "First step should be BeginTx",
                    q_step_first * (1.expr() - begin_tx_selector),
                ))
            };

            let _last_step_check = {
                let end_block_selector =
                    step_curr.execution_state_selector([ExecutionState::EndBlock]);
                iter::once((
                    "Last step should be EndBlock",
                    q_step_last * (1.expr() - end_block_selector),
                ))
            };

            iter::once(sum_to_one)
                .chain(bool_checks)
                .map(move |(name, poly)| (name, q_usable.clone() * q_step.clone() * poly))
            // TODO: Enable these after test of CALLDATACOPY is complete.
            // .chain(first_step_check)
            // .chain(last_step_check)
        });

        meta.create_gate("q_step", |meta| {
            let q_usable = meta.query_selector(q_usable);
            let q_step_first = meta.query_selector(q_step_first);
            let q_step = meta.query_advice(q_step, Rotation::cur());
            let num_rows_left_cur = meta.query_advice(num_rows_until_next_step, Rotation::cur());
            let num_rows_left_next = meta.query_advice(num_rows_until_next_step, Rotation::next());
            let num_rows_left_inverse = meta.query_advice(num_rows_inv, Rotation::cur());

            let mut cb = BaseConstraintBuilder::default();
            // q_step needs to be enabled on the first row
            cb.condition(q_step_first, |cb| {
                cb.require_equal("q_step == 1", q_step.clone(), 1.expr());
            });
            // Except when step is enabled, the step counter needs to decrease by 1
            cb.condition(1.expr() - q_step.clone(), |cb| {
                cb.require_equal(
                    "num_rows_left_cur := num_rows_left_next + 1",
                    num_rows_left_cur.clone(),
                    num_rows_left_next + 1.expr(),
                );
            });
            // Enforce that q_step := num_rows_until_next_step == 0
            let is_zero = 1.expr() - (num_rows_left_cur.clone() * num_rows_left_inverse.clone());
            cb.require_zero(
                "num_rows_left_cur * is_zero == 0",
                num_rows_left_cur * is_zero.clone(),
            );
            cb.require_zero(
                "num_rows_left_inverse * is_zero == 0",
                num_rows_left_inverse * is_zero.clone(),
            );
            cb.require_equal("q_step == is_zero", q_step, is_zero);
            // On each usable row
            cb.gate(q_usable)
        });

        // Use qs_byte_lookup as selector to do byte range lookup on each advice
        // column. In this way, ExecutionGadget could enable the byte range
        // lookup by enable qs_byte_lookup.
        for advice in advices {
            meta.lookup_any("Qs byte", |meta| {
                let advice = meta.query_advice(advice, Rotation::cur());
                let qs_byte_lookup = meta.query_advice(qs_byte_lookup, Rotation::cur());

                vec![
                    qs_byte_lookup.clone() * FixedTableTag::Range256.expr(),
                    qs_byte_lookup * advice,
                    0u64.expr(),
                    0u64.expr(),
                ]
                .into_iter()
                .zip(fixed_table.table_exprs(meta).to_vec().into_iter())
                .collect::<Vec<_>>()
            });
        }

        let mut stored_expressions_map = HashMap::new();
        macro_rules! configure_gadget {
            () => {
                Self::configure_gadget(
                    meta,
                    advices,
                    q_usable,
                    q_step,
                    num_rows_until_next_step,
                    q_step_first,
                    q_step_last,
                    qs_byte_lookup,
                    &power_of_randomness,
                    &step_curr,
                    &mut independent_lookups,
                    &mut presets_map,
                    &mut height_map,
                    &mut stored_expressions_map,
                )
            };
        }

        let config = Self {
            q_usable,
            q_step,
            num_rows_until_next_step,
            num_rows_inv,
            q_step_first,
            q_step_last,
            advices,
            add_gadget: configure_gadget!(),
            mul_gadget: configure_gadget!(),
            bitwise_gadget: configure_gadget!(),
            begin_tx_gadget: configure_gadget!(),
            byte_gadget: configure_gadget!(),
            calldatacopy_gadget: configure_gadget!(),
            calldataload_gadget: configure_gadget!(),
            calldatasize_gadget: configure_gadget!(),
            caller_gadget: configure_gadget!(),
            call_value_gadget: configure_gadget!(),
            comparator_gadget: configure_gadget!(),
            dup_gadget: configure_gadget!(),
            end_block_gadget: configure_gadget!(),
            end_tx_gadget: configure_gadget!(),
            error_oog_static_memory_gadget: configure_gadget!(),
            jump_gadget: configure_gadget!(),
            jumpdest_gadget: configure_gadget!(),
            jumpi_gadget: configure_gadget!(),
            gas_gadget: configure_gadget!(),
            memory_gadget: configure_gadget!(),
            copy_to_memory_gadget: configure_gadget!(),
            pc_gadget: configure_gadget!(),
            pop_gadget: configure_gadget!(),
            push_gadget: configure_gadget!(),
            selfbalance_gadget: configure_gadget!(),
            signed_comparator_gadget: configure_gadget!(),
            signextend_gadget: configure_gadget!(),
            stop_gadget: configure_gadget!(),
            swap_gadget: configure_gadget!(),
            msize_gadget: configure_gadget!(),
            coinbase_gadget: configure_gadget!(),
            timestamp_gadget: configure_gadget!(),
            number_gadget: configure_gadget!(),
            sload_gadget: configure_gadget!(),
            sstore_gadget: configure_gadget!(),
            extcodehash_gadget: configure_gadget!(),
            iszero_gadget: configure_gadget!(),
            step: step_curr,
            presets_map,
            height_map,
            stored_expressions_map,
        };

        Self::configure_lookup(
            meta,
            q_usable,
            q_step,
            fixed_table,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            independent_lookups,
        );

        config
    }

    pub fn get_step_height(&self, execution_state: ExecutionState) -> usize {
        *self
            .height_map
            .get(&execution_state)
            .unwrap_or_else(|| panic!("Execution state unknown: {:?}", execution_state))
    }

    #[allow(clippy::too_many_arguments)]
    fn configure_gadget<G: ExecutionGadget<F>>(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; STEP_WIDTH],
        q_usable: Selector,
        q_step: Column<Advice>,
        num_rows_until_next_step: Column<Advice>,
        q_step_first: Selector,
        q_step_last: Selector,
        qs_byte_lookup: Column<Advice>,
        power_of_randomness: &[Expression<F>; 31],
        step_curr: &Step<F>,
        independent_lookups: &mut Vec<Vec<Lookup<F>>>,
        presets_map: &mut HashMap<ExecutionState, Vec<Preset<F>>>,
        height_map: &mut HashMap<ExecutionState, usize>,
        stored_expressions_map: &mut HashMap<ExecutionState, Vec<StoredExpression<F>>>,
    ) -> G {
        // Configure the gadget with the max height first so we can find out the actual
        // height
        let height = {
            let step_next = &Step::new(meta, qs_byte_lookup, advices, MAX_STEP_HEIGHT);
            let mut cb = ConstraintBuilder::new(
                step_curr,
                step_next,
                power_of_randomness,
                G::EXECUTION_STATE,
            );
            G::configure(&mut cb);
            let (_, _, _, _, height, _) = cb.build();
            step_curr.rotation_offset + height
        };

        // Now actually configure the gadget with the correct minimal height
        let step_next = &Step::new(meta, qs_byte_lookup, advices, height);
        let mut cb = ConstraintBuilder::new(
            step_curr,
            step_next,
            power_of_randomness,
            G::EXECUTION_STATE,
        );

        let gadget = G::configure(&mut cb);

        // Enforce the step height for this opcode
        let mut num_rows_until_next_step_next = 0.expr();
        meta.create_gate("query num rows", |meta| {
            num_rows_until_next_step_next =
                meta.query_advice(num_rows_until_next_step, Rotation::next());
            vec![0.expr()]
        });
        cb.require_equal(
            "num_rows_until_next_step_next := height - 1",
            num_rows_until_next_step_next,
            (height - 1).expr(),
        );

        let (constraints, constraints_first_step, lookups, presets, _, stored_expressions) =
            cb.build();

        debug_assert!(
            presets_map.insert(G::EXECUTION_STATE, presets).is_none(),
            "execution state already configured"
        );
        debug_assert!(
            height_map.insert(G::EXECUTION_STATE, height).is_none(),
            "execution state already configured"
        );
        debug_assert!(
            stored_expressions_map
                .insert(G::EXECUTION_STATE, stored_expressions)
                .is_none(),
            "execution state already configured"
        );

        // Enforce the logic for this opcode
        let q_steps: &dyn Fn(&mut VirtualCells<F>) -> Expression<F> =
            &|meta| meta.query_advice(q_step, Rotation::cur());
        let q_steps_first: &dyn Fn(&mut VirtualCells<F>) -> Expression<F> =
            &|meta| meta.query_selector(q_step_first);
        for (selector, constraints) in [
            (q_steps, constraints),
            (q_steps_first, constraints_first_step),
        ] {
            if !constraints.is_empty() {
                meta.create_gate(G::NAME, |meta| {
                    let q_usable = meta.query_selector(q_usable);
                    let selector = selector(meta);
                    constraints.into_iter().map(move |(name, constraint)| {
                        (name, q_usable.clone() * selector.clone() * constraint)
                    })
                });
            }
        }

        // Enforce the state transitions for this opcode
        meta.create_gate("Constrain state machine transitions", |meta| {
            let q_usable = meta.query_selector(q_usable);
            let q_step = meta.query_advice(q_step, Rotation::cur());
            let q_step_last = meta.query_selector(q_step_last);

            // ExecutionState transition should be correct.
            iter::empty()
                .chain(
                    IntoIterator::into_iter([
                        (
                            "EndTx can only transit to BeginTx or EndBlock",
                            ExecutionState::EndTx,
                            vec![ExecutionState::BeginTx, ExecutionState::EndBlock],
                        ),
                        (
                            "EndBlock can only transit to EndBlock",
                            ExecutionState::EndBlock,
                            vec![ExecutionState::EndBlock],
                        ),
                    ])
                    .filter(move |(_, from, _)| *from == G::EXECUTION_STATE)
                    .map(|(_, _, to)| {
                        1.expr() - step_next.execution_state_selector(to)
                    }),
                )
                .chain(
                    IntoIterator::into_iter([
                        (
                            "Only EndTx can transit to BeginTx",
                            ExecutionState::BeginTx,
                            vec![ExecutionState::EndTx],
                        ),
                        (
                            "Only ExecutionState which halts or BeginTx can transit to EndTx",
                            ExecutionState::EndTx,
                            ExecutionState::iterator()
                                .filter(ExecutionState::halts)
                                .chain(iter::once(ExecutionState::BeginTx))
                                .collect(),
                        ),
                        (
                            "Only EndTx or EndBlock can transit to EndBlock",
                            ExecutionState::EndBlock,
                            vec![ExecutionState::EndTx, ExecutionState::EndBlock],
                        ),
                        (
                            "Only ExecutionState which copies memory to memory can transit to CopyToMemory",
                            ExecutionState::CopyToMemory,
                            vec![ExecutionState::CopyToMemory, ExecutionState::CALLDATACOPY],
                        ),
                    ])
                    .filter(move |(_, _, from)| !from.contains(&G::EXECUTION_STATE))
                    .map(|(_, to, _)| {
                        step_next.execution_state_selector([to])
                    }),
                )
                // Accumulate all state transition checks.
                // This can be done because all summed values are enforced to be boolean.
                .reduce(|accum, poly| accum + poly)
                .map(move |poly| {
                        q_usable.clone()
                            * q_step.clone()
                            * (1.expr() - q_step_last.clone())
                            * step_curr.execution_state_selector([G::EXECUTION_STATE])
                            * poly
                })
        });

        // Push lookups of this ExecutionState to independent_lookups for
        // further configuration in configure_lookup.
        independent_lookups.push(lookups.iter().map(|(_, lookup)| lookup.clone()).collect());

        gadget
    }

    #[allow(clippy::too_many_arguments)]
    fn configure_lookup<TxTable, RwTable, BytecodeTable, BlockTable>(
        meta: &mut ConstraintSystem<F>,
        q_usable: Selector,
        q_step: Column<Advice>,
        fixed_table: [Column<Fixed>; 4],
        tx_table: TxTable,
        rw_table: RwTable,
        bytecode_table: BytecodeTable,
        block_table: BlockTable,
        independent_lookups: Vec<Vec<Lookup<F>>>,
    ) where
        TxTable: LookupTable<F, 4>,
        RwTable: LookupTable<F, 11>,
        BytecodeTable: LookupTable<F, 4>,
        BlockTable: LookupTable<F, 3>,
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
                let acc_lookups = acc_lookups_of_table.entry(table).or_insert_with(Vec::new);
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
            ($id:path, $table:ident, $descrip:expr) => {
                if let Some(acc_lookups) = acc_lookups_of_table.remove(&$id) {
                    for input_exprs in acc_lookups {
                        meta.lookup_any(concat!("LOOKUP: ", stringify!($descrip)), |meta| {
                            let q_usable = meta.query_selector(q_usable);
                            let q_step = meta.query_advice(q_step, Rotation::cur());
                            input_exprs
                                .into_iter()
                                .zip($table.table_exprs(meta).to_vec().into_iter())
                                .map(|(input, table)| {
                                    (q_usable.clone() * q_step.clone() * input, table)
                                })
                                .collect::<Vec<_>>()
                        });
                    }
                }
            };
        }

        lookup!(Table::Fixed, fixed_table, "Fixed table");
        lookup!(Table::Tx, tx_table, "Tx table");
        lookup!(Table::Rw, rw_table, "RW table");
        lookup!(Table::Bytecode, bytecode_table, "Bytecode table");
        lookup!(Table::Block, block_table, "Block table");
    }

    /// Assign block
    /// When exact is enabled, assign exact steps in block without padding for
    /// unit test purpose
    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
        _exact: bool,
    ) -> Result<(), Error> {
        let power_of_randomness = (1..32)
            .map(|exp| block.randomness.pow(&[exp, 0, 0, 0]))
            .collect::<Vec<F>>()
            .try_into()
            .unwrap();

        layouter.assign_region(
            || "Execution step",
            |mut region| {
                let mut offset = 0;

                self.q_step_first.enable(&mut region, offset)?;

                let mut last_height = 0;
                for transaction in &block.txs {
                    for (step, step_next) in transaction.steps.iter().zip(
                        transaction
                            .steps
                            .iter()
                            .map(Some)
                            .skip(1)
                            .chain(iter::once(None)),
                    ) {
                        let call = &transaction.calls[step.call_index];

                        let height = self.get_step_height(step.execution_state);

                        self.assign_exec_step(
                            &mut region,
                            offset,
                            block,
                            transaction,
                            call,
                            step,
                            height,
                            step_next,
                            power_of_randomness,
                        )?;

                        for idx in 0..height {
                            let offset = offset + idx;
                            self.q_usable.enable(&mut region, offset)?;
                            region.assign_advice(
                                || "step selector",
                                self.q_step,
                                offset,
                                || Ok(if idx == 0 { F::one() } else { F::zero() }),
                            )?;
                            let value = if idx == 0 {
                                F::zero()
                            } else {
                                F::from((height - idx) as u64)
                            };
                            region.assign_advice(
                                || "step height",
                                self.num_rows_until_next_step,
                                offset,
                                || Ok(value),
                            )?;
                            region.assign_advice(
                                || "step height inv",
                                self.num_rows_inv,
                                offset,
                                || Ok(value.invert().unwrap_or(F::zero())),
                            )?;
                        }

                        offset += height;
                        last_height = height;
                    }
                }
                // These are still referenced (but not used) in next rows
                region.assign_advice(
                    || "step height",
                    self.num_rows_until_next_step,
                    offset,
                    || Ok(F::zero()),
                )?;
                region.assign_advice(
                    || "step height inv",
                    self.q_step,
                    offset,
                    || Ok(F::zero()),
                )?;

                // If not exact:
                // TODO: Pad leftover region to the desired capacity
                // TODO: Enable q_step_last
                self.q_step_last.enable(&mut region, offset - last_height)?;

                Ok(())
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
        height: usize,
        step_next: Option<&ExecStep>,
        power_of_randomness: [F; 31],
    ) -> Result<(), Error> {
        let region = &mut CachedRegion::<'_, '_, F>::new(
            region,
            power_of_randomness,
            STEP_WIDTH,
            MAX_STEP_HEIGHT * 2,
            self.advices[0].index(),
            offset,
        );

        // Also set the witnesses of the next step
        // These may be used in stored expressions and
        // so their witness values need to be known to be able
        // to correctly calculate the intermediate value.
        if let Some(step_next) = step_next {
            self.assign_exec_step_int(
                region,
                offset + height,
                block,
                transaction,
                call,
                step_next,
            )?;
        }

        self.assign_exec_step_int(region, offset, block, transaction, call, step)
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_exec_step_int(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.step
            .assign_exec_step(region, offset, block, transaction, call, step)?;

        for (cell, value) in self
            .presets_map
            .get(&step.execution_state)
            .expect("not implemented")
        {
            cell.assign(region, offset, Some(*value))?;
        }

        macro_rules! assign_exec_step {
            ($gadget:expr) => {
                $gadget.assign_exec_step(region, offset, block, transaction, call, step)?
            };
        }

        match step.execution_state {
            ExecutionState::BeginTx => assign_exec_step!(self.begin_tx_gadget),
            ExecutionState::EndTx => assign_exec_step!(self.end_tx_gadget),
            ExecutionState::EndBlock => {
                assign_exec_step!(self.end_block_gadget)
            }
            ExecutionState::STOP => assign_exec_step!(self.stop_gadget),
            ExecutionState::ADD => assign_exec_step!(self.add_gadget),
            ExecutionState::MUL => assign_exec_step!(self.mul_gadget),
            ExecutionState::BITWISE => assign_exec_step!(self.bitwise_gadget),
            ExecutionState::SIGNEXTEND => {
                assign_exec_step!(self.signextend_gadget)
            }
            ExecutionState::CMP => assign_exec_step!(self.comparator_gadget),
            ExecutionState::SCMP => {
                assign_exec_step!(self.signed_comparator_gadget)
            }
            ExecutionState::BYTE => assign_exec_step!(self.byte_gadget),
            ExecutionState::POP => assign_exec_step!(self.pop_gadget),
            ExecutionState::MEMORY => assign_exec_step!(self.memory_gadget),
            ExecutionState::PC => assign_exec_step!(self.pc_gadget),
            ExecutionState::MSIZE => assign_exec_step!(self.msize_gadget),
            ExecutionState::JUMP => assign_exec_step!(self.jump_gadget),
            ExecutionState::JUMPI => assign_exec_step!(self.jumpi_gadget),
            ExecutionState::JUMPDEST => {
                assign_exec_step!(self.jumpdest_gadget)
            }
            ExecutionState::GAS => assign_exec_step!(self.gas_gadget),
            ExecutionState::PUSH => assign_exec_step!(self.push_gadget),
            ExecutionState::DUP => assign_exec_step!(self.dup_gadget),
            ExecutionState::SWAP => assign_exec_step!(self.swap_gadget),
            ExecutionState::CALLER => assign_exec_step!(self.caller_gadget),
            ExecutionState::CALLVALUE => {
                assign_exec_step!(self.call_value_gadget)
            }
            ExecutionState::COINBASE => assign_exec_step!(self.coinbase_gadget),
            ExecutionState::TIMESTAMP => {
                assign_exec_step!(self.timestamp_gadget)
            }
            ExecutionState::NUMBER => {
                assign_exec_step!(self.number_gadget)
            }
            ExecutionState::SELFBALANCE => assign_exec_step!(self.selfbalance_gadget),
            ExecutionState::SLOAD => assign_exec_step!(self.sload_gadget),
            ExecutionState::SSTORE => assign_exec_step!(self.sstore_gadget),
            ExecutionState::CALLDATACOPY => {
                assign_exec_step!(self.calldatacopy_gadget)
            }
            ExecutionState::EXTCODEHASH => {
                assign_exec_step!(self.extcodehash_gadget)
            }
            ExecutionState::CopyToMemory => {
                assign_exec_step!(self.copy_to_memory_gadget)
            }
            ExecutionState::CALLDATALOAD => {
                assign_exec_step!(self.calldataload_gadget)
            }
            ExecutionState::ErrorOutOfGasStaticMemoryExpansion => {
                assign_exec_step!(self.error_oog_static_memory_gadget)
            }
            ExecutionState::CALLDATASIZE => {
                assign_exec_step!(self.calldatasize_gadget)
            }
            ExecutionState::ISZERO => assign_exec_step!(self.iszero_gadget),
            _ => unimplemented!(),
        }

        // Fill in witness values for stored expressions
        for stored_expression in self
            .stored_expressions_map
            .get(&step.execution_state)
            .expect("not implemented")
        {
            stored_expression.assign(region, offset)?;
        }

        Ok(())
    }
}

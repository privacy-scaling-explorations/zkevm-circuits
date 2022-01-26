use crate::{
    evm_circuit::{
        param::{STEP_HEIGHT, STEP_WIDTH},
        step::{ExecutionState, Step},
        table::{LookupTable, Table},
        util::{
            constraint_builder::ConstraintBuilder, random_linear_combine,
            CellType,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::{Column, ConstraintSystem, Error, Expression, Fixed, Selector},
};
use std::collections::HashMap;

mod add;
mod begin_tx;
mod bitwise;
mod byte;
mod coinbase;
mod comparator;
mod dup;
mod error_oog_pure_memory;
mod jump;
mod jumpdest;
mod jumpi;
mod memory;
mod msize;
mod mul;
mod pc;
mod pop;
mod push;
mod signed_comparator;
mod signextend;
mod stop;
mod swap;

use add::AddGadget;
use begin_tx::BeginTxGadget;
use bitwise::BitwiseGadget;
use byte::ByteGadget;
use coinbase::CoinbaseGadget;
use comparator::ComparatorGadget;
use dup::DupGadget;
use error_oog_pure_memory::ErrorOOGPureMemoryGadget;
use jump::JumpGadget;
use jumpdest::JumpdestGadget;
use jumpi::JumpiGadget;
use memory::MemoryGadget;
use msize::MsizeGadget;
use mul::MulGadget;
use pc::PcGadget;
use pop::PopGadget;
use push::PushGadget;
use signed_comparator::SignedComparatorGadget;
use signextend::SignextendGadget;
use stop::StopGadget;
use swap::SwapGadget;

use super::util::{CachedRegion, CellColumn, IntermediateResult};

pub(crate) trait ExecutionGadget<F: FieldExt> {
    const NAME: &'static str;

    const EXECUTION_STATE: ExecutionState;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self;

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
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
    q_step_first: Selector,
    step: Step<F>,
    intermediates_map: HashMap<ExecutionState, Vec<IntermediateResult<F>>>,
    add_gadget: AddGadget<F>,
    mul_gadget: MulGadget<F>,
    bitwise_gadget: BitwiseGadget<F>,
    begin_tx_gadget: BeginTxGadget<F>,
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
    signed_comparator_gadget: SignedComparatorGadget<F>,
    signextend_gadget: SignextendGadget<F>,
    stop_gadget: StopGadget<F>,
    swap_gadget: SwapGadget<F>,
    msize_gadget: MsizeGadget<F>,
    coinbase_gadget: CoinbaseGadget<F>,
}

impl<F: FieldExt> ExecutionConfig<F> {
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
        RwTable: LookupTable<F, 8>,
        BytecodeTable: LookupTable<F, 4>,
        BlockTable: LookupTable<F, 3>,
    {
        let q_step = meta.complex_selector();
        let q_step_first = meta.complex_selector();
        let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());

        let step_curr = Step::new(meta, advices, false);
        let step_next = Step::new(meta, advices, true);

        meta.create_gate("Constrain execution state", |meta| {
            let q_step = meta.query_selector(q_step);
            let q_step_first = meta.query_selector(q_step_first);

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
            let bool_checks =
                step_curr.state.execution_state.iter().map(|cell| {
                    (
                        "Representation for execution_state should be bool",
                        cell.expr() * (1u64.expr() - cell.expr()),
                    )
                });

            // TODO: ExecutionState transition needs to be constraint to avoid
            // transition from non-terminator to BeginTx.

            let first_step_check = {
                let begin_tx_selector =
                    step_curr.execution_state_selector(ExecutionState::BeginTx);
                std::iter::once((
                    "First step should be BeginTx",
                    q_step_first * (begin_tx_selector - 1u64.expr()),
                ))
            };

            std::iter::once(sum_to_one)
                .chain(bool_checks)
                .map(move |(name, poly)| (name, q_step.clone() * poly))
                .chain(first_step_check)
        });

        let mut intermediates_map = HashMap::new();
        let mut columns = step_curr.cell_manager.columns.clone();
        macro_rules! configure_gadget {
            () => {
                Self::configure_gadget(
                    meta,
                    q_step,
                    q_step_first,
                    &power_of_randomness,
                    &step_curr,
                    &step_next,
                    &mut intermediates_map,
                    &mut columns,
                )
            };
        }

        let config = Self {
            q_step,
            q_step_first,
            add_gadget: configure_gadget!(),
            mul_gadget: configure_gadget!(),
            bitwise_gadget: configure_gadget!(),
            begin_tx_gadget: configure_gadget!(),
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
            signed_comparator_gadget: configure_gadget!(),
            signextend_gadget: configure_gadget!(),
            stop_gadget: configure_gadget!(),
            swap_gadget: configure_gadget!(),
            msize_gadget: configure_gadget!(),
            coinbase_gadget: configure_gadget!(),
            step: step_curr,
            intermediates_map,
        };

        Self::configure_lookup(
            meta,
            fixed_table,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            &power_of_randomness,
            &columns,
        );

        config
    }

    #[allow(clippy::too_many_arguments)]
    fn configure_gadget<G: ExecutionGadget<F>>(
        meta: &mut ConstraintSystem<F>,
        q_step: Selector,
        q_step_first: Selector,
        power_of_randomness: &[Expression<F>; 31],
        step_curr: &Step<F>,
        step_next: &Step<F>,
        intermediates_map: &mut HashMap<
            ExecutionState,
            Vec<IntermediateResult<F>>,
        >,
        columns: &mut Vec<CellColumn<F>>,
    ) -> G {
        // Setup the cell manager to the latest layout
        let mut cell_manager = step_curr.cell_manager.clone();
        for (to, from) in cell_manager.columns.iter_mut().zip(columns.iter()) {
            to.cell_type = from.cell_type;
        }

        let mut cb = ConstraintBuilder::new(
            cell_manager,
            step_curr,
            step_next,
            power_of_randomness,
            G::EXECUTION_STATE,
        );

        let gadget = G::configure(&mut cb);
        println!(
            "{}: {} lookups, {} intermediates, {} cells ({} bytes)",
            G::NAME,
            cb.lookups.len(),
            cb.intermediate_results.len(),
            cb.num_cells,
            cb.num_bytes
        );

        let (
            constraints,
            constraints_first_step,
            new_columns,
            intermediate_results,
        ) = cb.build();
        assert!(
            intermediates_map
                .insert(G::EXECUTION_STATE, intermediate_results)
                .is_none(),
            "execution state already configured"
        );

        // Copy the updated column layout
        *columns = new_columns;

        for (selector, constraints) in [
            (q_step, constraints),
            (q_step_first, constraints_first_step),
        ] {
            if !constraints.is_empty() {
                meta.create_gate(G::NAME, |meta| {
                    let selector = meta.query_selector(selector);

                    constraints.into_iter().map(move |(name, constraint)| {
                        (name, selector.clone() * constraint)
                    })
                });
            }
        }

        gadget
    }

    #[allow(clippy::too_many_arguments)]
    fn configure_lookup<TxTable, RwTable, BytecodeTable, BlockTable>(
        meta: &mut ConstraintSystem<F>,
        fixed_table: [Column<Fixed>; 4],
        tx_table: TxTable,
        rw_table: RwTable,
        bytecode_table: BytecodeTable,
        block_table: BlockTable,
        power_of_randomness: &[Expression<F>; 31],
        columns: &[CellColumn<F>],
    ) where
        TxTable: LookupTable<F, 4>,
        RwTable: LookupTable<F, 8>,
        BytecodeTable: LookupTable<F, 4>,
        BlockTable: LookupTable<F, 3>,
    {
        let mut num_lookups = 0;
        for column in columns.iter() {
            //println!("{} -> {:?}", column.index, column.cell_type);
            if let CellType::Lookup(table) = column.cell_type {
                meta.lookup_any(|meta| {
                    let table_expressions = match table {
                        Table::Fixed => {
                            fixed_table.table_exprs(meta).to_vec()
                        }
                        Table::Tx => tx_table.table_exprs(meta).to_vec(),
                        Table::Rw => rw_table.table_exprs(meta).to_vec(),
                        Table::Bytecode => {
                            bytecode_table.table_exprs(meta).to_vec()
                        }
                        Table::Block => {
                            block_table.table_exprs(meta).to_vec()
                        }
                    };
                    let table = random_linear_combine(
                        table_expressions,
                        power_of_randomness,
                    );
                    vec![(column.expr.clone(), table)]
                });
                num_lookups += 1;
            }
        }
        println!("num lookups/row: {}", num_lookups);
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
                        let call = &transaction.calls[step.call_index];

                        self.q_step.enable(&mut region, offset)?;
                        if offset == 0 {
                            self.q_step_first.enable(&mut region, offset)?;
                        }

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
        )?;

        // TODO: Pad leftover region to the desired capacity

        Ok(())
    }

    /// Assign exact steps in block without padding for unit test purpose
    pub fn assign_block_exact(
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
                        let call = &transaction.calls[step.call_index];

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
        println!("Step {}", offset);

        let mut cached_region =
            CachedRegion::<'_, '_, F>::new(region, block.randomness);

        self.step
            .assign_exec_step(&mut cached_region, offset, call, step)?;

        macro_rules! assign_exec_step {
            ($gadget:expr) => {
                $gadget.assign_exec_step(
                    &mut cached_region,
                    offset,
                    block,
                    transaction,
                    call,
                    step,
                )?
            };
        }

        match step.execution_state {
            ExecutionState::BeginTx => assign_exec_step!(self.begin_tx_gadget),
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
            ExecutionState::PUSH => assign_exec_step!(self.push_gadget),
            ExecutionState::DUP => assign_exec_step!(self.dup_gadget),
            ExecutionState::SWAP => assign_exec_step!(self.swap_gadget),
            ExecutionState::COINBASE => assign_exec_step!(self.coinbase_gadget),
            ExecutionState::ErrorOutOfGasPureMemory => {
                assign_exec_step!(self.error_oog_pure_memory_gadget)
            }
            _ => unimplemented!(),
        }

        for intermediate in self
            .intermediates_map
            .get(&step.execution_state)
            .expect("not implemented")
        {
            intermediate.assign(&mut cached_region, offset)?;
        }

        Ok(())
    }
}

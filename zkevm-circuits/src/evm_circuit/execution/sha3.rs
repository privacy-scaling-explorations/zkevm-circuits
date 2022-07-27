use bus_mapping::{circuit_input_builder::CopyDataType, evm::OpcodeId};
use eth_types::{evm_types::GasCost, Field};
use gadgets::util::Expr;
use halo2_proofs::plonk::Error;

use crate::evm_circuit::{
    param::N_BYTES_MEMORY_WORD_SIZE,
    step::ExecutionState,
    util::{
        common_gadget::SameContextGadget,
        constraint_builder::{ConstraintBuilder, StepStateTransition, Transition},
        memory_gadget::{MemoryAddressGadget, MemoryCopierGasGadget, MemoryExpansionGadget},
        CachedRegion, Cell, Word,
    },
    witness::{Block, Call, ExecStep, Transaction},
};

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct Sha3Gadget<F> {
    same_context: SameContextGadget<F>,
    sha3_rlc: Word<F>,
    rlc_acc: Cell<F>,
    /// Opcode CODECOPY has a dynamic gas cost:
    /// gas_code = static_gas * minimum_word_size + memory_expansion_cost
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    /// Opcode CODECOPY needs to copy code bytes into memory. We account for
    /// the copying costs using the memory copier gas gadget.
    memory_copier_gas: MemoryCopierGasGadget<F, { GasCost::COPY_SHA3 }>,
    /// RW inverse counter from the copy table at the start of related copy
    /// steps.
    copy_rwc_inc: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for Sha3Gadget<F> {
    const EXECUTION_STATE: ExecutionState = ExecutionState::SHA3;

    const NAME: &'static str = "SHA3";

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let offset = cb.query_cell();
        let size = cb.query_rlc();
        let sha3_rlc = cb.query_word();

        cb.stack_pop(offset.expr());
        cb.stack_pop(size.expr());
        cb.stack_push(sha3_rlc.expr());

        let memory_address = MemoryAddressGadget::construct(cb, offset, size);
        let memory_expansion = MemoryExpansionGadget::construct(
            cb,
            cb.curr.state.memory_word_size.expr(),
            [memory_address.address()],
        );
        let memory_copier_gas = MemoryCopierGasGadget::construct(
            cb,
            memory_address.length(),
            memory_expansion.gas_cost(),
        );

        let copy_rwc_inc = cb.query_cell();
        let rlc_acc = cb.query_cell();
        cb.copy_table_lookup(
            cb.curr.state.call_id.expr(),
            CopyDataType::Memory.expr(),
            cb.curr.state.call_id.expr(),
            CopyDataType::RlcAcc.expr(),
            memory_address.offset(),
            memory_address.address(),
            0.expr(), // dst_id for CopyDataType::RlcAcc is 0.
            memory_address.length(),
            rlc_acc.expr(),
            cb.curr.state.rw_counter.expr() + cb.rw_counter_offset().expr(),
            copy_rwc_inc.expr(),
        );
        cb.keccak_table_lookup(memory_address.length(), rlc_acc.expr(), sha3_rlc.expr());

        let step_state_transition = StepStateTransition {
            rw_counter: Transition::Delta(cb.rw_counter_offset() + copy_rwc_inc.expr()),
            program_counter: Transition::Delta(1.expr()),
            stack_pointer: Transition::Delta(1.expr()),
            memory_word_size: Transition::To(memory_expansion.next_memory_word_size()),
            gas_left: Transition::Delta(
                -(OpcodeId::SHA3.constant_gas_cost().expr() + memory_copier_gas.gas_cost()),
            ),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            sha3_rlc,
            rlc_acc,
            memory_expansion,
            memory_copier_gas,
            copy_rwc_inc,
        }
    }

    fn assign_exec_step(
        &self,
        _region: &mut CachedRegion<'_, '_, F>,
        _offset: usize,
        _block: &Block<F>,
        _transaction: &Transaction,
        _call: &Call,
        _step: &ExecStep,
    ) -> Result<(), Error> {
        // TODO(rohit): assign to SHA3 gadget
        unimplemented!()
    }
}

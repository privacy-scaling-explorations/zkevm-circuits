//! This module contains the CircuitInputBuilder, which is an object that takes types from geth /
//! web3 and outputs the circuit inputs.
use crate::eth_types::{self, Address, GethExecStep, GethExecTrace};
use crate::evm::GlobalCounter;
use crate::evm::OpcodeId;
use crate::exec_trace::OperationRef;
use crate::operation::container::OperationContainer;
use crate::operation::{Op, Operation};
use crate::{BlockConstants, Error};
use core::fmt::Debug;

/// An execution step of the EVM.
#[derive(Debug)]
pub struct ExecStep {
    /// The opcode ID
    pub op: OpcodeId,
    /// The global counter when this step was executed
    pub gc: GlobalCounter,
    /// The list of references to Operations in the container
    pub bus_mapping_instance: Vec<OperationRef>,
}

impl ExecStep {
    /// Create a new Self from a `geth_step`.
    pub fn new(geth_step: &GethExecStep, gc: GlobalCounter) -> Self {
        ExecStep {
            op: geth_step.op,
            gc,
            bus_mapping_instance: Vec::new(),
        }
    }
}

/// Context of a [`Block`] which can mutate in a [`Transaction`].
#[derive(Debug)]
pub struct BlockContext {
    /// Used to track the global counter in every operation in the block.
    pub gc: GlobalCounter,
}

impl Default for BlockContext {
    fn default() -> Self {
        Self::new()
    }
}

impl BlockContext {
    /// Create a new Self
    pub fn new() -> Self {
        Self {
            gc: GlobalCounter::new(),
        }
    }
}

/// Circuit Input related to a block.
#[derive(Debug)]
pub struct Block {
    /// Constants associated to this block and the chain.
    pub constants: BlockConstants,
    /// Container of operations done in this block.
    pub container: OperationContainer,
    txs: Vec<Transaction>,
}

impl Block {
    /// Create a new block.
    pub fn new<TX>(
        _eth_block: &eth_types::Block<TX>,
        constants: BlockConstants,
    ) -> Self {
        Self {
            constants,
            container: OperationContainer::new(),
            txs: Vec::new(),
        }
    }

    /// Return the list of transactions of this block.
    pub fn txs(&self) -> &[Transaction] {
        &self.txs
    }

    #[cfg(test)]
    pub fn txs_mut(&mut self) -> &mut Vec<Transaction> {
        &mut self.txs
    }
}

#[derive(Debug)]
/// Context of a Call during a [`Transaction`] which can mutate in an [`ExecStep`].
pub struct CallContext {
    address: Address,
}

#[derive(Debug)]
/// Context of a [`Transaction`] which can mutate in an [`ExecStep`].
pub struct TransactionContext {
    call_ctxs: Vec<CallContext>,
}

impl TransactionContext {
    /// Create a new Self.
    pub fn new(eth_tx: &eth_types::Transaction) -> Self {
        let mut call_ctxs = Vec::new();
        if let Some(addr) = eth_tx.to {
            call_ctxs.push(CallContext { address: addr });
        }
        Self { call_ctxs }
    }
}

#[derive(Debug)]
/// Result of the parsing of an Ethereum Transaction.
pub struct Transaction {
    steps: Vec<ExecStep>,
}

impl Transaction {
    /// Create a new Self.
    pub fn new(_eth_tx: &eth_types::Transaction) -> Self {
        Self { steps: Vec::new() }
    }

    /// Return the list of execution steps of this transaction.
    pub fn steps(&self) -> &[ExecStep] {
        &self.steps
    }

    #[cfg(test)]
    pub fn steps_mut(&mut self) -> &mut Vec<ExecStep> {
        &mut self.steps
    }
}

/// Reference to the internal state of the CircuitInputBuilder in a particular [`ExecStep`].
pub struct CircuitInputStateRef<'a> {
    /// Block
    pub block: &'a mut Block,
    /// Block Context
    pub block_ctx: &'a mut BlockContext,
    /// Transaction
    pub tx: &'a mut Transaction,
    /// Transaction Context
    pub tx_ctx: &'a mut TransactionContext,
    /// Step
    pub step: &'a mut ExecStep,
}

impl<'a> CircuitInputStateRef<'a> {
    /// Push an [`Operation`] into the [`OperationContainer`] with the next [`GlobalCounter`] and
    /// then adds a reference to the stored operation ([`OperationRef`]) inside the bus-mapping
    /// instance of the current [`ExecStep`].  Then increase the block_ctx [`GlobalCounter`] by
    /// one.
    pub fn push_op<T: Op>(&mut self, op: T) {
        let op_ref = self
            .block
            .container
            .insert(Operation::new(self.block_ctx.gc.inc_pre(), op));
        self.step.bus_mapping_instance.push(op_ref);
    }
}

#[derive(Debug)]
/// Builder to generate a complete circuit input from data gathered from a geth instance.
/// This structure is the centre of the crate and is intended to be the only
/// entry point to it. The `CircuitInputBuilder` works in several steps:
///
/// 1. Take a [`eth_types::Block`] to build the circuit input associated with the block.
/// 2. For each [`eth_types::Transaction`] in the block, take the [`eth_types::GethExecTrace`] to
///    build the circuit input associated with each transaction, and the bus-mapping operations
///    associated with each `eth_types::GethExecStep`] in the [`eth_types::GethExecTrace`].
///
/// The generated bus-mapping operations are:
/// [`StackOp`](crate::operation::StackOp)s,
/// [`MemoryOp`](crate::operation::MemoryOp)s and
/// [`StorageOp`](crate::operation::StorageOp), which correspond to each
/// [`OpcodeId`](crate::evm::OpcodeId)s used in each `ExecTrace` step so that the State Proof
/// witnesses are already generated on a structured manner and ready to be added into the State
/// circuit.
pub struct CircuitInputBuilder {
    /// Block
    pub block: Block,
    /// Block Context
    pub block_ctx: BlockContext,
}

impl<'a> CircuitInputBuilder {
    /// Create a new CircuitInputBuilder from the given `eth_block` and `constants`.
    pub fn new<TX>(
        eth_block: eth_types::Block<TX>,
        constants: BlockConstants,
    ) -> Self {
        Self {
            block: Block::new(&eth_block, constants),
            block_ctx: BlockContext::new(),
        }
    }

    /// Obtain a mutable reference to the state that the `CircuitInputBuilder` maintains,
    /// contextualized to a particular transaction and a particular execution step in that
    /// transaction.
    pub fn state_ref(
        &'a mut self,
        tx: &'a mut Transaction,
        tx_ctx: &'a mut TransactionContext,
        step: &'a mut ExecStep,
    ) -> CircuitInputStateRef {
        CircuitInputStateRef {
            block: &mut self.block,
            block_ctx: &mut self.block_ctx,
            tx,
            tx_ctx,
            step,
        }
    }

    /// Handle a transaction with its corresponding execution trace to generate all the associated
    /// operations.  Each operation is registered in `self.block.container`, and each step stores
    /// the [`OperationRef`] to each of the generated operations.
    pub fn handle_tx(
        &mut self,
        eth_tx: &eth_types::Transaction,
        geth_trace: &GethExecTrace,
    ) -> Result<(), Error> {
        let mut tx = Transaction::new(eth_tx);
        let mut tx_ctx = TransactionContext::new(eth_tx);
        for (index, geth_step) in geth_trace.struct_logs.iter().enumerate() {
            let mut step = ExecStep::new(geth_step, self.block_ctx.gc);
            let mut state_ref = self.state_ref(&mut tx, &mut tx_ctx, &mut step);
            geth_step.op.gen_associated_ops(
                &mut state_ref,
                &geth_trace.struct_logs[index..],
            )?;
            tx.steps.push(step);
        }
        self.block.txs.push(tx);
        Ok(())
    }
}

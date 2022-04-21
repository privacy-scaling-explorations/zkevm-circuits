//! This module contains the CircuitInputBuilder, which is an object that takes
//! types from geth / web3 and outputs the circuit inputs.

mod access;
mod block;
mod call;
mod execution;
mod input_state_ref;
#[cfg(test)]
mod tracer_tests;
mod transaction;

use self::access::gen_state_access_trace;
use crate::error::Error;
use crate::evm::opcodes::{gen_associated_ops, gen_begin_tx_ops, gen_end_tx_ops};
use crate::operation::{CallContextField, RW};
use crate::rpc::GethClient;
use crate::state_db::{self, CodeDB, StateDB};
pub use access::{Access, AccessSet, AccessValue, CodeSource};
pub use block::{Block, BlockContext};
pub use call::{Call, CallContext, CallKind};
use core::fmt::Debug;
use eth_types::{self, Address, GethExecStep, GethExecTrace, Word};
use ethers_providers::JsonRpcClient;
pub use execution::{CopyDetails, ExecState, ExecStep, StepAuxiliaryData};
pub use input_state_ref::CircuitInputStateRef;
use std::collections::HashMap;
pub use transaction::{Transaction, TransactionContext};

/// Builder to generate a complete circuit input from data gathered from a geth
/// instance. This structure is the centre of the crate and is intended to be
/// the only entry point to it. The `CircuitInputBuilder` works in several
/// steps:
///
/// 1. Take a [`eth_types::Block`] to build the circuit input associated with
/// the block. 2. For each [`eth_types::Transaction`] in the block, take the
/// [`eth_types::GethExecTrace`] to    build the circuit input associated with
/// each transaction, and the bus-mapping operations    associated with each
/// `eth_types::GethExecStep`] in the [`eth_types::GethExecTrace`].
///
/// The generated bus-mapping operations are:
/// [`StackOp`](crate::operation::StackOp)s,
/// [`MemoryOp`](crate::operation::MemoryOp)s and
/// [`StorageOp`](crate::operation::StorageOp), which correspond to each
/// [`OpcodeId`](crate::evm::OpcodeId)s used in each `ExecTrace` step so that
/// the State Proof witnesses are already generated on a structured manner and
/// ready to be added into the State circuit.
#[derive(Debug)]
pub struct CircuitInputBuilder {
    /// StateDB key-value DB
    pub sdb: StateDB,
    /// Map of account codes by code hash
    pub code_db: CodeDB,
    /// Block
    pub block: Block,
    /// Block Context
    pub block_ctx: BlockContext,
}

impl<'a> CircuitInputBuilder {
    /// Create a new CircuitInputBuilder from the given `eth_block` and
    /// `constants`.
    pub fn new(sdb: StateDB, code_db: CodeDB, block: Block) -> Self {
        Self {
            sdb,
            code_db,
            block,
            block_ctx: BlockContext::new(),
        }
    }

    /// Obtain a mutable reference to the state that the `CircuitInputBuilder`
    /// maintains, contextualized to a particular transaction and a
    /// particular execution step in that transaction.
    pub fn state_ref(
        &'a mut self,
        tx: &'a mut Transaction,
        tx_ctx: &'a mut TransactionContext,
    ) -> CircuitInputStateRef {
        CircuitInputStateRef {
            sdb: &mut self.sdb,
            code_db: &mut self.code_db,
            block: &mut self.block,
            block_ctx: &mut self.block_ctx,
            tx,
            tx_ctx,
        }
    }

    /// Create a new Transaction from a [`eth_types::Transaction`].
    pub fn new_tx(
        &mut self,
        eth_tx: &eth_types::Transaction,
        is_success: bool,
    ) -> Result<Transaction, Error> {
        let call_id = self.block_ctx.rwc.0;

        self.block_ctx.call_map.insert(
            call_id,
            (
                eth_tx
                    .transaction_index
                    .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?
                    .as_u64() as usize,
                0,
            ),
        );

        Transaction::new(call_id, &self.sdb, &mut self.code_db, eth_tx, is_success)
    }

    /// Iterate over all generated CallContext RwCounterEndOfReversion
    /// operations and set the correct value. This is required because when we
    /// generate the RwCounterEndOfReversion operation in
    /// `gen_associated_ops` we don't know yet which value it will take,
    /// so we put a placeholder; so we do it here after the values are known.
    pub fn set_value_ops_call_context_rwc_eor(&mut self) {
        for oper in self.block.container.call_context.iter_mut() {
            let op = oper.op_mut();
            if matches!(op.field, CallContextField::RwCounterEndOfReversion) {
                let (tx_idx, call_idx) = self
                    .block_ctx
                    .call_map
                    .get(&op.call_id)
                    .expect("call_id not found in call_map");
                op.value = self.block.txs[*tx_idx].calls()[*call_idx]
                    .rw_counter_end_of_reversion
                    .into();
            }
        }
    }

    /// Handle a block by handling each transaction to generate all the
    /// associated operations.
    pub fn handle_block(
        &mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<(), Error> {
        for (tx_index, tx) in eth_block.transactions.iter().enumerate() {
            let geth_trace = &geth_traces[tx_index];
            self.handle_tx(tx, geth_trace, tx_index + 1 == eth_block.transactions.len())?;
        }
        self.set_value_ops_call_context_rwc_eor();
        Ok(())
    }

    /// Handle a transaction with its corresponding execution trace to generate
    /// all the associated operations.  Each operation is registered in
    /// `self.block.container`, and each step stores the
    /// [`OperationRef`](crate::exec_trace::OperationRef) to each of the
    /// generated operations.
    fn handle_tx(
        &mut self,
        eth_tx: &eth_types::Transaction,
        geth_trace: &GethExecTrace,
        is_last_tx: bool,
    ) -> Result<(), Error> {
        let mut tx = self.new_tx(eth_tx, !geth_trace.failed)?;
        let mut tx_ctx = TransactionContext::new(eth_tx, geth_trace, is_last_tx)?;

        // TODO: Move into gen_associated_steps with
        // - execution_state: BeginTx
        // - op: None
        // Generate BeginTx step
        let begin_tx_step = gen_begin_tx_ops(&mut self.state_ref(&mut tx, &mut tx_ctx))?;
        tx.steps_mut().push(begin_tx_step);

        for (index, geth_step) in geth_trace.struct_logs.iter().enumerate() {
            let mut state_ref = self.state_ref(&mut tx, &mut tx_ctx);
            log::trace!("handle {}th opcode {:?} ", index, geth_step.op);
            let exec_steps = gen_associated_ops(
                &geth_step.op,
                &mut state_ref,
                &geth_trace.struct_logs[index..],
            )?;
            tx.steps_mut().extend(exec_steps);
        }

        // TODO: Move into gen_associated_steps with
        // - execution_state: EndTx
        // - op: None
        // Generate EndTx step
        let end_tx_step = gen_end_tx_ops(&mut self.state_ref(&mut tx, &mut tx_ctx))?;
        tx.steps_mut().push(end_tx_step);

        self.sdb.commit_tx();
        self.block.txs.push(tx);

        Ok(())
    }
}

/// Retrieve the init_code from memory for {CREATE, CREATE2}
pub fn get_create_init_code(step: &GethExecStep) -> Result<&[u8], Error> {
    let offset = step.stack.nth_last(1)?;
    let length = step.stack.nth_last(2)?;
    Ok(&step.memory.0[offset.low_u64() as usize..(offset.low_u64() + length.low_u64()) as usize])
}

/// Retrieve the memory offset and length of call.
pub fn get_call_memory_offset_length(step: &GethExecStep, nth: usize) -> Result<(u64, u64), Error> {
    let offset = step.stack.nth_last(nth)?;
    let length = step.stack.nth_last(nth + 1)?;
    if length.is_zero() {
        Ok((0, 0))
    } else {
        Ok((offset.low_u64(), length.low_u64()))
    }
}

type EthBlock = eth_types::Block<eth_types::Transaction>;

/// Struct that wraps a GethClient and contains methods to perform all the steps
/// necessary to generate the circuit inputs for a block by querying geth for
/// the necessary information and using the CircuitInputBuilder.
pub struct BuilderClient<P: JsonRpcClient> {
    cli: GethClient<P>,
    chain_id: Word,
    history_hashes: Vec<Word>,
}

impl<P: JsonRpcClient> BuilderClient<P> {
    /// Create a new BuilderClient
    pub async fn new(client: GethClient<P>) -> Result<Self, Error> {
        let chain_id = client.get_chain_id().await?;

        Ok(Self {
            cli: client,
            chain_id: chain_id.into(),
            // TODO: Get history hashes
            history_hashes: Vec::new(),
        })
    }

    /// Step 1. Query geth for Block, Txs and TxExecTraces
    pub async fn get_block(
        &self,
        block_num: u64,
    ) -> Result<(EthBlock, Vec<eth_types::GethExecTrace>), Error> {
        let eth_block = self.cli.get_block_by_number(block_num.into()).await?;
        let geth_traces = self.cli.trace_block_by_number(block_num.into()).await?;
        Ok((eth_block, geth_traces))
    }

    /// Step 2. Get State Accesses from TxExecTraces
    pub fn get_state_accesses(
        &self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<AccessSet, Error> {
        let mut block_access_trace = vec![Access::new(
            None,
            RW::WRITE,
            AccessValue::Account {
                address: eth_block.author,
            },
        )];
        for (tx_index, tx) in eth_block.transactions.iter().enumerate() {
            let geth_trace = &geth_traces[tx_index];
            let tx_access_trace = gen_state_access_trace(eth_block, tx, geth_trace)?;
            block_access_trace.extend(tx_access_trace);
        }

        Ok(AccessSet::from(block_access_trace))
    }

    /// Step 3. Query geth for all accounts, storage keys, and codes from
    /// Accesses
    pub async fn get_state(
        &self,
        block_num: u64,
        access_set: AccessSet,
    ) -> Result<
        (
            Vec<eth_types::EIP1186ProofResponse>,
            HashMap<Address, Vec<u8>>,
        ),
        Error,
    > {
        let mut proofs = Vec::new();
        for (address, key_set) in access_set.state {
            let mut keys: Vec<Word> = key_set.iter().cloned().collect();
            keys.sort();
            let proof = self
                .cli
                .get_proof(address, keys, (block_num - 1).into())
                .await
                .unwrap();
            proofs.push(proof);
        }
        let mut codes: HashMap<Address, Vec<u8>> = HashMap::new();
        for address in access_set.code {
            let code = self
                .cli
                .get_code(address, (block_num - 1).into())
                .await
                .unwrap();
            codes.insert(address, code);
        }
        Ok((proofs, codes))
    }

    /// Step 4. Build a partial StateDB from step 3
    pub fn build_state_code_db(
        &self,
        proofs: Vec<eth_types::EIP1186ProofResponse>,
        codes: HashMap<Address, Vec<u8>>,
    ) -> (StateDB, CodeDB) {
        let mut sdb = StateDB::new();
        for proof in proofs {
            let mut storage = HashMap::new();
            for storage_proof in proof.storage_proof {
                storage.insert(storage_proof.key, storage_proof.value);
            }
            sdb.set_account(
                &proof.address,
                state_db::Account {
                    nonce: proof.nonce,
                    balance: proof.balance,
                    storage,
                    code_hash: proof.code_hash,
                },
            )
        }

        let mut code_db = CodeDB::new();
        for (_address, code) in codes {
            code_db.insert(code.clone());
        }
        (sdb, code_db)
    }

    /// Step 5. For each step in TxExecTraces, gen the associated ops and state
    /// circuit inputs
    pub fn gen_inputs_from_state(
        &self,
        sdb: StateDB,
        code_db: CodeDB,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<CircuitInputBuilder, Error> {
        let block = Block::new(self.chain_id, self.history_hashes.clone(), eth_block)?;
        let mut builder = CircuitInputBuilder::new(sdb, code_db, block);
        builder.handle_block(eth_block, geth_traces)?;
        Ok(builder)
    }

    /// Perform all the steps to generate the circuit inputs
    pub async fn gen_inputs(&self, block_num: u64) -> Result<CircuitInputBuilder, Error> {
        let (eth_block, geth_traces) = self.get_block(block_num).await?;
        let access_set = self.get_state_accesses(&eth_block, &geth_traces)?;
        let (proofs, codes) = self.get_state(block_num, access_set).await?;
        let (state_db, code_db) = self.build_state_code_db(proofs, codes);
        let builder = self.gen_inputs_from_state(state_db, code_db, &eth_block, &geth_traces)?;
        Ok(builder)
    }
}

#[cfg(test)]
mod tracer_tests {
    use crate::state_db::Account;

    use super::*;
    use eth_types::evm_types::{stack::Stack, Gas, OpcodeId};
    use eth_types::{address, bytecode, geth_types::GethData, word, Bytecode, ToWord, Word};
    use lazy_static::lazy_static;
    use mock::test_ctx::{helpers::*, TestContext};
    use mock::MOCK_COINBASE;
    use pretty_assertions::assert_eq;
    use std::iter::FromIterator;

    // Helper struct that contains a CircuitInputBuilder, a particuar tx and a
    // particular execution step so that we can easily get a
    // CircuitInputStateRef to have a context in order to get the error at a
    // given step.
    struct CircuitInputBuilderTx {
        builder: CircuitInputBuilder,
        tx: Transaction,
        tx_ctx: TransactionContext,
        step: ExecStep,
    }

    impl CircuitInputBuilderTx {
        fn new(geth_data: &GethData, geth_step: &GethExecStep) -> Self {
            let block = crate::mock::BlockData::new_from_geth_data(geth_data.clone());
            let mut builder = block.new_circuit_input_builder();
            let tx = builder
                .new_tx(&block.eth_block.transactions[0], true)
                .unwrap();
            let tx_ctx = TransactionContext::new(
                &block.eth_block.transactions[0],
                &GethExecTrace {
                    gas: Gas(0),
                    failed: false,
                    return_value: "".to_owned(),
                    struct_logs: vec![geth_step.clone()],
                },
                false,
            )
            .unwrap();
            Self {
                builder,
                tx,
                tx_ctx,
                step: ExecStep::new(geth_step, 0, RWCounter::new(), 0),
            }
        }

        fn state_ref(&mut self) -> CircuitInputStateRef {
            self.builder.state_ref(&mut self.tx, &mut self.tx_ctx)
        }
    }

    lazy_static! {
        static ref ADDR_A: Address = Address::zero();
        static ref WORD_ADDR_A: Word = ADDR_A.to_word();
        static ref ADDR_B: Address = address!("0x0000000000000000000000000000000000000123");
        static ref WORD_ADDR_B: Word = ADDR_B.to_word();
    }

    fn mock_internal_create() -> Call {
        Call {
            call_id: 0,
            caller_id: 0,
            kind: CallKind::Create,
            is_static: false,
            is_root: false,
            is_persistent: false,
            is_success: false,
            rw_counter_end_of_reversion: 0,
            caller_address: *ADDR_A,
            address: *ADDR_B,
            code_source: CodeSource::Memory,
            code_hash: Hash::zero(),
            depth: 2,
            value: Word::zero(),
            call_data_offset: 0,
            call_data_length: 0,
            return_data_offset: 0,
            return_data_length: 0,
        }
    }

    //
    // Geth Errors ignored
    //
    // These errors happen in a CALL, CALLCODE, DELEGATECALL or STATICCALL, and
    // are used internally but not propagated in geth to the scope where the
    // tracer is used.

    fn check_err_depth(step: &GethExecStep, next_step: Option<&GethExecStep>) -> bool {
        matches!(
            step.op,
            OpcodeId::CALL
                | OpcodeId::CALLCODE
                | OpcodeId::DELEGATECALL
                | OpcodeId::STATICCALL
                | OpcodeId::CREATE
                | OpcodeId::CREATE2
        ) && step.error.is_none()
            && result(next_step).is_zero()
            && step.depth == 1025
    }

    #[test]
    fn tracer_err_depth() {
        // Recursive CALL will exaust the call depth
        let code = bytecode! {
                 PUSH1(0x0) // retLength
                 PUSH1(0x0) // retOffset
                 PUSH1(0x0) // argsLength
                 PUSH1(0x0) // argsOffset
                 PUSH1(0x42) // value
                 PUSH32(*WORD_ADDR_A) // addr
                 PUSH32(0x8_0000_0000_0000_u64) // gas
                 CALL
                 PUSH2(0xab)
                 STOP
        };

        // Create a custom tx setting Gas to
        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(*ADDR_A)
                    .balance(Word::from(1u64 << 20))
                    .code(code);
                accs[1]
                    .address(address!("0x0000000000000000000000000000000000000010"))
                    .balance(Word::from(10u64.pow(19)));
            },
            |mut txs, accs| {
                txs[0]
                    .to(accs[0].address)
                    .from(accs[1].address)
                    .gas(Word::from(10u64.pow(15)));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let struct_logs = &block.geth_traces[0].struct_logs;

        // get last CALL
        let (index, step) = block.geth_traces[0]
            .struct_logs
            .iter()
            .enumerate()
            .rev()
            .find(|(_, s)| s.op == OpcodeId::CALL)
            .unwrap();
        let next_step = block.geth_traces[0].struct_logs.get(index + 1);
        assert_eq!(step.op, OpcodeId::CALL);
        assert_eq!(step.depth, 1025u16);
        assert_eq!(step.error, None);
        // Some sanity checks
        assert_eq!(struct_logs[index + 1].op, OpcodeId::PUSH2);
        assert_eq!(struct_logs[index + 1].depth, 1025u16);
        assert_eq!(struct_logs[index + 1].stack, Stack(vec![Word::zero()])); // success = 0
        assert_eq!(struct_logs[index + 2].op, OpcodeId::STOP);
        assert_eq!(struct_logs[index + 2].depth, 1025u16);

        assert!(check_err_depth(step, next_step));

        let mut builder = CircuitInputBuilderTx::new(&block, step);
        assert_eq!(
            builder.state_ref().get_step_err(step, next_step).unwrap(),
            Some(ExecError::Depth)
        );
    }

    #[test]
    fn tracer_err_insufficient_balance() {
        let code_a = bytecode! {
            PUSH1(0x0) // retLength
            PUSH1(0x0) // retOffset
            PUSH1(0x0) // argsLength
            PUSH1(0x0) // argsOffset
            PUSH32(Word::from(0x1000)) // value
            PUSH32(*WORD_ADDR_B) // addr
            PUSH32(0x1_0000) // gas
            CALL

            PUSH2(0xaa)
        };
        let code_b = bytecode! {
            PUSH1(0x01) // value
            PUSH1(0x02) // key
            SSTORE

            PUSH3(0xbb)
        };

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<3, 2>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x0000000000000000000000000000000000000000"))
                    .code(code_a);
                accs[1]
                    .address(address!("0x000000000000000000000000000000000cafe001"))
                    .code(code_b);
                accs[2]
                    .address(address!("0x000000000000000000000000000000000cafe002"))
                    .balance(Word::from(1u64 << 30));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[2].address);
                txs[1]
                    .to(accs[1].address)
                    .from(accs[2].address)
                    .nonce(Word::one());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        // get last CALL
        let (index, step) = block.geth_traces[0]
            .struct_logs
            .iter()
            .enumerate()
            .rev()
            .find(|(_, s)| s.op == OpcodeId::CALL)
            .unwrap();
        let next_step = block.geth_traces[0].struct_logs.get(index + 1);
        assert_eq!(step.error, None);
        assert_eq!(next_step.unwrap().op, OpcodeId::PUSH2);
        assert_eq!(next_step.unwrap().stack, Stack(vec![Word::zero()])); // success = 0

        let mut builder = CircuitInputBuilderTx::new(&block, step);
        builder.builder.sdb.set_account(
            &ADDR_A,
            Account {
                nonce: Word::zero(),
                balance: Word::from(555u64), /* same value as in
                                              * `mock::new_tracer_account` */
                storage: HashMap::new(),
                code_hash: Hash::zero(),
            },
        );
        assert_eq!(
            builder.state_ref().get_step_err(step, next_step).unwrap(),
            Some(ExecError::InsufficientBalance)
        );
    }

    #[test]
    fn tracer_err_address_collision() {
        // We do CREATE2 twice with the same parameters, with a code_creater
        // that outputs the same, which will lead to the same new
        // contract address.
        let code_creator = bytecode! {
            PUSH1(0x00) // value
            PUSH1(0x00) // offset
            MSTORE
            PUSH1(0x01) // length
            PUSH1(0x00) // offset
            RETURN
        };

        // code_a calls code_b which executes code_creator in CREATE2
        let code_a = bytecode! {
            PUSH1(0x0) // retLength
            PUSH1(0x0) // retOffset
            PUSH1(0x0) // argsLength
            PUSH1(0x0) // argsOffset
            PUSH1(0x0) // value
            PUSH32(*WORD_ADDR_B) // addr
            PUSH32(0x1_0000) // gas
            CALL

            PUSH2(0xaa)
        };

        let mut code_b = Bytecode::default();
        // pad code_creator to multiple of 32 bytes
        let len = code_creator.code().len();
        let code_creator: Vec<u8> = code_creator
            .code()
            .iter()
            .cloned()
            .chain(0u8..((32 - len % 32) as u8))
            .collect();
        for (index, word) in code_creator.chunks(32).enumerate() {
            code_b.push(32, Word::from_big_endian(word));
            code_b.push(32, Word::from(index * 32));
            code_b.write_op(OpcodeId::MSTORE);
        }
        let code_b_end = bytecode! {
            PUSH3(0x123456) // salt
            PUSH1(len) // length
            PUSH1(0x00) // offset
            PUSH1(0x00) // value
            CREATE2

            PUSH3(0x123456) // salt
            PUSH1(len) // length
            PUSH1(0x00) // offset
            PUSH1(0x00) // value
            CREATE2

            PUSH3(0xbb)
        };
        code_b.append(&code_b_end);
        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<3, 2>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x0000000000000000000000000000000000000000"))
                    .code(code_a);
                accs[1].address(*ADDR_B).code(code_b);
                accs[2]
                    .address(address!("0x000000000000000000000000000000000cafe002"))
                    .balance(Word::from(1u64 << 30));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[2].address);
                txs[1]
                    .to(accs[1].address)
                    .from(accs[2].address)
                    .nonce(Word::one());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        // get last CREATE2
        let (index, step) = block.geth_traces[0]
            .struct_logs
            .iter()
            .enumerate()
            .rev()
            .find(|(_, s)| s.op == OpcodeId::CREATE2)
            .unwrap();
        let next_step = block.geth_traces[0].struct_logs.get(index + 1);

        let create2_address: Address = {
            // get first RETURN
            let (index, _) = block.geth_traces[0]
                .struct_logs
                .iter()
                .enumerate()
                .find(|(_, s)| s.op == OpcodeId::RETURN)
                .unwrap();
            let next_step = block.geth_traces[0].struct_logs.get(index + 1);
            let addr_word = next_step.unwrap().stack.last().unwrap();
            addr_word.to_address()
        };

        let mut builder = CircuitInputBuilderTx::new(&block, step);
        // Set up call context at CREATE2
        builder.tx_ctx.call_is_success.push(false);
        builder.state_ref().push_call(mock_internal_create(), step);
        // Set up account and contract that exist during the second CREATE2
        builder.builder.sdb.set_account(
            &ADDR_B,
            Account {
                nonce: Word::zero(),
                balance: Word::from(555u64), /* same value as in
                                              * `mock::new_tracer_account` */
                storage: HashMap::new(),
                code_hash: Hash::zero(),
            },
        );
        builder.builder.sdb.set_account(
            &create2_address,
            Account {
                nonce: Word::zero(),
                balance: Word::zero(),
                storage: HashMap::new(),
                code_hash: Hash::zero(),
            },
        );
        assert_eq!(
            builder.state_ref().get_step_err(step, next_step).unwrap(),
            Some(ExecError::ContractAddressCollision)
        );
    }

    fn check_err_code_store_out_of_gas(
        step: &GethExecStep,
        next_step: Option<&GethExecStep>,
    ) -> bool {
        let length = step.stack.nth_last(1).unwrap();
        step.op == OpcodeId::RETURN
            && step.error.is_none()
            && result(next_step).is_zero()
            && Word::from(200) * length > Word::from(step.gas.0)
    }

    #[test]
    fn tracer_err_code_store_out_of_gas() {
        // code_creator outputs an empty array of length 0x100, which will
        // exhaust the gas to store the code.
        let code_len = 0x100;
        let code_creator = bytecode! {
            PUSH1(Word::zero()) // value
            PUSH32(code_len) // offset
            MSTORE
            PUSH32(code_len) // length
            PUSH1(0x00) // offset
            RETURN
        };

        // code_a calls code_b which executes code_creator in CREATE
        let code_a = bytecode! {
            PUSH1(0x0) // retLength
            PUSH1(0x0) // retOffset
            PUSH1(0x0) // argsLength
            PUSH1(0x0) // argsOffset
            PUSH1(0x0) // value
            PUSH32(*WORD_ADDR_B) // addr
            PUSH32(0x1_0000) // gas
            CALL

            PUSH2(0xaa)
        };

        let mut code_b = Bytecode::default();
        // pad code_creator to multiple of 32 bytes
        let len = code_creator.code().len();
        let code_creator: Vec<u8> = code_creator
            .code()
            .iter()
            .cloned()
            .chain(0..(32 - len % 32) as u8)
            .collect();
        for (index, word) in code_creator.chunks(32).enumerate() {
            code_b.push(32, Word::from_big_endian(word));
            code_b.push(32, Word::from(index * 32));
            code_b.write_op(OpcodeId::MSTORE);
        }
        let code_b_end = bytecode! {
            PUSH32(len) // length
            PUSH1(0x00) // offset
            PUSH1(0x00) // value
            CREATE

            PUSH3(0xbb)
        };
        code_b.append(&code_b_end);
        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<3, 2>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x0000000000000000000000000000000000000000"))
                    .code(code_a);
                accs[1].address(*ADDR_B).code(code_b);
                accs[2]
                    .address(address!("0x000000000000000000000000000000000cafe002"))
                    .balance(Word::from(1u64 << 30));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[2].address);
                txs[1]
                    .to(accs[1].address)
                    .from(accs[2].address)
                    .nonce(Word::one());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        // get last RETURN
        let (index, step) = block.geth_traces[0]
            .struct_logs
            .iter()
            .enumerate()
            .rev()
            .find(|(_, s)| s.op == OpcodeId::RETURN)
            .unwrap();
        let next_step = block.geth_traces[0].struct_logs.get(index + 1);
        assert!(check_err_code_store_out_of_gas(step, next_step));

        let mut builder = CircuitInputBuilderTx::new(&block, step);
        // Set up call context at CREATE
        builder.tx_ctx.call_is_success.push(false);
        builder.state_ref().push_call(mock_internal_create(), step);
        assert_eq!(
            builder.state_ref().get_step_err(step, next_step).unwrap(),
            Some(ExecError::CodeStoreOutOfGas)
        );
    }

    fn check_err_invalid_code(step: &GethExecStep, next_step: Option<&GethExecStep>) -> bool {
        let offset = step.stack.nth_last(0).unwrap();
        let length = step.stack.nth_last(1).unwrap();
        step.op == OpcodeId::RETURN
            && step.error.is_none()
            && result(next_step).is_zero()
            && length > Word::zero()
            && !step.memory.0.is_empty()
            && step.memory.0.get(offset.low_u64() as usize) == Some(&0xef)
    }

    #[test]
    fn tracer_err_invalid_code() {
        // code_creator outputs byte array that starts with 0xef, which is
        // invalid code.
        let code_creator = bytecode! {
            PUSH32(word!("0xef00000000000000000000000000000000000000000000000000000000000000")) // value
            PUSH1(0x00) // offset
            MSTORE
            PUSH1(0x01) // length
            PUSH1(0x00) // offset
            RETURN
        };

        // code_a calls code_b which executes code_creator in CREATE
        let code_a = bytecode! {
            PUSH1(0x0) // retLength
            PUSH1(0x0) // retOffset
            PUSH1(0x0) // argsLength
            PUSH1(0x0) // argsOffset
            PUSH1(0x0) // value
            PUSH32(*WORD_ADDR_B) // addr
            PUSH32(0x1_0000) // gas
            CALL

            PUSH2(0xaa)
        };

        let mut code_b = Bytecode::default();
        // pad code_creator to multiple of 32 bytes
        let len = code_creator.code().len();
        let code_creator: Vec<u8> = code_creator
            .code()
            .iter()
            .cloned()
            .chain(0u8..((32 - len % 32) as u8))
            .collect();
        for (index, word) in code_creator.chunks(32).enumerate() {
            code_b.push(32, Word::from_big_endian(word));
            code_b.push(32, Word::from(index * 32));
            code_b.write_op(OpcodeId::MSTORE);
        }
        let code_b_end = bytecode! {
            PUSH1(len) // length
            PUSH1(0x00) // offset
            PUSH1(0x00) // value
            CREATE

            PUSH3(0xbb)
        };
        code_b.append(&code_b_end);
        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<3, 2>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x0000000000000000000000000000000000000000"))
                    .code(code_a);
                accs[1].address(*ADDR_B).code(code_b);
                accs[2]
                    .address(address!("0x000000000000000000000000000000000cafe002"))
                    .balance(Word::from(1u64 << 30));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[2].address);
                txs[1]
                    .to(accs[1].address)
                    .from(accs[2].address)
                    .nonce(Word::one());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        // get last RETURN
        let (index, step) = block.geth_traces[0]
            .struct_logs
            .iter()
            .enumerate()
            .rev()
            .find(|(_, s)| s.op == OpcodeId::RETURN)
            .unwrap();
        let next_step = block.geth_traces[0].struct_logs.get(index + 1);
        assert!(check_err_invalid_code(step, next_step));

        let mut builder = CircuitInputBuilderTx::new(&block, step);
        // Set up call context at RETURN
        builder.tx_ctx.call_is_success.push(false);
        builder.state_ref().push_call(mock_internal_create(), step);
        assert_eq!(
            builder.state_ref().get_step_err(step, next_step).unwrap(),
            Some(ExecError::InvalidCreationCode)

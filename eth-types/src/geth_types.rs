//! Types needed for generating Ethereum traces

use crate::{
    evm_types::{self, GasCost},
    keccak256,
    sign_types::{biguint_to_32bytes_le, ct_option_ok_or, recover_pk, SignData, SECP256K1_Q},
    AccessList, Address, Block, Bytecode, Bytes, Error, GethExecTrace, Hash, ToBigEndian,
    ToLittleEndian, ToWord, Word, H256, U64,
};
use ethers_core::{
    types::{
        transaction::{eip2718::TypedTransaction, response},
        Eip1559TransactionRequest, Eip2930TransactionRequest, NameOrAddress, TransactionRequest,
    },
    utils::get_contract_address,
};
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::halo2curves::{group::ff::PrimeField, secp256k1};
use num::Integer;
use num_bigint::BigUint;
use serde::{Serialize, Serializer};
use serde_with::serde_as;
use std::collections::HashMap;
use strum_macros::EnumIter;

/// Tx type
#[derive(Default, Debug, Copy, Clone, EnumIter, Serialize, PartialEq, Eq)]
pub enum TxType {
    /// EIP 155 tx
    #[default]
    Eip155 = 0,
    /// Pre EIP 155 tx
    PreEip155,
    /// EIP 1559 tx
    Eip1559,
    /// EIP 2930 tx
    Eip2930,
}

impl From<TxType> for usize {
    fn from(value: TxType) -> Self {
        value as usize
    }
}

impl From<TxType> for u64 {
    fn from(value: TxType) -> Self {
        value as u64
    }
}

impl TxType {
    /// If this type is PreEip155
    pub fn is_pre_eip155(&self) -> bool {
        matches!(*self, TxType::PreEip155)
    }

    /// If this type is EIP155 or not
    pub fn is_eip155(&self) -> bool {
        matches!(*self, TxType::Eip155)
    }

    /// If this type is Eip1559 or not
    pub fn is_eip1559(&self) -> bool {
        matches!(*self, TxType::Eip1559)
    }

    /// If this type is Eip2930 or not
    pub fn is_eip2930(&self) -> bool {
        matches!(*self, TxType::Eip2930)
    }

    /// Get the type of transaction
    pub fn get_tx_type(tx: &crate::Transaction) -> Self {
        match tx.transaction_type {
            Some(x) if x == U64::from(1) => Self::Eip2930,
            Some(x) if x == U64::from(2) => Self::Eip1559,
            _ => match tx.v.as_u64() {
                0 | 1 | 27 | 28 => Self::PreEip155,
                _ => Self::Eip155,
            },
        }
    }

    /// Return the recovery id of signature for recovering the signing pk
    pub fn get_recovery_id(&self, v: u64) -> u8 {
        let recovery_id = match *self {
            TxType::Eip155 => (v + 1) % 2,
            TxType::PreEip155 => {
                assert!(v == 0x1b || v == 0x1c, "v: {v}");
                v - 27
            }
            TxType::Eip1559 => {
                assert!(v <= 1);
                v
            }
            TxType::Eip2930 => {
                assert!(v <= 1);
                v
            }
        };

        recovery_id as u8
    }
}

/// Get the RLP bytes for signing
pub fn get_rlp_unsigned(tx: &crate::Transaction) -> Vec<u8> {
    let sig_v = tx.v;
    match TxType::get_tx_type(tx) {
        TxType::Eip155 => {
            let mut tx: TransactionRequest = tx.into();
            tx.chain_id = Some(tx.chain_id.unwrap_or_else(|| {
                let recv_v = TxType::Eip155.get_recovery_id(sig_v.as_u64()) as u64;
                (sig_v - recv_v - 35) / 2
            }));
            tx.rlp().to_vec()
        }
        TxType::PreEip155 => {
            let tx: TransactionRequest = tx.into();
            tx.rlp_unsigned().to_vec()
        }
        TxType::Eip1559 => {
            let tx: Eip1559TransactionRequest = tx.into();
            let typed_tx: TypedTransaction = tx.into();
            typed_tx.rlp().to_vec()
        }
        TxType::Eip2930 => {
            let tx: Eip2930TransactionRequest = tx.into();
            let typed_tx: TypedTransaction = tx.into();
            typed_tx.rlp().to_vec()
        }
    }
}

/// Definition of all of the data related to an account.
#[serde_as]
#[derive(PartialEq, Eq, Debug, Default, Clone, Serialize)]
pub struct Account {
    /// Address
    pub address: Address,
    /// Nonce.
    /// U64 type is required to serialize into proper hex with 0x prefix
    pub nonce: U64,
    /// Balance
    pub balance: Word,
    /// EVM Code
    pub code: Bytes,
    /// Storage
    #[serde(serialize_with = "serde_account_storage")]
    pub storage: HashMap<Word, Word>,
}

impl Account {
    /// Return if account is empty or not.
    pub fn is_empty(&self) -> bool {
        self.nonce.is_zero()
            && self.balance.is_zero()
            && self.code.is_empty()
            && self.storage.is_empty()
    }

    /// Generate an account that is either empty or has code, balance, and non-zero nonce
    pub fn mock_code_balance(code: Bytecode) -> Self {
        let is_empty = code.codesize() == 0;
        Self {
            address: Address::repeat_byte(0xff),
            code: code.into(),
            nonce: U64::from(!is_empty as u64),
            balance: if is_empty { 0 } else { 0xdeadbeefu64 }.into(),
            ..Default::default()
        }
    }

    /// Generate an account that has 100 ETH
    pub fn mock_100_ether(code: Bytecode) -> Self {
        Self {
            address: Address::repeat_byte(0xfe),
            balance: Word::from(10).pow(20.into()),
            code: code.into(),
            ..Default::default()
        }
    }
}

fn serde_account_storage<S: Serializer>(
    to_serialize: &HashMap<Word, Word>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    to_serialize
        .iter()
        .map(|(k, v)| (Hash::from(k.to_be_bytes()), Hash::from(v.to_be_bytes())))
        .collect::<HashMap<_, _>>()
        .serialize(serializer)
}

/// Definition of all of the constants related to an Ethereum block and
/// chain to be used as setup for the external tracer.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize)]
pub struct BlockConstants {
    /// coinbase
    pub coinbase: Address,
    /// time
    pub timestamp: Word,
    /// Block number
    /// U64 type is required to serialize into proper hex with 0x prefix
    pub number: U64,
    /// difficulty
    pub difficulty: Word,
    /// gas limit
    pub gas_limit: Word,
    /// base fee
    pub base_fee: Word,
}

impl<TX> TryFrom<&Block<TX>> for BlockConstants {
    type Error = Error;

    fn try_from(block: &Block<TX>) -> Result<Self, Self::Error> {
        Ok(Self {
            coinbase: block.author.ok_or(Error::IncompleteBlock)?,
            timestamp: block.timestamp,
            number: block.number.ok_or(Error::IncompleteBlock)?,
            difficulty: if block.difficulty.is_zero() {
                block.mix_hash.unwrap_or_default().to_fixed_bytes().into()
            } else {
                block.difficulty
            },
            gas_limit: block.gas_limit,
            base_fee: block.base_fee_per_gas.ok_or(Error::IncompleteBlock)?,
        })
    }
}

impl BlockConstants {
    /// Generates a new `BlockConstants` instance from it's fields.
    pub fn new(
        coinbase: Address,
        timestamp: Word,
        number: U64,
        difficulty: Word,
        gas_limit: Word,
        base_fee: Word,
    ) -> BlockConstants {
        BlockConstants {
            coinbase,
            timestamp,
            number,
            difficulty,
            gas_limit,
            base_fee,
        }
    }
}

/// Definition of all of the constants related to an Ethereum withdrawal.
#[derive(Debug, Default, Clone, Serialize)]
pub struct Withdrawal {
    /// Unique identifier of a withdrawal. This value starts from 0 and then increases
    /// monotonically.
    pub id: u64,
    /// Unique identifier of a validator.
    pub validator_id: u64,
    /// Address to be withdrawn to.
    pub address: Address,
    /// Withdrawal amount in Gwei.
    pub amount: u64,
}

/// Definition of all of the constants related to an Ethereum transaction.
#[derive(Debug, Default, Clone, Serialize)]
pub struct Transaction {
    /// Tx type
    pub tx_type: TxType,
    /// Sender address
    pub from: Address,
    /// Recipient address (None for contract creation)
    /// Avoid direct read from this field. We set this field public to construct the struct
    pub to: Option<Address>,
    /// Transaction nonce
    /// U64 type is required to serialize into proper hex with 0x prefix
    pub nonce: U64,
    /// Gas Limit / Supplied gas
    /// U64 type is required to serialize into proper hex with 0x prefix
    pub gas_limit: U64,
    /// Transferred value
    pub value: Word,
    /// Gas Price
    pub gas_price: Word,
    /// Gas fee cap
    pub gas_fee_cap: Option<Word>,
    /// Gas tip cap
    pub gas_tip_cap: Option<Word>,
    /// The compiled code of a contract OR the first 4 bytes of the hash of the
    /// invoked method signature and encoded parameters. For details see
    /// Ethereum Contract ABI
    pub call_data: Bytes,
    /// Access list
    pub access_list: Option<AccessList>,

    /// "v" value of the transaction signature
    pub v: u64,
    /// "r" value of the transaction signature
    pub r: Word,
    /// "s" value of the transaction signature
    pub s: Word,

    /// RLP bytes
    pub rlp_bytes: Vec<u8>,
    /// RLP unsigned bytes
    pub rlp_unsigned_bytes: Vec<u8>,

    /// Transaction hash
    pub hash: H256,
}

impl From<&Transaction> for crate::Transaction {
    fn from(tx: &Transaction) -> crate::Transaction {
        crate::Transaction {
            from: tx.from,
            to: tx.to,
            nonce: tx.nonce.to_word(),
            gas: tx.gas_limit.to_word(),
            value: tx.value,
            gas_price: Some(tx.gas_price),
            max_priority_fee_per_gas: tx.gas_tip_cap,
            max_fee_per_gas: tx.gas_fee_cap,
            input: tx.call_data.clone(),
            access_list: tx.access_list.clone(),
            v: tx.v.into(),
            r: tx.r,
            s: tx.s,
            ..Default::default()
        }
    }
}

impl From<&crate::Transaction> for Transaction {
    fn from(tx: &crate::Transaction) -> Transaction {
        Transaction {
            tx_type: TxType::get_tx_type(tx),
            from: tx.from,
            to: tx.to,
            nonce: tx.nonce.as_u64().into(),
            gas_limit: tx.gas.as_u64().into(),
            value: tx.value,
            gas_price: tx.gas_price.unwrap_or_default(),
            gas_tip_cap: tx.max_priority_fee_per_gas,
            gas_fee_cap: tx.max_fee_per_gas,
            call_data: tx.input.clone(),
            access_list: tx.access_list.clone(),
            v: tx.v.as_u64(),
            r: tx.r,
            s: tx.s,
            rlp_bytes: tx.rlp().to_vec(),
            rlp_unsigned_bytes: get_rlp_unsigned(tx),
            hash: tx.hash,
        }
    }
}

impl From<&Transaction> for TransactionRequest {
    fn from(tx: &Transaction) -> TransactionRequest {
        TransactionRequest {
            from: Some(tx.from),
            to: tx.to.map(NameOrAddress::Address),
            gas: Some(tx.gas_limit.to_word()),
            gas_price: Some(tx.gas_price),
            value: Some(tx.value),
            data: Some(tx.call_data.clone()),
            nonce: Some(tx.nonce.to_word()),
            ..Default::default()
        }
    }
}

impl Transaction {
    /// Create a dummy Transaction with zero values
    pub fn dummy() -> Self {
        Self {
            from: Address::zero(),
            to: Some(Address::zero()),
            nonce: U64::zero(),
            gas_limit: U64::zero(),
            value: Word::zero(),
            gas_price: Word::zero(),
            gas_tip_cap: Some(Word::zero()),
            gas_fee_cap: Some(Word::zero()),
            call_data: Bytes::new(),
            access_list: None,
            v: 0,
            r: Word::zero(),
            s: Word::zero(),
            ..Default::default()
        }
    }
    /// Return the SignData associated with this Transaction.
    pub fn sign_data(&self, chain_id: u64) -> Result<SignData, Error> {
        let sig_r_le = self.r.to_le_bytes();
        let sig_s_le = self.s.to_le_bytes();
        let sig_r = ct_option_ok_or(
            secp256k1::Fq::from_repr(sig_r_le),
            Error::Signature(libsecp256k1::Error::InvalidSignature),
        )?;
        let sig_s = ct_option_ok_or(
            secp256k1::Fq::from_repr(sig_s_le),
            Error::Signature(libsecp256k1::Error::InvalidSignature),
        )?;
        // msg = rlp([nonce, gasPrice, gas, to, value, data, sig_v, r, s])
        let req: TransactionRequest = self.into();
        let msg = req.chain_id(chain_id).rlp();
        let msg_hash: [u8; 32] = keccak256(&msg);
        let v = self
            .v
            .checked_sub(35 + chain_id * 2)
            .ok_or(Error::Signature(libsecp256k1::Error::InvalidSignature))? as u8;
        let pk = recover_pk(v, &self.r, &self.s, &msg_hash)?;
        // msg_hash = msg_hash % q
        let msg_hash = BigUint::from_bytes_be(msg_hash.as_slice());
        let msg_hash = msg_hash.mod_floor(&*SECP256K1_Q);
        let msg_hash_le = biguint_to_32bytes_le(msg_hash);
        let msg_hash = ct_option_ok_or(
            secp256k1::Fq::from_repr(msg_hash_le),
            libsecp256k1::Error::InvalidMessage,
        )?;
        Ok(SignData {
            signature: (sig_r, sig_s, v),
            pk,
            msg,
            msg_hash,
        })
    }

    /// Compute call data gas cost from call data
    pub fn call_data_gas_cost(&self) -> u64 {
        self.call_data
            .iter()
            .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 })
    }

    /// Compute the intrinsic gas cost
    pub fn intrinsic_gas_cost(&self) -> u64 {
        let is_create = self.is_create() as u64;
        // Calculate gas cost of init code for EIP-3860.
        let init_code_gas_cost =
            ((self.call_data.len() as u64 + 31) / 32) * evm_types::INIT_CODE_WORD_GAS;
        is_create * (GasCost::CREATION_TX + init_code_gas_cost)
            + (1 - is_create) * GasCost::TX
            + self.call_data_gas_cost()
    }

    /// Get the "to" address. If `to` is None then zero address
    pub fn to_or_zero(&self) -> Address {
        self.to.unwrap_or_default()
    }
    /// Get the "to" address. If `to` is None then compute contract address
    pub fn to_or_contract_addr(&self) -> Address {
        self.to
            .unwrap_or_else(|| get_contract_address(self.from, self.nonce.to_word()))
    }
    /// Determine if this transaction is a contract create transaction
    pub fn is_create(&self) -> bool {
        self.to.is_none()
    }

    /// Convert to transaction response
    pub fn to_response(
        &self,
        transaction_index: U64,
        chain_id: Word,
        block_number: U64,
    ) -> response::Transaction {
        response::Transaction {
            from: self.from,
            to: self.to,
            value: self.value,
            input: self.call_data.clone(),
            gas_price: Some(self.gas_price),
            access_list: self.access_list.clone(),
            nonce: self.nonce.to_word(),
            gas: self.gas_limit.to_word(),
            transaction_index: Some(transaction_index),
            r: self.r,
            s: self.s,
            v: U64::from(self.v),
            block_number: Some(block_number),
            transaction_type: Some(U64::from(self.tx_type as u64)),
            max_priority_fee_per_gas: self.gas_tip_cap,
            max_fee_per_gas: self.gas_fee_cap,
            chain_id: Some(chain_id),
            ..response::Transaction::default()
        }
    }
    /// Convenient method for gas limit
    pub fn gas(&self) -> u64 {
        self.gas_limit.as_u64()
    }
}

/// GethData is a type that contains all the information of a Ethereum block
#[derive(Debug, Clone)]
pub struct GethData {
    /// chain id
    pub chain_id: Word,
    /// history hashes contains most recent 256 block hashes in history, where
    /// the latest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// Block from geth
    pub eth_block: Block<crate::Transaction>,
    /// Execution Trace from geth
    pub geth_traces: Vec<GethExecTrace>,
    /// Accounts
    pub accounts: Vec<Account>,
}

impl GethData {
    /// Signs transactions with selected wallets
    pub fn sign(&mut self, wallets: &HashMap<Address, LocalWallet>) {
        for tx in self.eth_block.transactions.iter_mut() {
            let wallet = wallets.get(&tx.from).unwrap();
            assert_eq!(Word::from(wallet.chain_id()), self.chain_id);
            let geth_tx: Transaction = (&*tx).into();
            let req: TransactionRequest = (&geth_tx).into();
            let sig = wallet
                .sign_transaction_sync(&req.chain_id(self.chain_id.as_u64()).into())
                .unwrap();
            tx.v = U64::from(sig.v);
            tx.r = sig.r;
            tx.s = sig.s;
        }
    }
}

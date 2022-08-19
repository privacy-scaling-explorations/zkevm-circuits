//! Mock Transaction definition and builder related methods.

use super::{MOCK_ACCOUNTS, MOCK_CHAIN_ID, MOCK_GASPRICE};
use eth_types::{
    geth_types::Transaction as GethTransaction, AccessList, Address, Bytes, Hash, Transaction,
    Word, U64,
};
use ethers_core::{
    rand::{CryptoRng, RngCore},
    types::TransactionRequest,
    utils::keccak256,
};
use ethers_signers::{LocalWallet, Signer};

#[derive(Debug, Clone)]
pub enum AddrOrWallet {
    Addr(Address),
    Wallet(LocalWallet),
}

impl From<Address> for AddrOrWallet {
    fn from(addr: Address) -> Self {
        AddrOrWallet::Addr(addr)
    }
}

impl From<LocalWallet> for AddrOrWallet {
    fn from(wallet: LocalWallet) -> Self {
        AddrOrWallet::Wallet(wallet)
    }
}

impl AddrOrWallet {
    /// Generates a random Wallet from a random secpk256 keypair
    pub fn random<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        AddrOrWallet::Wallet(LocalWallet::new(rng))
    }
}

impl AddrOrWallet {
    fn address(&self) -> Address {
        match self {
            Self::Addr(addr) => addr.clone(),
            Self::Wallet(wallet) => wallet.address(),
        }
    }

    fn is_wallet(&self) -> bool {
        match self {
            Self::Wallet(_) => true,
            _ => false,
        }
    }

    /// Returns the underlying wallet stored in the enum.
    /// # Panics
    /// This function will panic if the enum does not contain a [`LocalWallet`]
    /// and instead contains the [`Address`] variant.
    fn as_wallet(&self) -> LocalWallet {
        match self {
            Self::Wallet(wallet) => wallet.to_owned(),
            _ => panic!("Broken AddrOrWallet invariant"),
        }
    }
}

#[derive(Debug, Clone)]
/// Mock structure which represents a Transaction and can be used for tests.
/// It contains all the builder-pattern methods required to be able to specify
/// any of it's details.
pub struct MockTransaction {
    hash: Option<Hash>,
    nonce: Word,
    block_hash: Hash,
    block_number: U64,
    transaction_index: U64,
    from: AddrOrWallet,
    to: Option<AddrOrWallet>,
    value: Word,
    gas_price: Word,
    gas: Word,
    input: Bytes,
    v: Option<U64>,
    r: Option<Word>,
    s: Option<Word>,
    transaction_type: U64,
    access_list: AccessList,
    max_priority_fee_per_gas: Word,
    max_fee_per_gas: Word,
    chain_id: Word,
}

impl Default for MockTransaction {
    fn default() -> Self {
        MockTransaction {
            hash: Some(Hash::zero()),
            nonce: Word::zero(),
            block_hash: Hash::zero(),
            block_number: U64::zero(),
            transaction_index: U64::zero(),
            from: AddrOrWallet::Addr(MOCK_ACCOUNTS[0]),
            to: None,
            value: Word::zero(),
            gas_price: *MOCK_GASPRICE,
            gas: Word::from(1_000_000u64),
            input: Bytes::default(),
            v: None,
            r: None,
            s: None,
            transaction_type: U64::zero(),
            access_list: AccessList::default(),
            max_priority_fee_per_gas: Word::zero(),
            max_fee_per_gas: Word::zero(),
            chain_id: *MOCK_CHAIN_ID,
        }
    }
}

impl From<MockTransaction> for Transaction {
    fn from(mock: MockTransaction) -> Self {
        Transaction {
            hash: mock.hash.unwrap_or_default(),
            nonce: mock.nonce,
            block_hash: Some(mock.block_hash),
            block_number: Some(mock.block_number),
            transaction_index: Some(mock.transaction_index),
            from: mock.from.address(),
            to: mock.to.map(|addr| addr.address()),
            value: mock.value,
            gas_price: Some(mock.gas_price),
            gas: mock.gas,
            input: mock.input,
            v: mock.v.unwrap_or_default(),
            r: mock.r.unwrap_or_default(),
            s: mock.s.unwrap_or_default(),
            transaction_type: Some(mock.transaction_type),
            access_list: Some(mock.access_list),
            max_priority_fee_per_gas: Some(mock.max_priority_fee_per_gas),
            max_fee_per_gas: Some(mock.max_fee_per_gas),
            chain_id: Some(mock.chain_id),
        }
    }
}

impl From<MockTransaction> for GethTransaction {
    fn from(mock: MockTransaction) -> Self {
        GethTransaction::from_eth_tx(&Transaction {
            hash: mock.hash.unwrap_or_default(),
            nonce: mock.nonce,
            block_hash: Some(mock.block_hash),
            block_number: Some(mock.block_number),
            transaction_index: Some(mock.transaction_index),
            from: mock.from.address(),
            to: mock.to.map(|addr| addr.address()),
            value: mock.value,
            gas_price: Some(mock.gas_price),
            gas: mock.gas,
            input: mock.input,
            v: mock.v.unwrap_or_default(),
            r: mock.r.unwrap_or_default(),
            s: mock.s.unwrap_or_default(),
            transaction_type: Some(mock.transaction_type),
            access_list: Some(mock.access_list),
            max_priority_fee_per_gas: Some(mock.max_priority_fee_per_gas),
            max_fee_per_gas: Some(mock.max_fee_per_gas),
            chain_id: Some(mock.chain_id),
        })
    }
}

impl MockTransaction {
    /// TODO: This should be computed based on the fields of the Tx by
    /// default unless `Some(hash)` is specified on build process.
    pub fn hash(&mut self, hash: Hash) -> &mut Self {
        self.hash = Some(hash);
        self
    }

    /// Set nonce field for the MockTransaction.
    pub fn nonce(&mut self, nonce: Word) -> &mut Self {
        self.nonce = nonce;
        self
    }

    /// Set block_hash field for the MockTransaction.
    pub fn block_hash(&mut self, block_hash: Hash) -> &mut Self {
        self.block_hash = block_hash;
        self
    }

    /// Set block_number field for the MockTransaction.
    pub fn block_number(&mut self, block_number: u64) -> &mut Self {
        self.block_number = U64::from(block_number);
        self
    }

    /// Set transaction_idx field for the MockTransaction.
    pub fn transaction_idx(&mut self, transaction_idx: u64) -> &mut Self {
        self.transaction_index = U64::from(transaction_idx);
        self
    }

    /// Set from field for the MockTransaction.
    pub fn from<T: Into<AddrOrWallet>>(&mut self, from: T) -> &mut Self {
        self.from = from.into();
        self
    }

    /// Set to field for the MockTransaction.
    pub fn to<T: Into<AddrOrWallet>>(&mut self, to: T) -> &mut Self {
        self.to = Some(to.into());
        self
    }

    /// Set value field for the MockTransaction.
    pub fn value(&mut self, value: Word) -> &mut Self {
        self.value = value;
        self
    }

    /// Set gas_price field for the MockTransaction.
    pub fn gas_price(&mut self, gas_price: Word) -> &mut Self {
        self.gas_price = gas_price;
        self
    }

    /// Set gas field for the MockTransaction.
    pub fn gas(&mut self, gas: Word) -> &mut Self {
        self.gas = gas;
        self
    }

    /// Set input field for the MockTransaction.
    pub fn input(&mut self, input: Bytes) -> &mut Self {
        self.input = input;
        self
    }

    /// Set sig_data field for the MockTransaction.
    pub fn sig_data(&mut self, data: (u64, Word, Word)) -> &mut Self {
        self.v = Some(U64::from(data.0));
        self.r = Some(data.1);
        self.s = Some(data.2);
        self
    }

    /// Set transaction_type field for the MockTransaction.
    pub fn transaction_type(&mut self, transaction_type: u64) -> &mut Self {
        self.transaction_type = U64::from(transaction_type);
        self
    }

    /// Set access_list field for the MockTransaction.
    pub fn access_list(&mut self, access_list: AccessList) -> &mut Self {
        self.access_list = access_list;
        self
    }

    /// Set max_priority_fee_per_gas field for the MockTransaction.
    pub fn max_priority_fee_per_gas(&mut self, max_priority_fee_per_gas: Word) -> &mut Self {
        self.max_priority_fee_per_gas = max_priority_fee_per_gas;
        self
    }

    /// Set max_fee_per_gas field for the MockTransaction.
    pub fn max_fee_per_gas(&mut self, max_fee_per_gas: Word) -> &mut Self {
        self.max_fee_per_gas = max_fee_per_gas;
        self
    }

    /// Set chain_id field for the MockTransaction.
    pub(crate) fn chain_id(&mut self, chain_id: Word) -> &mut Self {
        self.chain_id = chain_id;
        self
    }

    /// Consumes the mutable ref to the MockTransaction returning the structure
    /// by value.
    pub fn build(&mut self) -> Self {
        let tx = TransactionRequest::new()
            .from(self.from.address())
            .to(self.to.clone().unwrap().address())
            .nonce(self.nonce)
            .value(self.value)
            .data(self.input.clone())
            .gas(self.gas)
            .gas_price(self.gas_price);

        let tx_rlp = tx.rlp(self.chain_id.low_u64());
        let sighash = keccak256(tx_rlp.as_ref()).into();
        match (self.v, self.r, self.s) {
            (Some(_), Some(_), Some(_)) => {
                // We already set some signature params. We just compute the hash in case it's
                // not already set.
                if self.hash.is_none() {
                    self.hash(Hash::from(sighash));
                }
            }
            (None, None, None) => {
                // Compute sig params and set them in case we have a wallet as `from` attr.
                if self.from.is_wallet() && self.hash.is_none() {
                    let wallet = LocalWallet::from(self.from.as_wallet());
                    let sig = wallet.sign_hash(sighash, true);
                    // Set sig parameters
                    self.sig_data((sig.v, sig.s, sig.r));
                    // Compute tx hash in case is not already set
                    if self.hash.is_none() {
                        let tmp_tx = Transaction::from(self.to_owned());
                        self.hash(tmp_tx.hash());
                    }
                }
            }
            _ => unimplemented!(),
        }

        self.to_owned()
    }
}

//! Mock Block definition and builder related methods.

use crate::{MockTransaction, MOCK_BASEFEE, MOCK_CHAIN_ID, MOCK_DIFFICULTY, MOCK_GASLIMIT};
use eth_types::{Address, Block, Bytes, Hash, Transaction, Word, H64, U64};
use ethers_core::{
    types::{Bloom, OtherFields},
    utils::keccak256,
};

#[derive(Clone, Debug)]
/// Mock structure which represents an Ethereum Block and can be used for tests.
/// It contains all the builder-pattern methods required to be able to specify
/// any of it's details.
pub struct MockBlock {
    // Block (header) hash
    hash: Option<Hash>,
    // Block header (ordered as hashed)
    parent_hash: Hash,
    uncles_hash: Hash,
    author: Address,
    state_root: Hash,
    transactions_root: Hash,
    receipts_root: Hash,
    logs_bloom: Option<Bloom>,
    difficulty: Word,
    number: U64,
    gas_limit: Word,
    gas_used: Word,
    timestamp: Word,
    extra_data: Bytes,
    mix_hash: Hash,
    nonce: H64,
    base_fee_per_gas: Option<Word>, // London upgrade, EIP-1559
    withdrawal_hash: Option<Hash>,  // Shanghai upgrade, EIP-4895
    // Other information
    total_difficulty: Word,
    seal_fields: Vec<Bytes>,
    uncles: Vec<Hash>,
    pub(crate) transactions: Vec<MockTransaction>,
    size: Word,
    // This field is handled here as we assume that all block txs have the same ChainId.
    // Also, the field is stored in the block_table since we don't have a chain_config
    // structure/table.
    pub(crate) chain_id: Word,
}

impl Default for MockBlock {
    fn default() -> Self {
        MockBlock {
            hash: Some(Hash::zero()),
            // Header
            parent_hash: Hash::zero(),
            uncles_hash: Hash::zero(),
            author: Address::zero(),
            state_root: Hash::zero(),
            transactions_root: Hash::zero(),
            receipts_root: Hash::zero(),
            logs_bloom: None,
            difficulty: *MOCK_DIFFICULTY,
            number: U64([0u64]),
            gas_limit: *MOCK_GASLIMIT,
            gas_used: Word::zero(),
            timestamp: Word::from(123456789u64),
            extra_data: Bytes::default(),
            mix_hash: Hash::zero(),
            nonce: H64::zero(),
            base_fee_per_gas: Some(*MOCK_BASEFEE),
            withdrawal_hash: None,
            // Other information
            total_difficulty: Word::zero(),
            seal_fields: Vec::new(),
            uncles: Vec::new(),
            transactions: Vec::new(),
            size: Word::zero(),
            chain_id: *MOCK_CHAIN_ID,
        }
    }
}

impl From<MockBlock> for Block<Transaction> {
    fn from(mut mock: MockBlock) -> Self {
        Block {
            hash: mock.hash.or_else(|| Some(Hash::default())),
            // Header
            parent_hash: mock.parent_hash,
            uncles_hash: mock.uncles_hash,
            author: Some(mock.author),
            state_root: mock.state_root,
            transactions_root: mock.transactions_root,
            receipts_root: mock.receipts_root,
            logs_bloom: mock.logs_bloom,
            difficulty: mock.difficulty,
            number: Some(mock.number),
            gas_limit: mock.gas_limit,
            gas_used: mock.gas_used,
            timestamp: mock.timestamp,
            extra_data: mock.extra_data,
            mix_hash: Some(mock.mix_hash),
            nonce: Some(mock.nonce),
            base_fee_per_gas: mock.base_fee_per_gas,
            // Other information
            total_difficulty: Some(mock.total_difficulty),
            seal_fields: mock.seal_fields,
            uncles: mock.uncles,
            transactions: mock
                .transactions
                .iter_mut()
                .map(|mock_tx| (mock_tx.chain_id(mock.chain_id).to_owned()).into())
                .collect::<Vec<Transaction>>(),
            size: Some(mock.size),
            other: OtherFields::default(),
        }
    }
}

impl From<MockBlock> for Block<()> {
    fn from(mock: MockBlock) -> Self {
        Block {
            hash: mock.hash.or_else(|| Some(Hash::default())),
            // Header
            parent_hash: mock.parent_hash,
            uncles_hash: mock.uncles_hash,
            author: Some(mock.author),
            state_root: mock.state_root,
            transactions_root: mock.transactions_root,
            receipts_root: mock.receipts_root,
            logs_bloom: mock.logs_bloom,
            difficulty: mock.difficulty,
            number: Some(mock.number),
            gas_limit: mock.gas_limit,
            gas_used: mock.gas_used,
            timestamp: mock.timestamp,
            extra_data: mock.extra_data,
            mix_hash: Some(mock.mix_hash),
            nonce: Some(mock.nonce),
            base_fee_per_gas: mock.base_fee_per_gas,
            // Other information
            total_difficulty: Some(mock.total_difficulty),
            seal_fields: mock.seal_fields,
            uncles: mock.uncles,
            transactions: vec![],
            size: Some(mock.size),
            other: OtherFields::default(),
        }
    }
}

impl MockBlock {
    /// Compute the hash of the block's header
    // For more details, look at https://ethereum.stackexchange.com/questions/67055/block-header-hash-verification?noredirect=1&lq=1
    // and add "withdrawalRoot" at the end for Shanghai blocks
    pub fn hash(&mut self) -> &mut Self {
        let block_hash = {
            let mut stream = ethers_core::utils::rlp::RlpStream::new();
            // We encode the BaseFee only for upgrades higher or equal to London
            let list_length: usize = match (self.base_fee_per_gas, self.withdrawal_hash) {
                (Some(_), Some(_)) => 17,
                (Some(_), None) => 16,
                (None, Some(_)) => panic!("withdrawalsRoot given, baseFeePerGas missing"),
                (None, None) => 15,
            };
            stream.begin_list(list_length);
            stream.append(&self.parent_hash);
            stream.append(&self.uncles_hash);
            stream.append(&self.author);
            stream.append(&self.state_root);
            stream.append(&self.transactions_root);
            stream.append(&self.receipts_root);
            stream.append(&self.logs_bloom.unwrap()); //
            stream.append(&self.difficulty);
            stream.append(&self.number);
            stream.append(&self.gas_limit);
            stream.append(&self.gas_used);
            stream.append(&self.timestamp);
            stream.append(&self.extra_data.to_vec());
            stream.append(&self.mix_hash);
            stream.append(&self.nonce);
            match self.base_fee_per_gas {
                Some(base_fee_per_gas) => stream.append(&base_fee_per_gas),
                _ => &mut stream,
            };
            match self.withdrawal_hash {
                Some(withdrawal_hash) => stream.append(&withdrawal_hash),
                _ => &mut stream,
            };
            let rlp_encoding = stream.out().to_vec();
            keccak256(rlp_encoding)
        };

        self.hash = Some(eth_types::H256(block_hash));
        self
    }

    /// Set parent_hash field for the MockBlock.
    pub fn parent_hash(&mut self, parent_hash: Hash) -> &mut Self {
        self.parent_hash = parent_hash;
        self
    }

    /// Set uncles_hash field for the MockBlock.
    pub fn uncles_hash(&mut self, uncles_hash: Hash) -> &mut Self {
        self.uncles_hash = uncles_hash;
        self
    }

    /// Set author field for the MockBlock.
    pub fn author(&mut self, author: Address) -> &mut Self {
        self.author = author;
        self
    }

    /// Set state_root field for the MockBlock.
    pub fn state_root(&mut self, state_root: Hash) -> &mut Self {
        self.state_root = state_root;
        self
    }

    /// Set transactions_root field for the MockBlock.
    pub fn transactions_root(&mut self, transactions_root: Hash) -> &mut Self {
        self.transactions_root = transactions_root;
        self
    }

    /// Set receipts_root field for the MockBlock.
    pub fn receipts_root(&mut self, receipts_root: Hash) -> &mut Self {
        self.receipts_root = receipts_root;
        self
    }

    /// Set logs_bloom field for the MockBlock.
    pub fn logs_bloom(&mut self, logs_bloom: Bloom) -> &mut Self {
        self.logs_bloom = Some(logs_bloom);
        self
    }

    /// Set difficulty field for the MockBlock.
    pub fn difficulty(&mut self, difficulty: Word) -> &mut Self {
        self.difficulty = difficulty;
        self
    }

    /// Set number field for the MockBlock.
    pub fn number(&mut self, number: u64) -> &mut Self {
        self.number = U64::from(number);
        self
    }

    /// Set gas_limit field for the MockBlock.
    pub fn gas_limit(&mut self, gas_limit: Word) -> &mut Self {
        self.gas_limit = gas_limit;
        self
    }

    /// Set gas_used field for the MockBlock.
    pub fn gas_used(&mut self, gas_used: Word) -> &mut Self {
        self.gas_used = gas_used;
        self
    }

    /// Set timestamp field for the MockBlock.
    pub fn timestamp(&mut self, timestamp: Word) -> &mut Self {
        self.timestamp = timestamp;
        self
    }

    /// Set extra_data field for the MockBlock.
    pub fn extra_data(&mut self, extra_data: Bytes) -> &mut Self {
        self.extra_data = extra_data;
        self
    }

    /// Set mix_hash field for the MockBlock.
    pub fn mix_hash(&mut self, mix_hash: Hash) -> &mut Self {
        self.mix_hash = mix_hash;
        self
    }

    /// Set nonce field for the MockBlock.
    pub fn nonce(&mut self, nonce: H64) -> &mut Self {
        self.nonce = nonce;
        self
    }

    /// Set base_fee_per_gas field for the MockBlock.
    pub fn base_fee_per_gas(&mut self, base_fee_per_gas: Option<Word>) -> &mut Self {
        self.base_fee_per_gas = base_fee_per_gas;
        self
    }

    /// Set withdrawal_hash field for the MockBlock.
    pub fn withdrawal_hash(&mut self, withdrawal_hash: Option<Hash>) -> &mut Self {
        self.withdrawal_hash = withdrawal_hash;
        self
    }

    /// Set total_difficulty field for the MockBlock.
    pub fn total_difficulty(&mut self, total_difficulty: Word) -> &mut Self {
        self.total_difficulty = total_difficulty;
        self
    }

    /// Set seal_fields field for the MockBlock.
    pub fn seal_fields(&mut self, seal_fields: Vec<Bytes>) -> &mut Self {
        self.seal_fields = seal_fields;
        self
    }

    /// Set uncles field for the MockBlock.
    pub fn uncles(&mut self, uncles: Vec<Hash>) -> &mut Self {
        self.uncles = uncles;
        self
    }

    /// Set transactions field for the MockBlock.
    pub fn transactions<I: IntoIterator<Item = MockTransaction>>(
        &mut self,
        transactions: I,
    ) -> &mut Self {
        self.transactions.extend(transactions);
        self
    }

    /// Set size field for the MockBlock.
    pub fn size(&mut self, size: Word) -> &mut Self {
        self.size = size;
        self
    }

    /// Set chain_id field for the MockBlock.
    pub fn chain_id(&mut self, chain_id: Word) -> &mut Self {
        self.chain_id = chain_id;
        self
    }

    /// Finalizes the current MockBlock under construction returning a new
    /// instance to it.
    pub fn build(&mut self) -> Self {
        self.to_owned()
    }
}

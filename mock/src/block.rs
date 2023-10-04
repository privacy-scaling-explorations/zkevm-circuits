//! Mock Block definition and builder related methods.

use crate::{
    withdrawal::MockWithdrawal, MockTransaction, MOCK_BASEFEE, MOCK_CHAIN_ID, MOCK_DIFFICULTY,
    MOCK_GASLIMIT,
};
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
    pub(crate) withdrawals: Vec<MockWithdrawal>,
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
            withdrawal_hash: Some(Hash::zero()),
            // Other information
            total_difficulty: Word::zero(),
            seal_fields: Vec::new(),
            uncles: Vec::new(),
            transactions: Vec::new(),
            withdrawals: Vec::new(),
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
            withdrawals_root: mock.withdrawal_hash,
            withdrawals: Some(
                mock.withdrawals
                    .iter_mut()
                    .map(|mock_wd| mock_wd.to_owned().into())
                    .collect(),
            ),
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
            withdrawals_root: mock.withdrawal_hash,
            withdrawals: Some(
                mock.withdrawals
                    .iter()
                    .map(|mock_wd| mock_wd.to_owned().into())
                    .collect(),
            ),
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

#[cfg(test)]
mod block_tests {
    use crate::MockBlock;
    use eth_types::{Address, Bytes, Hash, Word, H64};
    use ethers_core::types::Bloom;
    use std::str::FromStr;

    #[test]
    fn test_blockhash() {
        // Checking legacy block
        // curl -X POST --data '{"id":1,"jsonrpc":2.0,"method":"eth_getBlockByNumber","params":["0x61a80",false]}' https://mainnet.infura.io/v3/<API_KEY>
        let mut mock_block = MockBlock::default();
        mock_block.parent_hash(
            Hash::from_str("0x1e77d8f1267348b516ebc4f4da1e2aa59f85f0cbd853949500ffac8bfc38ba14")
                .unwrap(),
        );
        mock_block.uncles_hash(
            Hash::from_str("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
                .unwrap(),
        );
        mock_block.author(Address::from_str("0x2a65Aca4D5fC5B5C859090a6c34d164135398226").unwrap());
        mock_block.state_root(
            Hash::from_str("0x0b5e4386680f43c224c5c037efc0b645c8e1c3f6b30da0eec07272b4e6f8cd89")
                .unwrap(),
        );
        mock_block.transactions_root(
            Hash::from_str("0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
                .unwrap(),
        );
        mock_block.receipts_root(
            Hash::from_str("0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
                .unwrap(),
        );
        mock_block.logs_bloom(Bloom::from_str("0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap());
        mock_block.difficulty(Word::from_str("0x57a418a7c3e").unwrap());
        mock_block.number(400000);
        mock_block.gas_limit(Word::from_str("2fefd8").unwrap());
        mock_block.gas_used(Word::from_str("0x").unwrap());
        mock_block.timestamp(Word::from_str("0x5622efdc").unwrap());
        mock_block
            .extra_data(Bytes::from_str("0xd583010202844765746885676f312e35856c696e7578").unwrap());
        mock_block.mix_hash(
            Hash::from_str("0x3fbea7af642a4e20cd93a945a1f5e23bd72fc5261153e09102cf718980aeff38")
                .unwrap(),
        );
        mock_block.nonce(H64::from_low_u64_be(0x6af23caae95692ef));
        mock_block.base_fee_per_gas(None);
        mock_block.hash();

        let expected_hash =
            Hash::from_str("0x5d15649e25d8f3e2c0374946078539d200710afc977cdfc6a977bd23f20fa8e8")
                .unwrap();
        assert!(expected_hash.eq(&mock_block.hash.unwrap()));

        // Checking block from London upgrade
        // curl -X POST --data '{"id":1,"jsonrpc":2.0,"method":"eth_getBlockByNumber","params":["0x1000000",false]}' https://mainnet.infura.io/v3/<API_KEY>
        let mut mock_block = MockBlock::default();
        mock_block.parent_hash(
            Hash::from_str("0xf34c3c11b35466e5595e077239e6b25a7c3ec07a214b2492d42ba6d73d503a1b")
                .unwrap(),
        );
        mock_block.uncles_hash(
            Hash::from_str("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
                .unwrap(),
        );
        mock_block.author(Address::from_str("0x1f9090aae28b8a3dceadf281b0f12828e676c326").unwrap());
        mock_block.state_root(
            Hash::from_str("0x8e8b72abe2caef6bcbc4919ae6a372aac81d75abc21a472f1b6f4964d72c9ddc")
                .unwrap(),
        );
        mock_block.transactions_root(
            Hash::from_str("0x6c171b24bd12308508639790b82bb5318493016ec46e4688427449f6f6b8f354")
                .unwrap(),
        );
        mock_block.receipts_root(
            Hash::from_str("0xec59796c98c8d82b77b4a28aedd21c2e9422871631a447eb6407c9cf6817d2d8")
                .unwrap(),
        );
        mock_block.logs_bloom(Bloom::from_str("0xa821ad60a15607455d2c8b3ca14ae1a608a1efbb8fb1201781096041f4d3ec105cd59bf117887838c4627f2eea0d255e66237252ba96fae7422d9a1272ef68f2a0a841cf6c08852ffb23d0297038a6a480a54c29555c7c49f88bbe56f8613965d24ccb3402e6b1e800499f10280c3d511858b0750056a7b6560933df4d5a7f143a5d937710521518a8fcdd43fd7202fc05e8578bd5494a5da4a83560095f90279a9d7b2b36a7614b9791e6c02ab6a8a996686a4034c7a3877be514c6936b245be3d01452b1a704f6f9288282fa39b1056fed026a9eaed455a6895a36283cf540d3b7f608a10200bbc90c1785018104f01a502c8c556c2341e9096ef8d222d683").unwrap());
        mock_block.difficulty(Word::from_str("0x0").unwrap());
        mock_block.number(u64::from_str_radix("0x1000000".trim_start_matches("0x"), 16).unwrap());
        mock_block.gas_limit(Word::from_str("0x1c9c380").unwrap());
        mock_block.gas_used(Word::from_str("0xef2f92").unwrap());
        mock_block.timestamp(Word::from_str("0x6407537f").unwrap());
        let mock_block =
            mock_block.extra_data(Bytes::from_str("0x7273796e632d6275696c6465722e78797a").unwrap());
        mock_block.mix_hash(
            Hash::from_str("0x9f5fd11335938ac040c82dc4330a99957a81fa480e548570f71baa1cd245d4bb")
                .unwrap(),
        );
        mock_block.nonce(H64::from_low_u64_be(0x0000000000000000));
        mock_block.base_fee_per_gas(Word::from_str("0xe538bec8c").ok());
        mock_block.hash();

        let expected_hash =
            Hash::from_str("0xb1214baed59ee19bce48b3a2df4d9c485848ac91ac3cb286298f93a274eecd3c")
                .unwrap();
        assert!(expected_hash.eq(&mock_block.hash.unwrap()));

        // Checking block from Shanghai upgrade
        // curl -X POST --data '{"id":1,"jsonrpc":2.0,"method":"eth_getBlockByNumber","params":["0x10a7606",false]}' https://mainnet.infura.io/v3/<API_KEY>
        let mut mock_block = MockBlock::default();
        mock_block.parent_hash(
            Hash::from_str("0xae2f1c5b67a147b9d6aa6c2bf9ea4388093437fe75091516dfdc26a39e9981fb")
                .unwrap(),
        );
        mock_block.uncles_hash(
            Hash::from_str("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
                .unwrap(),
        );
        mock_block.author(Address::from_str("0x07e62776b74032b9b0ef2ed76313a376f886c3f7").unwrap());
        mock_block.state_root(
            Hash::from_str("0x45f5e077a3d4b0e4a4ad741fd5c0417b617eac9d7bd32ed9ce7c3cff67deffcf")
                .unwrap(),
        );
        mock_block.transactions_root(
            Hash::from_str("0xfd2114109ef14dc78b599f523230504f1853adc192bacdec78e08020cc834f12")
                .unwrap(),
        );
        mock_block.receipts_root(
            Hash::from_str("0xed2dfe9e1ca3e7dc4afbc8e5287150e9b18dba98ee29061bd9e632f06f900924")
                .unwrap(),
        );
        mock_block.logs_bloom(Bloom::from_str("0xf5233021e9079e6870b92930b0849b29fde349248a1841680b03081bcc1b0dd3bde71dd0c05092304f5c3b154375890bc7eda030ba80bd645059938935aea2510c05546a250ca838ed034658d8dc11e9321ae28984ee5eb4511b554fd9211f12ef06bd607b6aa43f354ef92080b9b8d9965254f10a28de6393014bb5c829295e0d3a17538a0439d540dd945c4b0a514673c35ce1fd2b066e772cf84bd0b0d0a0bf0ab96a838cecdd0e86d1fffd967dbc0c45fd50c438c08b03e60e4e800c4b6fef5804536e4a557aa401cc74774f5402454b6c42f26ca7dc8d343bf758927f85a8b1a51c0bc0c0a029479b86994ba815df23521d8bb88376212bf917a113d661").unwrap());
        mock_block.difficulty(Word::from_str("0x0").unwrap());
        mock_block.number(u64::from_str_radix("0x10a7606".trim_start_matches("0x"), 16).unwrap());
        mock_block.gas_limit(Word::from_str("0x1c9c380").unwrap());
        mock_block.gas_used(Word::from_str("0xeff5b6").unwrap());
        mock_block.timestamp(Word::from_str("0x6486d6f7").unwrap());
        let mock_block =
            mock_block.extra_data(Bytes::from_str("0x6279206275696c64657230783639").unwrap());
        mock_block.mix_hash(
            Hash::from_str("0xeac230d2eebab509486741a8bb4aba8326bc008dec386f8ecc8ce5a0ff686089")
                .unwrap(),
        );
        mock_block.nonce(H64::from_low_u64_be(0x0000000000000000));
        mock_block.base_fee_per_gas(Word::from_str("0x3ceefcf19").ok());
        mock_block.withdrawal_hash(
            Hash::from_str("0xcebc2de77cef99baaae4833df486458f7716e822f7354d678852c205d12f12f3")
                .ok(),
        );
        mock_block.hash();

        let expected_hash =
            Hash::from_str("0xd15d1ed6795d3f5cc849c2f19fc1c7350c8ab816c6b832ff639e5de00893f249")
                .unwrap();
        assert!(expected_hash.eq(&mock_block.hash.unwrap()));
    }
}

use std::{collections::HashSet, ops::Deref, sync::Arc};

use eth_types::{Field, ToScalar};
use ethers::{
    abi::Address,
    prelude::{k256::ecdsa::SigningKey, SignerMiddleware, *},
    providers::{Http, Provider},
    signers::Wallet,
    types::{
        transaction::eip2930::{AccessList, AccessListItem},
        BlockId, BlockNumber, H256, U256, U64,
    },
};
use eyre::Result;

use mpt_witness_generator::{ProofType, TrieModification};
use zkevm_circuits::{
    mpt_circuit::witness_row::Node,
    table::mpt_table::MPTProofType,
    util::word::{self, Word},
};

#[derive(Default, Debug, Clone)]
pub struct Transforms {
    pub block_no: U64,
    pub prev_state_root: H256,
    pub curr_state_root: H256,
    pub trie_modifications: Vec<TrieModification>,
}

trait TrieModificationBuilder {
    fn balance(address: Address, balance: U256) -> Self;
    fn nonce(address: Address, nonce: U64) -> Self;
    fn codehash(address: Address, code_hash: H256) -> Self;
    fn storage(address: Address, key: H256, value: U256) -> Self;
}

impl TrieModificationBuilder for TrieModification {
    fn balance(address: Address, balance: U256) -> Self {
        Self {
            typ: ProofType::BalanceChanged,
            balance,
            address,
            ..Default::default()
        }
    }
    fn nonce(address: Address, nonce: U64) -> Self {
        Self {
            typ: ProofType::NonceChanged,
            address,
            nonce,
            ..Default::default()
        }
    }
    fn codehash(address: Address, code_hash: H256) -> Self {
        Self {
            typ: ProofType::CodeHashChanged,
            address,
            code_hash,
            ..Default::default()
        }
    }
    fn storage(address: Address, key: H256, value: U256) -> Self {
        Self {
            typ: ProofType::StorageChanged,
            address,
            key,
            value,
            ..Default::default()
        }
    }
}

#[derive(Default)]
pub struct LightClientWitness<F: Field> {
    pub transforms: Transforms,
    pub lc_witness: SingleTrieModifications<F>,
    pub mpt_witness: Vec<Node>,
}

#[derive(Default, Clone)]
pub struct SingleTrieModification<F: Field> {
    pub typ: F,
    pub address: F,
    pub value: word::Word<F>,
    pub key: word::Word<F>,
    pub old_root: word::Word<F>,
    pub new_root: word::Word<F>,
}

#[derive(Default, Clone)]
pub struct SingleTrieModifications<F: Field>(pub Vec<SingleTrieModification<F>>);

impl<F: Field> Deref for SingleTrieModifications<F> {
    type Target = Vec<SingleTrieModification<F>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct PublicInputs<F: Field>(pub Vec<F>);
impl<F: Field> Deref for PublicInputs<F> {
    type Target = Vec<F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Field> From<&SingleTrieModifications<F>> for PublicInputs<F> {
    fn from(stm: &SingleTrieModifications<F>) -> Self {
        let mut inputs = vec![
            stm.0[0].old_root.lo(),
            stm.0[0].old_root.hi(),
            stm.0.last().unwrap().new_root.lo(),
            stm.0.last().unwrap().new_root.hi(),
            F::from(stm.0.len() as u64),
        ];

        for proof in &stm.0 {
            inputs.push(proof.typ);
            inputs.push(proof.address);
            inputs.push(proof.value.lo());
            inputs.push(proof.value.hi());
            inputs.push(proof.key.lo());
            inputs.push(proof.key.hi());
        }

        PublicInputs(inputs)
    }
}

impl<F: Field> PublicInputs<F> {
    pub fn serialize(&self) -> Vec<u8> {
        self.0[5..].iter().map(|f| f.to_repr()).flatten().collect()
    }
    pub fn unserialize(old_root: H256, prev_root: H256, bytes: Vec<u8>) -> PublicInputs<F> {
        let mut pi = Vec::new();

        pi.push(F::from((bytes.len() as u64) / 6));

        let mut chunks = bytes.chunks_exact(32);
        while let Some(chunk) = chunks.next() {
            let typ = F::from_repr(chunk.try_into().unwrap()).unwrap();
            let address = F::from_repr(chunks.next().unwrap().try_into().unwrap()).unwrap();
            let value_lo = F::from_repr(chunks.next().unwrap().try_into().unwrap()).unwrap();
            let value_hi = F::from_repr(chunks.next().unwrap().try_into().unwrap()).unwrap();
            let key_lo = F::from_repr(chunks.next().unwrap().try_into().unwrap()).unwrap();
            let key_hi = F::from_repr(chunks.next().unwrap().try_into().unwrap()).unwrap();

            pi.append(&mut vec![typ, address, value_lo, value_hi, key_lo, key_hi]);
        }

        PublicInputs(pi)
    }
}

impl<F: Field> LightClientWitness<F> {
    pub async fn build(
        client: Arc<SignerMiddleware<Provider<Http>, Wallet<SigningKey>>>,
        provider: &str,
        block_no: U64,
        access_list: Option<AccessList>,
    ) -> Result<Option<Self>> {
        let transforms = Self::get_transforms(client, block_no, access_list).await?;
        println!("### trns : {:#?}", transforms);
        if transforms.prev_state_root == transforms.curr_state_root {
            Ok(None)
        } else {
            let (mpt_witness, lc_witness) = Self::mpt_witness(&transforms, provider)?;
            Ok(Some(Self {
                transforms,
                mpt_witness,
                lc_witness,
            }))
        }
    }

    async fn get_transforms(
        client: Arc<SignerMiddleware<Provider<Http>, Wallet<SigningKey>>>,
        block_no: U64,
        access_list: Option<AccessList>,
    ) -> Result<Transforms> {
        let mut trie_modifications = Vec::new();

        // get previous block and this block
        let prev_block = client
            .get_block(BlockId::Number(BlockNumber::Number(block_no - 1)))
            .await?
            .unwrap();
        let curr_block = client
            .get_block_with_txs(BlockId::Number(BlockNumber::Number(block_no)))
            .await?
            .unwrap();

        println!(
            "Checking transition from\n  block {} {:?}\n  to {} {:?}",
            block_no - 1,
            prev_block.state_root,
            block_no,
            curr_block.state_root
        );

        let mut access_list = if let Some(access_list) = access_list {
            access_list
        } else {
            client
                .provider()
                .request(
                    "eth_getAccessListByNumber",
                    vec![format!("0x{:x}", block_no)],
                )
                .await?
        };

        // add coinbase to the access list
        let mut extra_addrs = HashSet::from([curr_block.author.unwrap()]);
        for tx in curr_block.transactions {
            extra_addrs.insert(tx.from);
            if let Some(addr) = tx.to {
                extra_addrs.insert(addr);
            }
        }

        for addr in extra_addrs {
            if !access_list.0.iter().any(|a| a.address == addr) {
                access_list.0.push(AccessListItem {
                    address: addr,
                    storage_keys: Vec::new(),
                });
            }
        }

        for entry in access_list.0 {
            let AccessListItem {
                address,
                storage_keys,
            } = entry;

            let old = client
                .get_proof(
                    address,
                    storage_keys.clone(),
                    Some(BlockId::Number(BlockNumber::Number(block_no - 1))),
                )
                .await?;

            let new = client
                .get_proof(
                    address,
                    storage_keys.clone(),
                    Some(BlockId::Number(BlockNumber::Number(block_no))),
                )
                .await?;

            // if nothing changed, skip
            if old.balance == new.balance
                && old.nonce == new.nonce
                && old.code_hash == new.code_hash
                && old.storage_hash == new.storage_hash
            {
                println!("Skipping {:?} as nothing changed", address);
                continue;
            }

            // check for this address changes
            if old.nonce != new.nonce {
                trie_modifications.push(TrieModification::nonce(address, new.nonce));
            }
            if old.balance != new.balance {
                trie_modifications.push(TrieModification::balance(address, new.balance));
            }
            if old.code_hash != new.code_hash {
                trie_modifications.push(TrieModification::codehash(address, new.code_hash));
            }

            for key in storage_keys {
                let new = new.storage_proof.iter().find(|p| p.key == key).unwrap();
                trie_modifications.push(TrieModification::storage(address, key, new.value));
            }
        }

        Ok(Transforms {
            block_no,
            curr_state_root: curr_block.state_root,
            prev_state_root: prev_block.state_root,
            trie_modifications,
        })
    }

    fn mpt_witness(
        trns: &Transforms,
        provider: &str,
    ) -> Result<(Vec<Node>, SingleTrieModifications<F>)> {
        let nodes = mpt_witness_generator::get_witness(
            trns.block_no.as_u64() - 1,
            &trns.trie_modifications,
            provider,
        );

        let witness_previous_state_root = H256::from_slice(&nodes[0].values[0][1..33]);
        let non_disabled_node = |n: &&Node| {
            n.start
                .as_ref()
                .map_or(false, |v| v.proof_type != MPTProofType::Disabled)
        };
        let witness_current_state_root =
            H256::from_slice(&nodes.iter().rev().find(non_disabled_node).unwrap().values[1][1..33]);

        // crate::utils::print_nodes(&nodes);

        // check if the roots matches
        assert_eq!(
            witness_previous_state_root, trns.prev_state_root,
            "previous state root does not match"
        );
        assert_eq!(
            witness_current_state_root, trns.curr_state_root,
            "current state root does not match"
        );

        // extract roots
        let mut lc_proofs = Vec::new();
        for node in nodes.iter() {
            let Some(start) = &node.start else {
                continue;
            };
            if start.proof_type == MPTProofType::Disabled {
                continue;
            }

            let from_root = H256::from_slice(&node.values[0][1..33]);
            let to_root = H256::from_slice(&node.values[1][1..33]);

            // check proof type
            assert_eq!(
                start.proof_type as u64,
                trns.trie_modifications[lc_proofs.len()].typ as u64
            );

            let m = &trns.trie_modifications[lc_proofs.len()];

            let changes = match m.typ {
                ProofType::BalanceChanged => vec![(
                    ProofType::BalanceChanged,
                    m.address,
                    m.balance,
                    H256::zero(),
                )],
                ProofType::NonceChanged => vec![(
                    ProofType::NonceChanged,
                    m.address,
                    U256::from(m.nonce.0[0]),
                    H256::zero(),
                )],
                ProofType::StorageChanged => {
                    vec![(ProofType::StorageChanged, m.address, m.value, m.key)]
                }
                ProofType::CodeHashChanged => {
                    vec![(
                        ProofType::CodeHashChanged,
                        m.address,
                        U256::from_little_endian(&m.code_hash.0),
                        H256::zero(),
                    )]
                }
                _ => {
                    println!("type unimplemented: {:?}", m.typ);
                    unimplemented!()
                }
            };

            for (proof_type, address, value, key) in changes {
                let lc_proof = SingleTrieModification::<F> {
                    typ: F::from(proof_type as u64),
                    address: address.to_scalar().unwrap(),
                    value: Word::<F>::from(value),
                    key: Word::<F>::from(key),
                    old_root: Word::<F>::from(from_root),
                    new_root: Word::<F>::from(to_root),
                };
                lc_proofs.push(lc_proof);
            }
        }

        Ok((nodes, SingleTrieModifications(lc_proofs)))
    }
}

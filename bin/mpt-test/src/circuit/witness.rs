//! Generate witness for the StateUpdate circuit.

use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Deref,
    str::FromStr,
    time::Duration,
};

use eth_types::{Field, ToScalar};

use ethers::{
    abi::Address,
    prelude::*,
    providers::{Http, Provider},
    types::{
        transaction::eip2930::{AccessList, AccessListItem},
        BlockId, BlockNumber, H256, U256, U64,
    },
};
use eyre::Result;

use geth_utils::mpt::{ProofType, TrieModification};
use zkevm_circuits::{
    mpt_circuit::witness_row::Node, table::mpt_table::MPTProofType, util::word::WordLoHi,
};

lazy_static! {
    static ref DEFAULT_CODE_HASH: H256 =
        H256::from_str("0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
            .unwrap();
}

#[derive(Default, Clone)]
pub struct FieldTrieModification<F: Field> {
    pub typ: F,
    pub address: F,
    pub value: WordLoHi<F>,
    pub key: WordLoHi<F>,
    pub old_root: WordLoHi<F>,
    pub new_root: WordLoHi<F>,
}

#[derive(Default, Clone)]
pub struct FieldTrieModifications<F: Field>(pub Vec<FieldTrieModification<F>>);

impl<F: Field> Deref for FieldTrieModifications<F> {
    type Target = Vec<FieldTrieModification<F>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Default, Debug, Clone)]
struct Transforms {
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
    fn storage_does_not_exist(address: Address, key: H256, value: U256) -> Self;
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
    fn storage_does_not_exist(address: Address, key: H256, value: U256) -> Self {
        Self {
            typ: ProofType::StorageDoesNotExist,
            address,
            key,
            value,
            ..Default::default()
        }
    }
}

#[derive(Default)]
pub struct Witness<F: Field> {
    pub lc_witness: FieldTrieModifications<F>,
    pub mpt_witness: Vec<Node>,
}

impl<F: Field> Witness<F> {
    pub async fn build(
        provider_url: &str,
        block_no: U64,
        access_list: Option<AccessList>,
        include_unchanged: bool,
    ) -> Result<Option<Self>> {
        let provider: Provider<Http> =
            Provider::<Http>::try_from(provider_url)?.interval(Duration::from_millis(10u64));

        let transforms =
            Self::get_transforms(provider, block_no, access_list, include_unchanged).await?;

        if transforms.prev_state_root == transforms.curr_state_root {
            Ok(None)
        } else {
            let (mpt_witness, lc_witness) = Self::mpt_witness(&transforms, provider_url)?;
            Ok(Some(Self {
                mpt_witness,
                lc_witness,
            }))
        }
    }

    async fn get_transforms(
        provider: Provider<Http>,
        block_no: U64,
        access_list: Option<AccessList>,
        include_initial_values: bool,
    ) -> Result<Transforms> {
        // get previous block and this block
        let prev_block: Block<TxHash> = provider
            .get_block(BlockId::Number(BlockNumber::Number(block_no - 1)))
            .await?
            .unwrap();

        let curr_block = provider
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
            provider
                .request(
                    "eth_getAccessListByNumber",
                    vec![format!("0x{:x}", block_no)],
                )
                .await?
        };

        // sanitize access_list
        let mut access_list_map = BTreeMap::new();
        for item in access_list.0.iter_mut() {
            let entry = access_list_map
                .entry(item.address)
                .or_insert_with(BTreeSet::new);
            for key in item.storage_keys.iter() {
                entry.insert(*key);
            }
        }
        let mut access_list = AccessList(
            access_list_map
                .into_iter()
                .map(|(address, storage_keys)| AccessListItem {
                    address,
                    storage_keys: storage_keys.into_iter().collect(),
                })
                .collect(),
        );

        // add coinbase to the access list
        let mut extra_addrs = BTreeSet::from([curr_block.author.unwrap()]);
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

        let mut initial_values = Vec::new();
        let mut changed_values = Vec::new();

        // Put the read proofs first:
        if include_initial_values {
            for entry in access_list.clone().0 {
                let AccessListItem {
                    address,
                    storage_keys,
                } = entry;

                let old = provider
                    .get_proof(
                        address,
                        storage_keys.clone(),
                        Some(BlockId::Number(BlockNumber::Number(block_no - 1))),
                    )
                    .await?;

                // Skip if the account doesn't exist in the old block.
                if old.balance.is_zero()
                    && old.code_hash.is_zero()
                    && old.nonce.is_zero()
                    && old.storage_hash.is_zero()
                {
                    continue;
                }

                initial_values.push(TrieModification::balance(address, old.balance));
                initial_values.push(TrieModification::nonce(address, old.nonce));
                initial_values.push(TrieModification::codehash(address, old.code_hash));

                for key in storage_keys.iter() {
                    let old = old.storage_proof.iter().find(|p| p.key == *key).unwrap();
                    if old.value == U256::zero() {
                        initial_values.push(TrieModification::storage_does_not_exist(
                            address, *key, old.value,
                        ));
                    } else {
                        initial_values.push(TrieModification::storage(address, *key, old.value));
                    }
                }
            }
        }

        for entry in access_list.0 {
            let AccessListItem {
                address,
                storage_keys,
            } = entry;

            let old = provider
                .get_proof(
                    address,
                    storage_keys.clone(),
                    Some(BlockId::Number(BlockNumber::Number(block_no - 1))),
                )
                .await?;

            let new = provider
                .get_proof(
                    address,
                    storage_keys.clone(),
                    Some(BlockId::Number(BlockNumber::Number(block_no))),
                )
                .await?;

            // if nothing changed, append all values
            if old.balance == new.balance
                && old.nonce == new.nonce
                && old.code_hash == new.code_hash
                && old.storage_hash == new.storage_hash
                && !include_initial_values
            {
                continue;
            }

            // check for this address changes
            if old.nonce != new.nonce {
                changed_values.push(TrieModification::nonce(address, new.nonce));
            }
            if old.balance != new.balance {
                changed_values.push(TrieModification::balance(address, new.balance));
            }

            if old.code_hash != new.code_hash && new.code_hash != *DEFAULT_CODE_HASH {
                changed_values.push(TrieModification::codehash(address, new.code_hash));
            }

            for key in storage_keys {
                let new = new.storage_proof.iter().find(|p| p.key == key).unwrap();
                let old = old.storage_proof.iter().find(|p| p.key == key).unwrap();
                if !(old.value == U256::zero() && new.value == U256::zero()) {
                    changed_values.push(TrieModification::storage(address, key, new.value));
                }
            }
        }

        println!("initial_values.len(): {}", initial_values.len());
        println!("changed_values.len(): {}", changed_values.len());

        let mut trie_modifications = initial_values;
        trie_modifications.append(&mut changed_values);

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
    ) -> Result<(Vec<Node>, FieldTrieModifications<F>)> {
        let json = geth_utils::get_witness(
            trns.block_no.as_u64() - 1,
            &trns.trie_modifications,
            provider,
        );
        let nodes = zkevm_circuits::mpt_circuit::load_proof(json.as_bytes())?;

        let witness_previous_state_root = H256::from_slice(&nodes[0].values[0][1..33]);
        let non_disabled_node = |n: &&Node| {
            n.start
                .as_ref()
                .map_or(false, |v| v.proof_type != MPTProofType::Disabled)
        };
        let witness_current_state_root =
            H256::from_slice(&nodes.iter().rev().find(non_disabled_node).unwrap().values[1][1..33]);

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
                ProofType::BalanceChanged => (
                    ProofType::BalanceChanged,
                    m.address,
                    m.balance,
                    H256::zero(),
                ),
                ProofType::NonceChanged => (
                    ProofType::NonceChanged,
                    m.address,
                    U256::from(m.nonce.0[0]),
                    H256::zero(),
                ),
                ProofType::StorageChanged => (ProofType::StorageChanged, m.address, m.value, m.key),
                ProofType::CodeHashChanged => (
                    ProofType::CodeHashChanged,
                    m.address,
                    U256::from_big_endian(&m.code_hash.0),
                    H256::zero(),
                ),
                ProofType::StorageDoesNotExist => {
                    (ProofType::StorageDoesNotExist, m.address, m.value, m.key)
                }
                _ => {
                    println!("type unimplemented: {:?}", m.typ);
                    unimplemented!()
                }
            };

            let (proof_type, address, value, key) = changes;

            let lc_proof = FieldTrieModification::<F> {
                typ: F::from(proof_type as u64),
                address: address.to_scalar().unwrap(),
                value: WordLoHi::<F>::from(value),
                key: WordLoHi::<F>::from(key),
                old_root: WordLoHi::<F>::from(from_root),
                new_root: WordLoHi::<F>::from(to_root),
            };
            lc_proofs.push(lc_proof);
        }

        Ok((nodes, FieldTrieModifications(lc_proofs)))
    }
}

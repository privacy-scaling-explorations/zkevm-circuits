use std::{collections::HashSet, sync::Arc};

use ethers::{
    abi::Address,
    prelude::{k256::ecdsa::SigningKey, SignerMiddleware},
    providers::{Http, Provider},
    signers::Wallet,
    types::{
        transaction::eip2930::{AccessList, AccessListItem},
        BlockId, BlockNumber, EIP1186ProofResponse, H256, U256, U64,
    },
};
use ethers::prelude::*;
use eyre::Result;
use eth_types::{Field, ToScalar};

use mpt_witness_generator::ProofType;
use zkevm_circuits::{mpt_circuit::witness_row::Node, table::mpt_table::MPTProofType, util::word::{Word, self}};

#[derive(Default, Debug, Clone)]
pub struct Transform {
    pub typ: ProofType,
    pub key: H256,
    pub value: U256,
    pub address: Address,
    pub nonce: U64,
    pub balance: U256,
    pub code_hash: H256,
}

#[derive(Default, Debug, Clone)]
pub struct Transforms {
    pub block_no: U64,
    pub prev_state_root: H256,
    pub curr_state_root: H256,
    pub mods: Vec<Transform>,
}

impl Transform {
    fn create(proof: &EIP1186ProofResponse) -> Self {
        Self {
            typ: ProofType::AccountCreate,
            key: H256::zero(),
            value: U256::zero(),
            address: proof.address,
            nonce: proof.nonce,
            balance: proof.balance,
            code_hash: proof.code_hash,
        }
    }
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
    fn storage_changed(address: Address, key: H256, value: U256) -> Self {
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
pub struct LightClientWitness<F: Field>(pub Vec<LightClientProof<F>>);

#[derive(Default, Clone)]
pub struct LightClientProof<F : Field> {
    pub typ: F,
    pub address: F,
    pub value: word::Word<F>,
    pub key: word::Word<F>,
    pub old_root: word::Word<F>,
    pub new_root: word::Word<F>,
}

impl<F: Field> LightClientWitness<F> {
    pub fn public_inputs(&self) -> Vec<F> {
        let mut inputs = Vec::new();
            inputs.push(self.0[0].old_root.lo());
            inputs.push(self.0[0].old_root.hi());
            inputs.push(self.0[self.0.len()-1].new_root.lo());
            inputs.push(self.0[self.0.len()-1].new_root.hi());


        inputs.push(F::from(self.0.len() as u64));

        for proof in &self.0 {
            inputs.push(proof.typ);
            inputs.push(proof.address);
            inputs.push(proof.value.lo());
            inputs.push(proof.value.hi());
            inputs.push(proof.key.lo());
            inputs.push(proof.key.hi());
        }

        inputs

    }
}

impl Transforms {
    pub(crate) async fn new(
        client: Arc<SignerMiddleware<Provider<Http>, Wallet<SigningKey>>>,
        block_no: U64,
        access_list : Option<AccessList>,
    ) -> Result<Transforms> {
        let mut mods = Vec::new();

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
            .request("eth_getAccessListByNumber", vec![format!("0x{:x}", block_no)])
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
            if (old.balance.is_zero() && !new.balance.is_zero())
                || (old.nonce.is_zero() && !new.nonce.is_zero())
            {
                mods.push(Transform::create(&new));
            } else {
                if old.balance != new.balance {
                    mods.push(Transform::balance(address, new.balance));
                }
                if old.nonce != new.nonce {
                    mods.push(Transform::nonce(address, new.nonce));
                }
            }

            for key in storage_keys {
                let new = new.storage_proof.iter().find(|p| p.key == key).unwrap();
                mods.push(Transform::storage_changed(address, key, new.value));
            }
        }

        Ok(Transforms {
            block_no,
            curr_state_root: curr_block.state_root,
            prev_state_root: prev_block.state_root,
            mods,
        })
    }

    pub fn mpt_witness<F: Field>(&self, provider: &str) -> Result<(Vec<Node>, LightClientWitness<F>)> {
        let mods: Vec<_> = self
            .mods
            .iter()
            .map(|m| mpt_witness_generator::TrieModification {
                typ: m.typ,
                key: m.key,
                value: {
                    let mut bytes = [0u8; 32];
                    m.value.to_little_endian(&mut bytes);
                    U256::from_little_endian(&bytes)
                },
                address: m.address,
                nonce: m.nonce,
                balance: m.balance,
                code_hash: m.code_hash,
            })
            .collect();

        let nodes = mpt_witness_generator::get_witness(self.block_no.as_u64() - 1, &mods, provider);

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
            witness_previous_state_root, self.prev_state_root,
            "previous state root does not match"
        );
        assert_eq!(
            witness_current_state_root, self.curr_state_root,
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

            // check if the roots matches
            if lc_proofs.len() == 0 {
                assert_eq!(from_root, self.prev_state_root);
            }
            if lc_proofs.len() == self.mods.len() {
                assert_eq!(to_root, self.curr_state_root);
            }

            // check proof type
            assert_eq!(
                start.proof_type as u64,
                self.mods[lc_proofs.len()].typ as u64
            );

            let m = &self.mods[lc_proofs.len()];

            let changes = match m.typ {
                ProofType::BalanceChanged => vec![(ProofType::BalanceChanged, m.address, m.balance, H256::zero())],
                ProofType::NonceChanged => vec![(ProofType::NonceChanged, m.address, U256::from(m.nonce.0[0]), H256::zero())],
                ProofType::StorageChanged => vec![(ProofType::StorageChanged, m.address, m.value, m.key)],
                 _ => unimplemented!()
            };

            for (proof_type, address,value, key) in changes {
            let lc_proof = LightClientProof::<F> {
                typ: F::from(start.proof_type as u64),
                address: address.to_scalar().unwrap(),
                value: Word::<F>::from(value),
                key: Word::<F>::from(key),
                old_root: Word::<F>::from(from_root),
                new_root: Word::<F>::from(to_root),
            };
            lc_proofs.push(lc_proof);
        }


        }



        Ok((nodes, LightClientWitness(lc_proofs)))
    }

}

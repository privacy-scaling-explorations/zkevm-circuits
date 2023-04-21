use eth_types::Field;
use num_enum::TryFromPrimitive;
use std::{convert::TryFrom, marker::PhantomData};

use crate::mpt_circuit::param::{
    ARITY, BRANCH_0_KEY_POS, DRIFTED_POS, IS_ACCOUNT_DELETE_MOD_POS, IS_BALANCE_MOD_POS,
    IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, IS_CODEHASH_MOD_POS,
    IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
    IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, IS_NONCE_MOD_POS,
    IS_NON_EXISTING_ACCOUNT_POS, IS_STORAGE_MOD_POS, RLP_LIST_LONG, RLP_LIST_SHORT,
};
use crate::{
    mpt_circuit::param::{
        COUNTER_WITNESS_LEN, HASH_WIDTH, IS_NON_EXISTING_STORAGE_POS, NOT_FIRST_LEVEL_POS,
    },
    table::ProofType,
};

use super::helpers::Indexable;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum StorageRowType {
    KeyS,
    ValueS,
    KeyC,
    ValueC,
    Drifted,
    Wrong,
    Count,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum AccountRowType {
    KeyS,
    KeyC,
    NonceS,
    BalanceS,
    StorageS,
    CodehashS,
    NonceC,
    BalanceC,
    StorageC,
    CodehashC,
    Drifted,
    Wrong,
    Count,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum ExtensionBranchRowType {
    Mod,
    Child0,
    Child1,
    Child2,
    Child3,
    Child4,
    Child5,
    Child6,
    Child7,
    Child8,
    Child9,
    Child10,
    Child11,
    Child12,
    Child13,
    Child14,
    Child15,
    KeyS,
    ValueS,
    KeyC,
    ValueC,
    Count,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum StartRowType {
    RootS,
    RootC,
    Count,
}

/// MPT branch node
#[derive(Clone, Debug)]
pub struct BranchNode {
    pub(crate) modified_index: usize,
    pub(crate) drifted_index: usize,
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
}

/// MPT extension node
#[derive(Clone, Debug)]
pub struct ExtensionNode {
    pub(crate) list_rlp_bytes: Vec<u8>,
}

/// MPT start node
#[derive(Clone, Debug)]
pub struct StartNode {
    pub(crate) proof_type: ProofType,
}

/// MPT extension branch node
#[derive(Clone, Debug)]
pub struct ExtensionBranchNode {
    pub(crate) is_extension: bool,
    pub(crate) is_placeholder: [bool; 2],
    pub(crate) extension: ExtensionNode,
    pub(crate) branch: BranchNode,
}

/// MPT account node
#[derive(Clone, Debug)]
pub struct AccountNode {
    pub(crate) address: Vec<u8>,
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) drifted_rlp_bytes: Vec<u8>,
    pub(crate) wrong_rlp_bytes: Vec<u8>,
}

/// MPT storage node
#[derive(Clone, Debug)]
pub struct StorageNode {
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_rlp_bytes: [Vec<u8>; 2],
    pub(crate) drifted_rlp_bytes: Vec<u8>,
    pub(crate) wrong_rlp_bytes: Vec<u8>,
}

/// MPT node
#[derive(Clone, Debug, Default)]
pub struct Node {
    pub(crate) start: Option<StartNode>,
    pub(crate) extension_branch: Option<ExtensionBranchNode>,
    pub(crate) account: Option<AccountNode>,
    pub(crate) storage: Option<StorageNode>,
    /// MPT node values
    pub values: Vec<Vec<u8>>,
}

#[derive(Debug, Eq, PartialEq, TryFromPrimitive)]
#[repr(u8)]
pub(crate) enum MptWitnessRowType {
    InitBranch = 0,
    BranchChild = 1,
    StorageLeafSKey = 2,
    StorageLeafCKey = 3,
    HashToBeComputed = 5,
    AccountLeafKeyS = 6,
    AccountLeafKeyC = 4,
    AccountLeafNonceBalanceS = 7,
    AccountLeafNonceBalanceC = 8,
    AccountLeafRootCodehashS = 9,
    AccountLeafNeighbouringLeaf = 10,
    AccountLeafRootCodehashC = 11,
    StorageLeafSValue = 13,
    StorageLeafCValue = 14,
    NeighbouringStorageLeaf = 15,
    ExtensionNodeS = 16,
    ExtensionNodeC = 17,
    AccountNonExisting = 18,
    StorageNonExisting = 19,
}

/// MPT witness row
#[derive(Clone, Debug)]
pub struct MptWitnessRow<F> {
    pub(crate) bytes: Vec<u8>,
    pub(crate) rlp_bytes: Vec<u8>,
    pub(crate) is_extension: bool,
    pub(crate) is_placeholder: [bool; 2],
    pub(crate) modified_index: usize,
    pub(crate) drifted_index: usize,
    pub(crate) proof_type: ProofType,
    pub(crate) address: Vec<u8>,
    _marker: PhantomData<F>,
}

impl<F: Field> MptWitnessRow<F> {
    /// New MPT witness row
    pub fn new(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            rlp_bytes: Vec::new(),
            is_extension: false,
            is_placeholder: [false; 2],
            modified_index: 0,
            drifted_index: 0,
            proof_type: ProofType::Disabled,
            address: Vec::new(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn s(&self) -> Vec<u8> {
        self.bytes[0..34].to_owned()
    }

    pub(crate) fn c(&self) -> Vec<u8> {
        self.bytes[34..68].to_owned()
    }

    pub(crate) fn get_type(&self) -> MptWitnessRowType {
        MptWitnessRowType::try_from(self.get_byte_rev(1)).unwrap()
    }

    pub(crate) fn get_byte_rev(&self, rev_index: usize) -> u8 {
        self.bytes[self.len() - rev_index]
    }

    pub(crate) fn get_byte(&self, index: usize) -> u8 {
        self.bytes[index]
    }

    pub(crate) fn len(&self) -> usize {
        self.bytes.len()
    }

    pub(crate) fn not_first_level(&self) -> u8 {
        self.get_byte_rev(NOT_FIRST_LEVEL_POS)
    }

    pub(crate) fn s_root_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 4 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 4 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
    }

    pub(crate) fn c_root_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 3 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 3 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
    }

    pub(crate) fn address_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 2 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 2 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
    }

    pub(crate) fn main(&self) -> &[u8] {
        &self.bytes[0..self.bytes.len() - 1]
    }
}

// TODO(Brecht): Do all of this on the MPT proof generation side
/// MPT prepare witness
pub fn prepare_witness<F: Field>(witness: &mut [MptWitnessRow<F>]) -> Vec<Node> {
    for (_, row) in witness
        .iter_mut()
        .filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed)
        .enumerate()
    {
        // Get the proof type directly
        if row.get_byte_rev(IS_STORAGE_MOD_POS) == 1 {
            row.proof_type = ProofType::StorageChanged;
        }
        if row.get_byte_rev(IS_NONCE_MOD_POS) == 1 {
            row.proof_type = ProofType::NonceChanged;
        }
        if row.get_byte_rev(IS_BALANCE_MOD_POS) == 1 {
            row.proof_type = ProofType::BalanceChanged;
        }
        if row.get_byte_rev(IS_CODEHASH_MOD_POS) == 1 {
            row.proof_type = ProofType::CodeHashExists;
        }
        if row.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) == 1 {
            row.proof_type = ProofType::AccountDestructed;
        }
        if row.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) == 1 {
            row.proof_type = ProofType::AccountDoesNotExist;
        }
        if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1 {
            row.proof_type = ProofType::StorageDoesNotExist;
        }

        // Separate the list rlp bytes from the key bytes
        if row.get_type() == MptWitnessRowType::StorageLeafSKey
            || row.get_type() == MptWitnessRowType::StorageLeafCKey
            || row.get_type() == MptWitnessRowType::StorageNonExisting
            || row.get_type() == MptWitnessRowType::NeighbouringStorageLeaf
            || row.get_type() == MptWitnessRowType::AccountLeafKeyS
            || row.get_type() == MptWitnessRowType::AccountLeafKeyC
            || row.get_type() == MptWitnessRowType::AccountNonExisting
            || row.get_type() == MptWitnessRowType::AccountLeafNeighbouringLeaf
            || row.get_type() == MptWitnessRowType::ExtensionNodeS
        {
            let len = if row.get_type() == MptWitnessRowType::ExtensionNodeS {
                34
            } else {
                36
            };
            let mut key_bytes = row.bytes[0..len].to_owned();
            
            const RLP_LIST_LONG_1: u8 = RLP_LIST_LONG + 1;
            const RLP_LIST_LONG_2: u8 = RLP_LIST_LONG + 2;
            let mut is_short = false;
            let mut is_long = false;
            let mut is_very_long = false;
            let mut is_string = false;
            match key_bytes[0] {
                RLP_LIST_SHORT..=RLP_LIST_LONG => is_short = true,
                RLP_LIST_LONG_1 => is_long = true,
                RLP_LIST_LONG_2 => is_very_long = true,
                _ => is_string = true,
            }

            let num_rlp_bytes = if is_short {
                1
            } else if is_long {
                2
            } else if is_very_long {
                3
            } else {
                if row.get_type() == MptWitnessRowType::ExtensionNodeS {
                    0
                } else if is_string {
                    unreachable!()
                } else {
                    unreachable!()
                }
            };

            //println!("bytes: {:?}", key_bytes);
            row.rlp_bytes = key_bytes[..num_rlp_bytes].to_vec();
            for byte in key_bytes[..num_rlp_bytes].iter_mut() {
                *byte = 0;
            }
            key_bytes.rotate_left(num_rlp_bytes);
            row.bytes = [key_bytes.clone(), row.bytes[len..].to_owned()].concat();

            //println!("list : {:?}", row.rlp_bytes);
            //println!("key  : {:?}", row.bytes);
        }

        // Separate the RLP bytes and shift the value bytes to the start of the row
        if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS
            || row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceC
        {
            row.rlp_bytes = [row.bytes[..2].to_owned(), row.bytes[34..36].to_owned()].concat();

            let nonce = row.bytes[2..34].to_owned();
            let balance = row.bytes[36..68].to_owned();

            row.bytes = [
                nonce,
                vec![0; 2],
                balance,
                vec![0; 2],
                row.bytes[68..].to_owned(),
            ]
            .concat();
        }

        if row.get_type() == MptWitnessRowType::InitBranch {
            // Extract the RLP bytes
            row.rlp_bytes = [row.bytes[4..7].to_owned(), row.bytes[7..10].to_owned()].concat();

            // Store a single value that the branch is an extension node or not
            row.is_extension = row.get_byte(IS_EXT_LONG_ODD_C16_POS)
                + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
                + row.get_byte(IS_EXT_SHORT_C16_POS)
                + row.get_byte(IS_EXT_SHORT_C1_POS)
                + row.get_byte(IS_EXT_LONG_EVEN_C16_POS)
                + row.get_byte(IS_EXT_LONG_EVEN_C1_POS)
                == 1;
            row.is_placeholder = [
                row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 1,
                row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 1,
            ];
            row.modified_index = row.get_byte(BRANCH_0_KEY_POS) as usize;
            row.drifted_index = row.get_byte(DRIFTED_POS) as usize;
            // Move the modified branch into the init row
            row.bytes = [vec![0; 68], row.bytes[68..].to_owned()].concat();
        }

        // Shift the value bytes to the start of the row
        if row.get_type() == MptWitnessRowType::StorageLeafSValue
            || row.get_type() == MptWitnessRowType::StorageLeafCValue
        {
            row.rlp_bytes = vec![row.bytes[0]];
            row.bytes = [row.bytes[1..].to_owned()].concat();
        }
    }

    let cached_witness = witness.to_owned();
    for (idx, row) in witness
        .iter_mut()
        .filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed)
        .enumerate()
    {
        if row.get_type() == MptWitnessRowType::InitBranch {
            // Move the modified branch into the init row
            let mod_bytes = cached_witness[idx + 1 + row.modified_index].c();
            row.bytes = [mod_bytes, row.bytes[34..].to_owned()].concat();
        }
    }

    let mut nodes = Vec::new();
    let witness = witness
        .iter()
        .filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed)
        .collect::<Vec<_>>();
    let mut offset = 0;
    while offset < witness.len() {
        //println!("offset: {}", offset);
        let mut new_proof = offset == 0;
        if offset > 0 {
            let row_prev = witness[offset - 1].clone();
            let not_first_level_prev = row_prev.not_first_level();
            let not_first_level_cur = witness[offset].not_first_level();
            if not_first_level_cur == 0 && not_first_level_prev == 1 {
                new_proof = true;
            }
        }

        if new_proof {
            let mut new_row = witness[offset].clone();
            new_row.bytes = [
                vec![160; 1],
                new_row.s_root_bytes().to_owned(),
                vec![0; 1],
                vec![160; 1],
                new_row.c_root_bytes().to_owned(),
                vec![0; 1],
            ]
            .concat();

            let mut node_rows = vec![Vec::new(); StartRowType::Count as usize];
            node_rows[StartRowType::RootS as usize] = new_row.s();
            node_rows[StartRowType::RootC as usize] = new_row.c();

            let start_node = StartNode {
                proof_type: new_row.proof_type.clone(),
            };
            let mut node = Node::default();
            node.start = Some(start_node);
            node.values = node_rows;
            nodes.push(node);
        }

        if witness[offset].get_type() == MptWitnessRowType::InitBranch {
            let row_init = witness[offset].to_owned();
            let is_placeholder = row_init.is_placeholder.clone();
            let is_extension = row_init.is_extension;
            let modified_index = row_init.modified_index;
            let mut drifted_index = row_init.drifted_index;
            // If no placeholder branch, we set `drifted_pos = modified_node`. This
            // is needed just to make some other constraints (`s_mod_node_hash_rlc`
            // and `c_mod_node_hash_rlc` correspond to the proper node) easier to write.
            if !is_placeholder[true.idx()] && !is_placeholder[false.idx()] {
                drifted_index = modified_index;
            }
            let branch_list_rlp_bytes = [
                row_init.rlp_bytes[0..3].to_owned(),
                row_init.rlp_bytes[3..6].to_owned(),
            ];
            let child_bytes: [Vec<u8>; ARITY + 1] =
                array_init::array_init(|i| witness[offset + i].s());
            let ext_list_rlp_bytes = witness[offset + 17].rlp_bytes.to_owned();

            let mut node_rows = vec![Vec::new(); ExtensionBranchRowType::Count as usize];
            for idx in 0..ARITY + 1 {
                node_rows[idx] = child_bytes[idx].clone();
            }
            node_rows[ExtensionBranchRowType::KeyS as usize] = witness[offset + 17].s();
            node_rows[ExtensionBranchRowType::ValueS as usize] = witness[offset + 17].c();
            node_rows[ExtensionBranchRowType::KeyC as usize] = witness[offset + 18].s();
            node_rows[ExtensionBranchRowType::ValueC as usize] = witness[offset + 18].c();
            offset += 19;

            let extension_branch_node = ExtensionBranchNode {
                is_extension,
                is_placeholder,
                extension: ExtensionNode {
                    list_rlp_bytes: ext_list_rlp_bytes,
                },
                branch: BranchNode {
                    modified_index,
                    drifted_index,
                    list_rlp_bytes: branch_list_rlp_bytes,
                },
            };
            let mut node = Node::default();
            node.extension_branch = Some(extension_branch_node);
            node.values = node_rows;
            nodes.push(node);
        } else if witness[offset].get_type() == MptWitnessRowType::StorageLeafSKey {
            let row_key = [&witness[offset + 0], &witness[offset + 2]];
            let row_value = [&witness[offset + 1], &witness[offset + 3]];
            let row_drifted = &witness[offset + 4];
            let row_wrong = &witness[offset + 5];
            offset += 6;

            let list_rlp_bytes = [
                row_key[true.idx()].rlp_bytes.to_owned(),
                row_key[false.idx()].rlp_bytes.to_owned(),
            ];
            let value_rlp_bytes = [
                row_value[true.idx()].rlp_bytes.to_owned(),
                row_value[false.idx()].rlp_bytes.to_owned(),
            ];
            let drifted_rlp_bytes = row_drifted.rlp_bytes.clone();
            let wrong_rlp_bytes = row_wrong.rlp_bytes.clone();

            let mut node_rows = vec![Vec::new(); StorageRowType::Count as usize];
            node_rows[StorageRowType::KeyS as usize] = row_key[true.idx()].s();
            node_rows[StorageRowType::ValueS as usize] = row_value[true.idx()].s();
            node_rows[StorageRowType::KeyC as usize] = row_key[false.idx()].s();
            node_rows[StorageRowType::ValueC as usize] = row_value[false.idx()].s();
            node_rows[StorageRowType::Drifted as usize] = row_drifted.s();
            node_rows[StorageRowType::Wrong as usize] = row_wrong.s();

            let storage_node = StorageNode {
                list_rlp_bytes,
                value_rlp_bytes,
                drifted_rlp_bytes,
                wrong_rlp_bytes,
            };
            let mut node = Node::default();
            node.storage = Some(storage_node);
            node.values = node_rows;
            nodes.push(node);
        } else if witness[offset].get_type() == MptWitnessRowType::AccountLeafKeyS {
            let key_s = witness[offset].to_owned();
            let key_c = witness[offset + 1].to_owned();
            let nonce_balance_s = witness[offset + 3].to_owned();
            let nonce_balance_c = witness[offset + 4].to_owned();
            let storage_codehash_s = witness[offset + 5].to_owned();
            let storage_codehash_c = witness[offset + 6].to_owned();
            let row_drifted = witness[offset + 7].to_owned();
            let row_wrong = witness[offset + 2].to_owned();
            let address = witness[offset].address_bytes().to_owned();
            offset += 8;

            let list_rlp_bytes = [key_s.rlp_bytes.to_owned(), key_c.rlp_bytes.to_owned()];
            let value_rlp_bytes = [
                nonce_balance_s.rlp_bytes[..2].to_owned(),
                nonce_balance_c.rlp_bytes[..2].to_owned(),
            ];
            let value_list_rlp_bytes = [
                nonce_balance_s.rlp_bytes[2..].to_owned(),
                nonce_balance_c.rlp_bytes[2..].to_owned(),
            ];
            let drifted_rlp_bytes = row_drifted.rlp_bytes.clone();
            let wrong_rlp_bytes = row_wrong.rlp_bytes.clone();

            let mut node_rows = vec![Vec::new(); AccountRowType::Count as usize];
            node_rows[AccountRowType::KeyS as usize] = key_s.s();
            node_rows[AccountRowType::KeyC as usize] = key_c.s();
            node_rows[AccountRowType::NonceS as usize] = nonce_balance_s.s();
            node_rows[AccountRowType::BalanceS as usize] = nonce_balance_s.c();
            node_rows[AccountRowType::StorageS as usize] = storage_codehash_s.s();
            node_rows[AccountRowType::CodehashS as usize] = storage_codehash_s.c();
            node_rows[AccountRowType::NonceC as usize] = nonce_balance_c.s();
            node_rows[AccountRowType::BalanceC as usize] = nonce_balance_c.c();
            node_rows[AccountRowType::StorageC as usize] = storage_codehash_c.s();
            node_rows[AccountRowType::CodehashC as usize] = storage_codehash_c.c();
            node_rows[AccountRowType::Drifted as usize] = row_drifted.s();
            node_rows[AccountRowType::Wrong as usize] = row_wrong.s();

            let account_node = AccountNode {
                address,
                list_rlp_bytes,
                value_rlp_bytes,
                value_list_rlp_bytes,
                drifted_rlp_bytes,
                wrong_rlp_bytes,
            };
            let mut node = Node::default();
            node.account = Some(account_node);
            node.values = node_rows;
            nodes.push(node);
        }
    }

    // Dummy end state
    let start_node = StartNode {
        proof_type: ProofType::Disabled,
    };
    let mut node = Node::default();
    node.start = Some(start_node);
    node.values = vec![vec![0; 34]; StartRowType::Count as usize];
    nodes.push(node);

    nodes
}

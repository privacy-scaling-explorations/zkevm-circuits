//! The MPT circuit implementation.
use eth_types::Field;
use gadgets::{impl_expr, util::Scalar};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use std::{convert::TryInto, env::var};

mod account_leaf;
mod branch;
mod columns;
mod extension;
mod extension_branch;
mod helpers;
mod param;
mod rlp_gadgets;
mod selectors;
mod start;
mod storage_leaf;
mod witness_row;

use columns::MainCols;
use extension_branch::ExtensionBranchConfig;
use witness_row::{MptWitnessRow, MptWitnessRowType};

use param::HASH_WIDTH;

use self::{
    account_leaf::AccountLeafConfig,
    helpers::key_memory,
    param::{
        ARITY, BRANCH_0_KEY_POS, DRIFTED_POS, IS_ACCOUNT_DELETE_MOD_POS, IS_BALANCE_MOD_POS,
        IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, IS_CODEHASH_MOD_POS,
        IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
        IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, IS_NONCE_MOD_POS,
        IS_NON_EXISTING_ACCOUNT_POS, IS_NON_EXISTING_STORAGE_POS, IS_STORAGE_MOD_POS,
        RLP_LIST_LONG, RLP_LIST_SHORT,
    },
    witness_row::{
        AccountNode, AccountRowType, BranchNode, ExtensionBranchNode, ExtensionBranchRowType,
        ExtensionNode, Node, StartNode, StartRowType, StorageNode, StorageRowType,
    },
};
use crate::mpt_circuit::helpers::Indexable;
use crate::{
    assign, assignf, circuit,
    circuit_tools::{cell_manager::CellManager, constraint_builder::merge_lookups, memory::Memory},
    matchr, matchw,
    mpt_circuit::{
        helpers::{extend_rand, main_memory, parent_memory, MPTConstraintBuilder},
        start::StartConfig,
        storage_leaf::StorageLeafConfig,
    },
    table::{DynamicTableColumns, KeccakTable, MptTable, ProofType},
    util::{power_of_randomness_from_instance, Challenges},
};

/// State machine config.
#[derive(Clone, Debug, Default)]
pub struct StateMachineConfig<F> {
    start_config: StartConfig<F>,
    branch_config: ExtensionBranchConfig<F>,
    storage_config: StorageLeafConfig<F>,
    account_config: AccountLeafConfig<F>,
}

/// Merkle Patricia Trie context
#[derive(Clone, Debug)]
pub struct MPTContext<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>,
    pub(crate) mpt_table: MptTable,
    pub(crate) main: MainCols<F>,
    pub(crate) managed_columns: Vec<Column<Advice>>,
    pub(crate) r: Vec<Expression<F>>,
    pub(crate) memory: Memory<F>,
}

impl<F: Field> MPTContext<F> {
    pub(crate) fn bytes(&self) -> Vec<Column<Advice>> {
        self.main.bytes.to_vec()
    }

    pub(crate) fn s(&self, meta: &mut VirtualCells<F>, rot: i32) -> Vec<Expression<F>> {
        self.bytes()[0..34]
            .iter()
            .map(|&byte| meta.query_advice(byte, Rotation(rot)))
            .collect::<Vec<_>>()
    }
}

/// Merkle Patricia Trie config.
#[derive(Clone)]
pub struct MPTConfig<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>,
    pub(crate) main: MainCols<F>,
    pub(crate) managed_columns: Vec<Column<Advice>>,
    pub(crate) memory: Memory<F>,
    keccak_table: KeccakTable,
    fixed_table: [Column<Fixed>; 3],
    state_machine: StateMachineConfig<F>,
    pub(crate) is_start: Column<Advice>,
    pub(crate) is_branch: Column<Advice>,
    pub(crate) is_account: Column<Advice>,
    pub(crate) is_storage: Column<Advice>,
    pub(crate) r: F,
    pub(crate) mpt_table: MptTable,
    cb: MPTConstraintBuilder<F>,
}

/// Enumerator to determine the type of row in the fixed table.
#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    /// All zero lookup data
    Disabled,
    /// Power of randomness: [1, r], [2, r^2],...
    RMult,
    /// 0 - 15
    Range16,
    /// 0 - 255
    Range256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen16,
}

impl_expr!(FixedTableTag);

#[derive(Default)]
pub(crate) struct MPTState<F> {
    pub(crate) memory: Memory<F>,
}

impl<F: Field> MPTState<F> {
    fn new(memory: &Memory<F>) -> Self {
        Self {
            memory: memory.clone(),
            ..Default::default()
        }
    }
}

impl<F: Field> MPTConfig<F> {
    /// Configure MPT Circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        keccak_table: KeccakTable,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_not_first = meta.fixed_column();

        let mpt_table = MptTable::construct(meta);

        let is_start = meta.advice_column();
        let is_branch = meta.advice_column();
        let is_account = meta.advice_column();
        let is_storage = meta.advice_column();

        let main = MainCols::new(meta);

        let fixed_table: [Column<Fixed>; 3] = (0..3)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let managed_columns = (0..20).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let memory_columns = (0..5).map(|_| meta.advice_column()).collect::<Vec<_>>();

        let mut memory = Memory::new(memory_columns);
        memory.allocate(meta, key_memory(false));
        memory.allocate(meta, key_memory(true));
        memory.allocate(meta, parent_memory(false));
        memory.allocate(meta, parent_memory(true));
        memory.allocate(meta, main_memory());

        let ctx = MPTContext {
            q_enable: q_enable.clone(),
            q_not_first: q_not_first.clone(),
            mpt_table: mpt_table.clone(),
            main: main.clone(),
            managed_columns: managed_columns.clone(),
            r: extend_rand(&power_of_randomness),
            memory: memory.clone(),
        };

        let mut state_machine = StateMachineConfig::default();

        let mut cb = MPTConstraintBuilder::new(33 + 10, None);
        meta.create_gate("MPT", |meta| {
            let cell_manager = CellManager::new(meta, &ctx.managed_columns);
            cb.base.set_cell_manager(cell_manager);

            circuit!([meta, cb.base], {
                // State machine
                // TODO(Brecht): state machine constraints
                ifx!{f!(q_enable) => {
                    // Always start with the start state
                    ifx! {not!(f!(q_not_first)) => {
                        require!(a!(is_start) => true);
                    }};
                    // Main state machine
                    matchx! {
                        a!(is_start) => {
                            state_machine.start_config = StartConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(is_branch) => {
                            state_machine.branch_config = ExtensionBranchConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(is_account) => {
                            state_machine.account_config = AccountLeafConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(is_storage) => {
                            state_machine.storage_config = StorageLeafConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        _ => (),
                    };
                    // Only account and storage rows can have lookups, disable lookups on all other rows
                    matchx! {
                        a!(is_account) => (),
                        a!(is_storage) => (),
                        _ => require!(a!(ctx.mpt_table.proof_type) => ProofType::Disabled.expr()),
                    }
                }}

                // TODO(Brecht): decode 1 RLP item/row
                /* Range checks */
                // These range checks ensure that the value in the RLP columns are all byte value.
                // These lookups also enforce the byte value to be zero the byte index >= length.
                // TODO(Brecht): do 2 bytes/lookup when circuit height >= 2**21
                /*ifx!{f!(position_cols.q_enable) => {
                    // Sanity checks (can be removed, here for safety)
                    require!(cb.length_s.sum_conditions() => bool);
                    // Range checks
                    for (idx, &byte) in ctx.s().into_iter().enumerate() {
                        require!((cb.get_range_s(), a!(byte), cb.get_length_s() - (idx + 1).expr()) => @"fixed");
                    }
                }}*/

                /* Populate lookup tables */
                require!(@"keccak" => keccak_table.columns().iter().map(|table| a!(table)).collect());
                require!(@"fixed" => fixed_table.iter().map(|table| f!(table)).collect());

                /* Memory banks */
                ifx!{f!(q_enable) => {
                    ctx.memory.generate_constraints(&mut cb.base, not!(f!(q_not_first)));
                }}
            });

            cb.base.generate_constraints()
        });

        let disable_lookups: usize = var("DISABLE_LOOKUPS")
            .unwrap_or_else(|_| "0".to_string())
            .parse()
            .expect("Cannot parse DISABLE_LOOKUPS env var as usize");
        if disable_lookups == 0 {
            cb.base.generate_lookups(
                meta,
                &[
                    vec!["fixed".to_string(), "keccak".to_string()],
                    ctx.memory.tags(),
                ]
                .concat(),
            );
        } else if disable_lookups == 1 {
            cb.base.generate_lookups(
                meta,
                &[vec!["keccak".to_string()], ctx.memory.tags()].concat(),
            );
        } else if disable_lookups == 2 {
            cb.base.generate_lookups(meta, &ctx.memory.tags());
        } else if disable_lookups == 3 {
            cb.base
                .generate_lookups(meta, &vec!["fixed".to_string(), "keccak".to_string()]);
        } else if disable_lookups == 4 {
            cb.base.generate_lookups(meta, &vec!["keccak".to_string()]);
        }

        println!("num lookups: {}", meta.lookups().len());
        println!("num advices: {}", meta.num_advice_columns());
        println!("num fixed: {}", meta.num_fixed_columns());
        //cb.base.print_stats();

        MPTConfig {
            q_enable,
            q_not_first,
            is_start,
            is_branch,
            is_account,
            is_storage,
            main,
            managed_columns,
            memory,
            keccak_table,
            fixed_table,
            state_machine,
            r: 0.scalar(),
            mpt_table,
            cb,
        }
    }

    /// Make the assignments to the MPTCircuit
    pub fn assign(
        &mut self,
        layouter: &mut impl Layouter<F>,
        witness: &mut [MptWitnessRow<F>],
        r: F,
    ) -> Result<(), Error> {
        self.r = r;
        let mut height = 0;
        let mut memory = self.memory.clone();

        // TODO(Brecht): change this on the witness generation side
        let mut key_rlp_bytes = Vec::new();
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

            if row.get_type() == MptWitnessRowType::BranchChild {
                //println!("- {:?}", row.bytes);
                let mut child_s_bytes = row.bytes[0..34].to_owned();
                if child_s_bytes[1] == 160 {
                    child_s_bytes[0] = 0;
                    child_s_bytes.rotate_left(1);
                } else {
                    child_s_bytes[0] = 0;
                    child_s_bytes[1] = 0;
                    child_s_bytes.rotate_left(2);
                };

                let mut child_c_bytes = row.bytes[34..68].to_owned();
                if child_c_bytes[1] == 160 {
                    child_c_bytes[0] = 0;
                    child_c_bytes.rotate_left(1);
                } else {
                    child_c_bytes[0] = 0;
                    child_c_bytes[1] = 0;
                    child_c_bytes.rotate_left(2);
                };

                row.bytes = [
                    child_s_bytes.clone(),
                    child_c_bytes.clone(),
                    row.bytes[68..].to_owned(),
                ]
                .concat();
                //println!("+ {:?}", row.bytes);
            }

            if row.get_type() == MptWitnessRowType::ExtensionNodeS
                || row.get_type() == MptWitnessRowType::ExtensionNodeC
            {
                //println!("- {:?}", row.bytes);
                let mut value_bytes = row.bytes[34..68].to_owned();
                if value_bytes[1] == 160 {
                    value_bytes[0] = 0;
                    value_bytes.rotate_left(1);
                } else {
                    value_bytes[0] = 0;
                    value_bytes[1] = 0;
                    value_bytes.rotate_left(2);
                };
                row.bytes = [
                    row.bytes[0..34].to_owned(),
                    value_bytes.clone(),
                    row.bytes[68..].to_owned(),
                ]
                .concat();
                //println!("+ {:?}", row.bytes);
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

                // Currently the list rlp bytes are dropped for non-key row, restore them here
                if key_bytes[0] < RLP_LIST_SHORT
                    && row.get_type() != MptWitnessRowType::ExtensionNodeS
                {
                    for idx in 0..key_rlp_bytes.len() {
                        key_bytes[idx] = key_rlp_bytes[idx];
                    }
                }

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

                //println!("bytes: {:?}", key_bytes);

                let num_rlp_bytes = if is_short {
                    1
                } else if is_long {
                    2
                } else if is_very_long {
                    3
                } else {
                    if row.get_type() == MptWitnessRowType::ExtensionNodeS {
                        0
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

                if row.get_type() == MptWitnessRowType::AccountLeafKeyS
                    || row.get_type() == MptWitnessRowType::StorageLeafSKey
                {
                    key_rlp_bytes = row.rlp_bytes.clone();
                }

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

            // Shift the value bytes to the start of the row
            if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                || row.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
            {
                let storage_root = row.bytes[1..34].to_owned();
                let codehash = row.bytes[35..68].to_owned();

                row.bytes = [
                    storage_root,
                    vec![0; 1],
                    codehash,
                    vec![0; 1],
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

        // TODO(Brecht): change this on the witness generation side
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
                    new_row.s_root_bytes().to_owned(),
                    vec![0; 2],
                    new_row.c_root_bytes().to_owned(),
                    vec![0; 2],
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
                    nonce_balance_s.rlp_bytes.clone(),
                    nonce_balance_c.rlp_bytes.clone(),
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
                    drifted_rlp_bytes,
                    wrong_rlp_bytes,
                };
                let mut node = Node::default();
                node.account = Some(account_node);
                node.values = node_rows;
                nodes.push(node);
            }
        }

        layouter.assign_region(
            || "MPT",
            |mut region| {
                let mut pv = MPTState::new(&self.memory);

                memory.clear_witness_data();

                let mut offset = 0;
                for node in nodes.iter() {
                    // Assign bytes
                    for (idx, bytes) in node.values.iter().enumerate() {
                        for (byte, &column) in bytes.iter().zip(self.main.bytes.iter()) {
                            assign!(region, (column, offset + idx) => byte.scalar())?;
                        }
                    }

                    // Assign nodes
                    if node.start.is_some() {
                        //println!("{}: start", offset);
                        assign!(region, (self.is_start, offset) => 1.scalar())?;
                        self.state_machine.start_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                        )?;
                    } else if node.extension_branch.is_some() {
                        //println!("{}: branch", offset);
                        assign!(region, (self.is_branch, offset) => 1.scalar())?;
                        self.state_machine.branch_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                        )?;
                    } else if node.storage.is_some() {
                        assign!(region, (self.is_storage, offset) => 1.scalar())?;
                        //println!("{}: storage", offset);
                        self.state_machine.storage_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                        )?;
                    } else if node.account.is_some() {
                        assign!(region, (self.is_account, offset) => 1.scalar())?;
                        //println!("{}: account", offset);
                        self.state_machine.account_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                        )?;
                    }

                    //println!("height: {}", node.bytes.len());
                    offset += node.values.len();
                }

                height = offset;
                memory = pv.memory;

                for offset in 0..height {
                    assignf!(region, (self.q_enable, offset) => true.scalar())?;
                    assignf!(region, (self.q_not_first, offset) => (offset != 0).scalar())?;
                }

                Ok(())
            },
        )?;

        memory.assign(layouter, height)?;

        Ok(())
    }

    fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                let mut offset = 0;

                // Zero lookup
                for fixed_table in self.fixed_table.iter() {
                    assignf!(region, (*fixed_table, offset) => 0.scalar())?;
                }
                offset += 1;

                // Mult table
                let mut mult = F::one();
                for ind in 0..(2 * HASH_WIDTH + 1) {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::RMult.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    assignf!(region, (self.fixed_table[2], offset) => mult)?;
                    mult *= randomness;
                    offset += 1;
                }

                // Byte range table
                for ind in 0..256 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::Range256.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    offset += 1;
                }

                // Byte range with length table
                // These fixed rows enable to easily check whether there are zeros in the unused columns (the number of unused columns vary).
                // The lookups ensure that when the unused columns start, the values in these columns are zeros -
                // when the unused columns start, the value that is used for the lookup in the last column is negative
                // and thus a zero is enforced.
                let max_length = 34i32 + 1;
                for (tag, range) in [
                    (FixedTableTag::RangeKeyLen256, 256),
                    (FixedTableTag::RangeKeyLen16, 16),
                ] {
                    for n in -512..max_length {
                        let range = if n < 0 { 1 } else { range };
                        for idx in 0..range {
                            let v = F::from(n.unsigned_abs() as u64)
                                * if n.is_negative() { -F::one() } else { F::one() };
                            assignf!(region, (self.fixed_table[0], offset) => tag.scalar())?;
                            assignf!(region, (self.fixed_table[1], offset) => idx.scalar())?;
                            assignf!(region, (self.fixed_table[2], offset) => v)?;
                            offset += 1;
                        }
                    }
                }

                // Nibble range table
                for ind in 0..16 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::Range16.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[derive(Default)]
struct MPTCircuit<F> {
    witness: Vec<Vec<u8>>,
    randomness: F,
}

impl<F: Field> Circuit<F> for MPTCircuit<F> {
    type Config = MPTConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let keccak_table = KeccakTable::construct(meta);
        let power_of_randomness: [Expression<F>; HASH_WIDTH] =
            power_of_randomness_from_instance(meta);
        MPTConfig::configure(meta, power_of_randomness, keccak_table)
    }

    fn synthesize(
        &self,
        mut config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut to_be_hashed = vec![];

        let mut witness_rows = vec![];
        for row in self.witness.iter() {
            if row[row.len() - 1] == 5 {
                to_be_hashed.push(row[0..row.len() - 1].to_vec());
            } else {
                let row = MptWitnessRow::new(row[0..row.len()].to_vec());
                witness_rows.push(row);
            }
        }

        config.load_fixed_table(&mut layouter, self.randomness)?;
        config.assign(&mut layouter, &mut witness_rows, self.randomness)?;

        let challenges = Challenges::mock(Value::known(self.randomness));
        config
            .keccak_table
            .dev_load(&mut layouter, &to_be_hashed, &challenges, false)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use halo2_proofs::{
        dev::MockProver,
        halo2curves::{bn256::Fr, FieldExt},
    };

    use std::fs;

    #[test]
    fn test_mpt() {
        // for debugging:
        let path = "src/mpt_circuit/tests";
        // let path = "tests";
        let files = fs::read_dir(path).unwrap();
        files
            .filter_map(Result::ok)
            .filter(|d| {
                if let Some(e) = d.path().extension() {
                    e == "json"
                } else {
                    false
                }
            })
            .enumerate()
            .for_each(|(idx, f)| {
                let path = f.path();
                let mut parts = path.to_str().unwrap().split('-');
                parts.next();
                let file = std::fs::File::open(path.clone());
                let reader = std::io::BufReader::new(file.unwrap());
                let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();

                let count = w.iter().filter(|r| r[r.len() - 1] != 5).count() * 2;
                let randomness: Fr = 123456789.scalar();
                let instance: Vec<Vec<Fr>> = (1..HASH_WIDTH + 1)
                    .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); count])
                    .collect();

                let circuit = MPTCircuit::<Fr> {
                    witness: w.clone(),
                    randomness,
                };

                println!("{} {:?}", idx, path);
                // let prover = MockProver::run(9, &circuit, vec![pub_root]).unwrap();
                let num_rows = w.len() * 2;
                let prover = MockProver::run(14 /* 9 */, &circuit, instance).unwrap();
                assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));
                //assert_eq!(prover.verify_par(), Ok(()));
                //prover.assert_satisfied();
            });
    }
}

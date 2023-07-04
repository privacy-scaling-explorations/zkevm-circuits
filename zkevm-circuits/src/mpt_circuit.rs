//! The MPT circuit implementation.
use eth_types::Field;
use gadgets::{
    impl_expr,
    util::{Expr, Scalar},
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase,
        VirtualCells,
    },
    poly::Rotation,
};

use std::{convert::TryInto, env::var};

mod account_leaf;
mod branch;
mod extension;
mod extension_branch;
mod helpers;
mod param;
mod rlp_gadgets;
mod start;
mod storage_leaf;
/// MPT witness row
pub mod witness_row;

use self::{
    account_leaf::AccountLeafConfig,
    helpers::{key_memory, RLPItemView},
    param::RLP_UNIT_NUM_BYTES,
    rlp_gadgets::decode_rlp,
    witness_row::{
        AccountRowType, ExtensionBranchRowType, Node, StartRowType, StorageRowType,
        NODE_RLP_TYPES_ACCOUNT, NODE_RLP_TYPES_BRANCH, NODE_RLP_TYPES_START,
        NODE_RLP_TYPES_STORAGE,
    },
};
use crate::{
    assign, assignf, circuit,
    circuit_tools::{
        cached_region::CachedRegion,
        cell_manager::{CellManager, DynamicLookupTable},
        memory::Memory,
    },
    evm_circuit::table::Table,
    mpt_circuit::{
        helpers::{
            main_memory, parent_memory, MPTConstraintBuilder, MainRLPGadget, MptCellType, FIXED,
            KECCAK, MULT,
        },
        start::StartConfig,
        storage_leaf::StorageLeafConfig,
    },
    table::{KeccakTable, LookupTable, MPTProofType, MptTable},
    util::Challenges,
};
use extension_branch::ExtensionBranchConfig;
use param::HASH_WIDTH;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum MPTRegion {
    Default,
    RLP,
    Start,
    Branch,
    Account,
    Storage,
    Count,
}

/// State machine config.
#[derive(Clone, Debug)]
pub struct StateMachineConfig<F> {
    is_start: Column<Advice>,
    is_branch: Column<Advice>,
    is_account: Column<Advice>,
    is_storage: Column<Advice>,

    start_config: StartConfig<F>,
    branch_config: ExtensionBranchConfig<F>,
    storage_config: StorageLeafConfig<F>,
    account_config: AccountLeafConfig<F>,
}

impl<F: Field> StateMachineConfig<F> {
    /// Construct a new StateMachine
    pub(crate) fn construct(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_start: meta.advice_column(),
            is_branch: meta.advice_column(),
            is_account: meta.advice_column(),
            is_storage: meta.advice_column(),
            start_config: StartConfig::default(),
            branch_config: ExtensionBranchConfig::default(),
            storage_config: StorageLeafConfig::default(),
            account_config: AccountLeafConfig::default(),
        }
    }

    /// Returns all state selectors
    pub(crate) fn state_selectors(&self) -> Vec<Column<Advice>> {
        vec![
            self.is_start,
            self.is_branch,
            self.is_account,
            self.is_storage,
        ]
    }

    pub(crate) fn step_constraints(
        &self,
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        height: usize,
    ) {
        circuit!([meta, cb], {
            // Because the state machine state is this height, we're already querying cells
            // at all of these rotations, so may as well keep things simple.
            // State selectors are already enforced to be boolean on each row.
            let mut sum = 0.expr();
            for rot in 1..height {
                for state_selector in self.state_selectors() {
                    sum = sum + a!(state_selector, rot);
                }
            }
            require!(sum => 0);
            // It should not be necessary to force the next row to have a state enabled
            // because we never use relative offsets between state machine states.
        })
    }
}

/// Merkle Patricia Trie context
#[derive(Clone, Debug)]
pub struct MPTContext<F> {
    pub(crate) mpt_table: MptTable,
    pub(crate) rlp_item: MainRLPGadget<F>,
    pub(crate) memory: Memory<F, MptCellType>,
}

/// RLP item type
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RlpItemType {
    /// Node (string with len == 0 or 32, OR list with len <= 31)
    Node,
    /// Value (string with len <= 32)
    Value,
    /// Hash (string with len == 32)
    Hash,
    /// Key (string with len <= 33)
    Key,
    /// Nibbles
    Nibbles,
}

impl<F: Field> MPTContext<F> {
    pub(crate) fn rlp_item(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut MPTConstraintBuilder<F>,
        idx: usize,
        item_type: RlpItemType,
    ) -> RLPItemView<F> {
        self.rlp_item.create_view(meta, cb, idx, item_type)
    }
}

/// Merkle Patricia Trie config.
#[derive(Clone)]
pub struct MPTConfig<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_first: Column<Fixed>,
    pub(crate) q_last: Column<Fixed>,
    pub(crate) memory: Memory<F, MptCellType>,
    pub(crate) mpt_table: MptTable,
    keccak_table: KeccakTable,
    fixed_table: [Column<Fixed>; 6],
    mult_table: [Column<Advice>; 2],
    rlp_item: MainRLPGadget<F>,
    state_machine: StateMachineConfig<F>,
    params: MPTCircuitParams,
    cb: MPTConstraintBuilder<F>,
}

/// Enumerator to determine the type of row in the fixed table.
#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    /// All zero lookup data
    Disabled,
    /// 0 - 15
    Range16,
    /// 0 - 255
    Range256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen16,
    /// Extesion key odd key
    ExtOddKey,
    /// RLP decoding
    RLP,
    /// TEMP
    RMult,
}
impl_expr!(FixedTableTag);

#[derive(Default)]
pub(crate) struct MPTState<F> {
    pub(crate) memory: Memory<F, MptCellType>,
}

impl<F: Field> MPTState<F> {
    fn new(memory: &Memory<F, MptCellType>) -> Self {
        Self {
            memory: memory.clone(),
        }
    }
}

impl<F: Field> MPTConfig<F> {
    /// Configure MPT Circuit
    pub fn new(
        meta: &mut ConstraintSystem<F>,
        challenges: Challenges<Expression<F>>,
        keccak_table: KeccakTable,
        params: MPTCircuitParams,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();

        let mpt_table = MptTable::construct(meta);

        let fixed_table: [Column<Fixed>; 6] = (0..6)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let mult_table: [Column<Advice>; 2] = (0..2)
            .map(|_| meta.advice_column_in(SecondPhase))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let memory_columns = (0..5).map(|_| meta.advice_column()).collect::<Vec<_>>();

        let mut state_machine = StateMachineConfig::construct(meta);
        let mut rlp_item = MainRLPGadget::default();

        let mut memory = Memory::new(memory_columns);
        memory.allocate(meta, key_memory(false), MptCellType::MemKeyCTable);
        memory.allocate(meta, key_memory(true), MptCellType::MemKeySTable);
        memory.allocate(meta, parent_memory(false), MptCellType::MemParentCTable);
        memory.allocate(meta, parent_memory(true), MptCellType::MemParentSTable);
        memory.allocate(meta, main_memory(), MptCellType::MemMainTable);

        let mut ctx = MPTContext {
            mpt_table,
            rlp_item: rlp_item.clone(),
            memory: memory.clone(),
        };

        let rlp_cm = CellManager::new(
            meta,
            // Type, #cols, phase, permutable
            vec![
                (MptCellType::StoragePhase1, 51, 1, false),
                (MptCellType::StoragePhase2, 5, 2, false),
                (MptCellType::StoragePhase3, 5, 3, false),
                (MptCellType::LookupByte, 4, 1, false),
                (MptCellType::Lookup(Table::Fixed), 4, 3, false),
                (MptCellType::Lookup(Table::Exp), 2, 3, false),
            ],
            0,
            1,
        );
        let state_cm = CellManager::new(
            meta,
            // Type, #cols, phase, permutable
            vec![
                (MptCellType::StoragePhase1, 20, 1, false),
                (MptCellType::StoragePhase2, 5, 2, false),
                (MptCellType::StoragePhase3, 5, 3, false),
                (MptCellType::LookupByte, 4, 1, false),
                (MptCellType::Lookup(Table::Fixed), 3, 3, false),
                (MptCellType::Lookup(Table::Keccak), 1, 3, false),
                (MptCellType::Lookup(Table::Exp), 2, 3, false),
                (MptCellType::MemParentSInput, 1, 3, false),
                (MptCellType::MemParentSTable, 1, 3, false),
                (MptCellType::MemParentCInput, 1, 3, false),
                (MptCellType::MemParentCTable, 1, 3, false),
                (MptCellType::MemKeySInput, 1, 3, false),
                (MptCellType::MemKeySTable, 1, 3, false),
                (MptCellType::MemKeyCInput, 1, 3, false),
                (MptCellType::MemKeyCTable, 1, 3, false),
                (MptCellType::MemMainInput, 1, 3, false),
                (MptCellType::MemMainTable, 1, 3, false),
            ],
            0,
            50,
        );

        let parent_s_table = DynamicLookupTable::from(&state_cm, MptCellType::MemParentSTable);
        let parent_c_table = DynamicLookupTable::from(&state_cm, MptCellType::MemParentCTable);
        let key_s_table = DynamicLookupTable::from(&state_cm, MptCellType::MemKeySTable);
        let key_c_table = DynamicLookupTable::from(&state_cm, MptCellType::MemKeyCTable);
        let main_table = DynamicLookupTable::from(&state_cm, MptCellType::MemMainTable);

        let r = 123456.expr();
        let mut cb = MPTConstraintBuilder::new(5, Some(challenges.clone()), None, r.expr());
        meta.create_gate("MPT", |meta| {
            circuit!([meta, cb], {
                // Populate lookup tables
                require!(@KECCAK => <KeccakTable as LookupTable<F>>::advice_columns(&keccak_table).iter().map(|table| a!(table)).collect());
                require!(@FIXED => fixed_table.iter().map(|table| f!(table)).collect());
                require!(@MULT => mult_table.iter().map(|table| a!(table)).collect());

                ifx!{f!(q_enable) => {
                    // Mult table
                    ifx! {f!(q_first) => {
                        require!(a!(mult_table[0]) => 0);
                        require!(a!(mult_table[1]) => 1);
                    }}
                    require!(a!(mult_table[0], 1) => a!(mult_table[0]) + 1.expr());
                    require!(a!(mult_table[1], 1) => a!(mult_table[1]) * challenges.keccak_input().expr());

                    // RLP item decoding unit
                    cb.base.set_cell_manager(rlp_cm.clone());
                    cb.base.push_region(MPTRegion::RLP as usize);
                    rlp_item = MainRLPGadget::construct(&mut cb, params);
                    cb.base.pop_region();
                    ctx.rlp_item = rlp_item.clone();

                    // Main MPT circuit
                    // State machine
                    cb.base.set_cell_manager(state_cm.clone());
                    ifx! {f!(q_first) + f!(q_last) => {
                        require!(a!(state_machine.is_start) => true);
                    }};
                    // Main state machine
                    matchx! {
                        a!(state_machine.is_start) => {
                            state_machine.step_constraints(meta, &mut cb, StartRowType::Count as usize);
                            cb.base.push_region(MPTRegion::Start as usize);
                            state_machine.start_config = StartConfig::configure(meta, &mut cb, ctx.clone());
                            ctx.memory.build_constraints(&mut cb.base, f!(q_first));
                            cb.base.pop_region();
                        },
                        a!(state_machine.is_branch) => {
                            state_machine.step_constraints(meta, &mut cb, ExtensionBranchRowType::Count as usize);
                            cb.base.push_region(MPTRegion::Branch as usize);
                            state_machine.branch_config = ExtensionBranchConfig::configure(meta, &mut cb, ctx.clone());
                            ctx.memory.build_constraints(&mut cb.base, f!(q_first));
                            cb.base.pop_region();
                        },
                        a!(state_machine.is_account) => {
                            state_machine.step_constraints(meta, &mut cb, AccountRowType::Count as usize);
                            cb.base.push_region(MPTRegion::Account as usize);
                            state_machine.account_config = AccountLeafConfig::configure(meta, &mut cb, ctx.clone());
                            ctx.memory.build_constraints(&mut cb.base, f!(q_first));
                            cb.base.pop_region();
                        },
                        a!(state_machine.is_storage) => {
                            state_machine.step_constraints(meta, &mut cb, StorageRowType::Count as usize);
                            cb.base.push_region(MPTRegion::Storage as usize);
                            state_machine.storage_config = StorageLeafConfig::configure(meta, &mut cb, ctx.clone());
                            ctx.memory.build_constraints(&mut cb.base, f!(q_first));
                            cb.base.pop_region();
                        },
                        _ => ctx.memory.build_constraints(&mut cb.base, f!(q_first)),
                    };
                    // Only account and storage rows can have lookups, disable lookups on all other rows
                    ifx! {not!(a!(state_machine.is_account) + a!(state_machine.is_storage)) => {
                        require!(a!(ctx.mpt_table.proof_type) => MPTProofType::Disabled.expr());
                    }}
                }}
            });

            cb.base.build_constraints()
        });

        let disable_lookups: usize = var("DISABLE_LOOKUPS")
            .unwrap_or_else(|_| "0".to_string())
            .parse()
            .expect("Cannot parse DISABLE_LOOKUPS env var as usize");
        if disable_lookups == 0 {
            cb.base.build_lookups(
                meta,
                vec![rlp_cm, state_cm],
                vec![
                    // TODO(Brecht): fix
                    //(MptCellType::Lookup(Table::Keccak), &keccak_table),
                    (MptCellType::Lookup(Table::Fixed), &fixed_table),
                    (MptCellType::Lookup(Table::Exp), &mult_table),
                    (MptCellType::MemParentSInput, &parent_s_table),
                    (MptCellType::MemParentCInput, &parent_c_table),
                    (MptCellType::MemKeySInput, &key_s_table),
                    (MptCellType::MemKeyCInput, &key_c_table),
                    (MptCellType::MemMainInput, &main_table),
                ],
            );
            cb.base.build_dynamic_lookups(
                meta,
                &[vec![FIXED]].concat(),
                vec![(FIXED, &fixed_table)],
            );
        } else if disable_lookups == 1 {
            cb.base.build_dynamic_lookups(
                meta,
                &[vec![KECCAK], ctx.memory.tags()].concat(),
                vec![(MptCellType::Lookup(Table::Fixed), &fixed_table)],
            );
        } else if disable_lookups == 2 {
            cb.base.build_dynamic_lookups(
                meta,
                &ctx.memory.tags(),
                vec![(MptCellType::Lookup(Table::Fixed), &fixed_table)],
            );
        } else if disable_lookups == 3 {
            cb.base.build_dynamic_lookups(
                meta,
                &[FIXED, KECCAK],
                vec![(MptCellType::Lookup(Table::Fixed), &fixed_table)],
            );
        } else if disable_lookups == 4 {
            cb.base.build_dynamic_lookups(
                meta,
                &[KECCAK],
                vec![(MptCellType::Lookup(Table::Fixed), &fixed_table)],
            );
        }

        println!("max expression degree: {}", meta.degree());
        println!("num lookups: {}", meta.lookups().len());
        println!("num advices: {}", meta.num_advice_columns());
        println!("num fixed: {}", meta.num_fixed_columns());
        // cb.base.print_stats();

        MPTConfig {
            q_enable,
            q_first,
            q_last,
            memory,
            keccak_table,
            fixed_table,
            mult_table,
            state_machine,
            rlp_item,
            params,
            mpt_table,
            cb,
        }
    }

    /// Make the assignments to the MPTCircuit
    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        nodes: &[Node],
        challenges: &Challenges<Value<F>>,
    ) -> Result<usize, Error> {
        let mut height = 0;
        layouter.assign_region(
            || "MPT",
            |mut region| {
                let r = F::from(123456u64);
                let mut keccak_r = F::ZERO;
                challenges.keccak_input().map(|v| keccak_r = v);

                let mut pv = MPTState::new(&self.memory);

                let mut offset = 0;
                for node in nodes.iter() {
                    //println!("offset: {}", offset);
                    let mut cached_region = CachedRegion::new(
                        &mut region,
                        r,
                        keccak_r,
                    );

                    let item_types = if node.start.is_some() {
                        NODE_RLP_TYPES_START.to_vec()
                    } else if node.extension_branch.is_some() {
                        NODE_RLP_TYPES_BRANCH.to_vec()
                    } else if node.account.is_some() {
                        NODE_RLP_TYPES_ACCOUNT.to_vec()
                    } else if node.storage.is_some() {
                        NODE_RLP_TYPES_STORAGE.to_vec()
                    } else {
                        unreachable!()
                    };

                    // Assign bytes
                    let mut rlp_values = Vec::new();
                    // Decompose RLP
                    for (idx, (bytes, item_type)) in node.values.iter().zip(item_types.iter()).enumerate() {
                        cached_region.push_region(offset + idx, MPTRegion::RLP as usize);
                        let rlp_value = self.rlp_item.assign(
                            &mut cached_region,
                            offset + idx,
                            bytes,
                            *item_type,
                        )?;
                        rlp_values.push(rlp_value);
                        cached_region.pop_region();
                    }

                    // Assign nodes
                    if node.start.is_some() {
                        // println!("{}: start", offset);
                        cached_region.push_region(offset, MPTRegion::Start as usize);
                        assign!(cached_region, (self.state_machine.is_start, offset) => "is_start", true.scalar())?;
                        self.state_machine.start_config.assign(
                            &mut cached_region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                        cached_region.pop_region();
                    } else if node.extension_branch.is_some() {
                        // println!("{}: branch", offset);
                        cached_region.push_region(offset, MPTRegion::Branch as usize);
                        assign!(cached_region, (self.state_machine.is_branch, offset) => "is_branch", true.scalar())?;
                        self.state_machine.branch_config.assign(
                            &mut cached_region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                        cached_region.pop_region();
                    } else if node.account.is_some() {
                        // println!("{}: account", offset);
                        cached_region.push_region(offset, MPTRegion::Account as usize);
                        assign!(cached_region, (self.state_machine.is_account, offset) => "is_account", true.scalar())?;
                        self.state_machine.account_config.assign(
                            &mut cached_region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                        cached_region.pop_region();
                    } else if node.storage.is_some() {
                        // println!("{}: storage", offset);
                        cached_region.push_region(offset, MPTRegion::Storage as usize);
                        assign!(cached_region, (self.state_machine.is_storage, offset) => "is_storage", true.scalar())?;
                        self.state_machine.storage_config.assign(
                            &mut cached_region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                        cached_region.pop_region();
                    }

                    offset += node.values.len();

                    pv.memory.assign(&mut cached_region, offset)?;

                    cached_region.assign_stored_expressions(&self.cb.base, challenges)?;
                }
                height = offset;

                // Make sure the circuit is high enough for the mult table
                while height < (2 * HASH_WIDTH + 1) {
                    height += 1;
                }

                for offset in 0..height {
                    assignf!(region, (self.q_enable, offset) => true.scalar())?;
                    assignf!(region, (self.q_first, offset) => (offset == 0).scalar())?;
                    assignf!(region, (self.q_last, offset) => (offset == height - 2).scalar())?;
                }

                Ok(())
            },
        )?;

        // memory.assign(layouter, height)?;

        Ok(height)
    }

    fn load_fixed_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
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
                let r = F::from(123456u64);
                let mut mult = F::ONE;
                for ind in 0..(2 * HASH_WIDTH + 1) {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::RMult.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    assignf!(region, (self.fixed_table[2], offset) => mult)?;
                    mult *= r;
                    offset += 1;
                }

                // Byte range table
                for ind in 0..256 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::Range256.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    offset += 1;
                }

                // Nibble range table
                for ind in 0..16 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::Range16.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ind.scalar())?;
                    offset += 1;
                }

                // Byte range with length table
                // This allows us to easily check whether there are zeros in the unused columns (the number of unused columns vary).
                // The lookups ensure that when the unused columns start, the values in these columns are zeros -
                // when the unused columns start, the value that is used for the lookup in the last column is zero or negative
                // and thus a zero is enforced.
                for (tag, range, out_of_range) in [
                    (FixedTableTag::RangeKeyLen256, 256, 1),
                    (FixedTableTag::RangeKeyLen16, 16, 16),
                ] {
                    let get_range = |n: i32| {
                        if n <= 0 { out_of_range } else { range }
                    };
                    let max_length = RLP_UNIT_NUM_BYTES as i32;
                    for idx in -max_length..=max_length {
                        if self.params.is_two_byte_lookup_enabled() {
                            let range1 = get_range(idx);
                            for byte1 in 0..range1 {
                                let range2 = get_range(idx - 1);
                                for byte2 in 0..range2 {
                                    assignf!(region, (self.fixed_table[0], offset) => tag.scalar())?;
                                    assignf!(region, (self.fixed_table[1], offset) => idx.scalar())?;
                                    assignf!(region, (self.fixed_table[2], offset) => byte1.scalar())?;
                                    assignf!(region, (self.fixed_table[3], offset) => byte2.scalar())?;
                                    offset += 1;
                                }
                            }
                        } else {
                            let range = get_range(idx);
                            for byte in 0..range {
                                assignf!(region, (self.fixed_table[0], offset) => tag.scalar())?;
                                assignf!(region, (self.fixed_table[1], offset) => idx.scalar())?;
                                assignf!(region, (self.fixed_table[2], offset) => byte.scalar())?;
                                offset += 1;
                            }
                        }
                }
            }

                // Compact encoding of the extension key, find out if the key is odd or not.
                // Even - The full byte is simply 0.
                assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::ExtOddKey.scalar())?;
                assignf!(region, (self.fixed_table[1], offset) => 0.scalar())?;
                assignf!(region, (self.fixed_table[2], offset) => false.scalar())?;
                offset += 1;
                // Odd - First nibble is 1, the second nibble can be any value.
                for idx in 0..16 {
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::ExtOddKey.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => ((0b1_0000) + idx).scalar())?;
                    assignf!(region, (self.fixed_table[2], offset) => true.scalar())?;
                    offset += 1;
                }

                // RLP
                for byte in 0..255 {
                    let (is_list, is_short, is_long, is_very_long) = decode_rlp(byte);
                    assignf!(region, (self.fixed_table[0], offset) => FixedTableTag::RLP.scalar())?;
                    assignf!(region, (self.fixed_table[1], offset) => byte.scalar())?;
                    assignf!(region, (self.fixed_table[2], offset) => is_list.scalar())?;
                    assignf!(region, (self.fixed_table[3], offset) => is_short.scalar())?;
                    assignf!(region, (self.fixed_table[4], offset) => is_long.scalar())?;
                    assignf!(region, (self.fixed_table[5], offset) => is_very_long.scalar())?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }

    fn load_mult_table(
        &self,
        layouter: &mut impl Layouter<F>,
        challenges: &Challenges<Value<F>>,
        height: usize,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mult table",
            |mut region| {
                let mut r = F::ZERO;
                challenges.keccak_input().map(|k| r = k);

                let mut mult = F::ONE;
                for idx in 0..=height {
                    assign!(region, (self.mult_table[0], idx) => idx.scalar())?;
                    assign!(region, (self.mult_table[1], idx) => mult)?;
                    mult *= r;
                }
                Ok(())
            },
        )
    }
}

/// MPT Circuit for proving the storage modification is valid.
#[derive(Default)]
struct MPTCircuit<F> {
    nodes: Vec<Node>,
    keccak_data: Vec<Vec<u8>>,
    degree: usize,
    randomness: F,
}

/// Super Circuit configuration parameters
#[derive(Copy, Clone, Default)]
pub struct MPTCircuitParams {
    degree: usize,
}

impl MPTCircuitParams {
    fn is_two_byte_lookup_enabled(&self) -> bool {
        self.degree >= 22
    }
}

impl<F: Field> Circuit<F> for MPTCircuit<F> {
    type Config = (MPTConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = MPTCircuitParams;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn params(&self) -> Self::Params {
        MPTCircuitParams {
            degree: self.degree,
        }
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenges_expr = challenges.exprs(meta);
        let keccak_table = KeccakTable::construct(meta);
        (
            MPTConfig::new(meta, challenges_expr, keccak_table, params),
            challenges,
        )
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!();
    }

    fn synthesize(
        &self,
        (config, _challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = _challenges.values(&mut layouter);
        let height = config.assign(&mut layouter, &self.nodes, &challenges)?;
        config.load_fixed_table(&mut layouter)?;
        config.load_mult_table(&mut layouter, &challenges, height)?;
        config
            .keccak_table
            .dev_load(&mut layouter, &self.keccak_data, &challenges)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
    use std::fs;

    #[test]
    fn test_mpt() {
        let path = "src/mpt_circuit/tests";
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
                let mut nodes: Vec<Node> = serde_json::from_reader(reader).unwrap();
                let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

                // TODO(Brecht): move to the witness geration side
                // Patch the hash value so its RLP encoding is valid
                for node in nodes.iter_mut() {
                    if node.start.is_some() {
                        for value in node.values.iter_mut() {
                            if value[0] == 0 {
                                value[0] = 160;
                            }
                        }
                    }
                }

                let randomness: Fr = 123456.scalar();

                let mut keccak_data = vec![];
                for node in nodes.iter() {
                    for k in node.keccak_data.iter() {
                        keccak_data.push(k.clone());
                    }
                }

                let degree = 14;
                let circuit = MPTCircuit::<Fr> {
                    nodes,
                    keccak_data,
                    randomness,
                    degree,
                };

                println!("{} {:?}", idx, path);
                let prover = MockProver::run(degree as u32, &circuit, vec![]).unwrap();
                assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));
                // assert_eq!(prover.verify_par(), Ok(()));
                // prover.assert_satisfied();
            });
    }
}

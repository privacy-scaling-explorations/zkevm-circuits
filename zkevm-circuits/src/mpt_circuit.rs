//! The MPT circuit implementation.
use eth_types::Field;
use gadgets::{
    impl_expr,
    util::{Expr, Scalar},
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
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
mod witness_row;

use self::{
    account_leaf::AccountLeafConfig,
    helpers::{key_memory, RLPItemView},
    witness_row::{StartRowType,ExtensionBranchRowType, AccountRowType, StorageRowType,Node},
};
use crate::{
    assign, assignf, circuit,
    circuit_tools::{
        cell_manager::CellManager, constraint_builder::ConstraintBuilder, memory::Memory,
    },
    mpt_circuit::{
        helpers::{main_memory, parent_memory, MPTConstraintBuilder, MainRLPGadget},
        start::StartConfig,
        storage_leaf::StorageLeafConfig,
    },
    table::{KeccakTable, LookupTable, MPTProofType, MptTable},
    util::Challenges,
};
use extension_branch::ExtensionBranchConfig;
use param::HASH_WIDTH;

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
}

/// Merkle Patricia Trie context
#[derive(Clone, Debug)]
pub struct MPTContext<F> {
    pub(crate) mpt_table: MptTable,
    pub(crate) rlp_item: MainRLPGadget<F>,
    pub(crate) challenges: Challenges<Expression<F>>,
    pub(crate) memory: Memory<F>,
    pub(crate) r: Expression<F>,
}

impl<F: Field> MPTContext<F> {
    pub(crate) fn rlp_item(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        idx: usize,
    ) -> RLPItemView<F> {
        // TODO(Brecht): Add RLP limitations like max num bytes
        self.rlp_item.create_view(meta, cb, idx, false)
    }

    pub(crate) fn nibbles(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut ConstraintBuilder<F>,
        idx: usize,
    ) -> RLPItemView<F> {
        self.rlp_item.create_view(meta, cb, idx, true)
    }
}

/// Merkle Patricia Trie config.
#[derive(Clone)]
pub struct MPTConfig<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_first: Column<Fixed>,
    pub(crate) q_last: Column<Fixed>,
    pub(crate) rows_left_in_state: Column<Fixed>,
    pub(crate) rlp_columns: Vec<Column<Advice>>,
    pub(crate) managed_columns: Vec<Column<Advice>>,
    pub(crate) memory: Memory<F>,
    keccak_table: KeccakTable,
    fixed_table: [Column<Fixed>; 3],
    rlp_item: MainRLPGadget<F>,
    state_machine: StateMachineConfig<F>,
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
    pub(crate) r: F,
    pub(crate) memory: Memory<F>,
}

impl<F: Field> MPTState<F> {
    fn new(memory: &Memory<F>, r: F) -> Self {
        Self {
            r,
            memory: memory.clone(),
            ..Default::default()
        }
    }
}

impl<F: Field> MPTConfig<F> {
    /// Configure MPT Circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        challenges: Challenges<Expression<F>>,
        keccak_table: KeccakTable,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();
        let rows_left_in_state = meta.fixed_column();

        let mpt_table = MptTable::construct(meta);

        let fixed_table: [Column<Fixed>; 3] = (0..3)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let rlp_columns = (0..50).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let managed_columns = (0..15).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let memory_columns = (0..5).map(|_| meta.advice_column()).collect::<Vec<_>>();

        let mut state_machine = StateMachineConfig::construct(meta);
        let mut rlp_item = MainRLPGadget::default();

        let mut memory = Memory::new(memory_columns);
        memory.allocate(meta, key_memory(false));
        memory.allocate(meta, key_memory(true));
        memory.allocate(meta, parent_memory(false));
        memory.allocate(meta, parent_memory(true));
        memory.allocate(meta, main_memory());

        let mut ctx = MPTContext {
            mpt_table: mpt_table.clone(),
            rlp_item: rlp_item.clone(),
            challenges: challenges.clone(),
            r: challenges.keccak_input(),
            memory: memory.clone(),
        };

        let mut cb = MPTConstraintBuilder::new(33 + 10, None);
        meta.create_gate("MPT", |meta| {
            circuit!([meta, cb.base], {
                // Populate lookup tables
                require!(@"keccak" => <KeccakTable as LookupTable<F>>::advice_columns(&keccak_table).iter().map(|table| a!(table)).collect());
                require!(@"fixed" => fixed_table.iter().map(|table| f!(table)).collect());

                ifx!{f!(q_enable) => {
                    // RLP item decoding unit
                    let mut cell_manager = CellManager::new(meta, &rlp_columns);
                    cell_manager.reset(1);
                    cb.base.set_cell_manager(cell_manager);
                    rlp_item = MainRLPGadget::construct(&mut cb, &ctx.r);
                    ctx.rlp_item = rlp_item.clone();

                    // Main MPT circuit
                    let cell_manager = CellManager::new(meta, &managed_columns);
                    cb.base.set_cell_manager(cell_manager);

                    // State machine
                    // TODO(Brecht): state machine constraints
                    // Always start and end with the start state
                    ifx! {f!(q_first) + f!(q_last) => {
                        require!(a!(state_machine.is_start) => true);
                    }};
                    // Main state machine
                    let sum_states = a!(state_machine.is_start) + a!(state_machine.is_branch) + a!(state_machine.is_account) + a!(state_machine.is_storage);
                    matchx! {
                        a!(state_machine.is_start) => {
                            require!(sum_states => true.expr());
                            require!(f!(rows_left_in_state) => (StartRowType::Count as usize).expr());
                            state_machine.start_config = StartConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(state_machine.is_branch) => {
                            require!(sum_states => true.expr());
                            require!(f!(rows_left_in_state) => (ExtensionBranchRowType::Count as usize ).expr());
                            require!(f!(rows_left_in_state, -1) => 1.expr());
                            state_machine.branch_config = ExtensionBranchConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(state_machine.is_account) => {
                            require!(sum_states => true.expr());
                            require!(f!(rows_left_in_state) => (AccountRowType::Count as usize).expr());
                            require!(f!(rows_left_in_state, -1) => 1.expr());
                            state_machine.account_config = AccountLeafConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        a!(state_machine.is_storage) => {
                            require!(sum_states => true.expr());
                            require!(f!(rows_left_in_state) => (StorageRowType::Count as usize).expr());
                            require!(f!(rows_left_in_state, -1) => 1.expr());
                            state_machine.storage_config = StorageLeafConfig::configure(meta, &mut cb, ctx.clone());
                        },
                        _ =>  require!(sum_states => false.expr()),
                    };
                    // Only account and storage rows can have lookups, disable lookups on all other rows
                    ifx! {not!(a!(state_machine.is_account) + a!(state_machine.is_storage)) => {
                        require!(a!(ctx.mpt_table.proof_type) => MPTProofType::Disabled.expr());
                    }}

                    // Memory banks
                    ctx.memory.generate_constraints(&mut cb.base, f!(q_first));
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
                    vec!["fixed".to_string() /* , "keccak".to_string() */],
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
        // cb.base.print_stats();

        MPTConfig {
            q_enable,
            q_first,
            q_last,
            rows_left_in_state,
            rlp_columns,
            managed_columns,
            memory,
            keccak_table,
            fixed_table,
            state_machine,
            rlp_item,
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
    ) -> Result<(), Error> {
        let mut height = 0;
        let mut memory = self.memory.clone();

        let mut r = F::zero();
        challenges.keccak_input().map(|v| r = v);

        layouter.assign_region(
            || "MPT",
            |mut region| {
                let mut pv = MPTState::new(&self.memory, r);

                memory.clear_witness_data();

                let mut offset = 0;
                for node in nodes.iter() {
                    // Assign bytes
                    let mut rlp_values = Vec::new();
                    for (idx, bytes) in node.values.iter().enumerate() {
                        let is_nibbles = node.extension_branch.is_some()
                            && idx == ExtensionBranchRowType::KeyC as usize;
                        let rlp_value = self.rlp_item.assign(
                            &mut region,
                            offset + idx,
                            bytes,
                            r,
                            is_nibbles,
                        )?;
                        rlp_values.push(rlp_value);
                        assignf!(region, (self.rows_left_in_state, offset + idx) => (node.values.len() - idx).scalar())?;
                    }

                    // Assign nodes
                    if node.start.is_some() {
                        // println!("{}: start", offset);
                        assign!(region, (self.state_machine.is_start, offset) => true.scalar())?;
                        self.state_machine.start_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                    } else if node.extension_branch.is_some() {
                        // println!("{}: branch", offset);
                        assign!(region, (self.state_machine.is_branch, offset) => true.scalar())?;
                        self.state_machine.branch_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                    } else if node.storage.is_some() {
                        // println!("{}: storage", offset);
                        assign!(region, (self.state_machine.is_storage, offset) => true.scalar())?;
                        self.state_machine.storage_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                    } else if node.account.is_some() {
                        // println!("{}: account", offset);
                        assign!(region, (self.state_machine.is_account, offset) => true.scalar())?;
                        self.state_machine.account_config.assign(
                            &mut region,
                            self,
                            &mut pv,
                            offset,
                            node,
                            &rlp_values,
                        )?;
                    }

                    offset += node.values.len();
                }

                height = offset;
                memory = pv.memory;

                for offset in 0..height {
                    assignf!(region, (self.q_enable, offset) => true.scalar())?;
                    assignf!(region, (self.q_first, offset) => (offset == 0).scalar())?;
                    assignf!(region, (self.q_last, offset) => (offset == height - 2).scalar())?;
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
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let mut r = F::zero();
        challenges.keccak_input().map(|v| r = v);

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
                // These fixed rows enable to easily check whether there are zeros in the unused columns (the number of unused columns vary).
                // The lookups ensure that when the unused columns start, the values in these columns are zeros -
                // when the unused columns start, the value that is used for the lookup in the last column is negative
                // and thus a zero is enforced.
                let max_length = 34i32;
                for (tag, range) in [
                    (FixedTableTag::RangeKeyLen256, 256),
                    (FixedTableTag::RangeKeyLen16, 16),
                ] {
                    for n in -max_length..=max_length {
                        let range = if n <= 0 && range == 256 { 1 } else { range };
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

                Ok(())
            },
        )
    }
}

#[derive(Default)]
struct MPTCircuit<F> {
    nodes: Vec<Node>,
    keccak_data: Vec<Vec<u8>>,
    randomness: F,
}

impl<F: Field> Circuit<F> for MPTCircuit<F> {
    type Config = (MPTConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // let challenges = Challenges::construct(meta);
        // let challenges_expr = challenges.exprs(meta);

        let r = 2u64;
        let challenges = Challenges::mock(
            Value::known(F::from(r)),
            Value::known(F::from(r)),
            Value::known(F::from(r)),
        );
        let challenges_expr = Challenges::mock(r.expr(), r.expr(), r.expr());

        let keccak_table = KeccakTable::construct(meta);
        // let randomness: F = 123456789.scalar();
        // Use a mock randomness instead of the randomness derived from the challange
        // (either from mock or real prover) to help debugging assignments.
        // let power_of_randomness: [Expression<F>; HASH_WIDTH] = array::from_fn(|i| {
        //    Expression::Constant(randomness.pow(&[1 + i as u64, 0, 0, 0]))
        //});
        let challenges = Challenges::construct(meta);
        (
            MPTConfig::configure(meta, challenges_expr, keccak_table),
            challenges,
        )
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // let challenges = challenges.values(&mut layouter);

        let r = self.randomness;
        let challenges = Challenges::mock(Value::known(r), Value::known(r), Value::known(r));

        config.load_fixed_table(&mut layouter, &challenges)?;
        config.assign(&mut layouter, &self.nodes, &challenges)?;

        config
            .keccak_table
            .dev_load(&mut layouter, &self.keccak_data, &challenges, false)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::mpt_circuit::witness_row::{prepare_witness, MptWitnessRow};

    use super::*;

    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

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

                let randomness: Fr = 2.scalar();

                let mut keccak_data = vec![];
                let mut witness_rows = vec![];
                for row in w.iter() {
                    if row[row.len() - 1] == 5 {
                        keccak_data.push(row[0..row.len() - 1].to_vec());
                    } else {
                        let row = MptWitnessRow::<Fr>::new(row[0..row.len()].to_vec());
                        witness_rows.push(row);
                    }
                }
                let nodes = prepare_witness(&mut witness_rows);
                let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

                let circuit = MPTCircuit::<Fr> {
                    nodes,
                    keccak_data,
                    randomness,
                };

                println!("{} {:?}", idx, path);
                // let prover = MockProver::run(9, &circuit, vec![pub_root]).unwrap();
                let prover = MockProver::run(14 /* 9 */, &circuit, vec![]).unwrap();
                assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));
                // assert_eq!(prover.verify_par(), Ok(()));
                // prover.assert_satisfied();
            });
    }

    #[test]
    fn graph_mpt() {
        use plotters::prelude::*;

        let path = "src/mpt_circuit/tests";
        let files = fs::read_dir(path).unwrap();
        let files: Vec<fs::DirEntry> = files
            .filter_map(Result::ok)
            .filter(|d| {
                if let Some(e) = d.path().extension() {
                    e == "json"
                } else {
                    false
                }
            }).collect();

        let path = &files[0].path();
        let mut parts = path.to_str().unwrap().split('-');
        parts.next();
        let file = std::fs::File::open(path.clone());
        let reader = std::io::BufReader::new(file.unwrap());
        let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();

        let randomness: Fr = 2.scalar();

        let mut keccak_data = vec![];
        let mut witness_rows = vec![];
        for row in w.iter() {
            if row[row.len() - 1] == 5 {
                keccak_data.push(row[0..row.len() - 1].to_vec());
            } else {
                let row = MptWitnessRow::<Fr>::new(row[0..row.len()].to_vec());
                witness_rows.push(row);
            }
        }
        let nodes = prepare_witness(&mut witness_rows);
        let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

        let circuit = MPTCircuit::<Fr> {
            nodes,
            keccak_data,
            randomness,
        };

        println!("Start graphing");

        let root = BitMapBackend::new("mpt-chip-layout.png", (2048, 7680)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("MPT Chip Layout", ("sans-serif", 60)).unwrap();

        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();

        // Generate the DOT graph string.
        let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
        print!("{}", dot_string);


    }
}

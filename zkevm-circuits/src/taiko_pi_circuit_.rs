//! Use the hash value as public input.

use crate::{
    assign,
    evm_circuit::table::Table::*,
    evm_circuit::{util::{constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon}, rlc}, table::Table},
    table::{byte_table::ByteTable, BlockContextFieldTag, BlockTable, KeccakTable, LookupTable},
    util::{Challenges, SubCircuitConfig, SubCircuit},
    circuit_tools::{
        constraint_builder::{ConstraintBuilder, RLCable, RLCChainable, TO_FIX, COMPRESS, REDUCE, RLCableValue},
        cell_manager::{CellManager, CellType, Cell, CellConfig, CellColumn}, gadgets::{IsEqualGadget, IsZeroGadget}, cached_region::{CachedRegion, self},
    },
    
    witness::{self, BlockContext}, circuit, assignf,
};
use gadgets::util::Scalar;
use eth_types::{Address, Field, ToBigEndian, ToWord, Word, H256};
use ethers_core::utils::keccak256;
use gadgets::{util::{or, select, Expr, and}, impl_expr};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, SecondPhase,
        Selector, VirtualCells,
    },
    poly::{Rotation},
};
use rand_chacha::rand_core::block;
use std::{marker::PhantomData, ops::Range, usize, default};

const BYTE_POW_BASE: u64 = 1 << 8;
const N: usize = 32;
const H: usize = 12;
const RPI_BYTES_LEN: usize = 32 * 10;
const USED_ROWS: usize = RPI_BYTES_LEN + 64;

const L1SIGNAL_IDX: usize = 0;
const PARENT_HASH: usize = 4;
const BLOCK_HASH: usize = 5;
const FIELD9_IDX: usize = 8;
const FIELD10_IDX: usize = 9;
const KECCAK_HI: usize = 10;
const KECCAK_LOW: usize = 11;


/// PublicData contains all the values that the PiCircuit receives as input
#[derive(Debug, Clone, Default)]
pub struct PublicData {
    /// l1 signal service address
    pub l1_signal_service: Word,
    /// l2 signal service address
    pub l2_signal_service: Word,
    /// l2 contract address
    pub l2_contract: Word,
    /// meta hash
    pub meta_hash: Word,
    /// block hash value
    pub block_hash: Word,
    /// the parent block hash
    pub parent_hash: Word,
    /// signal root
    pub signal_root: Word,
    /// extra message
    pub graffiti: Word,
    /// union field
    pub field9: Word, // prover[96:256]+parentGasUsed[64:96]+gasUsed[32:64]
    /// union field
    pub field10: Word, /* blockMaxGasLimit[192:256]+maxTransactionsPerBlock[128:
                        * 192]+maxBytesPerTxList[64:128] */

    // privates
    // Prover address
    prover: Address,
    // parent block gas used
    parent_gas_used: u32,
    // block gas used
    gas_used: u32,
    // blockMaxGasLimit
    block_max_gas_limit: u64,
    // maxTransactionsPerBlock: u64,
    max_transactions_per_block: u64,
    // maxBytesPerTxList: u64,
    max_bytes_per_tx_list: u64,

    block_context: BlockContext,
    chain_id: Word,
}

impl PublicData {
    fn assignments(&self) -> [(&'static str, Option<Word>, Vec<u8>); 10] {
        let res = [
            (
                "l1_signal_service",
                None,
                self.l1_signal_service.to_be_bytes().to_vec(),
            ),
            (
                "l2_signal_service",
                None,
                self.l2_signal_service.to_be_bytes().to_vec(),
            ),
            ("l2_contract", None, self.l2_contract.to_be_bytes().to_vec()),
            ("meta_hash", None, self.meta_hash.to_be_bytes().to_vec()),
            (
                "parent_hash",
                Some(self.block_context.number - 1),
                self.parent_hash.to_be_bytes().to_vec(),
            ),
            (
                "block_hash",
                Some(self.block_context.number),
                self.block_hash.to_be_bytes().to_vec(),
            ),
            ("signal_root", None, self.signal_root.to_be_bytes().to_vec()),
            ("graffiti", None, self.graffiti.to_be_bytes().to_vec()),
            (
                "prover+parentGasUsed+gasUsed",
                None,
                self.field9.to_be_bytes().to_vec(),
            ),
            (
                "blockMaxGasLimit+maxTransactionsPerBlock+maxBytesPerTxList",
                None,
                self.field10.to_be_bytes().to_vec(),
            ),
        ];
        res
    }

    /// get rpi bytes
    pub fn rpi_bytes(&self) -> Vec<u8> {
        self.assignments().iter().flat_map(|v| v.2.clone()).collect()
    }

    fn default<F: Default>() -> Self {
        Self::new::<F>(&witness::Block::default())
    }

    /// create PublicData from block and taiko
    pub fn new<F>(block: &witness::Block<F>) -> Self {
        use witness::left_shift;
        let field9 = left_shift(block.protocol_instance.prover, 96)
            + left_shift(block.protocol_instance.parent_gas_used as u64, 64)
            + left_shift(block.protocol_instance.gas_used as u64, 32);

        let field10 = left_shift(block.protocol_instance.block_max_gas_limit, 192)
            + left_shift(block.protocol_instance.max_transactions_per_block, 128)
            + left_shift(block.protocol_instance.max_bytes_per_tx_list, 64);
        PublicData {
            l1_signal_service: block.protocol_instance.l1_signal_service.to_word(),
            l2_signal_service: block.protocol_instance.l2_signal_service.to_word(),
            l2_contract: block.protocol_instance.l2_contract.to_word(),
            meta_hash: block.protocol_instance.meta_hash.hash().to_word(),
            block_hash: block.protocol_instance.block_hash.to_word(),
            parent_hash: block.protocol_instance.parent_hash.to_word(),
            signal_root: block.protocol_instance.signal_root.to_word(),
            graffiti: block.protocol_instance.graffiti.to_word(),
            prover: block.protocol_instance.prover,
            parent_gas_used: block.protocol_instance.parent_gas_used,
            gas_used: block.protocol_instance.gas_used,
            block_max_gas_limit: block.protocol_instance.block_max_gas_limit,
            max_transactions_per_block: block.protocol_instance.max_transactions_per_block,
            max_bytes_per_tx_list: block.protocol_instance.max_bytes_per_tx_list,
            field9,
            field10,
            block_context: block.context.clone(),
            chain_id: block.context.chain_id,
        }
    }

    fn get_pi(&self) -> H256 {
        let rpi_bytes = self.rpi_bytes();
        let rpi_keccak = keccak256(rpi_bytes);
        H256(rpi_keccak)
    }

    fn get_pi_hi_low(&self) -> [(&'static str, Option<Word>, Vec<u8>); 2] {
        let pi_bytes = self.get_pi().to_fixed_bytes();
        let res = [
            ("high_16_bytes_of_keccak_rpi", None, pi_bytes[..16].to_vec()),
            ("low_16_bytes_of_keccak_rpi", None, pi_bytes[16..].to_vec()),
        ];
        println!("-----res {:?}", res);
        res
    }   
}
/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct TaikoPiCircuitConfig<F: Field> {
    q_enable: Selector,
    public_input: Column<Instance>, // equality
    block_acc: Column<Advice>,
    field_gadget: FieldBytesGadget<F>,

    block_number: [Cell<F>;2], // Phase1
    keccak_output:[Cell<F>;2], // Phase2, equality

    block_table: BlockTable,
    keccak_table: KeccakTable,
    byte_table: ByteTable,

    // To annotate columns at assignment for debug purpose 
    col_configs: Vec<CellColumn<F, PiCellType>>,
}

/// Circuit configuration arguments
pub struct TaikoPiCircuitConfigArgs<F: Field> {
    /// BlockTable
    pub block_table: BlockTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// ByteTable
    pub byte_table: ByteTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PiCellType {
    Storage1,
    Storage2,
    Byte,
    Lookup(Table)
}
impl CellType for PiCellType {
    fn byte_type() -> Option<Self> {
        Some(Self::Byte)
    }
    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            1 => PiCellType::Storage1,
            2 => PiCellType::Storage2,
            _ => unimplemented!()
        }
    }
}
impl Default for PiCellType {
    fn default() -> Self {
        Self::Storage1
    }
}


impl<F: Field> SubCircuitConfig<F> for TaikoPiCircuitConfig<F> {
    type ConfigArgs = TaikoPiCircuitConfigArgs<F>;

        /// Return a new TaikoPiCircuitConfig
        fn new(
            meta: &mut ConstraintSystem<F>,
            Self::ConfigArgs {
                block_table,
                keccak_table,
                byte_table,
                challenges,
            }: Self::ConfigArgs,
        ) -> Self {
            let field_cm = CellManager::new(
                meta,
                vec![
                    (PiCellType::Byte, 32, 1, false),
                    (PiCellType::Storage1, 3, 1, false)
                ],
                0,
                1,
            );
            let state_cm = CellManager::new(
                meta,
                vec![
                    (PiCellType::Storage1, 1, 1, false),
                    (PiCellType::Storage2, 1, 2, true),
                ],
                0,
            12,
            );
            let mut cb: ConstraintBuilder<F, PiCellType> = ConstraintBuilder::new(4,  Some(field_cm.clone()), Some(challenges.evm_word()));
            cb.preload_tables(meta,
                &[
                   (PiCellType::Lookup(Keccak), &keccak_table), 
                   (PiCellType::Lookup(Bytecode), &byte_table), 
                   (PiCellType::Lookup(Block), &block_table)
                   ]
               );
            let q_enable = meta.complex_selector();
            let public_input = meta.instance_column();
            let block_acc = meta.advice_column_in(SecondPhase);
            let pi_field = FieldBytesGadget::config(&mut cb, &challenges);
            cb.set_cell_manager(state_cm.clone());
            let block_number = [();2].map(|_| cb.query_one(PiCellType::Storage1));
            let keccak_output = [();2].map(|_| cb.query_one(PiCellType::Storage2));
            meta.enable_equality(public_input);
            meta.create_gate(
                "PI acc constraints", 
                |meta| {
                    circuit!([meta, cb], {
                        // Field of PublicData
                        // start with field bytes rlc with keccak_r and increment with keccak_r
                        ifx!(pi_field.is_field.expr() => {
                            ifx!(pi_field.is_first.expr() => {
                                require!(a!(block_acc) => pi_field.keccak_field(meta, 0));
                            });
                            ifx!(not!(pi_field.is_last.expr()) => {
                                require!(
                                    a!(block_acc, 1) => a!(block_acc) * challenges.keccak_input() + pi_field.keccak_field(meta, 0)
                                );
                            })
                        } 
                        // Row with Keccak Hi/Low
                        // start with field bytes rlc with 1 << 8 and increment with evm_word
                         elsex {
                            ifx!(pi_field.is_first.expr() => {
                                require!(a!(block_acc) => pi_field.hi_low_field(meta, 0));
                            });
                            ifx!(not!(pi_field.is_last.expr()) => {
                                require!(
                                    a!(block_acc, 1) => a!(block_acc) * challenges.evm_word() + pi_field.hi_low_field(meta, 0)
                                );
                            })
                        });
                        let mut offset = PARENT_HASH;
                        for bn in &block_number {
                            require!(
                                (
                                    BlockContextFieldTag::BlockHash.expr(),
                                    bn.expr(),
                                    pi_field.evm_word_field(meta, offset)
                                ) => @PiCellType::Lookup(Table::Block), (TO_FIX)
                            );
                            offset += 1;
                        }
                        // require!(keccak_output[0].expr() => pi_field.hi_low_field(meta, KECCAK_HI));
                        // require!(keccak_output[1].expr() => pi_field.hi_low_field(meta, KECCAK_LOW));
                        // require!(
                        //     (
                        //         1.expr(),
                        //         a!(block_acc, FIELD10_IDX),
                        //         RPI_BYTES_LEN.expr(),
                        //         a!(block_acc, KECCAK_LOW)
                        //     )
                        //     => @PiCellType::Lookup(Table::Keccak), (TO_FIX)
                        // );
                    });
                    cb.build_constraints(Some(meta.query_selector(q_enable)))
                }
            );
            cb.build_equalities(meta);
            cb.build_lookups(
                meta, 
                &[field_cm.clone()],
                &[
                    (PiCellType::Byte, PiCellType::Lookup(Bytecode)),
                    (PiCellType::Lookup(Table::Keccak), PiCellType::Lookup(Table::Keccak)),
                    (PiCellType::Lookup(Table::Block), PiCellType::Lookup(Table::Block)),
                ],
                Some(q_enable)
            );
            let mut col_configs = field_cm.columns().to_vec();
            col_configs.append(&mut state_cm.columns().to_vec());
            Self {
                q_enable,
                public_input,
                block_acc,
                field_gadget: pi_field,
                block_number,
                keccak_output,
                block_table,
                keccak_table,
                byte_table,
                col_configs,
            }
        }

}

impl<F: Field> TaikoPiCircuitConfig<F> {
    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        public_data: &PublicData,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let pi_cells = layouter.assign_region(
        || "Pi",
        |mut region| {
                
                self.q_enable.enable(&mut region, 0)?;
                let mut region = CachedRegion::new(&mut region);
                region.annotate_columns(&self.col_configs);

                let mut block_acc = F::ZERO;
                let mut evm_word_r = F::ZERO;
                let mut keccak_r = F::ZERO;
                let hi_low_r = F::from(BYTE_POW_BASE);
                challenges.evm_word().map(|v| evm_word_r = v);
                challenges.keccak_input().map(|v| keccak_r = v);

                let mut assignments = public_data.assignments().to_vec();
                assignments.append(&mut public_data.get_pi_hi_low().to_vec());
                let mut i = 0;
                let mut pi_cells = Vec::new();
                for (annotation, block_number, bytes) in assignments {
                    println!("{:?} {:?}, len {:?}", i, annotation, bytes.len());
                    match i {
                        L1SIGNAL_IDX..=FIELD10_IDX => {
                            let field = self.field_gadget.assign(&mut region, i, keccak_r, &bytes)?;
                            block_acc = self.assign_acc(&mut region, i, keccak_r, block_acc, field)?;
                            if let Some(block_number) = block_number {
                                println!("  block_number {:?} => {:?} {:?}", block_number, self.block_number[i - PARENT_HASH].expr().identifier(), field);
                                println!("  {:?}", bytes);
                                assign!(region, self.block_number[i - PARENT_HASH], 0 => block_number.as_u64().scalar())?;
                            }
                        }
                        KECCAK_HI..=KECCAK_LOW => {
                            let mut bytes = bytes.clone();
                            bytes.reverse();
                            let field = self.field_gadget.assign(&mut region, i, hi_low_r, &bytes)?;
                            block_acc = self.assign_acc(&mut region, i, evm_word_r, block_acc, field)?;
                            pi_cells.push(assign!(region, self.keccak_output[i - KECCAK_HI], 0 => field)?);
                            println!("self.field_gadget.assign_bytes {:?}, {:?}", bytes, field);
                        },
                        _ => unimplemented!()
                    }
                    i += 1;
                }
                Ok(pi_cells)
            }
        )?;
        for (i, cell) in pi_cells.iter().enumerate() {
            layouter.constrain_instance(cell.cell(), self.public_input, i)?;
            println!("pi_cell {:?}", cell);
        }
        Ok(())
    }

    pub(crate) fn assign_acc(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        acc_r: F,
        prev: F,
        other: F,
    ) -> Result<F, Error> {
        let next = prev * acc_r + other;
        assign!(region, (self.block_acc, offset) => next)?;
        Ok(next)
    }
}


#[derive(Clone, Debug)]
struct FieldBytesGadget<F> {
    bytes: [Cell<F>; N],
    is_field: Cell<F>,
    is_first: Cell<F>,
    is_last: Cell<F>,
    word_r: Expression<F>,
    keccak_r: Expression<F>,
}

impl<F: Field> FieldBytesGadget<F> {

    fn config(cb: &mut ConstraintBuilder<F, PiCellType>, challenges: &Challenges<Expression<F>>) -> Self {
        Self {
            bytes: cb.query_bytes(),
            is_field: cb.query_bool(),
            is_first: cb.query_bool(),
            is_last: cb.query_bool(),
            word_r: challenges.evm_word().expr(),
            keccak_r: challenges.keccak_input().expr(),
        }
    } 

    fn bytes_expr(&self, meta: &mut VirtualCells<F>, idx: usize) -> Vec<Expression<F>> {
        self.bytes.iter().map(|b| b.rot(meta, idx)).collect()
    }

    /// RLC of bytes of a field with evm_word 1<<8
    fn hi_low_field(&self, meta: &mut VirtualCells<F>, idx: usize) -> Expression<F> {
        self.bytes_expr(meta, idx).rlc(&BYTE_POW_BASE.expr())
    }

    /// RLC of bytes of a field with evm_word
    fn evm_word_field(&self, meta: &mut VirtualCells<F>, idx: usize) -> Expression<F> {
        self.bytes_expr(meta, idx).rlc_rev(&self.word_r)
    }

    /// RLC of bytes of a field with keccak_input
    fn keccak_field(&self, meta: &mut VirtualCells<F>, idx: usize) -> Expression<F> {
        self.bytes_expr(meta, idx).rlc(&self.keccak_r)
    }

    // ------------------ Assign ------------------

    /// Returns the rlc of given bytes
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        r: F,
        bytes: &[u8],
    ) -> Result<F, Error> {
        // Assign the bytes
        for (byte, cell) in bytes.iter().zip(self.bytes.iter()) {
            assign!(region, cell, offset => byte.scalar())?;
        }
        self.assign_flags(region, offset)?;
        Ok(bytes.rlc_value(r))
    }

    pub(crate) fn assign_flags(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
    ) -> Result<(), Error> {
        match offset {
            L1SIGNAL_IDX..=FIELD10_IDX => {
                assign!(region, self.is_field, offset => true.scalar())?;
                if offset == L1SIGNAL_IDX {
                    assign!(region, self.is_first, offset => true.scalar())?;
                } else {
                    assign!(region, self.is_first, offset => false.scalar())?;
                }
                if offset == FIELD10_IDX {
                    assign!(region, self.is_last, offset => true.scalar())?;
                } else {
                    assign!(region, self.is_last, offset => false.scalar())?;   
                }
            },
            KECCAK_HI => {
                assign!(region, self.is_first, offset => true.scalar())?;
                assign!(region, self.is_field, offset => false.scalar())?;
                assign!(region, self.is_last, offset => false.scalar())?;
            },
            KECCAK_LOW => {
                assign!(region, self.is_first, offset => false.scalar())?;
                assign!(region, self.is_field, offset => false.scalar())?;
                assign!(region, self.is_last, offset => true.scalar())?;
            },
            _ => unreachable!(),
        };
        Ok(())
    }
}


/// Public Inputs Circuit
#[derive(Clone, Default, Debug)]
pub struct TaikoPiCircuit<F: Field> {
    /// PublicInputs data known by the verifier
    pub public_data: PublicData,
    _marker: PhantomData<F>,
}

impl<F: Field> TaikoPiCircuit<F> {
    /// Creates a new TaikoPiCircuit
    pub fn new(public_data: PublicData) -> Self {
        Self {
            public_data,
            _marker: PhantomData,
        }
    }
}


impl<F: Field> SubCircuit<F> for TaikoPiCircuit<F> {
    type Config = TaikoPiCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn min_num_rows_block(_block: &witness::Block<F>) -> (usize, usize) {
        (USED_ROWS, USED_ROWS)
    }

    fn new_from_block(block: &witness::Block<F>) -> Self {
        TaikoPiCircuit::new(PublicData::new(block))
    }

    /// Compute the public inputs for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        let keccak_rpi = self.public_data.get_pi();
        let keccak_hi = keccak_rpi
            .to_fixed_bytes()
            .iter()
            .take(16)
            .fold(F::ZERO, |acc, byte| {
                acc * F::from(BYTE_POW_BASE) + F::from(*byte as u64)
            });

        let keccak_lo = keccak_rpi
            .to_fixed_bytes()
            .iter()
            .skip(16)
            .fold(F::ZERO, |acc, byte| {
                acc * F::from(BYTE_POW_BASE) + F::from(*byte as u64)
            });

        let public_inputs = vec![keccak_hi, keccak_lo];
        vec![public_inputs]
    }

    /// Make the assignments to the PiCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.byte_table.load(layouter)?;
        config.assign(layouter, &self.public_data, challenges)
    }
}


// We define the PiTestCircuit as a wrapper over PiCircuit extended to take the
// generic const parameters MAX_TXS and MAX_CALLDATA.  This is necessary because
// the trait Circuit requires an implementation of `configure` that doesn't take
// any circuit parameters, and the PiCircuit defines gates that use rotations
// that depend on MAX_TXS and MAX_CALLDATA, so these two values are required
// during the configuration.
/// Test Circuit for PiCircuit
#[cfg(any(feature = "test", test))]
#[derive(Default, Clone)]
pub struct TaikoPiTestCircuit<F: Field>(pub TaikoPiCircuit<F>);

#[cfg(any(feature = "test", test))]
impl<F: Field> Circuit<F> for TaikoPiTestCircuit<F> {
    type Config = (TaikoPiCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let block_table = BlockTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let byte_table = ByteTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);
        (
            TaikoPiCircuitConfig::new(
                meta,
                TaikoPiCircuitConfigArgs {
                    block_table,
                    keccak_table,
                    byte_table,
                    challenges: challenge_exprs,
                },
            ),
            challenges,
        )
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        let public_data = &self.0.public_data;
        // assign block table
        let randomness = challenges.evm_word();
        config
            .block_table
            .load(&mut layouter, &public_data.block_context, randomness)?;
        // assign keccak table
        config
            .keccak_table
            .dev_load(&mut layouter, vec![&public_data.rpi_bytes()], &challenges)?;
        config.byte_table.load(&mut layouter)?;

        self.0.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

#[cfg(test)]
mod taiko_pi_circuit_test {

    use super::*;

    use eth_types::ToScalar;
    use halo2_proofs::{
        dev::{MockProver, VerifyFailure},
        halo2curves::bn256::Fr,
    };
    use lazy_static::lazy_static;
    use pretty_assertions::assert_eq;

    lazy_static! {
        static ref OMMERS_HASH: H256 = H256::from_slice(
            &hex::decode("1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
                .unwrap(),
        );
    }

    fn run<F: Field>(
        k: u32,
        public_data: PublicData,
        pi: Option<Vec<Vec<F>>>,
    ) -> Result<(), Vec<VerifyFailure>> {
        let circuit = TaikoPiTestCircuit::<F>(TaikoPiCircuit::new(public_data));
        let public_inputs = pi.unwrap_or_else(|| circuit.0.instance());
        println!("{:?}", public_inputs);
        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        prover.verify()
    }

    fn mock_public_data() -> PublicData {
        let mut public_data = PublicData::default::<Fr>();
        public_data.meta_hash = OMMERS_HASH.to_word();
        public_data.block_hash = OMMERS_HASH.to_word();
        public_data.block_context.block_hash = OMMERS_HASH.to_word();
        public_data.block_context.history_hashes = vec![Default::default(); 256];
        public_data.block_context.number = 300.into();
        public_data
    }

    #[test]
    fn test_default_pi() {
        let public_data = mock_public_data();

        let k = 17;
        assert_eq!(run::<Fr>(k, public_data, None), Ok(()));
    }

    #[test]
    fn test_fail_pi_hash() {
        let public_data = mock_public_data();

        let k = 17;
        match run::<Fr>(k, public_data, Some(vec![vec![Fr::zero(), Fr::one()]])) {
            Ok(_) => unreachable!("this case must fail"),
            Err(errs) => {
                assert_eq!(errs.len(), 4);
                for err in errs {
                    match err {
                        VerifyFailure::Permutation { .. } => return,
                        _ => unreachable!("unexpected error"),
                    }
                }
            }
        }
    }

    #[test]
    fn test_fail_pi_prover() {
        let mut public_data = mock_public_data();
        let address_bytes = [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        ];

        public_data.prover = Address::from_slice(&address_bytes);

        let prover: Fr = public_data.prover.to_scalar().unwrap();
        let k = 17;
        match run::<Fr>(
            k,
            public_data,
            Some(vec![vec![prover, Fr::zero(), Fr::one()]]),
        ) {
            Ok(_) => unreachable!("this case must fail"),
            Err(errs) => {
                assert_eq!(errs.len(), 4);
                for err in errs {
                    match err {
                        VerifyFailure::Permutation { .. } => return,
                        _ => unreachable!("unexpected error"),
                    }
                }
            }
        }
    }

    #[test]
    fn test_simple_pi() {
        let mut public_data = mock_public_data();
        let chain_id = 1337u64;
        public_data.chain_id = Word::from(chain_id);

        let k = 17;
        assert_eq!(run::<Fr>(k, public_data, None), Ok(()));
    }

    #[test]
    fn test_verify() {
        let mut block = witness::Block::<Fr>::default();

        block.eth_block.parent_hash = *OMMERS_HASH;
        block.eth_block.hash = Some(*OMMERS_HASH);
        block.protocol_instance.block_hash = *OMMERS_HASH;
        block.protocol_instance.parent_hash = *OMMERS_HASH;
        block.context.history_hashes = vec![OMMERS_HASH.to_word()];
        block.context.block_hash = OMMERS_HASH.to_word();
        block.context.number = 300.into();

        let public_data = PublicData::new(&block);

        let k = 17;

        assert_eq!(run::<Fr>(k, public_data, None), Ok(()));
    }
}
//! Use the hash value as public input.

use crate::{
    assign,
    evm_circuit::table::Table::*,
    evm_circuit::{util::{constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon}, rlc}, table::Table},
    table::{byte_table::ByteTable, BlockContextFieldTag, BlockTable, KeccakTable, LookupTable},
    util::{Challenges, SubCircuitConfig, SubCircuit},
    circuit_tools::{
        constraint_builder::{ConstraintBuilder, RLCable, RLCChainable, TO_FIX, COMPRESS, REDUCE, RLCableValue},
        cell_manager::{CellManager, CellType, Cell}, gadgets::{IsEqualGadget, IsZeroGadget}, cached_region::{CachedRegion, self},
    },
    
    witness::{self, BlockContext}, circuit,
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
    fn assignments(&self) -> [(&'static str, Option<Word>, [u8; 32]); 10] {
        let res = [
            (
                "l1_signal_service",
                None,
                self.l1_signal_service.to_be_bytes(),
            ),
            (
                "l2_signal_service",
                None,
                self.l2_signal_service.to_be_bytes(),
            ),
            ("l2_contract", None, self.l2_contract.to_be_bytes()),
            ("meta_hash", None, self.meta_hash.to_be_bytes()),
            (
                "parent_hash",
                Some(self.block_context.number - 1),
                self.parent_hash.to_be_bytes(),
            ),
            (
                "block_hash",
                Some(self.block_context.number),
                self.block_hash.to_be_bytes(),
            ),
            ("signal_root", None, self.signal_root.to_be_bytes()),
            ("graffiti", None, self.graffiti.to_be_bytes()),
            (
                "prover+parentGasUsed+gasUsed",
                None,
                self.field9.to_be_bytes(),
            ),
            (
                "blockMaxGasLimit+maxTransactionsPerBlock+maxBytesPerTxList",
                None,
                self.field10.to_be_bytes(),
            ),
        ];
        res.iter().for_each(|field|{
            println!("{:?}, len {:?}", field.0, field.2.len());
        });
        res
    }

    /// get rpi bytes
    pub fn rpi_bytes(&self) -> Vec<u8> {
        self.assignments().iter().flat_map(|v| v.2).collect()
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
}
/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct TaikoPiCircuitConfig<F: Field> {
    q_enable: Selector,
    public_input: Column<Instance>,
    q_state: Column<Advice>,
    block_acc: Column<Advice>,
    field_gadget: FieldBytesGadget<F>,


    block_table: BlockTable,
    keccak_table: KeccakTable,
    byte_table: ByteTable,
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
            let cm = CellManager::new(
                meta,
                vec![
                    (PiCellType::Byte, 32, 1, false),
                    (PiCellType::Storage1, 2, 1, false),
                    (PiCellType::Storage2, 2, 2, false),
                    ],
                    0,
                    H,
            );
            let mut cb: ConstraintBuilder<F, PiCellType> =  ConstraintBuilder::new(4,  Some(cm.clone()), Some(challenges.evm_word()));
            cb.preload_tables(meta,
                &[
                   (PiCellType::Lookup(Keccak), &keccak_table), 
                   (PiCellType::Lookup(Bytecode), &byte_table), 
                   (PiCellType::Lookup(Block), &block_table)
                   ]
               );
            
            let q_enable = meta.selector();
            let public_input = meta.instance_column();
            let q_state = meta.advice_column();
            let block_acc = meta.advice_column_in(SecondPhase);
            let mut field_gadget = FieldBytesGadget::config(&mut cb, challenges.clone());
            meta.create_gate(
                "PI acc constraints", 
                |meta| {
                    circuit!([meta, cb], {
                        for idx in 0..H {
                            match idx {
                                L1SIGNAL_IDX => {
                                    require!(a!(block_acc, idx) => field_gadget.evm_word_field(idx));
                                },
                                L1SIGNAL_IDX..=FIELD9_IDX => {
                                    require!(a!(block_acc, idx + 1) => field_gadget.block_input_acc(a!(block_acc), idx + 1));
                                    if idx == PARENT_HASH || idx == BLOCK_HASH {
                                        let block_number = field_gadget.set_block_number(&mut cb);
                                        // require!(
                                        //     (
                                        //         BlockContextFieldTag::BlockHash.expr(),
                                        //         block_number.expr(),
                                        //         field_gadget.evm_word_field(idx)
                                        //     ) => @PiCellType::Lookup(Table::Block), (TO_FIX)
                                        // );
                                    }
                                }
                                FIELD10_IDX => {
                                    field_gadget.set_keccak_input(&mut cb, block_acc.clone());
                                    require!(a!(block_acc, idx + 1) => field_gadget.keccak_field(KECCAK_HI));
                                },
                                KECCAK_HI => {
                                    require!(a!(block_acc, idx + 1) => field_gadget.keccak_output_acc(a!(block_acc), idx + 1));
                                    require!(x!(public_input) => a!(block_acc, idx));
                                },
                                KECCAK_LOW => {
                                    // require!(
                                    //     (
                                    //         1.expr(),
                                    //         field_gadget.keccak_input.clone().unwrap().expr(),
                                    //         RPI_BYTES_LEN.expr(),
                                    //         a!(block_acc)
                                    //     )
                                    //     => @PiCellType::Lookup(Table::Keccak), (TO_FIX)
                                    // );
                                    require!(x!(public_input) => a!(block_acc, idx));
                                }
                                _ => unimplemented!()
                            }
                        }
                    });
                    cb.build_constraints(Some(meta.query_selector(q_enable)))
                }
            );
            cb.build_equalities(meta);
            cb.build_lookups(
                meta, 
                &[cm], 
                &[
                    (PiCellType::Byte, PiCellType::Lookup(Bytecode)),
                    (PiCellType::Lookup(Table::Keccak), PiCellType::Lookup(Table::Keccak)),
                    (PiCellType::Lookup(Table::Block), PiCellType::Lookup(Table::Block)),
                ]
            );
            Self {
                q_enable,
                public_input,
                q_state,
                block_acc,
                field_gadget,
                block_table,
                keccak_table,
                byte_table,
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
        layouter.assign_region(
            || "Pi",
            |mut region| {
                self.q_enable.enable(&mut region, 0);
                let mut cached_region = CachedRegion::new(&mut region);
                let mut block_acc = F::ZERO;
                let mut r = F::ZERO;
                let mut offset = 0;
                println!("\n===================");
                for (i, (annotation, block_number, bytes)) in public_data
                    .assignments()
                    .iter()
                    .enumerate() {
                        println!("{:?}, len {:?}， offset {:?}", annotation, bytes.len(), offset);
                        match i {
                            i if i <= FIELD10_IDX => {
                                challenges.keccak_input().map(|v| r = v);
                                block_acc += self.field_gadget.assign_bytes(&mut cached_region, r, offset, i, bytes.as_ref())?;
                                let block_acc_cell = assign!(cached_region, (self.block_acc, offset) => block_acc)?;
                                if let Some(block_number) = block_number {
                                    println!("  block_number {:?}", block_number);
                                    self.field_gadget.assign_block_number(
                                        &mut cached_region, 
                                        offset, 
                                        block_number.as_u64().scalar()
                                    )?;                                    
                                }
                                
                                if i == FIELD10_IDX {
                                    println!("  PiState::Field10 {:?}", block_acc);
                                    self.field_gadget.assign_keccak_acc(
                                        &mut cached_region, 
                                        offset,
                                        block_acc_cell
                                    )?;
                                    block_acc = F::ZERO;
                                }
                            },
                            i if i == KECCAK_HI => {
                                println!("  PiState::Keccak {:?}", block_acc);
                                challenges.evm_word().map(|v| r = v);
                                block_acc += self.field_gadget.assign_bytes(&mut cached_region, r, offset, i, bytes.as_ref())?;
                                assign!(cached_region, (self.block_acc, offset) => block_acc)?;

                            },
                            i if i == KECCAK_LOW => {
                                println!("  PiState::Keccak {:?}", block_acc);
                                challenges.evm_word().map(|v| r = v);
                                block_acc += self.field_gadget.assign_bytes(&mut cached_region, r, offset, i, bytes.as_ref())?;
                                assign!(cached_region, (self.block_acc, offset) => block_acc)?;

                            },
                            _ => unreachable!(),
                        }
                        offset += 1;
                    }
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
struct FieldBytesGadget<F> {
    challenges: Option<Challenges<Expression<F>>>,
    bytes: [[Cell<F>; N]; H],
    block_number: Option<Cell<F>>,
    keccak_input: Option<Cell<F>>,

    keccak_exp: Expression<F>,
    evm_exp: Expression<F>
}

impl<F: Field> FieldBytesGadget<F> {

    fn config(cb: &mut ConstraintBuilder<F, PiCellType>, challenges: Challenges<Expression<F>>) -> Self {
        let mut bytes = Vec::new();
        for idx in 0..H {
            bytes.push(cb.query_bytes());
        }
        let keccak_exp = (0..N)
            .fold(1.expr(), |acc: Expression<F>, _|{
                acc * challenges.keccak_input()
            });
        let evm_exp = (0..N)
            .fold(1.expr(), |acc: Expression<F>, _|{
                acc * challenges.evm_word()
            });  
        Self {
            challenges: Some(challenges),
            bytes: bytes.try_into().unwrap(),
            block_number: None,
            keccak_input: None,
            keccak_exp,
            evm_exp,
        }
    } 

    fn bytes_expr(&self, idx: usize) -> Vec<Expression<F>> {
        self.bytes[idx].iter().map(|b| b.expr()).collect()
    }

    /// RLC of bytes of a field with evm_word 1<<8
    fn hi_low_fields_(&self, idx: usize) -> Expression<F> {
        self.bytes_expr(idx).rlc(&BYTE_POW_BASE.expr())
    }

    /// RLC of bytes of a field with evm_word
    fn evm_word_field(&self, idx: usize) -> Expression<F> {
        let r = self.challenges.clone().unwrap().evm_word().expr();
        self.bytes_expr(idx).rlc(&r)
    }

    /// RLC of bytes of a field with keccak_input
    fn keccak_field(&self, idx: usize) -> Expression<F> {
        let r = self.challenges.clone().unwrap().keccak_input().expr();
        self.bytes_expr(idx).rlc(&r)
    }
    
    // ------------------ Acc ------------------

    /// Next value of block field bytes RLC accumulator for keccak input, per row without offset
    fn block_input_acc(&self, prev_field: Expression<F>, idx: usize) -> Expression<F> {
        let r = self.challenges.clone().unwrap().keccak_input().expr();
        prev_field * self.keccak_exp.expr() + self.keccak_field(idx)
    }

    /// Next value of keccak output hi low bytes accumulator, per row without offset
    fn keccak_output_acc(&self, hi: Expression<F>, idx: usize) -> Expression<F> {
        let low = self.hi_low_fields_(idx);
        hi * self.evm_exp.expr() + low
    }

    // ------------------ Set Cell ------------------


    /// Init a cell for keccak input at the last row of all block fields
    fn set_keccak_input(
        &mut self, 
        cb: &mut ConstraintBuilder<F, PiCellType>,
        block_acc: Column<Advice>,
    ) -> Expression<F> {
        let keccak_input = cb.query_cell_with_type(PiCellType::Storage2);
        cb.enable_equality(keccak_input.column());
        cb.enable_equality(block_acc);
        self.keccak_input = Some(keccak_input.clone());
        keccak_input.expr()
    }

    /// Init a cell for block idx when we need to lookup block table
    fn set_block_number(&mut self, cb: &mut ConstraintBuilder<F, PiCellType>) -> Expression<F> {
        let block_number = cb.query_default();
        self.block_number = Some(block_number.clone());
        block_number.expr()
    }

    // ------------------ Assign ------------------

    /// Returns the rlc of given bytes
    pub(crate) fn assign_bytes(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        r: F,
        offset: usize,
        idx: usize,
        bytes: &[u8],
    ) -> Result<F, Error> {
        // Assign the bytes
        for (byte, column) in bytes.iter().zip(self.bytes[idx].iter()) {
            assign!(region, (column.column(), offset) => byte.scalar())?;
        }
        let mut rlc = bytes.rlc_value(r);
        Ok(rlc)
    }

    pub(crate) fn assign_block_number(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block_number: F,
    ) -> Result<(), Error> {
        if let Some(c) = &self.block_number {
            c.assign(region, offset, block_number)?;
            Ok(())
        } else {
            Err(Error::Synthesis)
        }
    }

    pub(crate) fn assign_keccak_acc(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block_acc_cell: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        if let Some(c) = &self.keccak_input {
            block_acc_cell.copy_advice(
                || "Copy block acc into cell for keccak input", 
                region.inner(), 
                c.column(), 
                offset
            )?;
            Ok(())
        } else {
            Err(Error::Synthesis)
        }
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

//! Use the hash value as public input.

use crate::{
    evm_circuit::util::constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon},
    table::{byte_table::ByteTable, BlockContextFieldTag, BlockTable, KeccakTable, LookupTable},
    util::{random_linear_combine_word as rlc, Challenges, SubCircuit, SubCircuitConfig},
    circuit_tools::{
        constraint_builder::ConstraintBuilder,
        cell_manager::{CellManager, CellType},
    },
    
    witness::{self, BlockContext}, circuit,
};
use eth_types::{Address, Field, ToBigEndian, ToWord, Word, H256};
use ethers_core::utils::keccak256;
use gadgets::util::{or, select, Expr};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, SecondPhase,
        Selector,
    },
    poly::Rotation,
};
use std::marker::PhantomData;

const MAX_DEGREE: usize = 9;
const RPI_CELL_IDX: usize = 0;
const RPI_RLC_ACC_CELL_IDX: usize = 1;
const BYTE_POW_BASE: u64 = 1 << 8;
const RPI_BYTES_LEN: usize = 32 * 10;
// 10 fields * 32B + lo(16B) + hi(16B) + keccak(32B)
const USED_ROWS: usize = RPI_BYTES_LEN + 64;

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
        [
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
        ]
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
    rpi_field_bytes: Column<Advice>,
    rpi_field_bytes_acc: Column<Advice>,
    rpi_rlc_acc: Column<Advice>,
    q_field_start: Selector,
    q_field_step: Selector,
    q_field_end: Selector,
    is_field_rlc: Column<Fixed>,

    byte_table: ByteTable,

    pi: Column<Instance>, // keccak_hi, keccak_lo

    q_keccak: Selector,
    keccak_table: KeccakTable,

    // External tables
    q_block_table: Selector,
    block_index: Column<Advice>,
    block_table: BlockTable,

    _marker: PhantomData<F>,
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

/// 
#[derive(Clone, Copy, Debug, num_enum::Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum PiCellType {
    ///
    #[num_enum(default)]
    Storage,
}
impl CellType for PiCellType {
    fn byte_type() -> Option<Self> {
        unimplemented!()
    }
    fn storage_for_phase(phase: u8) -> Self {
        unimplemented!()
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
        let rpi_field_bytes = meta.advice_column();
        let rpi_field_bytes_acc = meta.advice_column_in(SecondPhase);
        let rpi_rlc_acc = meta.advice_column_in(SecondPhase);
        let q_field_start = meta.complex_selector();
        let q_field_step = meta.complex_selector();
        let q_field_end = meta.complex_selector();
        let is_field_rlc = meta.fixed_column();

        let pi = meta.instance_column();

        let q_keccak = meta.complex_selector();
        let q_block_table = meta.complex_selector();
        let block_index = meta.advice_column();

        meta.enable_equality(rpi_field_bytes);
        meta.enable_equality(rpi_field_bytes_acc);
        meta.enable_equality(rpi_rlc_acc);
        meta.enable_equality(block_table.value);
        meta.enable_equality(pi);

        let cm = CellManager::new(
            meta,
            vec![
                (PiCellType::Storage, 3, 1, false),
            ],
            0,
            1,
        );
        let mut cb: ConstraintBuilder<F, PiCellType> =  ConstraintBuilder::new(4,  Some(cm), Some(challenges.evm_word()));


        meta.create_gate("Pi Gate", |meta| {
            circuit!([meta, cb], {
                cb.add_constraint("", 0.expr());
            });
            cb.build_constraints()
        });

        // field bytes
        meta.create_gate(
            "rpi_field_bytes_acc[i+1] = rpi_field_bytes_acc[i] * t + rpi_bytes[i+1]",
            |meta| {
                let mut bcb = BaseConstraintBuilder::new(MAX_DEGREE);

                let q_field_step = meta.query_selector(q_field_step);
                let rpi_field_bytes_acc_next =
                    meta.query_advice(rpi_field_bytes_acc, Rotation::next());
                let rpi_field_bytes_acc = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
                let rpi_field_bytes_next = meta.query_advice(rpi_field_bytes, Rotation::next());
                let is_field_rlc = meta.query_fixed(is_field_rlc, Rotation::next());
                let randomness = challenges.evm_word();
                let t = select::expr(is_field_rlc, randomness, BYTE_POW_BASE.expr());
                bcb.require_equal(
                    "rpi_field_bytes_acc[i+1] = rpi_field_bytes_acc[i] * t + rpi_bytes[i+1]",
                    rpi_field_bytes_acc_next,
                    rpi_field_bytes_acc * t + rpi_field_bytes_next,
                );
                bcb.gate(q_field_step)
            },
        );
        meta.create_gate("rpi_field_bytes_acc[0] = rpi_field_bytes[0]", |meta| {
            let mut bcb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_field_start = meta.query_selector(q_field_start);
            let rpi_field_bytes_acc = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
            let rpi_field_bytes = meta.query_advice(rpi_field_bytes, Rotation::cur());

            bcb.require_equal(
                "rpi_field_bytes_acc[0] = rpi_field_bytes[0]",
                rpi_field_bytes_acc,
                rpi_field_bytes,
            );
            bcb.gate(q_field_start)
        });

        // keccak in rpi
        meta.lookup_any("keccak(rpi)", |meta| {
            let q_keccak = meta.query_selector(q_keccak);
            let rpi_rlc = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
            let output = meta.query_advice(rpi_rlc_acc, Rotation::cur());
            [1.expr(), rpi_rlc, RPI_BYTES_LEN.expr(), output]
                .into_iter()
                .zip(keccak_table.table_exprs(meta).into_iter())
                .map(|(arg, table)| (q_keccak.expr() * arg, table))
                .collect::<Vec<_>>()
        });

        // in block table
        meta.lookup_any("in block table", |meta| {
            let q_block_table = meta.query_selector(q_block_table);
            let block_index = meta.query_advice(block_index, Rotation::cur());
            let block_hash = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
            [
                BlockContextFieldTag::BlockHash.expr(),
                block_index,
                block_hash,
            ]
            .into_iter()
            .zip(block_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (q_block_table.expr() * arg, table))
            .collect::<Vec<_>>()
        });
        // is byte
        meta.lookup_any("is_byte", |meta| {
            let q_field_step = meta.query_selector(q_field_start);
            let q_field_end = meta.query_selector(q_field_end);
            let is_field = or::expr([q_field_step, q_field_end]);
            let rpi_field_bytes = meta.query_advice(rpi_field_bytes, Rotation::cur());
            [rpi_field_bytes]
                .into_iter()
                .zip(byte_table.table_exprs(meta).into_iter())
                .map(|(arg, table)| (is_field.expr() * arg, table))
                .collect::<Vec<_>>()
        });

        Self {
            rpi_field_bytes,
            rpi_field_bytes_acc,
            rpi_rlc_acc,
            q_field_start,
            q_field_step,
            q_field_end,

            byte_table,
            is_field_rlc,

            pi, // keccak_hi, keccak_lo

            q_keccak,
            keccak_table,

            q_block_table,
            block_index,
            block_table,

            _marker: PhantomData,
        }
    }
}

impl<F: Field> TaikoPiCircuitConfig<F> {
    #[allow(clippy::too_many_arguments)]
    fn assign_pi_field(
        &self,
        region: &mut Region<'_, F>,
        offset: &mut usize,
        _annotation: &'static str,
        field_bytes: &[u8],
        rpi_rlc_acc: &mut Value<F>,
        challenges: &Challenges<Value<F>>,
        keccak_hi_lo: bool,
        block_number: Option<Word>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let len = field_bytes.len();
        let mut field_rlc_acc = Value::known(F::ZERO);
        let (use_rlc, t) = if len * 8 > F::CAPACITY as usize {
            (F::ONE, challenges.evm_word())
        } else {
            (F::ZERO, Value::known(F::from(BYTE_POW_BASE)))
        };

        let randomness = if keccak_hi_lo {
            challenges.evm_word()
        } else {
            challenges.keccak_input()
        };
        let mut cells = vec![None; field_bytes.len() + 2];
        for (i, byte) in field_bytes.iter().enumerate() {
            let row_offset = *offset + i;

            region.assign_fixed(
                || "is_field_rlc",
                self.is_field_rlc,
                row_offset,
                || Value::known(use_rlc),
            )?;

            // assign field bytes
            let field_byte_cell = region.assign_advice(
                || "field bytes",
                self.rpi_field_bytes,
                row_offset,
                || Value::known(F::from(*byte as u64)),
            )?;

            field_rlc_acc = field_rlc_acc * t + Value::known(F::from(*byte as u64));
            let rpi_cell = region.assign_advice(
                || "field bytes acc",
                self.rpi_field_bytes_acc,
                row_offset,
                || field_rlc_acc,
            )?;
            *rpi_rlc_acc = *rpi_rlc_acc * randomness + Value::known(F::from(*byte as u64));
            let rpi_rlc_acc_cell = region.assign_advice(
                || "rpi_rlc_acc",
                self.rpi_rlc_acc,
                row_offset,
                || *rpi_rlc_acc,
            )?;
            // setup selector
            if i == 0 {
                self.q_field_start.enable(region, row_offset)?;
            }
            // the last offset of field
            if i == field_bytes.len() - 1 {
                self.q_field_end.enable(region, row_offset)?;
                cells[RPI_CELL_IDX] = Some(rpi_cell);
                cells[RPI_RLC_ACC_CELL_IDX] = Some(rpi_rlc_acc_cell);
                if let Some(block_number) = block_number {
                    self.q_block_table.enable(region, row_offset)?;
                    region.assign_advice(
                        || "block_index",
                        self.block_index,
                        row_offset,
                        || Value::known(F::from(block_number.as_u64())),
                    )?;
                }
            } else {
                self.q_field_step.enable(region, row_offset)?;
            }
            cells[2 + i] = Some(field_byte_cell);
        }
        *offset += field_bytes.len();
        Ok(cells.into_iter().map(|cell| cell.unwrap()).collect())
    }

    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        public_data: &PublicData,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let pi = layouter.assign_region(
            || "region 0",
            |ref mut region| {
                let mut rpi_rlc_acc = Value::known(F::ZERO);
                let mut offset = 0;
                let mut rpi_rlc_acc_cell = None;
                for (annotation, block_number, field_bytes) in public_data.assignments() {
                    let cells = self.assign_pi_field(
                        region,
                        &mut offset,
                        annotation,
                        &field_bytes,
                        &mut rpi_rlc_acc,
                        challenges,
                        false,
                        block_number,
                    )?;
                    rpi_rlc_acc_cell = Some(cells[RPI_RLC_ACC_CELL_IDX].clone());
                }

                // input_rlc in self.rpi_field_bytes_acc
                // input_len in self.rpi_len_acc
                // output_rlc in self.rpi_rlc_acc
                let keccak_row = offset;
                let rpi_rlc_acc_cell = rpi_rlc_acc_cell.unwrap();
                rpi_rlc_acc_cell.copy_advice(
                    || "keccak(rpi)_input",
                    region,
                    self.rpi_field_bytes_acc,
                    keccak_row,
                )?;
                let keccak = public_data.get_pi();
                let mut keccak_input = keccak.to_fixed_bytes();
                keccak_input.reverse();
                let keccak_rlc = challenges
                    .evm_word()
                    .map(|randomness| rlc(keccak_input, randomness));
                let keccak_output_cell = region.assign_advice(
                    || "keccak(rpi)_output",
                    self.rpi_rlc_acc,
                    keccak_row,
                    || keccak_rlc,
                )?;
                self.q_keccak.enable(region, keccak_row)?;

                rpi_rlc_acc = Value::known(F::ZERO);
                offset += 1;
                let mut pi = Vec::with_capacity(2);

                for (idx, (annotation, field_bytes)) in [
                    (
                        "high_16_bytes_of_keccak_rpi",
                        &keccak.to_fixed_bytes()[..16],
                    ),
                    ("low_16_bytes_of_keccak_rpi", &keccak.to_fixed_bytes()[16..]),
                ]
                .into_iter()
                .enumerate()
                {
                    let cells = self.assign_pi_field(
                        region,
                        &mut offset,
                        annotation,
                        field_bytes,
                        &mut rpi_rlc_acc,
                        challenges,
                        true,
                        None,
                    )?;
                    pi.push(cells[RPI_CELL_IDX].clone());
                    if idx == 1 {
                        region.constrain_equal(
                            keccak_output_cell.cell(),
                            cells[RPI_RLC_ACC_CELL_IDX].cell(),
                        )?;
                    }
                }

                Ok(pi)
            },
        )?;
        for (idx, cell) in pi.into_iter().enumerate() {
            layouter.constrain_instance(cell.cell(), self.pi, idx)?;
        }
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

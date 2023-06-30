//! Use the hash value as public input.

use crate::{
    evm_circuit::util::constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon},
    table::{BlockTable, KeccakTable},
    util::{random_linear_combine_word as rlc, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use eth_types::{
    geth_types::BlockConstants, Address, Field, ToBigEndian, ToLittleEndian, ToScalar, ToWord,
    Word, H256,
};
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

const MAX_DEGREE: usize = 10;
const MIN_DEGREE: usize = 8;
const RPI_CELL_IDX: usize = 0;
const RPI_RLC_ACC_CELL_IDX: usize = 1;
const BYTE_POW_BASE: u64 = 1 << 8;
const RPI_BYTES_LEN: usize = 32 * 10;
const USED_ROWS: usize = RPI_BYTES_LEN + 64;

/// Values of the block table (as in the spec)
#[derive(Clone, Default, Debug)]
pub struct BlockValues {
    coinbase: Address,
    gas_limit: u64,
    number: u64,
    timestamp: u64,
    difficulty: Word,
    base_fee: Word, // NOTE: BaseFee was added by EIP-1559 and is ignored in legacy headers.
    chain_id: u64,
    block_hash: Word,
}

/// PublicData contains all the values that the PiCircuit recieves as input
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

    block_constants: BlockConstants,
    chain_id: Word,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FieldType {
    None,
    BlockHash,
}

impl PublicData {
    fn assignments(&self) -> [(&'static str, FieldType, [u8; 32]); 10] {
        use FieldType::*;
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
            ("parent_hash", None, self.parent_hash.to_be_bytes()),
            ("block_hash", BlockHash, self.block_hash.to_be_bytes()),
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

    fn rpi_bytes(&self) -> Vec<u8> {
        self.assignments().iter().flat_map(|v| v.2).collect()
    }

    fn default<F: Default>() -> Self {
        Self::new::<F>(&witness::Block::default(), &witness::Taiko::default())
    }

    /// create PublicData from block and taiko
    pub fn new<F>(block: &witness::Block<F>, taiko: &witness::Taiko) -> Self {
        // left shift x by n bits
        fn left_shift<T: ToWord>(x: T, n: u32) -> Word {
            assert!(n < 256);
            if n < 128 {
                return x.to_word() * Word::from(2u128.pow(n));
            }
            let mut bits = [0; 32];
            bits[..16].copy_from_slice(2u128.pow(n - 128).to_be_bytes().as_ref());
            bits[16..].copy_from_slice(0u128.to_be_bytes().as_ref());
            x.to_word() * Word::from(&bits[..])
        }

        let field9 = left_shift(taiko.prover, 96)
            + left_shift(taiko.parent_gas_used as u64, 64)
            + left_shift(taiko.gas_used as u64, 32);

        let field10 = left_shift(taiko.block_max_gas_limit, 192)
            + left_shift(taiko.max_transactions_per_block, 128)
            + left_shift(taiko.max_bytes_per_tx_list, 64);
        PublicData {
            l1_signal_service: taiko.l1_signal_service.to_word(),
            l2_signal_service: taiko.l2_signal_service.to_word(),
            l2_contract: taiko.l2_contract.to_word(),
            meta_hash: taiko.meta_hash.to_word(),
            block_hash: taiko.block_hash.to_word(),
            parent_hash: taiko.parent_hash.to_word(),
            signal_root: taiko.signal_root.to_word(),
            graffiti: taiko.graffiti.to_word(),
            prover: taiko.prover,
            parent_gas_used: taiko.parent_gas_used,
            gas_used: taiko.gas_used,
            block_max_gas_limit: taiko.block_max_gas_limit,
            max_transactions_per_block: taiko.max_transactions_per_block,
            max_bytes_per_tx_list: taiko.max_bytes_per_tx_list,
            field9,
            field10,
            block_constants: BlockConstants {
                coinbase: block.context.coinbase,
                timestamp: block.context.timestamp,
                number: block.context.number.as_u64().into(),
                difficulty: block.context.difficulty,
                gas_limit: block.context.gas_limit.into(),
                base_fee: block.context.base_fee,
            },
            chain_id: block.context.chain_id,
        }
    }

    fn get_pi(&self) -> H256 {
        let rpi_bytes = self.rpi_bytes();
        let rpi_keccak = keccak256(rpi_bytes);
        H256(rpi_keccak)
    }

    /// Returns struct with values for the block table
    pub fn get_block_table_values(&self) -> BlockValues {
        BlockValues {
            coinbase: self.block_constants.coinbase,
            gas_limit: self.block_constants.gas_limit.as_u64(),
            number: self.block_constants.number.as_u64(),
            timestamp: self.block_constants.timestamp.as_u64(),
            difficulty: self.block_constants.difficulty,
            base_fee: self.block_constants.base_fee,
            chain_id: self.chain_id.as_u64(),
            block_hash: self.block_hash,
        }
    }
}

/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct PiCircuitConfig<F: Field> {
    rpi_field_bytes: Column<Advice>,
    rpi_field_bytes_acc: Column<Advice>,
    rpi_rlc_acc: Column<Advice>,
    q_field_start: Selector,
    q_field_step: Selector,
    q_field_end: Selector,
    is_field_rlc: Column<Fixed>,

    q_start: Selector,
    q_not_end: Selector,

    is_byte: Column<Fixed>,

    pi: Column<Instance>, // keccak_hi, keccak_lo

    q_keccak: Selector,
    keccak_table: KeccakTable,

    // External tables
    block_table: BlockTable,

    _marker: PhantomData<F>,
}

/// Circuit configuration arguments
pub struct PiCircuitConfigArgs<F: Field> {
    /// BlockTable
    pub block_table: BlockTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for PiCircuitConfig<F> {
    type ConfigArgs = PiCircuitConfigArgs<F>;

    /// Return a new PiCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            block_table,
            keccak_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        let rpi_field_bytes = meta.advice_column();
        let rpi_field_bytes_acc = meta.advice_column_in(SecondPhase);
        let rpi_rlc_acc = meta.advice_column_in(SecondPhase);
        let q_field_start = meta.complex_selector();
        let q_field_step = meta.complex_selector();
        let q_field_end = meta.complex_selector();
        let q_start = meta.complex_selector();
        let q_not_end = meta.complex_selector();
        let is_byte = meta.fixed_column();
        let is_field_rlc = meta.fixed_column();

        let pi = meta.instance_column();

        let q_keccak = meta.complex_selector();

        meta.enable_equality(rpi_field_bytes);
        meta.enable_equality(rpi_field_bytes_acc);
        meta.enable_equality(rpi_rlc_acc);
        meta.enable_equality(block_table.value);
        meta.enable_equality(pi);

        // field bytes
        meta.create_gate(
            "rpi_field_bytes_acc[i+1] = rpi_field_bytes_acc[i] * t + rpi_bytes[i+1]",
            |meta| {
                let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

                let q_field_step = meta.query_selector(q_field_step);
                let rpi_field_bytes_acc_next =
                    meta.query_advice(rpi_field_bytes_acc, Rotation::next());
                let rpi_field_bytes_acc = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
                let rpi_field_bytes_next = meta.query_advice(rpi_field_bytes, Rotation::next());
                let is_field_rlc = meta.query_fixed(is_field_rlc, Rotation::next());
                let randomness = challenges.evm_word();
                let t = select::expr(is_field_rlc, randomness, BYTE_POW_BASE.expr());
                cb.require_equal(
                    "rpi_field_bytes_acc[i+1] = rpi_field_bytes_acc[i] * t + rpi_bytes[i+1]",
                    rpi_field_bytes_acc_next,
                    rpi_field_bytes_acc * t + rpi_field_bytes_next,
                );
                cb.gate(q_field_step)
            },
        );
        meta.create_gate("rpi_field_bytes_acc[0] = rpi_field_bytes[0]", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_field_start = meta.query_selector(q_field_start);
            let rpi_field_bytes_acc = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
            let rpi_field_bytes = meta.query_advice(rpi_field_bytes, Rotation::cur());

            cb.require_equal(
                "rpi_field_bytes_acc[0] = rpi_field_bytes[0]",
                rpi_field_bytes_acc,
                rpi_field_bytes,
            );
            cb.gate(q_field_start)
        });

        // keccak in rpi
        meta.lookup_any("keccak(rpi)", |meta| {
            let is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            let input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            let input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            let output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            let q_keccak = meta.query_selector(q_keccak);

            let rpi_rlc = meta.query_advice(rpi_field_bytes_acc, Rotation::cur());
            let output = meta.query_advice(rpi_rlc_acc, Rotation::cur());

            vec![
                (q_keccak.expr() * 1.expr(), is_enabled),
                (q_keccak.expr() * rpi_rlc, input_rlc),
                (q_keccak.expr() * RPI_BYTES_LEN.expr(), input_len),
                (q_keccak * output, output_rlc),
            ]
        });

        // is byte
        meta.lookup_any("is_byte", |meta| {
            let q_field_step = meta.query_selector(q_field_start);
            let q_field_end = meta.query_selector(q_field_end);
            let is_field = or::expr([q_field_step, q_field_end]);
            let rpi_field_bytes = meta.query_advice(rpi_field_bytes, Rotation::cur());

            let is_byte = meta.query_fixed(is_byte, Rotation::cur());
            vec![(is_field * rpi_field_bytes, is_byte)]
        });

        Self {
            rpi_field_bytes,
            rpi_field_bytes_acc,
            rpi_rlc_acc,
            q_field_start,
            q_field_step,
            q_field_end,

            q_start,
            q_not_end,
            is_byte,
            is_field_rlc,

            pi, // keccak_hi, keccak_lo

            q_keccak,
            keccak_table,

            block_table,

            _marker: PhantomData,
        }
    }
}

impl<F: Field> PiCircuitConfig<F> {
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
            } else {
                self.q_field_step.enable(region, row_offset)?;
            }
            cells[2 + i] = Some(field_byte_cell);
        }
        *offset += field_bytes.len();
        Ok(cells.into_iter().map(|cell| cell.unwrap()).collect())
    }

    #[allow(clippy::type_complexity)]
    fn assign_block_table(
        &self,
        region: &mut Region<'_, F>,
        public_data: &PublicData,
        challenges: &Challenges<Value<F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let block_values = public_data.get_block_table_values();
        let randomness = challenges.evm_word();
        let mut block_hash_cell = None;
        for (offset, (name, val)) in [
            (
                "coinbase",
                Value::known(block_values.coinbase.to_scalar().unwrap()),
            ),
            ("timestamp", Value::known(F::from(block_values.timestamp))),
            ("number", Value::known(F::from(block_values.number))),
            (
                "difficulty",
                randomness.map(|randomness| rlc(block_values.difficulty.to_le_bytes(), randomness)),
            ),
            ("gas_limit", Value::known(F::from(block_values.gas_limit))),
            (
                "base_fee",
                randomness.map(|randomness| rlc(block_values.base_fee.to_le_bytes(), randomness)),
            ),
            ("chain_id", Value::known(F::from(block_values.chain_id))),
            (
                "block_hash",
                randomness.map(|randomness| rlc(block_values.block_hash.to_le_bytes(), randomness)),
            ),
        ]
        .into_iter()
        .enumerate()
        {
            block_hash_cell =
                Some(region.assign_advice(|| name, self.block_table.value, offset, || val)?);
        }

        Ok(block_hash_cell.unwrap())
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
                // Assign block table
                let block_table_hash_cell =
                    self.assign_block_table(region, public_data, challenges)?;
                let mut rpi_rlc_acc = Value::known(F::ZERO);
                let mut offset = 0;
                let mut rpi_rlc_acc_cell = None;
                for (annotation, field_type, field_bytes) in public_data.assignments() {
                    let cells = self.assign_pi_field(
                        region,
                        &mut offset,
                        annotation,
                        &field_bytes,
                        &mut rpi_rlc_acc,
                        challenges,
                        false,
                    )?;
                    if field_type == FieldType::BlockHash {
                        region.constrain_equal(
                            block_table_hash_cell.cell(),
                            cells[RPI_CELL_IDX].cell(),
                        )?;
                    }
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
pub struct PiCircuit<F: Field> {
    /// PublicInputs data known by the verifier
    pub public_data: PublicData,

    _marker: PhantomData<F>,
}

impl<F: Field> PiCircuit<F> {
    /// Creates a new PiCircuit
    pub fn new(public_data: PublicData) -> Self {
        Self {
            public_data,
            _marker: PhantomData,
        }
    }

    /// create a new PiCircuit with extra data
    pub fn new_from_block_with_extra(block: &witness::Block<F>, taiko: &witness::Taiko) -> Self {
        PiCircuit::new(PublicData::new(block, taiko))
    }
}

impl<F: Field> SubCircuit<F> for PiCircuit<F> {
    type Config = PiCircuitConfig<F>;

    fn unusable_rows() -> usize {
        2usize.pow(MIN_DEGREE as u32) - USED_ROWS + 2
    }

    fn min_num_rows_block(_block: &witness::Block<F>) -> (usize, usize) {
        (USED_ROWS, USED_ROWS)
    }

    fn new_from_block(block: &witness::Block<F>) -> Self {
        PiCircuit::new(PublicData::new(block, &witness::Taiko::default()))
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
        layouter.assign_region(
            || "is_byte table",
            |mut region| {
                for i in 0..(1 << 8) {
                    region.assign_fixed(
                        || format!("row_{}", i),
                        config.is_byte,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }

                Ok(())
            },
        )?;
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
pub struct PiTestCircuit<F: Field>(pub PiCircuit<F>);

#[cfg(any(feature = "test", test))]
impl<F: Field> Circuit<F> for PiTestCircuit<F> {
    type Config = (PiCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let block_table = BlockTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);
        // let challenge_exprs = Challenges::mock(100.expr(), 100.expr());

        (
            PiCircuitConfig::new(
                meta,
                PiCircuitConfigArgs {
                    block_table,
                    keccak_table,
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
        // let challenges = Challenges::mock(Value::known(F::from(100)),
        // Value::known(F::from(100)));

        let public_data = &self.0.public_data;
        // assign keccak table
        config
            .keccak_table
            .dev_load(&mut layouter, vec![&public_data.rpi_bytes()], &challenges)?;

        self.0.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

#[cfg(test)]
mod pi_circuit_test {

    use super::*;

    use eth_types::{H64, U256, U64};
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
        let circuit = PiTestCircuit::<F>(PiCircuit::new(public_data));
        let public_inputs = pi.unwrap_or_else(|| circuit.0.instance());

        let prover = match MockProver::run(k, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        let res = prover.verify();
        res
    }

    #[test]
    fn test_default_pi() {
        const MAX_TXS: usize = 2;
        const MAX_CALLDATA: usize = 8;
        let mut public_data = PublicData::default::<Fr>();
        public_data.meta_hash = OMMERS_HASH.to_word();
        public_data.block_hash = OMMERS_HASH.to_word();

        let k = 17;
        assert_eq!(run::<Fr>(k, public_data, None), Ok(()));
    }

    #[test]
    fn test_fail_pi_hash() {
        const MAX_TXS: usize = 2;
        const MAX_CALLDATA: usize = 8;
        let public_data = PublicData::default::<Fr>();

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
        const MAX_TXS: usize = 2;
        const MAX_CALLDATA: usize = 8;
        let mut public_data = PublicData::default::<Fr>();
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
        let mut public_data = PublicData::default::<Fr>();
        let chain_id = 1337u64;
        public_data.chain_id = Word::from(chain_id);

        let k = 17;
        assert_eq!(run::<Fr>(k, public_data, None), Ok(()));
    }

    #[test]
    fn test_verify() {
        let prover =
            Address::from_slice(&hex::decode("Df08F82De32B8d460adbE8D72043E3a7e25A3B39").unwrap());

        let logs_bloom:[u8;256] = hex::decode("112d60abc05141f1302248e0f4329627f002380f1413820692911863e7d0871261aa07e90cc01a10c3ce589153570dc2db27b8783aa52bc19a5a4a836722e813190401b4214c3908cb8b468b510c3fe482603b00ca694c806206bf099279919c334541094bd2e085210373c0b064083242d727790d2eecdb2e0b90353b66461050447626366328f0965602e8a9802d25740ad4a33162142b08a1b15292952de423fac45d235622bb0ef3b2d2d4c21690d280a0b948a8a3012136542c1c4d0955a501a022e1a1a4582220d1ae50ba475d88ce0310721a9076702d29a27283e68c2278b93a1c60d8f812069c250042cc3180a8fd54f034a2da9a03098c32b03445").unwrap().try_into().unwrap();

        let mut block = witness::Block::<Fr>::default();
        block.eth_block.parent_hash = *OMMERS_HASH;
        block.eth_block.author = Some(prover);
        block.eth_block.state_root = *OMMERS_HASH;
        block.eth_block.transactions_root = *OMMERS_HASH;
        block.eth_block.receipts_root = *OMMERS_HASH;
        block.eth_block.logs_bloom = Some(logs_bloom.into());
        block.eth_block.difficulty = U256::from(0);
        block.eth_block.number = Some(U64::from(0));
        block.eth_block.gas_limit = U256::from(0);
        block.eth_block.gas_used = U256::from(0);
        block.eth_block.timestamp = U256::from(0);
        block.eth_block.extra_data = eth_types::Bytes::from([0; 0]);
        block.eth_block.mix_hash = Some(*OMMERS_HASH);
        block.eth_block.nonce = Some(H64::from([0, 0, 0, 0, 0, 0, 0, 0]));
        block.eth_block.base_fee_per_gas = Some(U256::from(0));

        let public_data = PublicData::new(&block, &witness::Taiko::default());

        let k = 17;

        assert_eq!(run::<Fr>(k, public_data, None), Ok(()));
    }
}

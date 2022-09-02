//! The transaction circuit implementation.

// Naming notes:
// - *_be: Big-Endian bytes
// - *_le: Little-Endian bytes

pub mod sign_verify;

use crate::table::{KeccakTable, TxFieldTag, TxTable};
use crate::util::{power_of_randomness_from_instance, random_linear_combine_word as rlc};
use bus_mapping::circuit_input_builder::keccak_inputs_tx_circuit;
use eth_types::{
    sign_types::SignData,
    {geth_types::Transaction, Address, Field, ToLittleEndian, ToScalar},
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression},
};
use itertools::Itertools;
use log::error;
use sign_verify::{SignVerifyChip, SignVerifyConfig};
use std::marker::PhantomData;

pub use halo2_proofs::halo2curves::{
    group::{
        ff::{Field as GroupField, PrimeField},
        prime::PrimeCurveAffine,
        Curve, Group, GroupEncoding,
    },
    secp256k1::{self, Secp256k1Affine, Secp256k1Compressed},
};
pub use sign_verify::{POW_RAND_SIZE, VERIF_HEIGHT};

/// Config for TxCircuit
#[derive(Clone, Debug)]
pub struct TxCircuitConfig<F: Field> {
    tx_id: Column<Advice>,
    tag: Column<Advice>,
    index: Column<Advice>,
    value: Column<Advice>,
    sign_verify: SignVerifyConfig<F>,
    keccak_table: KeccakTable,
    _marker: PhantomData<F>,
}

impl<F: Field> TxCircuitConfig<F> {
    /// Return a new TxCircuitConfig
    pub fn new(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; sign_verify::POW_RAND_SIZE],
        tx_table: TxTable,
        keccak_table: KeccakTable,
    ) -> Self {
        let tx_id = tx_table.tx_id;
        let tag = tx_table.tag;
        let index = tx_table.index;
        let value = tx_table.value;
        meta.enable_equality(value);

        let sign_verify = SignVerifyConfig::new(meta, power_of_randomness, keccak_table.clone());

        Self {
            tx_id,
            tag,
            index,
            value,
            sign_verify,
            keccak_table,
            _marker: PhantomData,
        }
    }

    /// Assigns a tx circuit row and returns the assigned cell of the value in
    /// the row.
    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_id: usize,
        tag: TxFieldTag,
        index: usize,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.assign_advice(
            || "tx_id",
            self.tx_id,
            offset,
            || Value::known(F::from(tx_id as u64)),
        )?;
        region.assign_advice(
            || "tag",
            self.tag,
            offset,
            || Value::known(F::from(tag as u64)),
        )?;
        region.assign_advice(
            || "index",
            self.index,
            offset,
            || Value::known(F::from(index as u64)),
        )?;
        region.assign_advice(|| "value", self.value, offset, || Value::known(value))
    }
}

/// Tx Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct TxCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    /// SignVerify chip
    pub sign_verify: SignVerifyChip<F, MAX_TXS>,
    /// Randomness for RLC encoding
    pub randomness: F,
    /// List of Transactions
    pub txs: Vec<Transaction>,
    /// Chain ID
    pub chain_id: u64,
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>
    TxCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    /// Return a new TxCircuit
    pub fn new(
        aux_generator: Secp256k1Affine,
        randomness: F,
        chain_id: u64,
        txs: Vec<Transaction>,
    ) -> Self {
        TxCircuit::<F, MAX_TXS, MAX_CALLDATA> {
            sign_verify: SignVerifyChip {
                aux_generator,
                window_size: 2,
                _marker: PhantomData,
            },
            randomness,
            txs,
            chain_id,
        }
    }

    /// Make the assignments to the TxCircuit
    pub fn assign(
        &self,
        config: &TxCircuitConfig<F>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        assert!(self.txs.len() <= MAX_TXS);
        let sign_datas: Vec<SignData> = self
            .txs
            .iter()
            .map(|tx| {
                tx.sign_data(self.chain_id).map_err(|e| {
                    error!("tx_to_sign_data error for tx {:?}", e);
                    Error::Synthesis
                })
            })
            .try_collect()?;

        let assigned_sig_verifs =
            self.sign_verify
                .assign(&config.sign_verify, layouter, self.randomness, &sign_datas)?;

        layouter.assign_region(
            || "tx table",
            |mut region| {
                let mut offset = 0;
                // Empty entry
                config.assign_row(&mut region, offset, 0, TxFieldTag::Null, 0, F::zero())?;
                offset += 1;
                // Assign al Tx fields except for call data
                let tx_default = Transaction::default();
                // for i in 0..MAX_TXS
                for (i, assigned_sig_verif) in assigned_sig_verifs.iter().enumerate() {
                    let tx = if i < self.txs.len() {
                        &self.txs[i]
                    } else {
                        &tx_default
                    };

                    let address_cell = assigned_sig_verif.address.cell();
                    let msg_hash_rlc_cell = assigned_sig_verif.msg_hash_rlc.cell();
                    let mut msg_hash_rlc_value = F::zero();
                    assigned_sig_verif.msg_hash_rlc.value().map(|f| {
                        msg_hash_rlc_value = *f;
                        f
                    });
                    for (tag, value) in &[
                        (
                            TxFieldTag::Nonce,
                            rlc(tx.nonce.to_le_bytes(), self.randomness),
                        ),
                        (TxFieldTag::Gas, F::from(tx.gas_limit.as_u64())),
                        (
                            TxFieldTag::GasPrice,
                            rlc(tx.gas_price.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::CallerAddress,
                            tx.from.to_scalar().expect("tx.from too big"),
                        ),
                        (
                            TxFieldTag::CalleeAddress,
                            tx.to
                                .unwrap_or_else(Address::zero)
                                .to_scalar()
                                .expect("tx.to too big"),
                        ),
                        (TxFieldTag::IsCreate, F::from(tx.to.is_none() as u64)),
                        (
                            TxFieldTag::Value,
                            rlc(tx.value.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::CallDataLength,
                            F::from(tx.call_data.0.len() as u64),
                        ),
                        (
                            TxFieldTag::CallDataGasCost,
                            F::from(
                                tx.call_data
                                    .0
                                    .iter()
                                    .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 }),
                            ),
                        ),
                        (TxFieldTag::TxSignHash, msg_hash_rlc_value),
                    ] {
                        let assigned_cell =
                            config.assign_row(&mut region, offset, i + 1, *tag, 0, *value)?;
                        offset += 1;

                        // Ref. spec 0. Copy constraints using fixed offsets between the tx rows and
                        // the SignVerifyChip
                        match tag {
                            TxFieldTag::CallerAddress => {
                                region.constrain_equal(assigned_cell.cell(), address_cell)?
                            }
                            TxFieldTag::TxSignHash => {
                                region.constrain_equal(assigned_cell.cell(), msg_hash_rlc_cell)?
                            }
                            _ => (),
                        }
                    }
                }

                // Assign call data
                let mut calldata_count = 0;
                for (i, tx) in self.txs.iter().enumerate() {
                    for (index, byte) in tx.call_data.0.iter().enumerate() {
                        assert!(calldata_count < MAX_CALLDATA);
                        config.assign_row(
                            &mut region,
                            offset,
                            i + 1, // tx_id
                            TxFieldTag::CallData,
                            index,
                            F::from(*byte as u64),
                        )?;
                        offset += 1;
                        calldata_count += 1;
                    }
                }
                for _ in calldata_count..MAX_CALLDATA {
                    config.assign_row(
                        &mut region,
                        offset,
                        0, // tx_id
                        TxFieldTag::CallData,
                        0,
                        F::zero(),
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> Circuit<F>
    for TxCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    type Config = TxCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = TxTable {
            tx_id: meta.advice_column(),
            tag: meta.advice_column(),
            index: meta.advice_column(),
            value: meta.advice_column(),
        };

        let power_of_randomness = power_of_randomness_from_instance(meta);
        let keccak_table = KeccakTable::construct(meta);
        TxCircuitConfig::new(meta, power_of_randomness, tx_table, keccak_table)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.sign_verify.load_range(&mut layouter)?;
        self.assign(&config, &mut layouter)?;
        config.keccak_table.load(
            &mut layouter,
            &keccak_inputs_tx_circuit(&self.txs[..], self.chain_id).map_err(|e| {
                error!("keccak_inputs_tx_circuit error: {:?}", e);
                Error::Synthesis
            })?,
            self.randomness,
        )
    }
}

#[cfg(test)]
mod tx_circuit_tests {
    use super::*;
    use eth_types::address;
    use halo2_proofs::{
        arithmetic::CurveAffine,
        dev::{MockProver, VerifyFailure},
        halo2curves::{bn256::Fr, group::Group},
    };
    use mock::AddrOrWallet;
    use pretty_assertions::assert_eq;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn run<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
        k: u32,
        txs: Vec<Transaction>,
        chain_id: u64,
    ) -> Result<(), Vec<VerifyFailure>> {
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        let aux_generator =
            <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();

        let randomness = F::random(&mut rng);
        let mut instance: Vec<Vec<F>> = (1..POW_RAND_SIZE + 1)
            .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); txs.len() * VERIF_HEIGHT])
            .collect();
        // SignVerifyChip -> ECDSAChip -> MainGate instance column
        instance.push(vec![]);
        let circuit = TxCircuit::<F, MAX_TXS, MAX_CALLDATA> {
            sign_verify: SignVerifyChip {
                aux_generator,
                window_size: 2,
                _marker: PhantomData,
            },
            randomness,
            txs,
            chain_id,
        };

        let prover = match MockProver::run(k, &circuit, instance) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        prover.verify()
    }

    // High memory usage test.  Run in serial with:
    // `cargo test [...] serial_ -- --ignored --test-threads 1`
    #[ignore]
    #[test]
    fn serial_test_tx_circuit_2tx() {
        const NUM_TXS: usize = 2;
        const MAX_TXS: usize = 2;
        const MAX_CALLDATA: usize = 32;

        let k = 19;
        assert_eq!(
            run::<Fr, MAX_TXS, MAX_CALLDATA>(
                k,
                mock::CORRECT_MOCK_TXS[..NUM_TXS]
                    .iter()
                    .map(|tx| Transaction::from(tx.clone()))
                    .collect_vec(),
                mock::MOCK_CHAIN_ID.as_u64()
            ),
            Ok(())
        );
    }

    // High memory usage test.  Run in serial with:
    // `cargo test [...] serial_ -- --ignored --test-threads 1`
    #[ignore]
    #[test]
    fn serial_test_tx_circuit_1tx() {
        const MAX_TXS: usize = 1;
        const MAX_CALLDATA: usize = 32;

        let chain_id: u64 = mock::MOCK_CHAIN_ID.as_u64();

        let tx: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();

        let k = 19;
        assert_eq!(
            run::<Fr, MAX_TXS, MAX_CALLDATA>(k, vec![tx], chain_id),
            Ok(())
        );
    }

    // High memory usage test.  Run in serial with:
    // `cargo test [...] serial_ -- --ignored --test-threads 1`
    #[ignore]
    #[test]
    fn serial_test_tx_circuit_bad_address() {
        const MAX_TXS: usize = 1;
        const MAX_CALLDATA: usize = 32;

        let mut tx = mock::CORRECT_MOCK_TXS[0].clone();
        // This address doesn't correspond to the account that signed this tx.
        tx.from = AddrOrWallet::from(address!("0x1230000000000000000000000000000000000456"));

        let k = 19;
        assert!(
            run::<Fr, MAX_TXS, MAX_CALLDATA>(k, vec![tx.into()], mock::MOCK_CHAIN_ID.as_u64())
                .is_err(),
        );
    }
}

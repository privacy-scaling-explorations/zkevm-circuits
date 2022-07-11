//! Mario Kart: Super Circuit
//! ⠀⠀⠀⠀⠀⠀⠀⢀⣀⣀⡀⠀⠀⠀⠀⠀⠀⠀
//! ⠀⠀⠀⠀⡠⣴⣮⣷⣶⡶⣾⣽⣶⢤⡀⠀⠀⠀
//! ⠀⠀⢠⣾⣿⢧⣾⣿⣿⣧⣿⣿⣿⣷⡱⡄⠀⠀
//! ⠀⣠⣿⣿⣯⣿⣿⣿⣿⡿⣼⣻⠿⠟⠛⠻⢦⡀
//! ⡼⠁⢿⣟⣎⣿⣿⠿⠟⠃⠉⠀⠀⠀⠀⠀⠀⣷
//! ⢳⡀⠀⠀⠀⠀⠀⠀⠀⣀⡠⡤⢲⣾⡏⢱⡠⠃
//! ⠀⠉⠲⡲⠒⠒⡖⠚⠿⢿⠃⠡⡀⠉⢁⠞⠀⠀
//! ⠀⠀⠀⠘⠳⢄⣘⢤⣀⠈⢂⣤⠴⠚⠁⠀⠀⠀
//! ⠀⠀⠀⠀⠀⠀⠀⠉⠉⠉⠁⠀⠀⠀⠀⠀⠀⠀

#![allow(missing_docs)]
// use halo2_proofs::plonk::*;

use crate::tx_circuit::{sign_verify, TxCircuit, TxCircuitConfig, TxTable};

use crate::bytecode_circuit::bytecode_unroller::{
    unroll, BytecodeTable, Config as BytecodeConfig, UnrolledBytecode,
};

use crate::util::Expr;
use crate::{
    evm_circuit::{
        table::FixedTableTag,
        witness::Block,
        EvmCircuit, {load_block, load_bytecodes, load_rws, load_txs},
    },
    rw_table::RwTable,
};
use eth_types::Field;
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::{Layouter, SimpleFloorPlanner},
    // dev::{MockProver, VerifyFailure},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};

#[derive(Clone)]
pub struct SuperCircuitConfig<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    tx_table: [Column<Advice>; 4],
    rw_table: RwTable,
    bytecode_table: [Column<Advice>; 5],
    block_table: [Column<Advice>; 3],
    evm_circuit: EvmCircuit<F>,
    tx_circuit: TxCircuitConfig<F>,
    bytecode_circuit: BytecodeConfig<F>,
}

#[derive(Default)]
pub struct SuperCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    // EVM Circuit
    block: Block<F>,
    fixed_table_tags: Vec<FixedTableTag>,
    // Tx Circuit
    tx_circuit: TxCircuit<F, MAX_TXS, MAX_CALLDATA>,
    // Bytecode Circuit
    // bytecodes: Vec<UnrolledBytecode<F>>,
    bytecode_size: usize,
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>
    SuperCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    pub fn get_num_rows_required(block: &Block<F>) -> usize {
        let mut cs = ConstraintSystem::default();
        let config = Self::configure(&mut cs);
        config.evm_circuit.get_num_rows_required(block)
    }
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> Circuit<F>
    for SuperCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    type Config = SuperCircuitConfig<F, MAX_TXS, MAX_CALLDATA>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = [(); 4].map(|_| meta.advice_column());
        let rw_table = RwTable::construct(meta);
        let bytecode_table = [(); 5].map(|_| meta.advice_column());
        let block_table = [(); 3].map(|_| meta.advice_column());

        // This gate is used just to get the array of expressions from the power of
        // randomness instance column, so that later on we don't need to query
        // columns everywhere, and can pass the power of randomness array
        // expression everywhere.  The gate itself doesn't add any constraints.
        let power_of_randomness = {
            let columns = [(); sign_verify::POW_RAND_SIZE].map(|_| meta.instance_column());
            let mut power_of_randomness = None;

            meta.create_gate("", |meta| {
                power_of_randomness =
                    Some(columns.map(|column| meta.query_instance(column, Rotation::cur())));

                [0.expr()]
            });

            power_of_randomness.unwrap()
        };

        Self::Config {
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            evm_circuit: EvmCircuit::configure(
                meta,
                power_of_randomness[..31]
                    .iter()
                    .cloned()
                    .collect::<Vec<Expression<F>>>()
                    .try_into()
                    .unwrap(),
                &tx_table,
                &rw_table,
                &bytecode_table,
                &block_table,
            ),
            tx_circuit: TxCircuitConfig::new(
                meta,
                power_of_randomness.clone(),
                TxTable {
                    tx_id: tx_table[0],
                    tag: tx_table[1],
                    index: tx_table[2],
                    value: tx_table[3],
                },
            ),
            bytecode_circuit: BytecodeConfig::configure(
                meta,
                power_of_randomness[0].clone(),
                BytecodeTable {
                    hash: bytecode_table[0],
                    tag: bytecode_table[1],
                    index: bytecode_table[2],
                    is_code: bytecode_table[3],
                    value: bytecode_table[4],
                },
            ),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // --- EVM Circuit ---
        config
            .evm_circuit
            .load_fixed_table(&mut layouter, self.fixed_table_tags.clone())?;
        config.evm_circuit.load_byte_table(&mut layouter)?;
        // load_txs(
        //     &config.tx_table,
        //     &mut layouter,
        //     &self.block.txs,
        //     self.block.randomness,
        // )?;
        load_rws(
            &config.rw_table,
            &mut layouter,
            &self.block.rws,
            self.block.randomness,
        )?;
        // load_bytecodes(
        //     &config.bytecode_table,
        //     &mut layouter,
        //     &self.block.bytecodes,
        //     self.block.randomness,
        // )?;
        load_block(
            &config.block_table,
            &mut layouter,
            &self.block.context,
            self.block.randomness,
        )?;
        config
            .evm_circuit
            .assign_block_exact(&mut layouter, &self.block)?;
        // --- Tx Circuit ---
        self.tx_circuit.assign(config.tx_circuit, &mut layouter)?;
        // --- Bytecode Circuit ---
        let bytecodes: Vec<UnrolledBytecode<F>> = self
            .block
            .bytecodes
            .iter()
            .map(|b| unroll(b.bytes.clone(), self.block.randomness))
            .collect();
        config
            .bytecode_circuit
            .load(&mut layouter, &bytecodes, self.block.randomness)?;
        config.bytecode_circuit.assign(
            &mut layouter,
            self.bytecode_size,
            &bytecodes,
            self.block.randomness,
        )?;
        Ok(())
    }
}

#[cfg(test)]
pub mod test {
    use eth_types::{Address, U64};
    use ethers_core::{types::TransactionRequest, utils::keccak256};
    use ethers_signers::LocalWallet;
    use std::collections::HashMap;
    // Testing function
    pub fn sign_txs(
        txs: &mut [eth_types::Transaction],
        chain_id: u64,
        wallets: &HashMap<Address, LocalWallet>,
    ) {
        for tx in txs.iter_mut() {
            let wallet = wallets.get(&tx.from).unwrap();
            let req = TransactionRequest::new()
                .from(tx.from)
                .to(tx.to.unwrap())
                .nonce(tx.nonce)
                .value(tx.value)
                .data(tx.input.clone())
                .gas(tx.gas)
                .gas_price(tx.gas_price.unwrap());
            let tx_rlp = req.rlp(chain_id);
            let sighash = keccak256(tx_rlp.as_ref()).into();
            let sig = wallet.sign_hash(sighash, true);
            tx.v = U64::from(sig.v);
            tx.r = sig.r;
            tx.s = sig.s;
        }
    }
}

#[cfg(test)]
mod super_circuit_tests {
    use super::test::*;
    use super::*;
    use crate::{
        evm_circuit::witness::block_convert,
        // test_util::{run_test_circuits, BytecodeTestConfig},
        tx_circuit::sign_verify::POW_RAND_SIZE,
    };
    use bus_mapping::mock::BlockData;
    use eth_types::{
        address, bytecode,
        geth_types::{self, GethData},
        Word,
    };
    use ethers_signers::{LocalWallet, Signer};
    use group::{Curve, Group};
    use halo2_proofs::dev::{MockProver, VerifyConfig, VerifyFailure};
    use mock::{TestContext, MOCK_CHAIN_ID};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use secp256k1::Secp256k1Affine;
    use std::collections::HashMap;
    use strum::IntoEnumIterator;

    struct Inputs<F: Field> {
        block: Block<F>,
        txs: Vec<geth_types::Transaction>,
        aux_generator: Secp256k1Affine,
    }

    fn run_test_circuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
        inputs: Inputs<F>,
        fixed_table_tags: Vec<FixedTableTag>,
    ) -> Result<(), Vec<VerifyFailure>> {
        let Inputs {
            block,
            txs,
            aux_generator,
        } = inputs;

        let log2_ceil = |n| u32::BITS - (n as u32).leading_zeros() - (n & (n - 1) == 0) as u32;

        let num_rows_required_for_steps =
            SuperCircuit::<F, MAX_TXS, MAX_CALLDATA>::get_num_rows_required(&block);

        let k = log2_ceil(
            64 + fixed_table_tags
                .iter()
                .map(|tag| tag.build::<F>().count())
                .sum::<usize>(),
        );
        let bytecodes_len = block
            .bytecodes
            .iter()
            .map(|bytecode| bytecode.bytes.len())
            .sum::<usize>();
        let k = k.max(log2_ceil(64 + bytecodes_len));
        let k = k.max(log2_ceil(64 + num_rows_required_for_steps));
        let k = k + 1;
        log::debug!("evm circuit uses k = {}", k);

        let mut instance: Vec<Vec<F>> = (1..POW_RAND_SIZE + 1)
            .map(|exp| vec![block.randomness.pow(&[exp as u64, 0, 0, 0]); (1 << k) - 64])
            .collect();
        // SignVerifyChip -> ECDSAChip -> MainGate instance column
        instance.push(vec![]);

        let chain_id = block.context.chain_id;
        let tx_circuit = TxCircuit::new(aux_generator, block.randomness, chain_id.as_u64(), txs);
        let circuit = SuperCircuit::<F, MAX_TXS, MAX_CALLDATA> {
            block,
            fixed_table_tags,
            tx_circuit,
            // bytecode_size: 2usize.pow(k),
            bytecode_size: bytecodes_len + 64,
        };
        let prover = MockProver::<F>::run(k, &circuit, instance).unwrap();
        prover.verify_par(VerifyConfig {
            selectors: true,
            gates: true,
            lookups: true,
            perms: true,
        })
    }

    fn run_test_circuit_complete_fixed_table<F: Field>(
        inputs: Inputs<F>,
    ) -> Result<(), Vec<VerifyFailure>> {
        const MAX_TXS: usize = 1;
        const MAX_CALLDATA: usize = 32;

        run_test_circuit::<F, MAX_TXS, MAX_CALLDATA>(inputs, FixedTableTag::iter().collect())
    }

    #[test]
    fn test_super_circuit() {
        let mut rng = ChaCha20Rng::seed_from_u64(2);

        let chain_id = (*MOCK_CHAIN_ID).as_u64();

        let bytecode = bytecode! {
            GAS
            STOP
        };

        let wallet_a = LocalWallet::new(&mut rng).with_chain_id(chain_id);

        let addr_a = wallet_a.address();
        let addr_b = address!("0x000000000000000000000000000000000000BBBB");

        let mut wallets = HashMap::new();
        wallets.insert(wallet_a.address(), wallet_a.clone());

        // Create a custom tx setting Gas to
        let mut block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(addr_b)
                    .balance(Word::from(1u64 << 20))
                    .code(bytecode);
                accs[1].address(addr_a).balance(Word::from(1u64 << 20));
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(Word::from(1_000_000u64));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        sign_txs(&mut block.eth_block.transactions, chain_id, &wallets);
        let txs = block
            .eth_block
            .transactions
            .iter()
            .map(|tx| geth_types::Transaction::from_eth_tx(tx))
            .collect();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        assert_eq!(builder.block.chain_id.as_u64(), chain_id);

        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .expect("could not handle block tx");
        let block = block_convert(&builder.block, &builder.code_db);

        let aux_generator =
            <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();
        let inputs = Inputs {
            block,
            txs,
            aux_generator,
        };

        let res = run_test_circuit_complete_fixed_table(inputs);
        if let Err(err) = res {
            eprintln!("Verification failures:");
            eprintln!("{:#?}", err);
            panic!("Failed verification");
        }
    }
}

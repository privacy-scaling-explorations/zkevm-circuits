use std::collections::HashMap;

use crate::{pi_circuit::dev::PiCircuitParams, util::unusable_rows, witness::block_convert};

use super::*;
use bus_mapping::{
    circuit_input_builder::FixedCParams, mock::BlockData, state_db::EMPTY_CODE_HASH_LE,
};
use eth_types::{bytecode, geth_types::GethData, Address, Word, H160, H256};
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::{
    dev::{MockProver, VerifyFailure},
    halo2curves::bn256::Fr,
};
use mock::{eth, TestContext, TestContext2, CORRECT_MOCK_TXS, MOCK_ACCOUNTS, MOCK_CHAIN_ID};
use rand::SeedableRng;
use rand_chacha::ChaChaRng;

#[test]
fn pi_circuit_unusable_rows() {
    assert_eq!(
        PiCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, PiCircuit::<Fr>>(PiCircuitParams {
            max_txs: 2,
            max_withdrawals: 5,
            max_calldata: 8,
        }),
    )
}

fn run<F: Field>(
    k: u32,
    max_txs: usize,
    max_withdrawals: usize,
    max_calldata: usize,
    max_withdrawals: usize,
    max_calldata: usize,
    public_data: PublicData,
) -> Result<(), Vec<VerifyFailure>> {
    let mut public_data = public_data;
    public_data.chain_id = *MOCK_CHAIN_ID;

    let circuit = PiCircuit::<F>::new(max_txs, max_withdrawals, max_calldata, public_data);

    let public_inputs = circuit.instance();

    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    prover.verify()
}

#[test]
fn test_default_pi() {
    let max_txs = 2;
    let max_withdrawals = 2;
    let max_calldata = 8;
    let public_data = PublicData::default();

    let k = 17;
    assert_eq!(
        run::<Fr>(k, max_txs, max_withdrawals, max_calldata, public_data),
        Ok(())
}
    let max_txs = 8;
    let max_withdrawals = 5;
    let max_calldata = 200;

    let mut public_data = PublicData::default();

    public_data.block_constants.coinbase = H160([1u8; 20]);
    let n_tx = 4;
    for i in 0..n_tx {
        public_data
            .transactions
            .push(CORRECT_MOCK_TXS[i].clone().into());
    }

    let k = 17;
    assert_eq!(
        run::<Fr>(k, max_txs, max_withdrawals, max_calldata, public_data),
        Ok(())
    );
}

#[test]
fn test_1tx_1maxtx() {
    const MAX_TXS: usize = 1;
    const MAX_WITHDRAWALS: usize = 1;
    const MAX_CALLDATA: usize = 32;
    let mut rng = ChaChaRng::seed_from_u64(2);
    let wallet_a = LocalWallet::new(&mut rng).with_chain_id(MOCK_CHAIN_ID.as_u64());

    let addr_a = wallet_a.address();
    let addr_b = MOCK_ACCOUNTS[0];

    let degree = 17;
    let calldata = vec![];
    let code = bytecode! {
        PUSH4(0x1000) // size
        PUSH2(0x00) // offset
        RETURN
    };
    let test_ctx = TestContext::<2, 1>::new(
        Some(vec![Word::from("0xdeadbeef")]),
        |accs| {
            accs[0].address(addr_b).balance(eth(10)).code(code);
            accs[1].address(addr_a).balance(eth(10));
        },
        |mut txs, accs| {
            txs[0]
                .from(accs[1].address)
                .to(accs[0].address)
                .input(calldata.into())
                .gas((1e16 as u64).into());
        },
        |block, _txs| {
            block
                .number(0xcafeu64)
                .chain_id(*MOCK_CHAIN_ID)
                .withdrawal_hash(Some(H256::from(*EMPTY_CODE_HASH_LE)))
        },
    )
    .unwrap();
    let mut wallets = HashMap::new();
    wallets.insert(wallet_a.address(), wallet_a);

    let mut block: GethData = test_ctx.into();
    let mut builder = BlockData::new_from_geth_data_with_params(
        block.clone(),
        FixedCParams {
            max_txs: MAX_TXS,
            max_withdrawals: MAX_WITHDRAWALS,
            max_calldata: MAX_CALLDATA,
            max_rws: 1 << (degree - 1),
            ..Default::default()
        },
    )
    .new_circuit_input_builder();

    block.sign(&wallets);

    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();

    let block = block_convert(&builder).unwrap();
    // MAX_TXS, MAX_TXS align with `CircuitsParams`
    let circuit = PiCircuit::<Fr>::new_from_block(&block);
    let public_inputs = circuit.instance();

    let prover = match MockProver::run(degree, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}

#[test]
fn test_1wd_1wdmax() {
    const MAX_TXS: usize = 1;
    const MAX_WITHDRAWALS: usize = 1;
    const MAX_CALLDATA: usize = 32;
    let mut rng = ChaChaRng::seed_from_u64(2);
    let wallet_a = LocalWallet::new(&mut rng).with_chain_id(MOCK_CHAIN_ID.as_u64());

    let addr_a = wallet_a.address();
    let addr_b = MOCK_ACCOUNTS[0];

    let degree = 17;
    let calldata = vec![];
    let code = bytecode! {
        PUSH4(0x1000) // size
        PUSH2(0x00) // offset
        RETURN
    };
    let test_ctx = TestContext2::<2, 1, 1>::new(
        Some(vec![Word::from("0xdeadbeef")]),
        |accs| {
            accs[0].address(addr_b).balance(eth(10)).code(code);
            accs[1].address(addr_a).balance(eth(10));
        },
        |mut txs, accs| {
            txs[0]
                .from(accs[1].address)
                .to(accs[0].address)
                .input(calldata.into())
                .gas((1e16 as u64).into());
        },
        |mut wds| {
            wds[0]
                .id(101)
                .validator_id(1)
                .address(Address::random())
                .amount(100);
        },
        |block, _txs| {
            block
                .number(0xcafeu64)
                .chain_id(*MOCK_CHAIN_ID)
                .withdrawal_hash(Some(H256::from_low_u64_le(0xabcd)))
    wallets.insert(wallet_a.address(), wallet_a);

    let mut block: GethData = test_ctx.into();
    let mut builder = BlockData::new_from_geth_data_with_params(
        block.clone(),
        FixedCParams {
            max_txs: MAX_TXS,
            max_withdrawals: MAX_WITHDRAWALS,
            max_calldata: MAX_CALLDATA,
            max_rws: 1 << (degree - 1),
            ..Default::default()
        },
    )
    .new_circuit_input_builder();

    block.sign(&wallets);

    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();

    let block = block_convert(&builder).unwrap();
    // MAX_TXS, MAX_TXS align with `CircuitsParams`
    let circuit = PiCircuit::<Fr>::new_from_block(&block);
    let public_inputs = circuit.instance();

    let prover = match MockProver::run(degree, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}

fn run_size_check<F: Field>(
    max_txs: usize,
    max_withdrawals: usize,
    max_calldata: usize,
    public_data: [PublicData; 2],
) {
    let circuit = PiCircuit::<F>::new(
        max_txs,
        max_withdrawals,
        max_calldata,
        public_data[0].clone(),
    );
    let public_inputs = circuit.instance();
    let prover1 = MockProver::run(20, &circuit, public_inputs).unwrap();

    let circuit2 = PiCircuit::<F>::new(
        max_txs,
        max_withdrawals,
        max_calldata,
        public_data[1].clone(),
    );
    let public_inputs = circuit2.instance();
    let prover2 = MockProver::run(20, &circuit, public_inputs).unwrap();

    assert_eq!(prover1.fixed(), prover2.fixed());
    assert_eq!(prover1.permutation(), prover2.permutation());
}

#[test]
fn variadic_size_check() {
    let max_txs = 8;
    let max_withdrawals = 5;
    let max_calldata = 200;

    let mut pub_dat_1 = PublicData {
        chain_id: *MOCK_CHAIN_ID,
        ..Default::default()
    };

    let n_tx = 2;
    for i in 0..n_tx {
        pub_dat_1
            .transactions
            .push(CORRECT_MOCK_TXS[i].clone().into());
    }

    let mut pub_dat_2 = PublicData {
        chain_id: *MOCK_CHAIN_ID,
        ..Default::default()
    };

    let n_tx = 4;
    for i in 0..n_tx {
        pub_dat_2
            .transactions
            .push(CORRECT_MOCK_TXS[i].clone().into());
    }

    run_size_check::<Fr>(
        max_txs,
        max_withdrawals,
        max_calldata,
        [pub_dat_1, pub_dat_2],
    );
}

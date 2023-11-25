use super::*;
use crate::util::{log2_ceil, unusable_rows};
use eth_types::address;
use halo2_proofs::{
    dev::{MockProver, VerifyFailure},
    halo2curves::bn256::Fr,
};
use mock::AddrOrWallet;

#[test]
fn tx_circuit_unusable_rows() {
    assert_eq!(
        TxCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, TxCircuit::<Fr>>(()),
    )
}

fn run<F: Field>(
    txs: Vec<Transaction>,
    chain_id: u64,
    max_txs: usize,
    max_calldata: usize,
) -> Result<(), Vec<VerifyFailure>> {
    let k = log2_ceil(
        TxCircuit::<Fr>::unusable_rows() + TxCircuit::<Fr>::min_num_rows(max_txs, max_calldata),
    );
    // SignVerifyChip -> ECDSAChip -> MainGate instance column
    let circuit = TxCircuit::<F>::new(max_txs, max_calldata, chain_id, txs);

    let prover = match MockProver::run(k, &circuit, vec![vec![]]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    prover.verify()
}

#[test]
fn tx_circuit_2tx_2max_tx() {
    const NUM_TXS: usize = 2;
    const MAX_TXS: usize = 2;
    const MAX_CALLDATA: usize = 32;

    assert_eq!(
        run::<Fr>(
            mock::CORRECT_MOCK_TXS[..NUM_TXS]
                .iter()
                .map(|tx| Transaction::from(tx.clone()))
                .collect_vec(),
            mock::MOCK_CHAIN_ID.as_u64(),
            MAX_TXS,
            MAX_CALLDATA
        ),
        Ok(())
    );
}

#[test]
fn tx_circuit_1tx_1max_tx() {
    const MAX_TXS: usize = 1;
    const MAX_CALLDATA: usize = 32;

    let chain_id: u64 = mock::MOCK_CHAIN_ID.as_u64();

    let tx: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();

    assert_eq!(run::<Fr>(vec![tx], chain_id, MAX_TXS, MAX_CALLDATA), Ok(()));
}

#[test]
fn tx_circuit_1tx_2max_tx() {
    const MAX_TXS: usize = 2;
    const MAX_CALLDATA: usize = 32;

    let chain_id: u64 = mock::MOCK_CHAIN_ID.as_u64();

    let tx: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();

    assert_eq!(run::<Fr>(vec![tx], chain_id, MAX_TXS, MAX_CALLDATA), Ok(()));
}

#[test]
fn tx_circuit_bad_address() {
    const MAX_TXS: usize = 1;
    const MAX_CALLDATA: usize = 32;

    let mut tx = mock::CORRECT_MOCK_TXS[0].clone();
    // This address doesn't correspond to the account that signed this tx.
    tx.from = AddrOrWallet::from(address!("0x1230000000000000000000000000000000000456"));

    assert!(run::<Fr>(
        vec![tx.into()],
        mock::MOCK_CHAIN_ID.as_u64(),
        MAX_TXS,
        MAX_CALLDATA
    )
    .is_err(),);
}

#[test]
fn variadic_size_check() {
    const MAX_TXS: usize = 2;
    const MAX_CALLDATA: usize = 32;

    let chain_id: u64 = mock::MOCK_CHAIN_ID.as_u64();
    let tx1: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();
    let tx2: Transaction = mock::CORRECT_MOCK_TXS[1].clone().into();
    let circuit = TxCircuit::<Fr>::new(MAX_TXS, MAX_CALLDATA, chain_id, vec![tx1.clone()]);
    let prover1 = MockProver::<Fr>::run(20, &circuit, vec![vec![]]).unwrap();

    let circuit = TxCircuit::<Fr>::new(MAX_TXS, MAX_CALLDATA, chain_id, vec![tx1, tx2]);
    let prover2 = MockProver::<Fr>::run(20, &circuit, vec![vec![]]).unwrap();

    assert_eq!(prover1.fixed(), prover2.fixed());
    assert_eq!(prover1.permutation(), prover2.permutation());
}

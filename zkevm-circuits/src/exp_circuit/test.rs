use bus_mapping::{circuit_input_builder::CircuitInputBuilder, evm::OpcodeId, mock::BlockData};
use eth_types::{bytecode, geth_types::GethData, Bytecode, Word};
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
use halo2_proofs::dev::{MockProver, VerifyFailure};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::{Circuit, ConstraintSystem};
use mock::TestContext;

use crate::evm_circuit::witness::block_convert;
pub use crate::exp_circuit::{ExpCircuit, ExpCircuitConfig};
use crate::table::ExpTable;
use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use crate::witness::Block;
use eth_types::Field;

impl<F: Field> Circuit<F> for ExpCircuit<F> {
    type Config = (ExpCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let exp_table = ExpTable::construct(meta);
        let challenges = Challenges::construct(meta);
        (ExpCircuitConfig::new(meta, exp_table), challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let challenges = challenges.values(&mut layouter);
        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

/// Test exponentiation circuit with the provided block witness
pub fn test_exp_circuit<F: Field>(k: u32, block: Block<F>) -> Result<(), Vec<VerifyFailure>> {
    let circuit = ExpCircuit::<F>::new(block);
    let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
    prover.verify()
}

fn gen_code_single(base: Word, exponent: Word) -> Bytecode {
    bytecode! {
        PUSH32(exponent)
        PUSH32(base)
        EXP
        STOP
    }
}

fn gen_code_multiple(args: Vec<(Word, Word)>) -> Bytecode {
    let mut code = Bytecode::default();
    for (base, exponent) in args.into_iter() {
        code.push(32, exponent);
        code.push(32, base);
        code.write_op(OpcodeId::EXP);
    }
    code.write_op(OpcodeId::STOP);
    code
}

fn gen_data(code: Bytecode) -> CircuitInputBuilder {
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    builder
}

fn test_ok(base: Word, exponent: Word, k: Option<u32>) {
    let code = gen_code_single(base, exponent);
    let builder = gen_data(code);
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_exp_circuit(k.unwrap_or(10), block), Ok(()));
}

fn test_ok_multiple(args: Vec<(Word, Word)>) {
    let code = gen_code_multiple(args);
    let builder = gen_data(code);
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_exp_circuit(20, block), Ok(()));
}

#[test]
fn exp_circuit_single() {
    test_ok(2.into(), 2.into(), None);
    test_ok(3.into(), 7.into(), None);
    test_ok(5.into(), 11.into(), None);
    test_ok(7.into(), 13.into(), None);
    test_ok(11.into(), 17.into(), None);
    test_ok(13.into(), 23.into(), None);
    test_ok(29.into(), 43.into(), None);
    test_ok(41.into(), 259.into(), None);
}

#[test]
fn exp_circuit_big() {
    test_ok(
        2.into(),
        Word::from_str_radix("0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE", 16).unwrap(),
        Some(20),
    );
}

#[test]
fn exp_circuit_multiple() {
    test_ok_multiple(vec![
        (3.into(), 7.into()),
        (5.into(), 11.into()),
        (7.into(), 13.into()),
        (11.into(), 17.into()),
        (13.into(), 23.into()),
        (29.into(), 43.into()),
        (41.into(), 259.into()),
    ]);
}

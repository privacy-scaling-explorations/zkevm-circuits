use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, SimpleFloorPlanner},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
};
use pasta_curves::pallas;
use std::marker::PhantomData;

pub const KECCAK_NUM_ROUNDS: usize = 24;

pub struct ThetaConfig<F> {
    _marker: PhantomData<F>,
}

pub struct RhoConfig<F> {
    _marker: PhantomData<F>,
}

pub struct PiConfig<F> {
    _marker: PhantomData<F>,
}

pub struct XiIotaConfig<F> {
    _marker: PhantomData<F>,
}

pub struct KeccakConfig<F> {
    // Each of these 25 lanes contains a 64-bit word.
    // The first 17 lanes (1088 bits) are used to absorb inputs.
    state: [Column<Advice>; 25],
    theta_config: ThetaConfig<F>,
    rho_config: RhoConfig<F>,
    pi_config: PiConfig<F>,
    xi_iota_config: XiIotaConfig<F>,
}

#[test]
fn keccak_hash() {
    use tiny_keccak::{Hasher, Keccak};
    let mut keccak = Keccak::v256();
    let mut output = [0u8; 32];
    keccak.update(b"foo");
    keccak.update(b"bar");
    keccak.finalize(&mut output);

    let expected = b"\x38\xd1\x8a\xcbg\xd2\\\x8b\xb9\x94'd\xb6/\x18\xe1pT\xf6j\x81{\xd4)T#\xad\xf9\xed\x98\x87>";

    assert_eq!(expected, &output);

    // let message = [Fp::rand(), Fp::rand()];
    // let output = poseidon::Hash::init(OrchardNullifier, ConstantLength::<2>)
    //     .hash(message);

    // let k = 6;
    // let circuit = HashCircuit {
    //     message: Some(message),
    //     output: Some(output),
    // };
    // let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    // assert_eq!(prover.verify(), Ok(()))
}

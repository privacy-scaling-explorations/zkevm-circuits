use halo2:: {
    pasta::Fp,
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Chip},
    plonk::{Circuit, ConstraintSystem, Error},
};

#[derive(Clone, Debug)]
pub struct KeccakConfig<F> {
    foo: F
}

pub struct KeccakChip<F: FieldExt> {
    config: KeccakConfig<F>,
}

impl<F: FieldExt> KeccakChip<F> {
    pub fn configure() -> KeccakConfig<F>{}
    pub fn construct(config: KeccakConfig<F>) -> Self {
        KeccakChip { config }
    }
}

impl<F: FieldExt> Chip<F> for KeccakChip<F> {
    type Config = KeccakConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}


#[derive(Default)]
struct HashCircuit {
    message: Option<[Fp; 2]>,
    output: Option<Fp>,
}

impl Circuit<Fp> for HashCircuit {
    type Config = KeccakConfig<Fp>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> KeccakConfig<Fp> {
    }

    fn synthesize(
        &self,
        config: KeccakConfig<Fp>,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = KeccakChip::construct(config.clone());

    }
}


#[test]
fn keccak_hash() {
    use tiny_keccak::{Keccak, Hasher};
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

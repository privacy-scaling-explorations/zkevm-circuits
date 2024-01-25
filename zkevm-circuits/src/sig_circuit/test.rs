use super::*;
use crate::util::Challenges;
use bus_mapping::circuit_input_builder::keccak_inputs_sign_verify;
use eth_types::sign_types::sign;
use halo2_proofs::{
    arithmetic::Field as HaloField,
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    halo2curves::{
        bn256::Fr,
        group::{Curve, Group},
        CurveAffine,
    },
    plonk::Circuit,
};
use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;

#[derive(Clone, Debug)]
struct TestCircuitSignVerifyConfig<F: Field> {
    sign_verify: SigCircuitConfig<F>,
    challenges: Challenges,
}

impl<F: Field> TestCircuitSignVerifyConfig<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let keccak_table = KeccakTable::construct(meta);
        let sig_table = SigTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let sign_verify = {
            let challenges = challenges.exprs(meta);
            SigCircuitConfig::new(
                meta,
                SigCircuitConfigArgs {
                    keccak_table,
                    sig_table,
                    challenges,
                },
            )
        };

        TestCircuitSignVerifyConfig {
            sign_verify,
            challenges,
        }
    }
}

#[derive(Default)]
struct TestCircuitSignVerify<F: Field> {
    sign_verify: SigCircuit<F>,
}

impl<F: Field> Circuit<F> for TestCircuitSignVerify<F> {
    type Config = TestCircuitSignVerifyConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TestCircuitSignVerifyConfig::new(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = config.challenges.values(&mut layouter);

        self.sign_verify.assign(
            &config.sign_verify,
            &mut layouter,
            &self.sign_verify.signatures,
            &challenges,
        )?;
        config.sign_verify._keccak_table.dev_load(
            &mut layouter,
            &keccak_inputs_sign_verify(&self.sign_verify.signatures),
            &challenges,
        )?;
        config.sign_verify.load_range(&mut layouter)?;
        Ok(())
    }
}

fn run<F: Field>(k: u32, max_verif: usize, signatures: Vec<SignData>) {
    let mut rng = XorShiftRng::seed_from_u64(2);
    let aux_generator = <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();

    // SigCircuit -> ECDSAChip -> MainGate instance column
    let circuit = TestCircuitSignVerify::<F> {
        sign_verify: SigCircuit {
            signatures,
            aux_generator,
            window_size: 4,
            max_verif,
            _marker: PhantomData,
        },
    };

    let prover = match MockProver::run(k, &circuit, vec![vec![]]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    prover.assert_satisfied_par();
}

// Generate a test key pair
fn gen_key_pair(rng: impl RngCore) -> (secp256k1::Fq, Secp256k1Affine) {
    // generate a valid signature
    let generator = Secp256k1Affine::generator();
    let sk = secp256k1::Fq::random(rng);
    let pk = generator * sk;
    let pk = pk.to_affine();

    (sk, pk)
}

// Generate a test message hash
fn gen_msg_hash(rng: impl RngCore) -> secp256k1::Fq {
    secp256k1::Fq::random(rng)
}

// Returns (r, s)
fn sign_with_rng(
    rng: impl RngCore,
    sk: secp256k1::Fq,
    msg_hash: secp256k1::Fq,
) -> (secp256k1::Fq, secp256k1::Fq, u8) {
    let randomness = secp256k1::Fq::random(rng);
    sign(randomness, sk, msg_hash)
}

#[test]
fn sign_verify() {
    // Vectors using `XorShiftRng::seed_from_u64(1)`
    // sk: 0x771bd7bf6c6414b9370bb8559d46e1cedb479b1836ea3c2e59a54c343b0d0495
    // pk: (
    //   0x8e31a3586d4c8de89d4e0131223ecfefa4eb76215f68a691ae607757d6256ede,
    //   0xc76fdd462294a7eeb8ff3f0f698eb470f32085ba975801dbe446ed8e0b05400b
    // )
    // pk_hash: d90e2e9d267cbcfd94de06fa7adbe6857c2c733025c0b8938a76beeefc85d6c7
    // addr: 0x7adbe6857c2c733025c0b8938a76beeefc85d6c7
    let mut rng = XorShiftRng::seed_from_u64(1);
    const MAX_VERIF: usize = 3;
    const NUM_SIGS: usize = 2;
    let mut signatures = Vec::new();
    for _ in 0..NUM_SIGS {
        let (sk, pk) = gen_key_pair(&mut rng);
        let msg_hash = gen_msg_hash(&mut rng);
        let sig = sign_with_rng(&mut rng, sk, msg_hash);
        signatures.push(SignData {
            signature: sig,
            pk,
            msg_hash,
        });
    }

    let k = 19;
    run::<Fr>(k, MAX_VERIF, signatures);
}

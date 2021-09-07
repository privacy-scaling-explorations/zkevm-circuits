use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, SimpleFloorPlanner},
    pasta::Fp,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector,
    },
    poly::Rotation,
};
use itertools::Itertools;
use pasta_curves::pallas;
use std::marker::PhantomData;

pub const KECCAK_NUM_ROUNDS: usize = 24;

pub struct ThetaConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ThetaConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> ThetaConfig<F> {
        meta.create_gate("theta", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let column_sum: [Expression<F>; 5] = (0..5)
                .map(|x| {
                    let state_x0 =
                        meta.query_advice(state[5 * x], Rotation::prev());
                    let state_x1 =
                        meta.query_advice(state[5 * x + 1], Rotation::prev());
                    let state_x2 =
                        meta.query_advice(state[5 * x + 2], Rotation::prev());
                    let state_x3 =
                        meta.query_advice(state[5 * x + 3], Rotation::prev());
                    let state_x4 =
                        meta.query_advice(state[5 * x + 4], Rotation::prev());
                    state_x0 + state_x1 + state_x2 + state_x3 + state_x4;
                })
                .into();

            (0..5)
                .cartesian_product(0..5)
                .map(|(x, y)| {
                    let new_state =
                        meta.query_advice(state[5 * x + y], Rotation::cur());
                    let old_state =
                        meta.query_advice(state[5 * x + y], Rotation::prev());
                    let right = old_state
                        + column_sum[(x + 4) % 5]
                        + Expression::Constant(F::from(13))
                            * column_sum[(x + 1) % 5];
                    q_enable * (new_state - right);
                })
                .into()
        });

        ThetaConfig {
            q_enable,
            state,
            _marker: PhantomData,
        }
    }
}

pub struct RhoConfig<F> {
    _marker: PhantomData<F>,
}

pub struct PiConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> PiConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> PiConfig<F> {
        meta.create_gate("pi", |meta| {
            let q_enable = meta.query_selector(q_enable);
            (0..5)
                .cartesian_product(0..5)
                .map(|(x, y)| {
                    let new_state =
                        meta.query_advice(state[5 * x + y], Rotation::cur());
                    let old_state = meta.query_advice(
                        state[5 * ((x + 3 * y) % 5) + x],
                        Rotation::prev(),
                    );
                    q_enable * (new_state - old_state);
                })
                .into()
        });

        PiConfig {
            q_enable,
            state,
            _marker: PhantomData,
        }
    }
}

pub struct XiIotaConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    round_constant: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> XiIotaConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        round_constant: Column<Advice>,
    ) -> XiIotaConfig<F> {
        let zero = Expression::Constant(F::from(0));
        let two = Expression::Constant(F::from(2));
        let three = Expression::Constant(F::from(3));
        meta.create_gate("xi and iota", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let round_constant =
                meta.query_advice(round_constant, Rotation::cur());
            (0..5)
                .cartesian_product(0..5)
                .map(|(x, y)| {
                    let a =
                        meta.query_advice(state[5 * x + y], Rotation::prev());
                    let x2 = (x + 1) % 5;
                    let b =
                        meta.query_advice(state[5 * x2 + y], Rotation::prev());
                    let x3 = (x + 2) % 5;
                    let c =
                        meta.query_advice(state[5 * x3 + y], Rotation::prev());
                    let d = if x == 0 && y == 0 {
                        round_constant
                    } else {
                        zero
                    };
                    let new_state =
                        meta.query_advice(state[5 * x + y], Rotation::cur());

                    q_enable
                        * (new_state - (two * a + b + three * c + two * d));
                })
                .into()
        });

        XiIotaConfig {
            q_enable,
            state,
            round_constant,
            _marker: PhantomData,
        }
    }
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

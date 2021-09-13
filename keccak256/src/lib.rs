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

pub const ROT_TABLE: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

pub struct RunningSumConfig<F> {
    q_enable: Selector,
    base_13_coef_col: Column<Advice>,
    base_13_slice_col: Column<Advice>,
    base_9_coef_col: Column<Advice>,
    base_9_slice_col: Column<Advice>,
    block_count_col: Column<Advice>,
    base_13_acc_col: Column<Advice>,
    base_9_acc_col: Column<Advice>,
    block_count_acc_col: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RunningSumConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        base_13_coef_col: Column<Advice>,
        base_13_slice_col: Column<Advice>,
        base_9_coef_col: Column<Advice>,
        base_9_slice_col: Column<Advice>,
        block_count_col: Column<Advice>,
        base_13_acc_col: Column<Advice>,
        base_9_acc_col: Column<Advice>,
        block_count_acc_col: Column<Advice>,
        chunk_idx: u64,
        step: u32,
    ) -> RunningSumConfig<F> {
        // TODO: lookup check, block count summing check
        meta.create_gate("running sum", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let base_13_coef =
                meta.query_advice(base_13_coef_col, Rotation::cur());
            let base_13_coef_next =
                meta.query_advice(base_13_coef_col, Rotation::next());
            let base_13_slice =
                meta.query_advice(base_13_slice_col, Rotation::cur());
            let base_9_coef =
                meta.query_advice(base_9_coef_col, Rotation::cur());
            let base_9_coef_next =
                meta.query_advice(base_9_coef_col, Rotation::next());
            let base_9_slice =
                meta.query_advice(base_9_slice_col, Rotation::cur());
            let block_count =
                meta.query_advice(block_count_col, Rotation::cur());
            let base_13_acc =
                meta.query_advice(base_13_acc_col, Rotation::cur());
            let base_13_acc_next =
                meta.query_advice(base_13_acc_col, Rotation::next());
            let base_9_acc = meta.query_advice(base_9_acc_col, Rotation::cur());
            let base_9_acc_next =
                meta.query_advice(base_9_acc_col, Rotation::next());
            let block_count_acc =
                meta.query_advice(block_count_acc_col, Rotation::cur());
            let block_count_acc_next =
                meta.query_advice(block_count_acc_col, Rotation::next());

            let coef_step_13 =
                Expression::Constant(F::from(u64::pow(13, step)));
            let coef_step_9 = Expression::Constant(F::from(u64::pow(9, step)));

            let expr_next_13_coef =
                base_13_coef_next - coef_step_13 * base_13_coef;
            let expr_next_9_coef =
                base_9_coef_next - coef_step_9 * base_13_coef;
            let expr_next_13_acc =
                (base_13_acc_next - base_13_acc) - base_13_coef * base_13_slice;
            let expr_next_9_acc =
                (base_9_acc_next - base_9_acc) - base_9_coef * base_9_slice;
            let expr_next_block_count_acc =
                block_count_acc_next - block_count_acc - block_count;
            // TODO: is this the correct way to check?
            vec![
                q_enable * expr_next_13_coef,
                q_enable * expr_next_9_coef,
                q_enable * expr_next_13_acc,
                q_enable * expr_next_9_acc,
                q_enable * expr_next_block_count_acc,
            ]
        });
        RunningSumConfig {
            q_enable,
            base_13_coef_col,
            base_13_slice_col,
            base_9_coef_col,
            base_9_slice_col,
            block_count_col,
            base_13_acc_col,
            base_9_acc_col,
            block_count_acc_col,
            _marker: PhantomData,
        }
    }
}

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
            let mut column_sum: Vec<Expression<F>> = Vec::new();
            for x in 0..5 {
                let state_x0 = meta.query_advice(state[5 * x], Rotation::cur());
                let state_x1 =
                    meta.query_advice(state[5 * x + 1], Rotation::cur());
                let state_x2 =
                    meta.query_advice(state[5 * x + 2], Rotation::cur());
                let state_x3 =
                    meta.query_advice(state[5 * x + 3], Rotation::cur());
                let state_x4 =
                    meta.query_advice(state[5 * x + 4], Rotation::cur());
                let sum = state_x0 + state_x1 + state_x2 + state_x3 + state_x4;
                column_sum.push(sum.clone());
            }
            let mut checks: Vec<Expression<F>> = Vec::new();

            for (x, y) in (0..5).cartesian_product(0..5) {
                let new_state =
                    meta.query_advice(state[5 * x + y], Rotation::next());
                let old_state =
                    meta.query_advice(state[5 * x + y], Rotation::cur());
                let right = old_state
                    + column_sum[(x + 4) % 5].clone()
                    + Expression::Constant(F::from(13))
                        * column_sum[(x + 1) % 5].clone();
                let check = q_enable.clone() * (new_state - right);
                checks.push(check.clone());
            }
            checks
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

impl<F: FieldExt> RhoConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) {
        meta.create_gate("rho", |meta| {});
    }
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
            let mut checks: Vec<Expression<F>> = Vec::new();
            for (x, y) in (0..5).cartesian_product(0..5) {
                let old_state = meta.query_advice(
                    state[5 * ((x + 3 * y) % 5) + x],
                    Rotation::cur(),
                );
                let new_state =
                    meta.query_advice(state[5 * x + y], Rotation::next());

                let check = q_enable.clone() * (new_state - old_state);
                checks.push(check.clone());
            }
            checks
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
            let mut checks: Vec<Expression<F>> = Vec::new();
            for (x, y) in (0..5).cartesian_product(0..5) {
                let a = meta.query_advice(state[5 * x + y], Rotation::cur());
                let x2 = (x + 1) % 5;
                let b = meta.query_advice(state[5 * x2 + y], Rotation::cur());
                let x3 = (x + 2) % 5;
                let c = meta.query_advice(state[5 * x3 + y], Rotation::cur());
                let d = if x == 0 && y == 0 {
                    round_constant.clone()
                } else {
                    zero.clone()
                };
                let new_state =
                    meta.query_advice(state[5 * x + y], Rotation::next());

                let check = q_enable.clone()
                    * (new_state
                        - (two.clone() * a
                            + b
                            + three.clone() * c
                            + two.clone() * d));
                checks.push(check.clone());
            }
            checks
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

use self::padding::PaddingConfig;
use crate::{
    keccak_arith::Keccak,
    permutation::{
        mixing::MixingConfig,
        tables::{FromBase9TableConfig, RangeCheckConfig},
    },
};
use eth_types::Field;
use gadgets::expression::*;
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Instance, Selector},
    poly::Rotation,
};

pub mod padding;
pub mod word_builder;

pub const MAX_INPUT_BYTES: usize = MAX_INPUT_WORDS * BYTES_PER_WORD;
pub const MAX_INPUT_WORDS: usize = MAX_PERM_ROUNDS * NEXT_INPUTS_WORDS;
pub const BYTES_PER_WORD: usize = 8;
pub const NEXT_INPUTS_WORDS: usize = 17;
pub const MAX_PERM_ROUNDS: usize = 10;

#[derive(Debug, Clone, Copy)]
/// Represents the State tag that represents which State is the permutation
/// representing.
pub enum StateTag {
    Start = 0,
    Continue = 1,
    Finalize = 2,
    End = 3,
}

pub struct KeccakConfig<F: Field> {
    table: FromBase9TableConfig<F>,
    round_ctant_b9: Column<Advice>,
    round_ctant_b13: Column<Advice>,
    round_constants_b9: Column<Instance>,
    round_constants_b13: Column<Instance>,
    mixing_config: MixingConfig<F>,
    padding_config: PaddingConfig<F>,
    q_enable: Selector,
    state_tag: Column<Advice>,
    input_len: Column<Advice>,
    input: Column<Advice>,
    input_padded: Column<Advice>,
    perm_count: Column<Advice>,
    acc_input: Column<Advice>,
    output_rlc: Column<Advice>,
    range_check_config: RangeCheckConfig<F, 136>,
}

impl<F: Field> KeccakConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let round_ctant_b9 = meta.advice_column();
        let round_ctant_b13 = meta.advice_column();
        let round_constants_b9 = meta.instance_column();
        let round_constants_b13 = meta.instance_column();

        meta.enable_equality(round_ctant_b9);
        meta.enable_equality(round_ctant_b13);

        let padding_config = PaddingConfig::configure(meta);

        let table = FromBase9TableConfig::configure(meta);
        let mixing_config = MixingConfig::configure(
            meta,
            &table,
            round_ctant_b9,
            round_ctant_b13,
            round_constants_b9,
            round_constants_b13,
        );

        let q_enable = meta.selector();
        let randomness = meta.instance_column();
        let state_tag = meta.advice_column();
        let input_len = meta.advice_column();
        let input = meta.advice_column();
        let input_padded = meta.advice_column();
        let perm_count = meta.advice_column();
        let acc_input = meta.advice_column();
        let output_rlc = meta.advice_column();
        let range_check_136 = RangeCheckConfig::<F, 136>::configure(meta);

        // Lookup to activate the valid Finalize place check
        // `(curr.perm_count * 136 - input_len) in 1~136`
        meta.lookup("Valid Finalize place", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let state_tag = meta.query_advice(state_tag, Rotation::cur());
            let input_len = meta.query_advice(input_len, Rotation::cur());
            let perm_count = meta.query_advice(perm_count, Rotation::cur());
            let state_finalize = generate_lagrange_base_polynomial(state_tag, 2, 0..=3);
            let perm_lookup_val = perm_count * Expression::Constant(F::from(136u64)) - input_len;
            // TODO: Permutation + Padding
            vec![(
                q_enable * state_finalize * perm_lookup_val,
                range_check_136.range,
            )]
        });

        // TODO: Pending to do the Lookup for the Permutation RLC check multipliyng the
        // selector by the is_continue_state tag
        meta.lookup("Valid permutation + padding", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let state_tag = meta.query_advice(state_tag, Rotation::cur());
            let input_len = meta.query_advice(input_len, Rotation::cur());
            let perm_count = meta.query_advice(perm_count, Rotation::cur());
            let state_continue = generate_lagrange_base_polynomial(state_tag, 1, 0..=3);

            // We check: `input_len - (136 * (perm_count + 1))`. If it evaluates to 0, we
            // need to pad and absorb.
            let have_to_pad_and_absorb = input_len
                - (Expression::Constant(F::from(136u64))
                    * (perm_count.clone() + Expression::Constant(F::one())));
            vec![(
                q_enable * state_con * perm_lookup_val,
                range_check_136.range,
            )]
        });

        /*
        1. Send to NewConfig: input_RLC, padded_input_RLC and output_RLC
        2. get_allocated_state and next_inputs and check `input_rlc` matches.
        3. Compute permutation with padde_input and check output_rlc
        */

        meta.create_gate("Start State", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let randomness = meta.query_instance(randomness, Rotation::cur());
            let next_state_tag = meta.query_advice(state_tag, Rotation::next());
            let state_tag = meta.query_advice(state_tag, Rotation::cur());
            let input_len = meta.query_advice(input_len, Rotation::cur());
            let next_input = meta.query_advice(input, Rotation::next());
            let input = meta.query_advice(input, Rotation::cur());
            let next_perm_count = meta.query_advice(perm_count, Rotation::next());
            let perm_count = meta.query_advice(perm_count, Rotation::cur());
            let next_acc_input = meta.query_advice(acc_input, Rotation::next());
            let acc_input = meta.query_advice(acc_input, Rotation::cur());
            let output_rlc = meta.query_advice(output_rlc, Rotation::cur());

            let state_start = generate_lagrange_base_polynomial(state_tag.clone(), 0, 0..=3);
            let state_continue = generate_lagrange_base_polynomial(state_tag.clone(), 1, 0..=3);
            let state_finalize = generate_lagrange_base_polynomial(state_tag.clone(), 2, 0..=3);
            let state_end = generate_lagrange_base_polynomial(state_tag, 3, 0..=3);

            let next_state_start =
                generate_lagrange_base_polynomial(next_state_tag.clone(), 0, 0..=3);
            let next_state_continue =
                generate_lagrange_base_polynomial(next_state_tag.clone(), 1, 0..=3);
            let next_state_finalize =
                generate_lagrange_base_polynomial(next_state_tag.clone(), 2, 0..=3);
            let next_state_end =
                generate_lagrange_base_polynomial(next_state_tag.clone(), 3, 0..=3);

            // We need to make sure that the lagrange interpolation results are boolean.
            // This expressions will be zero if the values are boolean.
            let is_bool_cur_state_start = bool_constraint_expr(state_start.clone());
            let is_bool_cur_state_continue = bool_constraint_expr(state_continue.clone());
            let is_bool_cur_state_finalize = bool_constraint_expr(state_finalize.clone());
            let is_bool_cur_state_end = bool_constraint_expr(state_end.clone());

            let is_bool_next_state_start = bool_constraint_expr(next_state_start.clone());
            let is_bool_next_state_continue = bool_constraint_expr(next_state_continue.clone());
            let is_bool_next_state_finalize = bool_constraint_expr(next_state_finalize.clone());
            let is_bool_next_state_end = bool_constraint_expr(next_state_end.clone());

            // ------------------------------------------------------- //
            // --------------------- Start State --------------------- //
            // ------------------------------------------------------- //

            // Constrain `current_state_tag = Start` && `next_state_tag in (Continue,
            // Finalize, End)` Note that the second condition is constrained via
            // negation. If it's not within `(Continue, Finalize, End)` it has to be
            // `Start`.
            let start_tag_correctness = (Expression::Constant(F::one()) - next_state_start)
                + is_bool_cur_state_start
                + is_bool_next_state_start;

            // Check `input_len === input === perm_count === acc_input === output === 0`
            // We do also need to make sure that we can't add non-binary numbers and get a
            // 0.
            let zero_assumptions = bool_constraint_expr(input_len.clone())
                + input_len.clone()
                + bool_constraint_expr(input.clone())
                + input
                + bool_constraint_expr(perm_count.clone())
                + perm_count.clone()
                + bool_constraint_expr(acc_input.clone())
                + acc_input.clone()
                + bool_constraint_expr(output_rlc.clone())
                + output_rlc;

            let start_constraint =
                (q_enable.clone() * state_start) * (start_tag_correctness + zero_assumptions);

            // ------------------------------------------------------- //
            // -------------------- Continue State ------------------- //
            // ------------------------------------------------------- //

            let absortion_check = {
                // `next.state_tag === Finalize`
                let next_state_tag_absortion = is_bool_next_state_finalize
                    + (Expression::Constant(F::one()) - next_state_finalize.clone());
                let next_input_is_zero =
                    next_input.clone() + bool_constraint_expr(next_input.clone());
                let have_to_pad_and_absorb = input_len
                    - (Expression::Constant(F::from(136u64))
                        * (perm_count.clone() + Expression::Constant(F::one())));

                // Absortion check
                state_continue.clone()
                    * have_to_pad_and_absorb
                    * (next_state_tag_absortion + next_input_is_zero)
            };

            // `next.acc_input === curr.acc_input * r**136 + next.input`
            let next_row_validity_input = next_acc_input.clone()
                - (acc_input.clone() * square_and_multiply(randomness, 136))
                + next_input;
            // `next.perm_count === curr.perm_count + 1`
            let next_row_validity_perm_count =
                next_perm_count.clone() - perm_count + Expression::Constant(F::one());
            // `next.state_tag in (Continue, Finalize)`
            let next_state_continue_or_finalize = (Expression::Constant(F::one())
                - next_state_finalize.clone())
                * (Expression::Constant(F::one()) - next_state_continue.clone());

            // Next Row validity + State transition Continue
            let continue_constraint = (q_enable.clone() * state_continue)
                * (next_row_validity_input
                    + next_row_validity_perm_count
                    + next_state_continue_or_finalize);

            // ------------------------------------------------------- //
            // -------------------- Finalize State ------------------- //
            // ------------------------------------------------------- //

            // Note that `(curr.perm_count * 136 - input_len) in 1~136` is checked in the
            // lookup table above.

            let next_row_validity_perm_count = next_perm_count - Expression::Constant(F::one());
            let next_row_validity_input = next_acc_input - acc_input;

            // State transition: (Continue, Finalize, End) all 3 states allowed
            let state_transition_finalize = (Expression::Constant(F::one()) - next_state_continue)
                * (Expression::Constant(F::one()) - next_state_finalize)
                * (Expression::Constant(F::one()) - next_state_end.clone());

            let finalize_constraint = (q_enable * state_finalize)
                * (state_transition_finalize
                    + next_row_validity_input
                    + next_row_validity_perm_count);

            // ------------------------------------------------------- //
            // ---------------------- End State ---------------------- //
            // ------------------------------------------------------- //

            // State transition: next.state_tag === End
            let end_constraint = state_end * (Expression::Constant(F::one()) - next_state_end);

            vec![
                start_constraint,
                continue_constraint,
                finalize_constraint,
                end_constraint,
            ]
        });

        Self {
            table,
            round_ctant_b9,
            round_ctant_b13,
            round_constants_b9,
            round_constants_b13,
            mixing_config,
            padding_config,
            q_enable,
            state_tag,
            input_len,
            input,
            input_padded,
            perm_count,
            acc_input,
            output_rlc,
            range_check_config: range_check_136,
        }
    }
}

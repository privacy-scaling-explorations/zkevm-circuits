use self::padding::PaddingConfig;
use crate::{
    keccak_arith::Keccak,
    permutation::{mixing::MixingConfig, tables::FromBase9TableConfig},
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
    input_no_padding: Column<Advice>,
    input_rlc: Column<Advice>,
    perm_count: Column<Advice>,
    acc_input: Column<Advice>,
    output_rlc: Column<Advice>,
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
        let state_tag = meta.advice_column();
        let input_len = meta.advice_column();
        let input_no_padding = meta.advice_column();
        let input_rlc = meta.advice_column();
        let perm_count = meta.advice_column();
        let acc_input = meta.advice_column();
        let output_rlc = meta.advice_column();

        meta.create_gate("Start State", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let next_state_tag = meta.query_advice(state_tag, Rotation::next());
            let state_tag = meta.query_advice(state_tag, Rotation::cur());
            let input_len = meta.query_advice(input_len, Rotation::cur());
            let input_no_padding = meta.query_advice(input_no_padding, Rotation::cur());
            let input_rlc = meta.query_advice(input_rlc, Rotation::cur());
            let perm_count = meta.query_advice(perm_count, Rotation::cur());
            let acc_input = meta.query_advice(acc_input, Rotation::cur());
            let output_rlc = meta.query_advice(output_rlc, Rotation::cur());

            let state_start = generate_lagrange_base_polynomial(state_tag.clone(), 0, 0..=3);
            let state_continue = generate_lagrange_base_polynomial(state_tag.clone(), 1, 0..=3);
            let state_finalize = generate_lagrange_base_polynomial(state_tag.clone(), 2, 0..=3);
            let state_end = generate_lagrange_base_polynomial(state_tag, 3, 0..=3);

            let next_state_start =
                generate_lagrange_base_polynomial(next_state_tag.clone(), 0, 0..=3);

            // We need to make sure that the lagrange interpolation results are boolean.
            // This expressions will be zero if the values are boolean.
            let is_bool_cur_state_start = bool_constraint_expr(state_start.clone());
            let is_bool_cur_state_continue = bool_constraint_expr(state_continue.clone());
            let is_bool_cur_state_finalize = bool_constraint_expr(state_finalize.clone());
            let is_bool_cur_state_end = bool_constraint_expr(state_end.clone());

            let is_bool_next_state_start = bool_constraint_expr(next_state_start.clone());

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
                + bool_constraint_expr(input_no_padding.clone())
                + input_no_padding
                + bool_constraint_expr(perm_count.clone())
                + perm_count.clone()
                + bool_constraint_expr(acc_input.clone())
                + acc_input
                + bool_constraint_expr(output_rlc.clone())
                + output_rlc;

            // ------------------------------------------------------- //
            // -------------------- Continue State ------------------- //
            // ------------------------------------------------------- //

            let next_state_is_finalize =
                generate_lagrange_base_polynomial(next_state_tag, 1, 0..=3);

            // We need to make sure that the lagrange interpolation results are boolean.
            // This expressions will be zero if the values are boolean.
            let is_bool_next_finalize_state = bool_constraint_expr(next_state_is_finalize.clone());

            // We check: `input_len - (136 * (perm_count + 1))`. If it evaluates to 0, we
            // need to pad and absorb.
            let have_to_pad_and_absorb = input_len
                - (Expression::Constant(F::from(136u64))
                    * (perm_count + Expression::Constant(F::one())));

            vec![Expression::Constant(F::zero())]
            //[(q_enable * state_start) * (start_tag_correctness + zero_assumptions)]
        });

        unimplemented!()
    }
}

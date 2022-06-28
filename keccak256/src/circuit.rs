use self::padding::PaddingConfig;
use crate::common::State;
use crate::rlc::RlcConfig;
use crate::{
    keccak_arith::Keccak,
    permutation::{
        base_conversion::BaseConversionConfig,
        circuit::KeccakFConfig,
        mixing::MixingConfig,
        tables::{FromBase9TableConfig, FromBinaryTableConfig, RangeCheckConfig},
        NextInput, PermutationInputs,
    },
};
use eth_types::Field;
use gadgets::expression::*;
use halo2_proofs::circuit::{layouter, Region};
use halo2_proofs::plonk::Assignment;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use std::convert::TryFrom;
use std::convert::TryInto;

pub mod padding;
pub mod word_builder;

pub const MAX_INPUT_BYTES: usize = MAX_INPUT_WORDS * BYTES_PER_WORD;
pub const MAX_INPUT_WORDS: usize = MAX_PERM_ROUNDS * NEXT_INPUTS_WORDS;
pub const BYTES_PER_WORD: usize = 8;
pub const NEXT_INPUTS_WORDS: usize = 17;
pub const NEXT_INPUTS_BYTES: usize = NEXT_INPUTS_WORDS * 8;
pub const STATE_WORDS: usize = 25;
pub const MAX_PERM_ROUNDS: usize = 10;

pub type AssignedState<F> = [AssignedCell<F, F>; STATE_WORDS];
pub type AssignedNextInput<F> = [AssignedCell<F, F>; NEXT_INPUTS_BYTES];

#[derive(Debug, Clone, Copy)]
/// Represents the State tag that represents which State is the permutation
/// representing.
pub enum StateTag {
    Start,
    Continue,
    Finalize,
    End,
}

impl StateTag {
    pub fn into_f<F: Field>(&self) -> F {
        match self {
            StateTag::Start => F::zero(),
            StateTag::Continue => F::one(),
            StateTag::Finalize => F::from(2u64),
            StateTag::End => F::from(3u64),
        }
    }

    pub fn is_continue(&self) -> bool {
        match self {
            StateTag::Continue => true,
            _ => false,
        }
    }

    pub fn is_finalize(&self) -> bool {
        match self {
            StateTag::Finalize => true,
            _ => false,
        }
    }

    pub fn is_end(&self) -> bool {
        match self {
            StateTag::End => true,
            _ => false,
        }
    }
}

/*
KeccakConfig
1. Fill lookup rows from other circuits which hold a &mut to the Config (or similar)
2. Once a hash is added it includes all the constraints that valiodate that the hash is correct.


KeccakTable {

}
keccakt_table.add_hash(&[u8])
keccak_table.lookup()
*/

#[derive(Debug, Clone)]
pub struct AssignedPermInput<F: Field> {
    state_tag: AssignedCell<F, F>,
    input_len: AssignedCell<F, F>,
    input: AssignedCell<F, F>,
    perm_count: AssignedCell<F, F>,
    acc_input: AssignedCell<F, F>,
    output: AssignedCell<F, F>,
}

impl<F: Field> AssignedPermInput<F> {
    fn new(
        state_tag: AssignedCell<F, F>,
        input_len: AssignedCell<F, F>,
        input: AssignedCell<F, F>,
        perm_count: AssignedCell<F, F>,
        acc_input: AssignedCell<F, F>,
        output: AssignedCell<F, F>,
    ) -> Self {
        Self {
            state_tag,
            input_len,
            input,
            perm_count,
            acc_input,
            output,
        }
    }
}

pub struct KeccakConfig<F: Field> {
    base_conv_b9_b13: BaseConversionConfig<F>,
    base_conv_b2_b9: BaseConversionConfig<F>,
    round_ctant_b9: Column<Advice>,
    round_ctant_b13: Column<Advice>,
    round_constants_b9: Column<Instance>,
    round_constants_b13: Column<Instance>,
    pub(crate) keccak_f_config: KeccakFConfig<F>,
    pub(crate) padding_config: PaddingConfig<F>,
    q_enable: Selector,
    state: [Column<Advice>; STATE_WORDS],
    next_inputs: [Column<Advice>; NEXT_INPUTS_BYTES + 1],
    state_tag: Column<Advice>,
    input_len: Column<Advice>,
    input: Column<Advice>,
    perm_count: Column<Advice>,
    acc_input: Column<Advice>,
    output_rlc: Column<Advice>,
    range_check_config: RangeCheckConfig<F, 136>,
    state_rlc_config: RlcConfig<F, STATE_WORDS>,
    absorb_inputs_rlc_config: RlcConfig<F, NEXT_INPUTS_BYTES>,
    acc_input_rlc_config: RlcConfig<F, { NEXT_INPUTS_BYTES + 1 }>,
    randomness: Column<Advice>,
    last_state: Option<AssignedState<F>>,
    last_perm: Option<AssignedPermInput<F>>,
    latest_acc_randomness: Option<AssignedCell<F, F>>,
}

impl<F: Field> KeccakConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let round_ctant_b9 = meta.advice_column();
        let round_ctant_b13 = meta.advice_column();
        let round_constants_b9 = meta.instance_column();
        let round_constants_b13 = meta.instance_column();

        meta.enable_equality(round_ctant_b9);
        meta.enable_equality(round_ctant_b13);

        let base_conv_lane = meta.advice_column();
        meta.enable_equality(base_conv_lane);

        let flag = meta.advice_column();
        meta.enable_equality(flag);

        let randomness = meta.advice_column();
        meta.enable_equality(randomness);

        let padding_config = PaddingConfig::configure(meta);

        let table_b9 = FromBase9TableConfig::configure(meta);
        let table_b2 = FromBinaryTableConfig::configure(meta);
        let base_conv_b9_b13 = BaseConversionConfig::configure(
            meta,
            table_b9.get_base_info(false),
            base_conv_lane,
            flag,
        );
        let base_conv_b2_b9 = BaseConversionConfig::configure(
            meta,
            table_b2.get_base_info(true),
            base_conv_lane,
            flag,
        );

        let state = [(); 25].map(|_| meta.advice_column()).map(|col| {
            meta.enable_equality(col);
            col
        });

        // The first position always stores the latest acc_input.
        let next_inputs = [(); NEXT_INPUTS_BYTES + 1]
            .map(|_| meta.advice_column())
            .map(|col| {
                meta.enable_equality(col);
                col
            });

        let q_enable = meta.selector();
        let state_tag = meta.advice_column();
        let input_len = meta.advice_column();
        let input = meta.advice_column();
        let perm_count = meta.advice_column();
        let acc_input = meta.advice_column();
        let output_rlc = meta.advice_column();
        let range_check_136 = RangeCheckConfig::<F, 136>::configure(meta);

        let state_rlc_config = RlcConfig::configure(meta, state, randomness, output_rlc);
        let absorb_inputs_rlc_config = RlcConfig::configure(
            meta,
            next_inputs[1..].try_into().unwrap(),
            randomness,
            output_rlc,
        );
        let acc_input_rlc_config = RlcConfig::configure(meta, next_inputs, randomness, acc_input);

        let keccak_f_config = KeccakFConfig::configure(
            meta,
            state,
            base_conv_b9_b13.clone(),
            base_conv_b2_b9.clone(),
            base_conv_lane,
            flag,
        );

        // Lookup to activate the valid Finalize place check
        // `(curr.perm_count * 136 - input_len) in 1~136`
        meta.lookup("Valid Finalize place", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let state_tag = meta.query_advice(state_tag, Rotation::cur());
            let input_len = meta.query_advice(input_len, Rotation::cur());
            let perm_count = meta.query_advice(perm_count, Rotation::cur());
            let state_finalize = generate_lagrange_base_polynomial(state_tag, 2, 0..=3);
            let perm_lookup_val = perm_count * Expression::Constant(F::from(136u64)) - input_len;
            vec![(
                q_enable * state_finalize * perm_lookup_val,
                range_check_136.range,
            )]
        });

        meta.create_gate("State gate", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let randomness = meta.query_advice(randomness, Rotation::cur());
            let next_state_tag = meta.query_advice(state_tag, Rotation::next());
            let state_tag = meta.query_advice(state_tag, Rotation::cur());
            let input_len = meta.query_advice(input_len, Rotation::cur());
            let next_input = meta.query_advice(input, Rotation::next());
            let input = meta.query_advice(input, Rotation::cur());
            let next_perm_count = meta.query_advice(perm_count, Rotation::next());
            let perm_count = meta.query_advice(perm_count, Rotation::cur());
            let next_acc_input = meta.query_advice(acc_input, Rotation::next());
            let acc_input = meta.query_advice(acc_input, Rotation::cur());
            let expected_output_rlc = meta.query_advice(output_rlc, Rotation::next());
            let output_rlc = meta.query_advice(output_rlc, Rotation::cur());

            let state_start = generate_lagrange_base_polynomial(state_tag.clone(), 0, 0..=3);
            let state_continue = generate_lagrange_base_polynomial(state_tag.clone(), 1, 0..=3);
            let state_finalize = generate_lagrange_base_polynomial(state_tag.clone(), 2, 0..=3);
            let state_end = generate_lagrange_base_polynomial(state_tag, 3, 0..=3);

            let next_state_start = Expression::Constant(F::one())
                - generate_lagrange_base_polynomial(next_state_tag.clone(), 0, 0..=3);
            let next_state_continue = Expression::Constant(F::one())
                - generate_lagrange_base_polynomial(next_state_tag.clone(), 1, 0..=3);
            let next_state_finalize = Expression::Constant(F::one())
                - generate_lagrange_base_polynomial(next_state_tag.clone(), 2, 0..=3);
            let next_state_end = Expression::Constant(F::one())
                - generate_lagrange_base_polynomial(next_state_tag.clone(), 3, 0..=3);

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

            let bool_state_checks = q_enable.clone()
                * (is_bool_cur_state_start
                    + is_bool_cur_state_continue
                    + is_bool_cur_state_finalize
                    + is_bool_cur_state_end
                    + is_bool_next_state_start
                    + is_bool_next_state_continue
                    + is_bool_next_state_finalize
                    + is_bool_next_state_end);
            // ------------------------------------------------------- //
            // --------------------- Start State --------------------- //
            // ------------------------------------------------------- //

            // Constrain `current_state_tag = Start` && `next_state_tag in (Continue,
            // Finalize, End)` Note that the second condition is constrained via
            // negation. If it's not within `(Continue, Finalize, End)` it has to be
            // `Start`.
            //
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
                (q_enable.clone() * state_start) * (next_state_start + zero_assumptions);

            // ------------------------------------------------------- //
            // -------------------- Continue State ------------------- //
            // ------------------------------------------------------- //

            // TODO: Figure out if the constraint for each permutation is needed.
            let absortion_check = {
                // `next.state_tag === Finalize`
                let next_input_is_zero =
                    next_input.clone() + bool_constraint_expr(next_input.clone());
                let have_to_pad_and_absorb = input_len
                    - (Expression::Constant(F::from(136u64))
                        * (perm_count.clone() + Expression::Constant(F::one())));

                // Absortion check
                state_continue.clone()
                    * have_to_pad_and_absorb
                    * (next_state_finalize.clone() + next_input_is_zero)
                //* (expected_output_rlc - output_rlc)
                // Not sure this is needed. We will end up with the final
                // out_rlc which is the one we will use and it's linked to all
                // the previous ones.
            };

            // `next.acc_input === curr.acc_input * r**136 + next.input`
            let next_row_validity_input = next_acc_input.clone()
                - (acc_input.clone() * square_and_multiply(randomness, 136))
                + next_input;
            // `next.perm_count === curr.perm_count + 1`
            let next_row_validity_perm_count =
                next_perm_count.clone() - perm_count + Expression::Constant(F::one());
            // `next.state_tag in (Continue, Finalize)`
            let next_state_continue_or_finalize =
                next_state_finalize.clone() * next_state_continue.clone();

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
            let state_transition_finalize =
                next_state_continue * next_state_finalize * next_state_end.clone();

            let finalize_constraint = (q_enable * state_finalize)
                * (state_transition_finalize
                    + next_row_validity_input
                    + next_row_validity_perm_count);

            // ------------------------------------------------------- //
            // ---------------------- End State ---------------------- //
            // ------------------------------------------------------- //

            // State transition: next.state_tag === End
            let end_constraint = state_end * next_state_end;

            vec![
                bool_state_checks,
                start_constraint,
                continue_constraint,
                finalize_constraint,
                end_constraint,
            ]
        });

        Self {
            base_conv_b9_b13,
            base_conv_b2_b9,
            round_ctant_b9,
            round_ctant_b13,
            round_constants_b9,
            round_constants_b13,
            keccak_f_config,
            padding_config,
            q_enable,
            state,
            next_inputs,
            state_tag,
            input_len,
            input,
            perm_count,
            acc_input,
            output_rlc,
            range_check_config: range_check_136,
            state_rlc_config,
            absorb_inputs_rlc_config,
            randomness,
            acc_input_rlc_config,
            last_state: None,
            last_perm: None,
            latest_acc_randomness: None,
        }
    }

    pub fn assign_hash(
        &mut self,
        layouter: &mut impl Layouter<F>,
        hash_data: &[u8],
        output: [u8; 32],
    ) -> Result<(), Error> {
        // If this is the first hash, we need to add an `Start` state first.
        if self.last_state.is_none() {
            let (start_state_perm, init_state, _init_absorb) = self.assign_start_state(layouter)?;
            self.last_state = Some(init_state);
            self.last_perm = Some(start_state_perm);
            self.latest_acc_randomness = Some(layouter.assign_region(
                || "Assign init_state",
                |mut region| {
                    // Dummy randomness
                    region.assign_advice(|| "randomness", self.randomness, 0, || Ok(F::one()))
                },
            )?);
        }

        // Fetch all the permutations we will need to assign.
        let perm_inputs = PermutationInputs::<F>::from_bytes(hash_data);

        // Init dummy randomness
        let randomness = layouter.assign_region(
            || "Assign init_state",
            |mut region| {
                // Dummy randomness
                region.assign_advice(|| "randomness", self.randomness, 0, || Ok(F::one()))
            },
        )?;

        // Init acc_len for this hash input.
        let mut acc_len = 0;

        // Assign the first permutation of the hash.
        acc_len += perm_inputs.0.first().unwrap().og_len;
        let (first_perm, first_state_out) = self.assign_permutation(
            layouter,
            self.last_state.clone().unwrap(),
            self.last_perm.clone().unwrap(),
            perm_inputs.0.first().cloned().unwrap(),
            acc_len,
            randomness.clone(),
        )?;
        // Store the actual latest state and permutation inside the config.
        self.last_state = Some(first_state_out);
        self.last_perm = Some(first_perm);

        for next_perm in perm_inputs.0.iter().skip(1) {
            acc_len += perm_inputs.0.first().unwrap().og_len;
            let (perm, state) = self.assign_permutation(
                layouter,
                self.last_state.clone().unwrap(),
                self.last_perm.clone().unwrap(),
                next_perm.clone(),
                acc_len,
                randomness.clone(),
            )?;

            // Store the actual latest state and permutation inside the config.
            self.last_state = Some(state);
            self.last_perm = Some(perm);
        }

        // TODO: Include the input_RLC and output_RLC into the lookup table as an entry.

        Ok(())
    }

    pub fn assign_start_state(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(AssignedPermInput<F>, AssignedState<F>, AssignedNextInput<F>), Error> {
        let (state_tag, input_len, input, perm_count, acc_input, output, in_state, absorb_inputs) =
            layouter.assign_region(
                || "Start state",
                |mut region| {
                    let state_tag = region.assign_advice(
                        || "State_tag ",
                        self.state_tag,
                        0,
                        || Ok(F::zero()),
                    )?;
                    let input_len = region.assign_advice(
                        || "Input len",
                        self.input_len,
                        0,
                        || Ok(F::zero()),
                    )?;
                    let input =
                        region.assign_advice(|| "Input rlc", self.input, 0, || Ok(F::zero()))?;
                    let perm_count = region.assign_advice(
                        || "Perm count",
                        self.perm_count,
                        0,
                        || Ok(F::zero()),
                    )?;
                    let acc_input = region.assign_advice(
                        || "Acc Input",
                        self.acc_input,
                        0,
                        || Ok(F::zero()),
                    )?;

                    let output = region.assign_advice(
                        || "Acc Input",
                        self.output_rlc,
                        0,
                        || Ok(F::zero()),
                    )?;

                    let state: [AssignedCell<F, F>; STATE_WORDS] = (0..STATE_WORDS)
                        .map(|idx| -> Result<AssignedCell<F, F>, Error> {
                            region.assign_advice(
                                || "input_state init",
                                self.state[idx],
                                0,
                                || Ok(F::zero()),
                            )
                        })
                        .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?
                        .try_into()
                        .unwrap();

                    // The first position is reserved to the
                    let absorb_inputs: [AssignedCell<F, F>; NEXT_INPUTS_BYTES] = (1
                        ..=NEXT_INPUTS_BYTES)
                        .map(|idx| -> Result<AssignedCell<F, F>, Error> {
                            region.assign_advice(
                                || "input_state init",
                                self.next_inputs[idx],
                                0,
                                || Ok(F::zero()),
                            )
                        })
                        .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?
                        .try_into()
                        .unwrap();
                    Ok((
                        state_tag,
                        input_len,
                        input,
                        perm_count,
                        acc_input,
                        output,
                        state,
                        absorb_inputs,
                    ))
                },
            )?;
        Ok((
            AssignedPermInput {
                state_tag,
                input_len,
                input,
                perm_count,
                acc_input,
                output,
            },
            in_state,
            absorb_inputs,
        ))
    }

    pub fn assign_end_state(
        &mut self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(AssignedPermInput<F>, AssignedState<F>, AssignedNextInput<F>), Error> {
        let (state_tag, input_len, input, perm_count, acc_input, output, in_state, absorb_inputs) =
            layouter.assign_region(
                || "End state",
                |mut region| {
                    let state_tag = region.assign_advice(
                        || "State_tag ",
                        self.state_tag,
                        0,
                        || Ok(StateTag::End.into_f()),
                    )?;
                    let input_len = region.assign_advice(
                        || "Input len",
                        self.input_len,
                        0,
                        || Ok(F::zero()),
                    )?;
                    let input =
                        region.assign_advice(|| "Input rlc", self.input, 0, || Ok(F::zero()))?;
                    let perm_count = region.assign_advice(
                        || "Perm count",
                        self.perm_count,
                        0,
                        || Ok(F::zero()),
                    )?;
                    let acc_input = region.assign_advice(
                        || "Acc Input",
                        self.acc_input,
                        0,
                        || Ok(F::zero()),
                    )?;

                    let output = region.assign_advice(
                        || "Acc Input",
                        self.output_rlc,
                        0,
                        || Ok(F::zero()),
                    )?;

                    let state: [AssignedCell<F, F>; STATE_WORDS] = (0..STATE_WORDS)
                        .map(|idx| -> Result<AssignedCell<F, F>, Error> {
                            region.assign_advice(
                                || "input_state init",
                                self.state[idx],
                                0,
                                || Ok(F::zero()),
                            )
                        })
                        .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?
                        .try_into()
                        .unwrap();
                    let absorb_inputs: [AssignedCell<F, F>; NEXT_INPUTS_BYTES] = (1
                        ..NEXT_INPUTS_BYTES + 1)
                        .map(|idx| -> Result<AssignedCell<F, F>, Error> {
                            region.assign_advice(
                                || "input_state init",
                                self.next_inputs[idx],
                                0,
                                || Ok(F::zero()),
                            )
                        })
                        .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?
                        .try_into()
                        .unwrap();
                    Ok((
                        state_tag,
                        input_len,
                        input,
                        perm_count,
                        acc_input,
                        output,
                        state,
                        absorb_inputs,
                    ))
                },
            )?;
        Ok((
            AssignedPermInput {
                state_tag,
                input_len,
                input,
                perm_count,
                acc_input,
                output,
            },
            in_state,
            absorb_inputs,
        ))
    }

    /// Assigns a permutation
    fn assign_permutation(
        &mut self,
        layouter: &mut impl Layouter<F>,
        in_state: AssignedState<F>,
        prev_perm: AssignedPermInput<F>,
        perm: NextInput<F>,
        acc_len: usize,
        randomness: AssignedCell<F, F>,
    ) -> Result<(AssignedPermInput<F>, AssignedState<F>), Error> {
        let absorb_inputs = layouter.assign_region(
            || "Assign perm_absorb inputs",
            |mut region| {
                let absorb_inputs: [AssignedCell<F, F>; NEXT_INPUTS_BYTES] = (1..NEXT_INPUTS_BYTES
                    + 1)
                    .map(|idx| -> Result<AssignedCell<F, F>, Error> {
                        region.assign_advice(
                            || "input_state init",
                            self.next_inputs[idx],
                            0,
                            || Ok(perm.unpadded_bytes[idx]),
                        )
                    })
                    .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?
                    .try_into()
                    .unwrap();
                Ok(absorb_inputs)
            },
        )?;

        let out_state = self.assign_permutation_and_padding(
            layouter,
            in_state,
            perm.unpadded_bytes,
            perm.state_tag.is_continue() || perm.state_tag.is_end(),
            acc_len,
            perm.og_len,
        )?;

        let out_state_rlc =
            self.state_rlc_config
                .assign_rlc(layouter, out_state.clone(), randomness.clone())?;

        let input_rlc = self.absorb_inputs_rlc_config.assign_rlc(
            layouter,
            absorb_inputs.clone(),
            randomness,
        )?;

        let (acc_input, last_randomness) = self
            .absorb_inputs_rlc_config
            .assign_rlc_retunring_last_randomness(
                layouter,
                [prev_perm.acc_input.clone()]
                    .iter()
                    .chain(absorb_inputs.iter())
                    .cloned()
                    .collect_vec()
                    .try_into()
                    .unwrap(),
                self.latest_acc_randomness.as_ref().cloned().unwrap(),
            )?;
        self.latest_acc_randomness = Some(last_randomness);

        let assigned_perm_input = layouter.assign_region(
            || "Start tag",
            |mut region| {
                // Enable selector for the current state "row".
                self.q_enable.enable(&mut region, 0)?;
                let state_tag = region.assign_advice(
                    || "State_tag ",
                    self.state_tag,
                    1,
                    || Ok(perm.state_tag.into_f()),
                )?;
                prev_perm.state_tag.copy_advice(
                    || "next_state_tag",
                    &mut region,
                    self.state_tag,
                    0,
                )?;
                let input_len = region.assign_advice(
                    || "Input len",
                    self.input_len,
                    1,
                    || Ok(F::from(perm.og_len as u64)),
                )?;
                prev_perm.input_len.copy_advice(
                    || "Next input len",
                    &mut region,
                    self.input_len,
                    0,
                )?;

                prev_perm
                    .input
                    .copy_advice(|| "Input rlc", &mut region, self.input, 0)?;
                let input_rlc =
                    input_rlc.copy_advice(|| "Next Input rlc", &mut region, self.input, 1)?;

                prev_perm.perm_count.copy_advice(
                    || "Perm count",
                    &mut region,
                    self.perm_count,
                    0,
                )?;
                let perm_count = region.assign_advice(
                    || "Next Perm count",
                    self.perm_count,
                    1,
                    || Ok(F::from(perm.perm_count as u64)),
                )?;

                let output = region.assign_advice(
                    || "Output rlc",
                    self.output_rlc,
                    1,
                    || Ok(out_state_rlc.value().copied().ok_or(Error::Synthesis)?),
                )?;
                prev_perm.output.copy_advice(
                    || "Next output rlc",
                    &mut region,
                    self.output_rlc,
                    0,
                )?;

                prev_perm
                    .acc_input
                    .copy_advice(|| "Acc input", &mut region, self.acc_input, 0)?;
                let acc_input =
                    acc_input.copy_advice(|| "Next acc_input", &mut region, self.acc_input, 1)?;

                // TODO: Assign expected_out_rlc so that we can constrain it.
                // Pending to see if the constraint applies or not.

                Ok(AssignedPermInput {
                    state_tag,
                    input: input_rlc,
                    input_len,
                    perm_count,
                    acc_input,
                    output,
                })
            },
        )?;

        Ok((assigned_perm_input, out_state))
    }

    pub(crate) fn assign_permutation_and_padding(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: [AssignedCell<F, F>; STATE_WORDS],
        unpadded: [F; NEXT_INPUTS_BYTES],
        is_finalize: bool,
        acc_len: usize,
        input_len: usize,
    ) -> Result<[AssignedCell<F, F>; 25], Error> {
        // TODO: Copy the input_len and acc_len instead of assign each time (See padding
        // config).
        //
        // TODO: Handle byteRLC.

        // Assign padding for each one of the cells
        let padded_input = self.padding_config.assign_region(
            layouter,
            is_finalize,
            input_len,
            acc_len,
            unpadded,
        )?;

        let out_state = self.keccak_f_config.assign_permutation(
            layouter,
            in_state,
            !is_finalize,
            padded_input,
        )?;

        Ok(out_state)
    }
}

pub(crate) fn compute_rlc_cells<F: Field, const N: usize>(
    witness: &[AssignedCell<F, F>; N],
    randomness: AssignedCell<F, F>,
) -> Result<F, Error> {
    let og_randomness = randomness.value().ok_or(Error::Synthesis)?;
    let mut randomness = og_randomness.clone();
    let witness = witness
        .iter()
        .map(|w| -> Result<F, Error> { w.value().cloned().ok_or(Error::Synthesis) })
        .collect::<Result<Vec<F>, Error>>()?;
    let mut rlc = witness[0].clone();

    // Compute rlc
    for value in witness[1..].iter() {
        rlc = rlc + value.clone() * randomness.clone();
        randomness = randomness * og_randomness.clone();
    }

    Ok(rlc)
}

pub(crate) fn compute_rlc_field<F: Field, const N: usize>(witness: &[F; N], randomness: F) -> F {
    let og_randomness = randomness;
    let mut randomness = og_randomness.clone();
    let mut rlc = witness[0].clone();

    // Compute rlc
    for value in witness[1..].iter() {
        rlc = rlc + value.clone() * randomness.clone();
        randomness = randomness * og_randomness.clone();
    }

    rlc
}

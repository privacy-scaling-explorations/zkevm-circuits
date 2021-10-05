pub struct RunningSumConfig<F> {
    q_enable: Selector,
    // coef, slice, acc
    base_13_cols: [Column<Advice>; 3],
    // coef, slice, acc
    base_9_cols: [Column<Advice>; 3],
    // block count, step 2 acc, step 3 acc
    block_count_cols: [Column<Advice>; 3],
    base_13_to_base_9_lookup: Base13toBase9TableConfig<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RunningSumConfig<F> {
    pub fn configure(
        q_enable: Selector,
        is_final: Selector,
        meta: &mut ConstraintSystem<F>,
        base_13_cols: [Column<Advice>; 3],
        base_9_cols: [Column<Advice>; 3],
        block_count_cols: [Column<Advice>; 3],
        step: u32,
    ) -> RunningSumConfig<F> {
        let base_13_to_base_9_lookup = Base13toBase9TableConfig::configure(
            meta,
            q_enable,
            base_13_cols[1],
            base_9_cols[1],
            block_count_cols[0],
        );

        // ? = non-zero
        // [?, ?, ?, ?] -> block_count = 0
        // [0, ?, ?, ?] -> block_count = 1
        // [0, 0, ?, ?] -> block_count = 2
        // [0, 0, 0, ?] -> block_count = 3
        // TODO: lookup check, block count summing check
        meta.create_gate("running sum", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_final = meta.query_selector(is_final);
            // coef is correctly computed
            // acc is correctly accumulated

            // slice 13 to slice 9 mapping is correctly looked up
            // block count is correctly looked up
            // block count, step 2 acc, step 3 acc are correctly
            // validated

            // what about the last row?

            let coef_13 = meta.query_advice(base_13_cols[0], Rotation::cur());
            let coef_13_next =
                meta.query_advice(base_13_cols[0], Rotation::next());
            let slice_13 = meta.query_advice(base_13_cols[1], Rotation::cur());
            let coef_9 = meta.query_advice(base_9_cols[0], Rotation::cur());
            let coef_9_next =
                meta.query_advice(base_9_cols[0], Rotation::next());
            let slice_9 = meta.query_advice(base_9_cols[1], Rotation::cur());
            let block_count =
                meta.query_advice(block_count_cols[0], Rotation::cur());
            let acc_13 = meta.query_advice(base_13_cols[2], Rotation::cur());
            let acc_13_next =
                meta.query_advice(base_13_cols[2], Rotation::next());
            let acc_9 = meta.query_advice(base_9_cols[2], Rotation::cur());
            let acc_9_next =
                meta.query_advice(base_9_cols[2], Rotation::next());
            let block_count_acc =
                meta.query_advice(block_count_cols[1], Rotation::cur());
            let block_count_acc_next =
                meta.query_advice(block_count_cols[1], Rotation::next());

            let coef_step_13 =
                Expression::Constant(F::from(u64::pow(13, step)));
            let coef_step_9 = Expression::Constant(F::from(u64::pow(9, step)));

            let expr_next_13_coef =
                coef_13_next - coef_step_13 * coef_13.clone();
            let expr_next_9_coef = coef_9_next - coef_step_9 * coef_9.clone();
            // next acc correctness
            let expr_next_13_acc =
                (acc_13 - acc_13_next.clone()) - coef_13 * slice_13;
            let expr_next_9_acc = (acc_9 - acc_9_next) - coef_9 * slice_9;
            let step2_acc =
                meta.query_advice(block_count_cols[1], Rotation::cur());
            let step2_acc_next =
                meta.query_advice(block_count_cols[1], Rotation::next());
            let step3_acc =
                meta.query_advice(block_count_cols[2], Rotation::cur());
            let step3_acc_next =
                meta.query_advice(block_count_cols[2], Rotation::next());

            let expr_next_block_count_acc =
                block_count_acc_next - block_count_acc - block_count.clone();

            let mut checks = vec![
                q_enable.clone() * expr_next_13_coef,
                q_enable.clone() * expr_next_9_coef,
                q_enable.clone() * expr_next_13_acc,
                q_enable.clone() * expr_next_9_acc,
                q_enable.clone() * expr_next_block_count_acc,
                q_enable.clone() * is_final * acc_13_next,
            ];
            // block_count acc correctness
            if step == 1 {
                checks.push(q_enable.clone() * block_count);
                checks.push(q_enable.clone() * (step2_acc_next - step2_acc));
                checks.push(q_enable * (step3_acc_next - step3_acc));
            } else if step == 2 {
                checks.push(
                    q_enable.clone()
                        * (step2_acc_next - step2_acc - block_count),
                );
                checks.push(q_enable * (step3_acc_next - step3_acc));
            } else if step == 3 {
                checks.push(q_enable.clone() * (step2_acc_next - step2_acc));
                checks.push(
                    q_enable * (step3_acc_next - step3_acc - block_count),
                );
            } else {
                unreachable!("step < 4");
            }

            checks
        });

        RunningSumConfig {
            q_enable,
            base_13_cols,
            base_9_cols,
            block_count_cols,
            base_13_to_base_9_lookup,
            _marker: PhantomData,
        }
    }
}

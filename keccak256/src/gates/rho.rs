pub struct RhoConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RhoConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) {
        for (x, y) in (0..5).cartesian_product(0..5) {
            let mut chunk_idx = 1;
            let rot = ROT_TABLE[x][y];

            let base_13_cols = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];
            let base_9_cols = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];
            let block_count_cols = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];

            let q_is_final = meta.selector();

            let q_running_sum = meta.selector();
            while chunk_idx < 64 {
                let step = get_step_size(chunk_idx, rot);
                RunningSumConfig::configure(
                    q_running_sum,
                    q_is_final,
                    meta,
                    base_13_cols,
                    base_9_cols,
                    block_count_cols,
                    step as u32,
                );
                chunk_idx += step;
            }
        }

        // TODO: block_count check
    }
}

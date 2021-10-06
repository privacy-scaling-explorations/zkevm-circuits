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
                    let lane = meta.query_advice(
                        state[5 * ((x + 3 * y) % 5) + x],
                        Rotation::cur(),
                    );
                    let new_lane =
                        meta.query_advice(state[5 * x + y], Rotation::next());

                    q_enable.clone() * (new_lane - lane)
                })
                .collect::<Vec<Expression<F>>>()
        });

        PiConfig {
            q_enable,
            state,
            _marker: PhantomData,
        }
    }
}

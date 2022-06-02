use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct FlagConfig<F> {
    flag: Column<Advice>,
    q_enable: Selector,
    _marker: PhantomData<F>,
}

impl<F: Field> FlagConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, flag: Column<Advice>) -> Self {
        meta.enable_equality(flag);

        let q_enable = meta.selector();

        meta.create_gate("Ensure flag consistency", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let f_positive = meta.query_advice(flag, Rotation::cur());
            let f_negative = meta.query_advice(flag, Rotation::next());
            let one = Expression::Constant(F::one());

            [
                (
                    "f_pos must be 1 or 0",
                    q_enable.clone() * (one.clone() - f_positive.clone()) * f_positive.clone(),
                ),
                (
                    "f_neg must be 1 - f_pos",
                    q_enable * (f_positive + f_negative - one),
                ),
            ]
        });

        Self {
            flag,
            q_enable,
            _marker: PhantomData,
        }
    }

    pub fn assign_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        flag: Option<bool>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "Flag and Negated flag assignation",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let positive = region.assign_advice(
                    || "flag positive",
                    self.flag,
                    0,
                    || {
                        flag.map(|flag| F::from(flag as u64))
                            .ok_or(Error::Synthesis)
                    },
                )?;
                let negative = region.assign_advice(
                    || "flag negative",
                    self.flag,
                    1,
                    || {
                        flag.map(|flag| F::from(!flag as u64))
                            .ok_or(Error::Synthesis)
                    },
                )?;

                Ok((positive, negative))
            },
        )
    }
}

use eth_types::Field;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct AddConfig<F> {
    q_enable: Selector,
    input: Column<Advice>,
    x: Column<Advice>,
    fixed: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: Field> AddConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        input: Column<Advice>,
        x: Column<Advice>,
        fixed: Column<Fixed>,
    ) -> Self {
        let q_enable = meta.selector();
        meta.enable_equality(x);
        meta.enable_equality(input);

        meta.create_gate("add", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let x = meta.query_advice(x, Rotation::cur());
            let input_next = meta.query_advice(input, Rotation::next());
            let input = meta.query_advice(input, Rotation::cur());
            let fixed = meta.query_fixed(fixed, Rotation::cur());
            vec![q_enable * (input_next - input - x * fixed)]
        });

        Self {
            q_enable,
            input,
            x,
            fixed,
            _marker: PhantomData,
        }
    }

    pub fn add_advice(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        x: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "add advice",
            |mut region| {
                let offset = 0;
                self.q_enable.enable(&mut region, offset)?;
                input.copy_advice(|| "input", &mut region, self.input, offset)?;
                x.copy_advice(|| "x", &mut region, self.x, offset)?;

                // constrain fixed to 1 for a simple add.
                region.assign_fixed(|| "1", self.fixed, offset, || Ok(F::one()))?;

                let offset = 1;
                region.assign_advice(
                    || "input + x",
                    self.input,
                    offset,
                    || {
                        Ok(input.value().cloned().ok_or(Error::Synthesis)?
                            + x.value().cloned().ok_or(Error::Synthesis)?)
                    },
                )
            },
        )
    }
    pub fn add_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "add fixed",
            |mut region| {
                let offset = 0;
                self.q_enable.enable(&mut region, offset)?;
                input.copy_advice(|| "input", &mut region, self.input, offset)?;

                {
                    // constrain advice to 1 for a simple add.
                    let x = region.assign_advice(|| "x", self.x, offset, || Ok(F::one()))?;
                    region.constrain_constant(x.cell(), F::one())?;
                }
                region.assign_fixed(|| "fixed value", self.fixed, offset, || Ok(value))?;

                let offset = 1;
                region.assign_advice(
                    || "input + x",
                    self.input,
                    offset,
                    || Ok(input.value().cloned().ok_or(Error::Synthesis)? + value),
                )
            },
        )
    }
    pub fn linear_combine<const N: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: [AssignedCell<F, F>; N],
        vs: [F; N],
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "linear combine",
            |mut region| {
                // | offset |        input |        x |   fixed |
                // | ------ | -----------: | -------: | ------: |
                // | 0      |            0 |       x0 |      v0 |
                // | 1      |         x0v0 |       x1 |      v1 |
                // | 2      | x0v0 + x1v1  |       x2 |      v2 |
                // | ...    |          ... |      ... |     ... |
                // | N - 1  |              |  x_(N-1) | v_(N-1) |
                // | N      |    (sum)     |          |         |
                let mut acc =
                    region.assign_advice(|| "input 0", self.input, 0, || Ok(F::zero()))?;
                region.constrain_constant(acc.cell(), F::zero())?;
                let mut sum = F::zero();
                for offset in 0..N {
                    self.q_enable.enable(&mut region, offset)?;
                    let x = xs[offset].copy_advice(|| "x", &mut region, self.x, offset)?;
                    let v = region.assign_fixed(|| "v", self.fixed, offset, || Ok(vs[offset]))?;
                    acc = region.assign_advice(
                        || "accumulation",
                        self.input,
                        offset + 1,
                        || {
                            sum += x.value().cloned().ok_or(Error::Synthesis)?
                                * v.value().cloned().ok_or(Error::Synthesis)?;
                            Ok(sum)
                        },
                    )?;
                }
                Ok(acc)
            },
        )
    }

    pub fn running_sum<const N: usize>(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: [AssignedCell<F, F>; N],
    ) -> Result<AssignedCell<F, F>, Error> {
        self.linear_combine(layouter, xs, [F::one(); N])
    }
}

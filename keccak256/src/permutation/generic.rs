use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

/// A versatile gate to do running sum, conditional add, and linear combination,
/// etc.
#[derive(Clone, Debug)]
pub struct GenericConfig<F> {
    q_enable: Selector,
    io: Column<Advice>,
    left: Column<Advice>,
    right: Column<Advice>,
    _marker: PhantomData<F>,
}

#[allow(dead_code)]
impl<F: Field> GenericConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 3],
        fixed: Column<Fixed>,
    ) -> Self {
        let q_enable = meta.selector();
        let [io, left, right] = advices;
        meta.enable_equality(io);
        meta.enable_equality(left);
        meta.enable_equality(right);
        meta.enable_constant(fixed);

        meta.create_gate("add", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let input = meta.query_advice(io, Rotation::cur());
            let output = meta.query_advice(io, Rotation::next());
            let left = meta.query_advice(left, Rotation::cur());
            let right = meta.query_advice(right, Rotation::cur());
            vec![q_enable * (output - input - left * right)]
        });

        Self {
            q_enable,
            io,
            left,
            right,
            _marker: PhantomData,
        }
    }

    fn add_generic(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Option<AssignedCell<F, F>>,
        left: Option<AssignedCell<F, F>>,
        right: Option<AssignedCell<F, F>>,
        value: Option<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "add advice",
            |mut region| {
                let offset = 0;
                self.q_enable.enable(&mut region, offset)?;
                let input = input.as_ref().map_or(
                    region.assign_advice_from_constant(|| "input is 0", self.io, offset, F::zero()),
                    |input| input.copy_advice(|| "input", &mut region, self.io, offset),
                )?;

                let left = match &left {
                    Some(x) => {
                        // copy x to use as a flag
                        (*x).copy_advice(|| "left adv", &mut region, self.left, offset)?
                    }
                    None => {
                        // constrain advice to 1 for a simple add.
                        region.assign_advice_from_constant(
                            || "left const",
                            self.left,
                            offset,
                            F::one(),
                        )?
                    }
                };

                let right = match &right {
                    Some(right) => {
                        if value.is_some() {
                            panic!("right and value can't be both some");
                        }
                        right.copy_advice(|| "right adv", &mut region, self.right, offset)?
                    }
                    None => {
                        match value {
                            Some(value) => region.assign_advice_from_constant(
                                || "fixed value",
                                self.right,
                                offset,
                                value,
                            )?,
                            None => {
                                // constrain fixed to 1 for a simple add.
                                region.assign_advice_from_constant(
                                    || "fixed value",
                                    self.right,
                                    offset,
                                    F::one(),
                                )?
                            }
                        }
                    }
                };

                let offset = 1;
                region.assign_advice(
                    || "input + x",
                    self.io,
                    offset,
                    || {
                        Ok(input.value().cloned().ok_or(Error::Synthesis)?
                            + left.value().cloned().ok_or(Error::Synthesis)?
                                * right.value().cloned().ok_or(Error::Synthesis)?)
                    },
                )
            },
        )
    }
    /// input += v * x
    pub fn add_advice_mul_const(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        x: AssignedCell<F, F>,
        v: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add_generic(layouter, Some(input), Some(x), None, Some(v))
    }
    /// input -= x
    pub fn sub_advice(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        x: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add_generic(layouter, Some(input), Some(x), None, Some(-F::one()))
    }
    /// input += v
    pub fn add_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add_generic(layouter, Some(input), None, None, Some(value))
    }
    /// output = input * v
    pub fn mul_fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add_generic(layouter, None, Some(input), None, Some(value))
    }
    /// input += flag * v
    /// No boolean check on the flag, we assume the flag is checked before
    /// copied to here
    pub fn conditional_add_const(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        flag: AssignedCell<F, F>,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add_generic(layouter, Some(input), Some(flag), None, Some(value))
    }
    /// input += flag * x
    /// No boolean check on the flag, we assume the flag is checked before
    /// copied to here
    pub fn conditional_add_advice(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        flag: AssignedCell<F, F>,
        x: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.add_generic(layouter, Some(input), Some(flag), Some(x), None)
    }
    fn linear_combine_generic(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: Vec<AssignedCell<F, F>>,
        ys: Option<Vec<AssignedCell<F, F>>>,
        vs: Option<Vec<F>>,
        outcome: Option<AssignedCell<F, F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        debug_assert_eq!(
            ys.is_some(),
            vs.is_none(),
            "They can't both some or both none"
        );
        if let Some(ref vs) = vs {
            debug_assert_eq!(xs.len(), vs.len());
        }
        if let Some(ref ys) = ys {
            debug_assert_eq!(xs.len(), ys.len());
        }
        layouter.assign_region(
            || "linear combine",
            |mut region| {
                // | offset |        input |        x |   y |
                // | ------ | -----------: | -------: | ------: |
                // | 0      |            0 |       x0 |      y0 |
                // | 1      |         x0y0 |       x1 |      y1 |
                // | 2      |  x0y0 + x1y1 |       x2 |      y2 |
                // | ...    |          ... |      ... |     ... |
                // | N - 1  |              |  x_(N-1) | y_(N-1) |
                // | N      |    (sum)     |          |         |
                let mut acc = region.assign_advice(|| "input 0", self.io, 0, || Ok(F::zero()))?;
                region.constrain_constant(acc.cell(), F::zero())?;
                let mut sum = F::zero();
                for (offset, x) in xs.iter().enumerate() {
                    self.q_enable.enable(&mut region, offset)?;
                    x.copy_advice(|| "x", &mut region, self.left, offset)?;
                    let right = {
                        match &vs {
                            Some(vs) => region.assign_advice_from_constant(
                                || "v",
                                self.right,
                                offset,
                                vs[offset],
                            )?,
                            None => match &ys {
                                Some(ys) => ys[offset].copy_advice(
                                    || "y",
                                    &mut region,
                                    self.right,
                                    offset,
                                )?,
                                None => {
                                    unreachable!()
                                }
                            },
                        }
                    };
                    acc = region.assign_advice(
                        || "accumulation",
                        self.io,
                        offset + 1,
                        || {
                            sum += x.value().cloned().ok_or(Error::Synthesis)?
                                * right.value().cloned().ok_or(Error::Synthesis)?;
                            Ok(sum)
                        },
                    )?;
                }
                if let Some(outcome) = &outcome {
                    if outcome.value().is_some() && acc.value().is_some() {
                        debug_assert_eq!(outcome.value(), acc.value());
                    }

                    region.constrain_equal(outcome.cell(), acc.cell())?;
                }
                Ok(acc)
            },
        )
    }

    pub fn linear_combine_consts(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: Vec<AssignedCell<F, F>>,
        vs: Vec<F>,
        outcome: Option<AssignedCell<F, F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.linear_combine_generic(layouter, xs, None, Some(vs), outcome)
    }

    pub fn linear_combine_advices(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: Vec<AssignedCell<F, F>>,
        ys: Vec<AssignedCell<F, F>>,
        outcome: Option<AssignedCell<F, F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.linear_combine_generic(layouter, xs, Some(ys), None, outcome)
    }

    pub fn running_sum(
        &self,
        layouter: &mut impl Layouter<F>,
        xs: Vec<AssignedCell<F, F>>,
        outcome: Option<AssignedCell<F, F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let len = xs.len();
        self.linear_combine_consts(
            layouter,
            xs,
            (0..len).map(|_| F::one()).collect_vec(),
            outcome,
        )
    }
}

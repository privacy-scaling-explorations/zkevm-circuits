use pairing::arithmetic::FieldExt;

use halo2::{
    circuit::{Cell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct BaseEvaluationConfig<F> {
    q_enable: Selector,
    // big-endian
    pub coef: Column<Advice>,
    power_of_base: F,
    acc: Column<Advice>,
}

impl<F: FieldExt> BaseEvaluationConfig<F> {
    /// # Side effect
    /// Enable equality on result and acc
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_base: F,
        result: Column<Advice>,
    ) -> Self {
        let q_enable = meta.selector();
        let coef = meta.advice_column();
        let acc = meta.advice_column();
        // Bind result to acc
        meta.enable_equality(result.into());
        // Bind first coef value to acc
        meta.enable_equality(coef.into());
        meta.enable_equality(acc.into());

        meta.create_gate("Running sum", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let coef = meta.query_advice(coef, Rotation::cur());
            let acc_prev = meta.query_advice(acc, Rotation::prev());
            let acc = meta.query_advice(acc, Rotation::cur());

            // acc_{i+1} = acc_{i} * base ** power + coef
            vec![(
                "running sum",
                q_enable * (acc - acc_prev * power_of_base - coef),
            )]
        });

        Self {
            q_enable,
            coef,
            power_of_base,
            acc,
        }
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        result: Cell,
        coefs: &[F],
    ) -> Result<(), Error> {
        let mut acc = F::zero();
        for (offset, &coef) in coefs.iter().enumerate() {
            acc = acc * self.power_of_base + coef;
            if offset != 0 {
                self.q_enable.enable(region, offset)?;
            }
            let coef_cell = region.assign_advice(
                || "Coef",
                self.coef,
                offset,
                || Ok(coef),
            )?;
            let acc_cell =
                region.assign_advice(|| "Acc", self.acc, offset, || Ok(acc))?;
            if offset == 0 {
                // bind first acc to first coef
                region.constrain_equal(acc_cell, coef_cell)?;
            } else if offset == coefs.len() - 1 {
                // bind last acc to result
                region.constrain_equal(acc_cell, result)?;
            }
        }
        Ok(())
    }
}

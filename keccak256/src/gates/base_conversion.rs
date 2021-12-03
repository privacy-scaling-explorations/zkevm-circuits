use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Selector, TableColumn, Error},
    poly::Rotation,
};

use crate::gates::gate_helpers::CellF;
use crate::gates::utils::RunningSum;
use pairing::arithmetic::FieldExt;

struct BaseConversionConfig<F> {
    q_enable: Selector,
    input_base: u64,
    output_base: u64,
    input_slices: Column<Advice>,
    output_slices: Column<Advice>,
    input_table_col: TableColumn,
    output_table_col: TableColumn,
    input_rs: RunningSum<F>,
    output_rs: RunningSum<F>,
}

impl<F: FieldExt> BaseConversionConfig<F> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        input_base: u64,
        output_base: u64,
        input_table_col: TableColumn,
        output_table_col: TableColumn,
        input_lane: Column<Advice>,
        output_lane: Column<Advice>,
    ) -> Self {
        let q_enable = meta.selector();
        let input_slices = meta.advice_column();
        let output_slices = meta.advice_column();

        meta.enable_equality(input_lane.into());
        meta.enable_equality(input_slices.into());
        meta.enable_equality(output_lane.into());
        meta.enable_equality(output_slices.into());

        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let input_slices = meta.query_advice(input_slices, Rotation::cur());
            let output_slices =
                meta.query_advice(output_slices, Rotation::cur());
            vec![
                (q_enable.clone() * input_slices, input_table_col),
                (q_enable * output_slices, output_table_col),
            ]
        });

        let input_rs = RunningSum::configure(meta, input_slices, input_lane);
        let output_rs = RunningSum::configure(meta, output_slices, output_lane);

        Self {
            q_enable,
            input_base,
            output_base,
            input_slices,
            output_slices,
            input_table_col,
            output_table_col,
            input_rs,
            output_rs,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input_lane: CellF<F>,
        output_lane: CellF<F>,
        b9_lane: CellF<F>,
        slicer: impl FnOnce(F) -> (Vec<F>, Vec<F>),
    ) -> Result<(), Error>{
        layouter.assign_region(
            || "Base conversion",
            |mut region| {
              
                Ok(())
            },
        )?;
        self.input_rs.assign_region(layouter, None, vec![])?;
        self.output_rs.assign_region(layouter, None, vec![])?;
        Ok(())
    }
}

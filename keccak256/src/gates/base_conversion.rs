use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};

use crate::gates::base_eval::BaseEvaluationConfig;
use crate::gates::gate_helpers::CellF;
use pairing::arithmetic::FieldExt;

struct BaseConversionConfig<F> {
    q_enable: Selector,
    chunk_num: u64,
    input_table_col: TableColumn,
    output_table_col: TableColumn,
    input_eval: BaseEvaluationConfig<F>,
    output_eval: BaseEvaluationConfig<F>,
}

impl<F: FieldExt> BaseConversionConfig<F> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        input_base: u64,
        output_base: u64,
        chunk_num: u64,
        input_table_col: TableColumn,
        output_table_col: TableColumn,
        input_lane: Column<Advice>,
        output_lane: Column<Advice>,
    ) -> Self {
        let q_enable = meta.selector();

        meta.enable_equality(input_lane.into());
        meta.enable_equality(output_lane.into());

        let input_eval =
            BaseEvaluationConfig::configure(meta, input_base, input_lane);
        let output_eval =
            BaseEvaluationConfig::configure(meta, output_base, output_lane);

        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let input_slices =
                meta.query_advice(input_eval.coef, Rotation::cur());
            let output_slices =
                meta.query_advice(output_eval.coef, Rotation::cur());
            vec![
                (q_enable.clone() * input_slices, input_table_col),
                (q_enable * output_slices, output_table_col),
            ]
        });

        Self {
            q_enable,
            chunk_num,
            input_table_col,
            output_table_col,
            input_eval,
            output_eval,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input_lane: CellF<F>,
        output_lane: CellF<F>,
        input_coefs: &Vec<F>,
        output_coefs: &Vec<F>,
        input_chunk_indices: Vec<u64>,
        ouput_chunk_indices: Vec<u64>,
    ) -> Result<(), Error> {
        self.chunk_num;
        self.input_eval.assign_region(
            layouter,
            input_lane,
            input_coefs,
            input_chunk_indices,
        )?;
        self.output_eval.assign_region(
            layouter,
            output_lane,
            output_coefs,
            ouput_chunk_indices,
        )?;
        Ok(())
    }
}

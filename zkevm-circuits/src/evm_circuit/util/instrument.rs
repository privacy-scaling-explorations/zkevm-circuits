use halo2_proofs::arithmetic::FieldExt;
use itertools::Itertools;

use crate::evm_circuit::step::ExecutionState;
use crate::evm_circuit::util::constraint_builder::ConstraintBuilder;
use crate::evm_circuit::util::CellType;

type StepSize = Vec<(CellType, ColumnSize)>;
type ColumnSize = (usize, usize, usize);

/// Instrument captures metrics during the compilation of a circuit.
#[derive(Clone, Debug, Default)]
pub(crate) struct Instrument {
    // States -> Cell Types -> (width, height, num_cells)
    states: Vec<(ExecutionState, StepSize)>,
}

impl Instrument {
    pub(crate) fn on_gadget_built<'a, F: FieldExt>(
        &mut self,
        execution_state: ExecutionState,
        cb: &ConstraintBuilder<'a, F>,
    ) {
        let sizes = cb
            .curr
            .cell_manager
            .get_stats()
            .into_iter()
            .sorted()
            .collect::<Vec<_>>();

        self.states.push((execution_state, sizes));
    }

    pub(crate) fn print(&self) {
        let mut states = self.states.clone();
        states.sort_by_key(|(_, sizes)| {
            let cells: usize = sizes.iter().map(|(_, (_, _, c))| *c).sum();
            cells
        });
        states.reverse();

        for (state, sizes) in states {
            println!("{: <14?} {:?}", state, state.responsible_opcodes());

            // Print overall metrics per execution state.
            let col_type = "*";
            let width: usize = sizes.iter().map(|(_, (w, _, _))| *w).sum();
            let top_height: usize = sizes.iter().map(|(_, (_, h, _))| *h).max().unwrap();
            let cells: usize = sizes.iter().map(|(_, (_, _, c))| *c).sum();
            let unused_cells = width * top_height - cells;
            let utilization =
                ((cells as f64) / (width as f64 * top_height as f64) * 100f64).round();

            println!(
                "  column_type        |  width | height |  cells | unused_cells | utilization"
            );
            println!("  {col_type:<18} | {width:>6} | {top_height:>6} | {cells:>6} | {unused_cells:>12} | {utilization:>6}%");

            sizes.iter().for_each(|(col_type, (width, height, cells))| {

                // Print metrics per column type.
                let col_type = format!("{:?}", col_type);
                let unused_cells = width * top_height - cells;
                let utilization = ((*cells as f64) / (*width as f64 * top_height as f64) * 100f64).round();
                println!("  {col_type:<18} | {width:>6} | {height:>6} | {cells:>6} | {unused_cells:>12} | {utilization:>6}%");
            });

            println!();
        }
    }
}

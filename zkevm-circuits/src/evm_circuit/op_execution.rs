use super::{
    param::{
        NUM_CELL_OP_EXECTION_STATE, NUM_CELL_OP_GADGET_SELECTOR,
        NUM_CELL_RESUMPTION,
    },
    Case, Cell, Constraint, CoreStateInstance, ExecutionStep, Lookup, Word,
};
use halo2::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{ConstraintSystem, Error, Expression},
};
use std::collections::HashMap;

mod arithmetic;
use arithmetic::AddGadget;

fn bool_switches_constraints<F: FieldExt>(
    bool_switches: &[Cell<F>],
) -> Vec<Expression<F>> {
    let one = Expression::Constant(F::one());

    let mut constraints = Vec::with_capacity(bool_switches.len() + 1);
    let mut sum_to_one = Expression::Constant(F::zero());

    for switch in bool_switches {
        constraints.push(switch.exp() * (one.clone() - switch.exp()));
        sum_to_one = sum_to_one + switch.exp();
    }

    constraints.push(one - sum_to_one);

    constraints
}

#[derive(Debug)]
struct CaseConfig {
    case: Case,
    num_word: usize,
    num_cell: usize,
    will_resume: bool,
}

impl CaseConfig {
    fn total_cells(&self) -> usize {
        32 * self.num_word
            + self.num_cell
            + if self.will_resume {
                NUM_CELL_RESUMPTION
            } else {
                0
            }
    }
}

#[derive(Debug)]
struct CaseAllocation<'a, F> {
    selector: &'a Cell<F>,
    words: Vec<Word<F>>,
    cells: &'a [Cell<F>],
    resumption: Option<&'a Resumption<F>>,
}

#[derive(Clone, Debug)]
struct Resumption<F> {
    caller_id: Cell<F>,
    gas_available: Cell<F>,
}

impl<F: FieldExt> Resumption<F> {
    fn new(cells: &[Cell<F>]) -> Self {
        assert_eq!(cells.len(), NUM_CELL_RESUMPTION);

        Self {
            caller_id: cells[0].clone(),
            gas_available: cells[1].clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct OpExecutionState<F> {
    is_executing: Cell<F>,
    global_counter: Cell<F>,
    call_id: Cell<F>,
    program_counter: Cell<F>,
    stack_pointer: Cell<F>,
    gas_counter: Cell<F>,
    opcode: Cell<F>,
}

impl<F: FieldExt> OpExecutionState<F> {
    pub(crate) fn new(cells: &[Cell<F>]) -> Self {
        assert_eq!(cells.len(), NUM_CELL_OP_EXECTION_STATE);

        Self {
            is_executing: cells[0].clone(),
            global_counter: cells[1].clone(),
            call_id: cells[2].clone(),
            program_counter: cells[3].clone(),
            stack_pointer: cells[4].clone(),
            gas_counter: cells[5].clone(),
            opcode: cells[6].clone(),
        }
    }
}

trait OpGadget<F: FieldExt> {
    const RESPONSIBLE_OPCODES: &'static [u8];

    const CASE_CONFIGS: &'static [CaseConfig];

    fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self;

    fn constraints(
        &self,
        op_execution_state_curr: &OpExecutionState<F>,
        op_execution_state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>>;

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        core_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error>;
}

#[derive(Clone)]
pub(crate) struct OpExecutionGadget<F> {
    r: F,
    op_execution_state_curr: OpExecutionState<F>,
    op_execution_state_next: OpExecutionState<F>,
    op_selectors: Vec<Cell<F>>,
    free_cells: Vec<Cell<F>>,
    resumption: Resumption<F>,
    // TODO: use OpcodeId from bus_mapping
    op_selector_idx_map: HashMap<u8, usize>,
    default_values_map: HashMap<(usize, Case), Vec<(usize, F)>>,
    add_gadget: AddGadget<F>,
}

impl<F: FieldExt> OpExecutionGadget<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        r: F,
        q_step: Expression<F>,
        op_execution_state_curr: OpExecutionState<F>,
        op_execution_state_next: OpExecutionState<F>,
        free_cells: Vec<Cell<F>>,
        independent_lookups: &mut Vec<(Expression<F>, Vec<Lookup<F>>)>,
    ) -> Self {
        let (op_selectors, free_cells) =
            free_cells.split_at(NUM_CELL_OP_GADGET_SELECTOR);
        let resumption = Resumption::new(
            &free_cells[free_cells.len() - NUM_CELL_RESUMPTION..],
        );

        let mut op_selector_idx_map = HashMap::new();
        let mut default_values_map = HashMap::new();
        let /* mut */ op_selector_idx = 0;

        let mut constraints = vec![Constraint {
            name: "op selectors",
            selector: Expression::Constant(F::one()),
            linear_combinations: bool_switches_constraints(op_selectors),
            lookups: vec![],
        }];

        macro_rules! constrcut_op_gadget {
            {} => {};
            {$name:ident = $gadget:ident} => {
                let $name = Self::constrcut_op_gadget::<$gadget::<F>>(
                    r,
                    &op_execution_state_curr,
                    &op_execution_state_next,
                    op_selectors,
                    op_selector_idx,
                    free_cells,
                    &resumption,
                    &mut op_selector_idx_map,
                    &mut default_values_map,
                    &mut constraints,
                );
            };
            {$name:ident = $gadget:ident;} => {
                constrcut_op_gadget!{$name = $gadget};
            };
            {$name:ident = $gadget:ident; $($tail:tt)+} => {
                constrcut_op_gadget!{$name = $gadget};
                op_selector_idx += 1;
                constrcut_op_gadget!{$($tail)+};
            };
        }

        constrcut_op_gadget! {
            add_gadget = AddGadget;
        }

        for constraint in constraints.into_iter() {
            let Constraint {
                name,
                selector: constraint_selector,
                linear_combinations,
                lookups,
            } = constraint;

            let synthetic_selector =
                q_step.clone() * constraint_selector.clone();

            meta.create_gate(name, |_| {
                if linear_combinations.is_empty() {
                    return vec![Expression::Constant(F::zero())];
                }
                linear_combinations
                    .into_iter()
                    .map(|poly| synthetic_selector.clone() * poly)
                    .collect::<Vec<_>>()
            });

            independent_lookups.push((synthetic_selector, lookups));
        }

        Self {
            r,
            op_execution_state_curr,
            op_execution_state_next,
            op_selectors: op_selectors.to_vec(),
            free_cells: free_cells.to_vec(),
            op_selector_idx_map,
            default_values_map,
            resumption,
            add_gadget,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn constrcut_op_gadget<O: OpGadget<F>>(
        r: F,
        op_execution_state_curr: &OpExecutionState<F>,
        op_execution_state_next: &OpExecutionState<F>,
        op_selectors: &[Cell<F>],
        op_selector_idx: usize,
        free_cells: &[Cell<F>],
        resumption: &Resumption<F>,
        op_selector_idx_map: &mut HashMap<u8, usize>,
        default_values_map: &mut HashMap<(usize, Case), Vec<(usize, F)>>,
        constraints: &mut Vec<Constraint<F>>,
    ) -> O {
        assert!(op_selector_idx < NUM_CELL_OP_GADGET_SELECTOR);

        let op_selector = op_selectors[op_selector_idx].clone();

        // opcode should only be handled by one gadget
        for opcode in O::RESPONSIBLE_OPCODES {
            assert!(
                op_selector_idx_map
                    .insert(*opcode, op_selector_idx)
                    .is_none(),
                "opcode is already handled by another gadget"
            );
        }

        let case_configs = O::CASE_CONFIGS;
        let num_case = case_configs.len();
        let case_selectors = &free_cells[..num_case];

        constraints.push(Constraint {
            name: "case selectors",
            selector: op_selector.exp(),
            linear_combinations: bool_switches_constraints(case_selectors),
            lookups: vec![],
        });

        let case_allocations = case_configs
            .iter()
            .enumerate()
            .map(|(case_selector_idx, case_config)| {
                let mut offset = num_case;
                let mut default_values = Vec::new();

                // case selector values to assign
                for idx in 0..case_configs.len() {
                    default_values.push((
                        idx,
                        F::from_u64((idx == case_selector_idx) as u64),
                    ));
                }

                let total_cells = num_case + case_config.total_cells();
                assert!(
                    total_cells <= free_cells.len(),
                    "too many cells allocated"
                );

                let num_cell_of_word = 32 * case_config.num_word;
                let words = free_cells[offset..offset + num_cell_of_word]
                    .chunks(32)
                    .map(|free_cells| Word::new(free_cells, r))
                    .collect::<Vec<_>>();
                offset += num_cell_of_word;

                let cells = &free_cells[offset..offset + case_config.num_cell];
                offset += case_config.num_cell;

                let resumption = if case_config.will_resume {
                    Some(resumption)
                } else {
                    None
                };

                let num_unused = free_cells.len() - total_cells;
                for idx in offset..offset + num_unused {
                    default_values.push((idx, F::zero()));
                }

                assert!(
                    default_values_map
                        .insert(
                            (op_selector_idx, case_config.case),
                            default_values
                        )
                        .is_none(),
                    "duplicated case configured"
                );

                let case_selector = &case_selectors[case_selector_idx];
                constraints.push(Constraint {
                    name: "case unused",
                    selector: op_selector.exp() * case_selector.exp(),
                    linear_combinations: (offset..offset + num_unused)
                        .map(|idx| free_cells[idx].exp())
                        .collect(),
                    lookups: vec![],
                });

                CaseAllocation {
                    selector: case_selector,
                    words,
                    cells,
                    resumption,
                }
            })
            .collect::<Vec<_>>();

        let gadget = O::construct(case_allocations);

        constraints.append(
            &mut gadget
                .constraints(op_execution_state_curr, op_execution_state_next)
                .into_iter()
                .map(|mut constraint| {
                    constraint.selector =
                        op_selector.exp() * constraint.selector.clone();
                    constraint
                })
                .collect(),
        );

        gadget
    }

    pub(crate) fn assign_execution_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        core_state: &mut CoreStateInstance,
        execution_step: Option<&ExecutionStep>,
    ) -> Result<(), Error> {
        assert!(core_state.is_executing);

        self.op_execution_state_curr.is_executing.assign(
            region,
            offset,
            Some(F::one()),
        )?;
        self.op_execution_state_curr.global_counter.assign(
            region,
            offset,
            Some(F::from_u64(core_state.global_counter as u64)),
        )?;
        self.op_execution_state_curr.call_id.assign(
            region,
            offset,
            Some(F::from_u64(core_state.call_id as u64)),
        )?;
        self.op_execution_state_curr.program_counter.assign(
            region,
            offset,
            Some(F::from_u64(core_state.program_counter as u64)),
        )?;
        self.op_execution_state_curr.stack_pointer.assign(
            region,
            offset,
            Some(F::from_u64(core_state.stack_pointer as u64)),
        )?;
        self.op_execution_state_curr.gas_counter.assign(
            region,
            offset,
            Some(F::from_u64(core_state.gas_counter as u64)),
        )?;

        if let Some(execution_step) = execution_step {
            self.op_execution_state_curr.opcode.assign(
                region,
                offset,
                Some(F::from_u64(execution_step.opcode as u64)),
            )?;

            let &op_selector_idx = self
                .op_selector_idx_map
                .get(&execution_step.opcode)
                .expect("opcode to be handled");
            for (idx, op_selector) in self.op_selectors.iter().enumerate() {
                op_selector.assign(
                    region,
                    offset,
                    Some(F::from_u64((idx == op_selector_idx) as u64)),
                )?;
            }

            let default_values = self
                .default_values_map
                .get(&(op_selector_idx, execution_step.case))
                .expect("case to be handled");
            for (idx, value) in default_values {
                self.free_cells[*idx].assign(region, offset, Some(*value))?;
            }

            match execution_step.opcode {
                1 | 3 => self.add_gadget.assign(
                    region,
                    offset,
                    core_state,
                    execution_step,
                )?,
                _ => unimplemented!(),
            }
        }

        Ok(())
    }
}

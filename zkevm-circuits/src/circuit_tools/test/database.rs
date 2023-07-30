
use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    plonk::{Circuit, ConstraintSystem, Advice, Fixed, Column, FirstPhase, Challenge, Error, SecondPhase, Selector, Expression, VirtualCells}, 
    circuit::{SimpleFloorPlanner, Layouter, layouter, Value},
    poly::Rotation,
};
use sha3::digest::typenum::IsEqual;
use crate::circuit_tools::{memory::{Memory}, constraint_builder::ConstraintBuilder, cell_manager::{CellManager, CellType, Cell}, gadgets::IsEqualGadget};

const MAX_DEG: usize = 5;

pub struct DBConfig<F: Field> {
    pub(crate) q_first: Column<Fixed>,
    pub(crate) operation: Operation<F>,
    pub(crate) id: Column<Advice>,
    pub(crate) balance: Column<Advice>,
    pub(crate) db_read: Option<DBRead<F>>
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DBCell {
    PhaseOne,
    PhaseTwo,
}

impl CellType for DBCell {
    fn byte_type() -> Option<Self> {
        None
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            1 => DBCell::PhaseOne,
            2 => DBCell::PhaseTwo,
            _ => unreachable!()
        }
    }
}

impl Default for DBCell {
    fn default() -> Self {
        DBCell::PhaseOne
    }
}

impl<F: Field> DBConfig<F> {
    pub fn new(
        meta: &mut ConstraintSystem<F>, 
    ) -> Self {
        let q_first = meta.fixed_column();
        let mut operation = Operation::default();
        let op_col = meta.advice_column();
        let amt_col = meta.advice_column();
        let id = meta.advice_column();
        let balance =  meta.advice_column();
        let mut db_read = DBRead::default();

        let mut memory = Memory::new(
            meta,
            vec![(DBCell::PhaseOne, 1)],
            0,
            5
        );
        let cm = CellManager::new(
            meta,
            vec![
                (DBCell::PhaseOne, 3, 1, false),
                (DBCell::PhaseTwo, 3, 2, false),
            ],
            0,
            5,
        );
        let mut cb =  ConstraintBuilder::new(MAX_DEG,  Some(cm), None);
        meta.create_gate("DB", |meta| {
            circuit!([meta, cb], {
                operation.init(meta, &mut cb, op_col, amt_col);
                let bd = memory.get_mut_bank(DBCell::PhaseOne);
                matchx!(
                    operation.is_deposit() => {
                        require!(a!(balance) => a!(balance, -1) + a!(amt_col));
                        bd.store(&mut cb, &[a!(id), a!(balance)]);
                    },
                    operation.is_withdraw() => {
                        require!(a!(balance) => a!(balance, -1) - a!(amt_col));
                        bd.store(&mut cb, &[a!(id), a!(balance)]);
                    },
                    _ => {
                        let id = cb.query_default();
                        let balance = cb.query_default();
                        bd.load(
                            "Check Balance", 
                            &mut cb, 
                            a!(operation.check_offset()), &[id.expr(), balance.expr()]
                        );
                        db_read.id = Some(id);
                        db_read.balance = Some(balance);
                    },
                );
                memory.build_constraints(&mut cb, f!(q_first));
                cb.build_constraints()
            })
        });
        memory.build_lookups(meta);
        DBConfig { q_first, operation, id, balance, db_read: Some(db_read)}
    }


}

#[derive(Default)]
pub struct Operation<F: Field> {
    pub(crate) operation: Option<Column<Advice>>,
    pub(crate) amount: Option<Column<Advice>>,
    is_deposit: IsEqualGadget<F>,
    is_withdraw: IsEqualGadget<F>,
}

impl<F: Field> Operation<F> {
    fn init(
        &mut self, 
        meta: &mut VirtualCells<'_, F>, 
        cb: &mut ConstraintBuilder<F, DBCell>, 
        op_col: Column<Advice>,
        amt_col: Column<Advice>,
    ) {
        circuit!([meta, cb], {
            self.operation = Some(op_col);
            self.amount = Some(amt_col);
            // 0 => deposit, 1 => withdraw, 
            // others => check balance with amount representing offset
            self.is_deposit = IsEqualGadget::construct(cb, a!(op_col), 0.expr());
            self.is_withdraw = IsEqualGadget::construct(cb, a!(op_col), 1.expr());
        });
    }
    fn is_deposit(&self) -> Expression<F> {
        self.is_deposit.expr()
    }
    fn is_withdraw(&self) -> Expression<F> {
        self.is_withdraw.expr()
    }
    fn check_offset(&self) -> Column<Advice> {
        self.amount.unwrap().clone()
    }
}

#[derive(Default, Clone)]
pub struct DBRead<F: Field>{
    id: Option<Cell<F>>,
    balance: Option<Cell<F>>,
}
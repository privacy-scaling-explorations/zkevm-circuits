use halo2_kzg::circuit::Cell;

#[derive(Debug)]
pub struct Lane<F> {
    pub cell: Cell,
    pub value: F,
}

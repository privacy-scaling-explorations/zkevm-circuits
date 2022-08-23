use std::marker::PhantomData;
use pairing::arithmetic::FieldExt;
use halo2_proofs::{plonk::{Advice, Column, ConstraintSystem}};

#[derive(Clone, Debug)]
pub(crate) struct StorageLeafCols<F> {
    pub(crate) is_s_key: Column<Advice>,
    pub(crate) is_s_value: Column<Advice>,
    pub(crate) is_c_key: Column<Advice>,
    pub(crate) is_c_value: Column<Advice>,
    /** it is at drifted_pos position in added branch,
    * note that this row could be omitted when there
    * is no added branch but then it would open a
    * vulnerability because the attacker could omit
    * these row in cases when it is needed too (and
    * constraints happen in this row) */
    pub(crate) is_in_added_branch: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> StorageLeafCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_s_key : meta.advice_column(),
            is_s_value : meta.advice_column(),
            is_c_key : meta.advice_column(),
            is_c_value : meta.advice_column(),
            is_in_added_branch : meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Default)]
pub(crate) struct StorageLeaf {
    pub(crate) is_s_key: bool,
    pub(crate) is_s_value: bool,
    pub(crate) is_c_key: bool,
    pub(crate) is_c_value: bool,
    pub(crate) is_in_added_branch: bool,
}

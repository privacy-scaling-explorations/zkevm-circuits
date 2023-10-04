use super::{
    lookups::Queries as LookupsQueries, multiple_precision_integer::Queries as MpiQueries, param::*,
};
use crate::{
    evm_circuit::util::{math_gadget::generate_lagrange_base_polynomial, not},
    table::{AccountFieldTag, MPTProofType},
    util::{word, Expr},
};
use bus_mapping::operation::Target;
use eth_types::Field;
use gadgets::binary_number::BinaryNumberConfig;
use halo2_proofs::{
    plonk::{Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use strum::IntoEnumIterator;

#[derive(Clone)]
pub struct RwTableQueries<F: Field> {
    pub rw_counter: Expression<F>,
    pub prev_rw_counter: Expression<F>,
    pub is_write: Expression<F>,
    pub tag: Expression<F>,
    pub id: Expression<F>,
    pub prev_id: Expression<F>,
    pub address: Expression<F>,
    pub prev_address: Expression<F>,
    pub field_tag: Expression<F>,
    pub storage_key: word::Word<Expression<F>>,
    pub value: word::Word<Expression<F>>,
    pub value_prev: word::Word<Expression<F>>, // meta.query(value, Rotation::prev())
    pub value_prev_column: word::Word<Expression<F>>, // meta.query(prev_value, Rotation::cur())
}

#[derive(Clone)]
pub struct MptUpdateTableQueries<F: Field> {
    pub address: Expression<F>,
    pub storage_key: word::Word<Expression<F>>,
    pub proof_type: Expression<F>,
    pub new_root: word::Word<Expression<F>>,
    pub old_root: word::Word<Expression<F>>,
    pub new_value: word::Word<Expression<F>>,
    pub old_value: word::Word<Expression<F>>,
}

#[derive(Clone)]
pub struct Queries<F: Field> {
    pub selector: Expression<F>,
    pub rw_table: RwTableQueries<F>,
    pub mpt_update_table: MptUpdateTableQueries<F>,
    pub lexicographic_ordering_selector: Expression<F>,
    pub rw_counter: MpiQueries<F, N_LIMBS_RW_COUNTER>,
    pub tag_bits: [Expression<F>; 4],
    pub id: MpiQueries<F, N_LIMBS_ID>,
    pub is_tag_and_id_unchanged: Expression<F>,
    pub address: MpiQueries<F, N_LIMBS_ACCOUNT_ADDRESS>,
    pub storage_key: MpiQueries<F, N_LIMBS_WORD>,
    pub initial_value: word::Word<Expression<F>>,
    pub initial_value_prev: word::Word<Expression<F>>,
    pub is_non_exist: Expression<F>,
    pub mpt_proof_type: Expression<F>,
    pub lookups: LookupsQueries<F>,
    pub first_different_limb: [Expression<F>; 4],
    pub not_first_access: Expression<F>,
    pub last_access: Expression<F>,
    pub state_root: word::Word<Expression<F>>,
    pub state_root_prev: word::Word<Expression<F>>,
}

type Constraint<F> = (&'static str, Expression<F>);
type Lookup<F> = (&'static str, Vec<(Expression<F>, Expression<F>)>);

pub struct ConstraintBuilder<F: Field> {
    pub constraints: Vec<Constraint<F>>,
    lookups: Vec<Lookup<F>>,
    condition: Expression<F>,
}

struct LookupBuilder<F>(Vec<(Expression<F>, Expression<F>)>);
impl<F: Field> LookupBuilder<F> {
    fn new() -> Self {
        Self(vec![])
    }
    fn add(mut self, e1: &Expression<F>, e2: &Expression<F>) -> Self {
        self.0.push((e1.clone(), e2.clone()));
        self
    }
    fn add_word(mut self, e1: &word::Word<Expression<F>>, e2: &word::Word<Expression<F>>) -> Self {
        self.0.push((e1.lo(), e2.lo()));
        self.0.push((e1.hi(), e2.hi()));
        self
    }
    fn build(self) -> Vec<(Expression<F>, Expression<F>)> {
        self.0
    }
}

impl<F: Field> ConstraintBuilder<F> {
    pub fn new() -> Self {
        Self {
            constraints: vec![],
            lookups: vec![],
            condition: 1.expr(),
        }
    }

    pub fn gate(&self, condition: Expression<F>) -> Vec<(&'static str, Expression<F>)> {
        self.constraints
            .iter()
            .cloned()
            .map(|(name, expression)| (name, condition.clone() * expression))
            .collect()
    }

    pub fn lookups(&self, meta: &mut ConstraintSystem<F>, selector: Column<Fixed>) {
        self.lookups.iter().cloned().for_each(|(name, mut lookup)| {
            meta.lookup_any(name, |meta| {
                let selector = meta.query_fixed(selector, Rotation::cur());
                for (expression, _) in lookup.iter_mut() {
                    *expression = expression.clone() * selector.clone();
                }
                lookup
            });
        });
    }

    pub fn build(&mut self, q: &Queries<F>) {
        self.build_general_constraints(q);
        self.condition(q.tag_matches(Target::Start), |cb| {
            cb.build_start_constraints(q)
        });
        self.condition(q.tag_matches(Target::Memory), |cb| {
            cb.build_memory_constraints(q)
        });
        self.condition(q.tag_matches(Target::Stack), |cb| {
            cb.build_stack_constraints(q)
        });
        self.condition(q.tag_matches(Target::Storage), |cb| {
            cb.build_account_storage_constraints(q)
        });
        self.condition(q.tag_matches(Target::TxAccessListAccount), |cb| {
            cb.build_tx_access_list_account_constraints(q)
        });
        self.condition(q.tag_matches(Target::TxAccessListAccountStorage), |cb| {
            cb.build_tx_access_list_account_storage_constraints(q)
        });
        self.condition(q.tag_matches(Target::TxRefund), |cb| {
            cb.build_tx_refund_constraints(q)
        });
        self.condition(q.tag_matches(Target::Account), |cb| {
            cb.build_account_constraints(q)
        });
        self.condition(q.tag_matches(Target::CallContext), |cb| {
            cb.build_call_context_constraints(q)
        });
        self.condition(q.tag_matches(Target::TxLog), |cb| {
            cb.build_tx_log_constraints(q)
        });
    }

    fn build_general_constraints(&mut self, q: &Queries<F>) {
        // tag value in RwTableTag range is enforced in BinaryNumberChip
        self.require_boolean("is_write is boolean", q.is_write());

        // 1 if first_different_limb is in the rw counter, 0 otherwise (i.e. any of the
        // 4 most significant bits are 0)
        self.require_equal(
            "not_first_access when first 16 limbs are same",
            q.not_first_access.clone(),
            q.first_different_limb[0].clone()
                * q.first_different_limb[1].clone()
                * q.first_different_limb[2].clone()
                * q.first_different_limb[3].clone(),
        );

        // When at least one of the keys (tag, id, address, field_tag, or storage_key)
        // in the current row differs from the previous row.
        self.condition(q.first_access(), |cb| {
            cb.require_zero(
                "first access reads don't change value (hi)",
                q.is_read() * (q.rw_table.value.hi() - q.initial_value().hi()),
            );
            cb.require_zero(
                "first access reads don't change value (lo)",
                q.is_read() * (q.rw_table.value.lo() - q.initial_value().lo()),
            );
            cb.require_word_equal(
                "value_prev column is initial_value for first access",
                q.value_prev_column(),
                q.initial_value.clone(),
            );
        });

        // When all the keys in the current row and previous row are equal.
        self.condition(q.not_first_access.clone(), |cb| {
            cb.require_zero(
                "non-first access reads don't change value (hi)",
                q.is_read() * (q.rw_table.value.hi() - q.rw_table.value_prev.hi()),
            );
            cb.require_zero(
                "non-first access reads don't change value (lo)",
                q.is_read() * (q.rw_table.value.lo() - q.rw_table.value_prev.lo()),
            );
            cb.require_zero(
                "initial value doesn't change in an access group (hi)",
                q.initial_value.hi() - q.initial_value_prev().hi(),
            );
            cb.require_zero(
                "initial value doesn't change in an access group (lo)",
                q.initial_value.lo() - q.initial_value_prev().lo(),
            );
        });
    }

    fn build_start_constraints(&mut self, q: &Queries<F>) {
        // 1.0. Unused keys are 0
        self.require_zero("field_tag is 0 for Start", q.field_tag());
        self.require_zero("address is 0 for Start", q.rw_table.address.clone());
        self.require_zero("id is 0 for Start", q.id());
        self.require_word_zero("storage_key is 0 for Start", q.rw_table.storage_key.clone());
        // 1.1. rw_counter increases by 1 for every non-first row
        self.require_zero(
            "rw_counter increases by 1 for every non-first row",
            q.lexicographic_ordering_selector.clone() * (q.rw_counter_change() - 1.expr()),
        );
        // 1.2. Start value is 0
        self.require_word_zero("Start value is 0", q.value());
        // 1.3. Start initial value is 0
        self.require_word_zero("Start initial_value is 0", q.initial_value());
        // 1.4. state_root is unchanged for every non-first row
        self.condition(q.lexicographic_ordering_selector.clone(), |cb| {
            cb.require_word_equal(
                "state_root is unchanged for Start",
                q.state_root(),
                q.state_root_prev(),
            )
        });
        self.require_word_zero("value_prev column is 0 for Start", q.value_prev_column());
    }

    fn build_memory_constraints(&mut self, q: &Queries<F>) {
        // 2.0. Unused keys are 0
        self.require_zero("field_tag is 0 for Memory", q.field_tag());
        self.require_word_zero(
            "storage_key is 0 for Memory",
            q.rw_table.storage_key.clone(),
        );
        // 2.1. First access for a set of all keys are 0 if READ
        self.condition(q.first_access() * q.is_read(), |cb| {
            cb.require_word_zero(
                "first access for a set of all keys are 0 if READ",
                q.value(),
            );
        });
        // could do this more efficiently by just asserting address = limb0 + 2^16 *
        // limb1?
        // 2.2. mem_addr in range
        for limb in &q.address.limbs[2..] {
            self.require_zero("memory address fits into 2 limbs", limb.clone());
        }
        // 2.3. value is a byte
        self.add_lookup(
            "memory value is a byte (lo is u8)",
            vec![(q.rw_table.value.lo(), q.lookups.u8.clone())],
        );
        self.require_zero("memory value is a byte (hi is 0)", q.rw_table.value.hi());
        // 2.4. Start initial value is 0
        self.require_word_zero("initial Memory value is 0", q.initial_value());
        // 2.5. state root does not change
        self.require_word_equal(
            "state_root is unchanged for Memory",
            q.state_root(),
            q.state_root_prev(),
        );
        self.require_word_equal(
            "value_prev column equals initial_value for Memory",
            q.value_prev_column(),
            q.initial_value(),
        );
    }

    fn build_stack_constraints(&mut self, q: &Queries<F>) {
        // 3.0. Unused keys are 0
        self.require_zero("field_tag is 0 for Stack", q.field_tag());
        self.require_word_zero("storage_key is 0 for Stack", q.rw_table.storage_key.clone());
        // 3.1. First access for a set of all keys
        self.require_zero(
            "first access to new stack address is a write",
            q.first_access() * (1.expr() - q.is_write()),
        );
        // 3.2. stack_ptr in range
        self.add_lookup(
            "stack address fits into 10 bits",
            vec![(q.rw_table.address.clone(), q.lookups.u10.clone())],
        );
        // 3.3. stack_ptr only increases by 0 or 1
        self.condition(q.is_tag_and_id_unchanged.clone(), |cb| {
            cb.require_boolean(
                "if previous row is also Stack with unchanged call id, address change is 0 or 1",
                q.address_change(),
            )
        });
        // 3.4. Stack initial value is 0
        self.require_word_zero("initial Stack value is 0", q.initial_value.clone());
        // 3.5 state root does not change
        self.require_word_equal(
            "state_root is unchanged for Stack",
            q.state_root(),
            q.state_root_prev(),
        );
        self.require_word_equal(
            "value_prev column equals initial_value for Stack",
            q.value_prev_column(),
            q.initial_value(),
        );
    }

    fn build_account_storage_constraints(&mut self, q: &Queries<F>) {
        // TODO: cold VS warm
        // ref. spec 4.0. Unused keys are 0
        self.require_zero("field_tag is 0 for AccountStorage", q.field_tag());

        // value = 0 means the leaf doesn't exist. 0->0 transition requires a
        // non-existing proof.
        let is_non_exist = q.is_non_exist();
        self.require_equal(
            "mpt_proof_type is field_tag or NonExistingStorageProof",
            q.mpt_proof_type(),
            is_non_exist.expr() * MPTProofType::StorageDoesNotExist.expr()
                + (1.expr() - is_non_exist) * MPTProofType::StorageChanged.expr(),
        );

        // ref. spec 4.1. MPT lookup for last access to (address, storage_key)
        self.condition(q.last_access(), |cb| {
            cb.add_lookup(
                "mpt_update exists in mpt circuit for AccountStorage last access",
                LookupBuilder::new()
                    .add(&q.rw_table.address, &q.mpt_update_table.address)
                    .add_word(&q.rw_table.storage_key, &q.mpt_update_table.storage_key)
                    .add(&q.mpt_proof_type(), &q.mpt_update_table.proof_type)
                    .add_word(&q.state_root(), &q.mpt_update_table.new_root)
                    .add_word(&q.state_root_prev(), &q.mpt_update_table.old_root)
                    .add_word(&q.value(), &q.mpt_update_table.new_value)
                    .add_word(&q.initial_value(), &q.mpt_update_table.old_value)
                    .build(),
            );
        });

        self.condition(q.not_first_access.clone(), |cb| {
            cb.require_word_equal(
                "value column at Rotation::prev() equals value_prev at Rotation::cur()",
                q.rw_table.value_prev.clone(),
                q.value_prev_column(),
            );
        });
    }

    fn build_tx_access_list_account_constraints(&mut self, q: &Queries<F>) {
        self.require_zero("field_tag is 0 for TxAccessListAccount", q.field_tag());
        self.require_word_zero(
            "storage_key is 0 for TxAccessListAccount",
            q.rw_table.storage_key.clone(),
        );
        self.require_word_boolean("TxAccessListAccount value is boolean", q.value());
        self.require_word_zero(
            "initial TxAccessListAccount value is false",
            q.initial_value(),
        );

        self.require_word_equal(
            "state_root is unchanged for TxAccessListAccount",
            q.state_root(),
            q.state_root_prev(),
        );

        self.condition(q.not_first_access.clone(), |cb| {
            cb.require_word_equal(
                "value column at Rotation::prev() equals value_prev at Rotation::cur()",
                q.rw_table.value_prev.clone(),
                q.value_prev_column(),
            );
        });
    }

    fn build_tx_access_list_account_storage_constraints(&mut self, q: &Queries<F>) {
        self.require_zero(
            "field_tag is 0 for TxAccessListAccountStorage",
            q.field_tag(),
        );
        self.require_word_boolean("TxAccessListAccountStorage value is boolean", q.value());
        self.require_word_zero(
            "initial TxAccessListAccountStorage value is false",
            q.initial_value(),
        );

        self.require_word_equal(
            "state_root is unchanged for TxAccessListAccountStorage",
            q.state_root(),
            q.state_root_prev(),
        );

        self.condition(q.not_first_access.clone(), |cb| {
            cb.require_word_equal(
                "value column at Rotation::prev() equals value_prev at Rotation::cur()",
                q.rw_table.value_prev.clone(),
                q.value_prev_column(),
            );
        });
    }

    fn build_tx_refund_constraints(&mut self, q: &Queries<F>) {
        // 7.0. `address`, `field_tag` and `storage_key` are 0
        self.require_zero("address is 0 for TxRefund", q.rw_table.address.clone());
        self.require_zero("field_tag is 0 for TxRefund", q.field_tag());
        self.require_word_zero(
            "storage_key is 0 for TxRefund",
            q.rw_table.storage_key.clone(),
        );
        // 7.1. `state root` is not changed
        self.require_word_equal(
            "state_root is unchanged for TxRefund",
            q.state_root(),
            q.state_root_prev(),
        );

        self.condition(q.not_first_access.clone(), |cb| {
            cb.require_word_equal(
                "value column at Rotation::prev() equals value_prev at Rotation::cur()",
                q.rw_table.value_prev.clone(),
                q.value_prev_column(),
            );
        });
        // 7.2. `initial value` is 0
        self.require_word_zero("initial TxRefund value is 0", q.initial_value());
    }

    fn build_account_constraints(&mut self, q: &Queries<F>) {
        // ref. spec 6.0. Unused keys are 0
        self.require_zero("id is 0 for Account", q.id());
        self.require_word_zero(
            "storage_key is 0 for Account",
            q.rw_table.storage_key.clone(),
        );
        self.require_in_set(
            "field_tag in AccountFieldTag range",
            q.field_tag(),
            set::<F, AccountFieldTag>(),
        );

        // We use code_hash = 0 as non-existing account state.  code_hash: 0->0
        // transition requires a non-existing proof.
        // is_non_exist degree = 4
        //   q.is_non_exist() degree = 1
        //   generate_lagrange_base_polynomial() degree = 3
        let is_non_exist = q.is_non_exist()
            * generate_lagrange_base_polynomial(
                q.field_tag(),
                AccountFieldTag::CodeHash as usize,
                [
                    AccountFieldTag::Nonce,
                    AccountFieldTag::Balance,
                    AccountFieldTag::CodeHash,
                ]
                .iter()
                .map(|t| *t as usize),
            );
        self.require_equal(
            "mpt_proof_type is field_tag or AccountDoesNotExist",
            q.mpt_proof_type(),
            // degree = max(4, 4 + 1) = 5
            is_non_exist.expr() * MPTProofType::AccountDoesNotExist.expr()
                + (1.expr() - is_non_exist) * q.field_tag(),
        );

        // last_access degree = 1
        self.condition(q.last_access(), |cb| {
            cb.add_lookup(
                "mpt_update exists in mpt circuit for Account last access",
                LookupBuilder::new()
                    .add(&q.rw_table.address, &q.mpt_update_table.address)
                    .add_word(&q.rw_table.storage_key, &q.mpt_update_table.storage_key)
                    .add(&q.mpt_proof_type(), &q.mpt_update_table.proof_type)
                    .add_word(&q.state_root(), &q.mpt_update_table.new_root)
                    .add_word(&q.state_root_prev(), &q.mpt_update_table.old_root)
                    .add_word(&q.value(), &q.mpt_update_table.new_value)
                    .add_word(&q.initial_value(), &q.mpt_update_table.old_value)
                    .build(),
            );
        });

        self.condition(q.not_first_access.clone(), |cb| {
            cb.require_word_equal(
                "value column at Rotation::prev() equals value_prev at Rotation::cur()",
                q.rw_table.value_prev.clone(),
                q.value_prev_column(),
            );
        });
    }

    fn build_call_context_constraints(&mut self, q: &Queries<F>) {
        self.require_zero("address is 0 for CallContext", q.rw_table.address.clone());
        self.require_word_zero(
            "storage_key is 0 for CallContext",
            q.rw_table.storage_key.clone(),
        );
        self.add_lookup(
            "field_tag in CallContextFieldTag range",
            vec![(q.field_tag(), q.lookups.call_context_field_tag.clone())],
        );
        self.require_word_zero("initial CallContext value is 0", q.initial_value());
        self.require_word_equal(
            "state_root is unchanged for CallContext",
            q.state_root(),
            q.state_root_prev(),
        );
        self.require_word_zero(
            "value_prev column is 0 for CallContext",
            q.value_prev_column(),
        );
    }

    fn build_tx_log_constraints(&mut self, q: &Queries<F>) {
        self.require_equal(
            "is_write is always true for TxLog",
            q.rw_table.is_write.clone(),
            1.expr(),
        );
        self.require_word_zero("initial TxLog value is 0", q.initial_value());

        self.require_word_equal(
            "state_root is unchanged for TxLog",
            q.state_root(),
            q.state_root_prev(),
        );
        self.require_word_equal(
            "value_prev column equals initial_value for TxLog",
            q.value_prev_column(),
            q.initial_value(),
        );
    }

    fn require_zero(&mut self, name: &'static str, e: Expression<F>) {
        self.constraints.push((name, self.condition.clone() * e));
    }

    fn require_word_zero(&mut self, name: &'static str, e: word::Word<Expression<F>>) {
        let (lo, hi) = e.into_lo_hi();
        self.constraints.push((name, self.condition.clone() * hi));
        self.constraints.push((name, self.condition.clone() * lo));
    }

    fn require_equal(&mut self, name: &'static str, left: Expression<F>, right: Expression<F>) {
        self.require_zero(name, left - right)
    }

    fn require_word_equal(
        &mut self,
        name: &'static str,
        left: word::Word<Expression<F>>,
        right: word::Word<Expression<F>>,
    ) {
        let (left_lo, left_hi) = left.into_lo_hi();
        let (right_lo, right_hi) = right.into_lo_hi();
        self.require_zero(name, left_hi - right_hi);
        self.require_zero(name, left_lo - right_lo);
    }

    fn require_boolean(&mut self, name: &'static str, e: Expression<F>) {
        self.require_zero(name, e.clone() * (1.expr() - e))
    }

    fn require_word_boolean(&mut self, name: &'static str, e: word::Word<Expression<F>>) {
        let (lo, hi) = e.into_lo_hi();
        self.require_zero(name, hi);
        self.require_zero(name, lo.clone() * (1.expr() - lo));
    }

    fn require_in_set(&mut self, name: &'static str, item: Expression<F>, set: Vec<Expression<F>>) {
        self.require_zero(
            name,
            set.iter().fold(1.expr(), |acc, element| {
                acc * (item.clone() - element.clone())
            }),
        );
    }

    fn add_lookup(&mut self, name: &'static str, lookup: Vec<(Expression<F>, Expression<F>)>) {
        let mut lookup = lookup;
        for (expression, _) in lookup.iter_mut() {
            *expression = expression.clone() * self.condition.clone();
        }
        self.lookups.push((name, lookup));
    }

    fn condition(&mut self, condition: Expression<F>, build: impl FnOnce(&mut Self)) {
        let original_condition = self.condition.clone();
        self.condition = self.condition.clone() * condition;
        build(self);
        self.condition = original_condition;
    }
}

impl<F: Field> Queries<F> {
    fn is_write(&self) -> Expression<F> {
        self.rw_table.is_write.clone()
    }

    fn is_read(&self) -> Expression<F> {
        not::expr(self.is_write())
    }

    fn id(&self) -> Expression<F> {
        self.rw_table.id.clone()
    }

    fn field_tag(&self) -> Expression<F> {
        self.rw_table.field_tag.clone()
    }

    fn value(&self) -> word::Word<Expression<F>> {
        self.rw_table.value.clone()
    }

    fn initial_value(&self) -> word::Word<Expression<F>> {
        self.initial_value.clone()
    }

    fn initial_value_prev(&self) -> word::Word<Expression<F>> {
        self.initial_value_prev.clone()
    }

    fn is_non_exist(&self) -> Expression<F> {
        self.is_non_exist.clone()
    }

    fn mpt_proof_type(&self) -> Expression<F> {
        self.mpt_proof_type.clone()
    }

    fn tag_matches(&self, tag: Target) -> Expression<F> {
        BinaryNumberConfig::<Target, 4>::value_equals_expr(tag, self.tag_bits.clone())
    }

    fn first_access(&self) -> Expression<F> {
        not::expr(self.not_first_access.clone())
    }

    fn address_change(&self) -> Expression<F> {
        self.rw_table.address.clone() - self.rw_table.prev_address.clone()
    }

    fn rw_counter_change(&self) -> Expression<F> {
        self.rw_table.rw_counter.clone() - self.rw_table.prev_rw_counter.clone()
    }

    fn last_access(&self) -> Expression<F> {
        self.last_access.clone()
    }

    fn state_root(&self) -> word::Word<Expression<F>> {
        self.state_root.clone()
    }

    fn state_root_prev(&self) -> word::Word<Expression<F>> {
        self.state_root_prev.clone()
    }

    fn value_prev_column(&self) -> word::Word<Expression<F>> {
        self.rw_table.value_prev_column.clone()
    }
}

fn set<F: Field, T: IntoEnumIterator + Expr<F>>() -> Vec<Expression<F>> {
    T::iter().map(|x| x.expr()).collect() // you don't need this collect if you
                                          // can figure out the return type
                                          // without it.
}

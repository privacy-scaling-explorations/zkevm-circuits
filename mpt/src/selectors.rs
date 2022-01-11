use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(crate) struct SelectorsConfig {}

// Ensures selectors are booleans. Ensures the proper order of rows.
pub(crate) struct SelectorsChip<F> {
    config: SelectorsConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SelectorsChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        is_branch_init: Column<Advice>,
        is_branch_child: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        is_leaf_s_key: Column<Advice>,
        is_leaf_s_value: Column<Advice>,
        is_leaf_c_key: Column<Advice>,
        is_leaf_c_value: Column<Advice>,
        is_account_leaf_key_s: Column<Advice>,
        is_account_leaf_nonce_balance_s: Column<Advice>,
        is_account_leaf_storage_codehash_s: Column<Advice>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        is_leaf_in_added_branch: Column<Advice>,
        is_extension_node_s: Column<Advice>,
        is_extension_node_c: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        is_modified: Column<Advice>,
        is_at_first_nibble: Column<Advice>,
    ) -> SelectorsConfig {
        let config = SelectorsConfig {};

        meta.create_gate("selectors", |meta| {
            let q_enable = q_enable(meta);

            let one = Expression::Constant(F::one());

            let mut constraints = vec![];
            let is_branch_init_cur =
                meta.query_advice(is_branch_init, Rotation::cur());
            let is_branch_child_cur =
                meta.query_advice(is_branch_child, Rotation::cur());
            let is_last_branch_child_cur =
                meta.query_advice(is_last_branch_child, Rotation::cur());
            let is_leaf_s_key =
                meta.query_advice(is_leaf_s_key, Rotation::cur());
            let is_leaf_s_value =
                meta.query_advice(is_leaf_s_value, Rotation::cur());
            let is_leaf_c_key =
                meta.query_advice(is_leaf_c_key, Rotation::cur());
            let is_leaf_c_value =
                meta.query_advice(is_leaf_c_value, Rotation::cur());

            let is_account_leaf_key_s =
                meta.query_advice(is_account_leaf_key_s, Rotation::cur());
            let is_account_leaf_nonce_balance_s = meta
                .query_advice(is_account_leaf_nonce_balance_s, Rotation::cur());
            let is_account_leaf_storage_codehash_s = meta.query_advice(
                is_account_leaf_storage_codehash_s,
                Rotation::cur(),
            );

            let is_account_leaf_storage_codehash_c = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation::cur(),
            );
            let sel1 = meta.query_advice(sel1, Rotation::cur());
            let sel2 = meta.query_advice(sel2, Rotation::cur());

            let bool_check_is_branch_init =
                is_branch_init_cur.clone() * (one.clone() - is_branch_init_cur);
            let bool_check_is_branch_child = is_branch_child_cur.clone()
                * (one.clone() - is_branch_child_cur.clone());
            let bool_check_is_last_branch_child = is_last_branch_child_cur
                .clone()
                * (one.clone() - is_last_branch_child_cur);
            let bool_check_is_leaf_s =
                is_leaf_s_key.clone() * (one.clone() - is_leaf_s_key);
            let bool_check_is_leaf_c =
                is_leaf_c_key.clone() * (one.clone() - is_leaf_c_key);

            let bool_check_is_leaf_s_value =
                is_leaf_s_value.clone() * (one.clone() - is_leaf_s_value);
            let bool_check_is_leaf_c_value =
                is_leaf_c_value.clone() * (one.clone() - is_leaf_c_value);

            let bool_check_is_account_leaf_key_s = is_account_leaf_key_s
                .clone()
                * (one.clone() - is_account_leaf_key_s);
            let bool_check_is_account_nonce_balance_s =
                is_account_leaf_nonce_balance_s.clone()
                    * (one.clone() - is_account_leaf_nonce_balance_s);
            let bool_check_is_account_storage_codehash_s =
                is_account_leaf_storage_codehash_s.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_s);
            let bool_check_is_account_storage_codehash_c =
                is_account_leaf_storage_codehash_c.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_c);

            let bool_check_sel1 = sel1.clone() * (one.clone() - sel1);
            let bool_check_sel2 = sel2.clone() * (one.clone() - sel2);

            // TODO: sel1 + sel2 = 1
            // However, in branch children, it can be sel1 + sel2 = 0 too - this
            // case is checked separately.

            // TODO order: is_last_branch_child followed by is_leaf_s followed by is_leaf_c
            // followed by is_leaf_key_nibbles
            // is_leaf_s_value ..., is_extension_node_s, is_extension_node_c, is_leaf_in_added_branch ...

            // TODO: account leaf constraints (order and also that account leaf selectors
            // are true only in account proof part & normal leaf selectors are true only
            // in storage part, for this we also need account proof selector and storage
            // proof selector - bool and strictly increasing for example. Also, is_account_leaf_key_nibbles
            // needs to be 1 in the previous row when the account/storage selector changes.

            // TODO: constraints for s_advices[IS_ADD_BRANCH_S_POS - LAYOUT_OFFSET]
            // and s_advices[IS_ADD_BRANCH_C_POS - LAYOUT_OFFSET] in branch init

            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_first_nibble =
                meta.query_advice(is_at_first_nibble, Rotation::cur());
            let is_leaf_in_added_branch =
                meta.query_advice(is_leaf_in_added_branch, Rotation::cur());
            let is_extension_node_s =
                meta.query_advice(is_extension_node_s, Rotation::cur());
            let is_extension_node_c =
                meta.query_advice(is_extension_node_c, Rotation::cur());

            constraints.push((
                "bool check is branch init",
                q_enable.clone() * bool_check_is_branch_init,
            ));
            constraints.push((
                "bool check is branch child",
                q_enable.clone() * bool_check_is_branch_child,
            ));
            constraints.push((
                "bool check is last branch child",
                q_enable.clone() * bool_check_is_last_branch_child,
            ));
            constraints.push((
                "bool check is leaf s",
                q_enable.clone() * bool_check_is_leaf_s,
            ));
            constraints.push((
                "bool check is leaf c",
                q_enable.clone() * bool_check_is_leaf_c,
            ));

            constraints.push((
                "bool check is leaf s value",
                q_enable.clone() * bool_check_is_leaf_s_value,
            ));
            constraints.push((
                "bool check is leaf c value",
                q_enable.clone() * bool_check_is_leaf_c_value,
            ));

            constraints.push((
                "bool check is leaf account key s",
                q_enable.clone() * bool_check_is_account_leaf_key_s,
            ));
            constraints.push((
                "bool check is leaf account nonce balance s",
                q_enable.clone() * bool_check_is_account_nonce_balance_s,
            ));
            constraints.push((
                "bool check is leaf account storage codehash s",
                q_enable.clone() * bool_check_is_account_storage_codehash_s,
            ));
            constraints.push((
                "bool check is leaf account storage codehash c",
                q_enable.clone() * bool_check_is_account_storage_codehash_c,
            ));
            constraints
                .push(("bool check sel1", q_enable.clone() * bool_check_sel1));
            constraints
                .push(("bool check sel2", q_enable.clone() * bool_check_sel2));

            let bool_check_is_modified =
                is_modified.clone() * (one.clone() - is_modified.clone());
            constraints.push((
                "bool check is_modified",
                q_enable.clone() * bool_check_is_modified,
            ));

            let bool_check_is_at_first_nibble = is_at_first_nibble.clone()
                * (one.clone() - is_at_first_nibble.clone());
            constraints.push((
                "bool check is_at_first_nibble",
                q_enable.clone() * bool_check_is_at_first_nibble,
            ));

            let bool_check_is_leaf_in_added_branch = is_leaf_in_added_branch
                .clone()
                * (one.clone() - is_leaf_in_added_branch.clone());
            constraints.push((
                "bool check is_leaf_in_added_branch",
                q_enable.clone() * bool_check_is_leaf_in_added_branch,
            ));

            let bool_check_is_extension_node_s = is_extension_node_s.clone()
                * (one.clone() - is_extension_node_s.clone());
            constraints.push((
                "bool check is_extension_node_s",
                q_enable.clone() * bool_check_is_extension_node_s,
            ));
            let bool_check_is_extension_node_c = is_extension_node_c.clone()
                * (one.clone() - is_extension_node_c.clone());
            constraints.push((
                "bool check is_extension_node_c",
                q_enable.clone() * bool_check_is_extension_node_c,
            ));

            constraints
        });

        config
    }

    pub fn construct(config: SelectorsConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for SelectorsChip<F> {
    type Config = SelectorsConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    helpers::{KeyDataWitness, ListKeyGadget, MPTConstraintBuilder},
    rlp_gadgets::RLPItemGadget,
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{cell_manager::Cell, constraint_builder::RLCChainable, gadgets::LtGadget},
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{helpers::num_nibbles, param::HASH_WIDTH},
    mpt_circuit::{
        helpers::{ext_key_rlc_calc_value, ext_key_rlc_expr, Indexable, KeyData, ParentData},
        FixedTableTag,
    },
    mpt_circuit::{MPTConfig, MPTState},
};

#[derive(Clone, Debug)]
pub(crate) struct ExtState<F> {
    pub(crate) key_rlc: Expression<F>,
    pub(crate) key_mult: Expression<F>,
    pub(crate) num_nibbles: Expression<F>,
    pub(crate) is_key_odd: Expression<F>,

    pub(crate) branch_rlp_rlc: [Expression<F>; 2],
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ExtensionGadget<F> {
    rlp_key: ListKeyGadget<F>,
    rlp_value: [RLPItemGadget<F>; 2],
    mult: Cell<F>,
    is_not_hashed: LtGadget<F, 2>,
    is_key_part_odd: Cell<F>,
    mult_key: Cell<F>,

    // Post extension state
    post_state: Option<ExtState<F>>,
}

impl<F: Field> ExtensionGadget<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        key_data: &KeyData<F>,
        parent_data: &[ParentData<F>; 2],
        is_placeholder: &[Cell<F>; 2],
    ) -> Self {
        let r = ctx.r.clone();

        let mut config = ExtensionGadget::default();

        circuit!([meta, cb.base], {
            // Data
            let key_bytes: [Vec<Expression<F>>; 2] = [ctx.s(meta, 17), ctx.s(meta, 18)];
            let value_bytes: [Vec<Expression<F>>; 2] = [ctx.c(meta, 17), ctx.c(meta, 18)];

            config.rlp_key = ListKeyGadget::construct(&mut cb.base, &key_bytes[0]);
            // TODO(Brecht): add lookup constraint
            config.is_key_part_odd = cb.base.query_cell();

            // We need to check that the nibbles we stored in s are between 0 and 15.
            cb.set_range_s(FixedTableTag::RangeKeyLen16.expr());

            let mut branch_rlp_rlc = vec![0.expr(); 2];
            for is_s in [true, false] {
                config.rlp_value[is_s.idx()] =
                    RLPItemGadget::construct(&mut cb.base, &value_bytes[is_s.idx()]);

                // In C we have the key nibbles, we check below only for S.
                if is_s {
                    // RLP encoding checks: [key, branch]
                    // Verify that the lenghts are consistent.
                    require!(config.rlp_key.rlp_list.len() => config.rlp_key.key_value.num_bytes() + config.rlp_value[is_s.idx()].num_bytes());

                    // Update the multiplier with the number of bytes on the first row
                    config.mult = cb.base.query_cell();
                    require!((FixedTableTag::RMult, config.rlp_key.num_bytes_on_key_row(), config.mult.expr()) => @"fixed");
                }

                // Extension node RLC
                let node_rlc = (config.rlp_key.rlc(&r), config.mult.expr())
                    .rlc_chain(config.rlp_value[is_s.idx()].rlc_rlp(&mut cb.base, &r));
                // Branch value data zero check
                cb.set_length_c(config.rlp_value[is_s.idx()].num_bytes());

                // The branch expected in the extension node
                branch_rlp_rlc[is_s.idx()] = config.rlp_value[is_s.idx()].rlc_rlp(&mut cb.base, &r);

                // Check if the extension node is in its parent.
                let (rlc, num_bytes, is_not_hashed) = {
                    if is_s {
                        config.is_not_hashed = LtGadget::construct(
                            &mut cb.base,
                            config.rlp_key.rlp_list.num_bytes(),
                            HASH_WIDTH.expr(),
                        );
                    }
                    (
                        node_rlc.expr(),
                        config.rlp_key.rlp_list.num_bytes(),
                        config.is_not_hashed.expr(),
                    )
                };
                ifx! {not!(is_placeholder[is_s.idx()]) => {
                    ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                        // Hashed branch hash in parent branch
                        require!((1, rlc, num_bytes, parent_data[is_s.idx()].rlc) => @"keccak");
                    } elsex {
                        // Non-hashed branch hash in parent branch
                        require!(rlc => parent_data[is_s.idx()].rlc);
                    }}
                }}
            }

            // Extension key zero check
            cb.set_length(config.rlp_key.num_bytes_on_key_row());

            // Calculate the number of bytes
            let key_len = config.rlp_key.key_value.len();
            // Calculate the number of nibbles
            let num_nibbles = num_nibbles::expr(key_len.expr(), config.is_key_part_odd.expr());
            // Make sure the nibble counter is updated correctly
            let num_nibbles = key_data.num_nibbles.expr() + num_nibbles.expr();

            // We need to take account the nibbles of the extension node.
            // The parity alternates when there's an even number of nibbles, remains the
            // same otherwise
            let is_key_odd = ifx! {config.is_key_part_odd => {
                not!(key_data.is_odd)
            } elsex {
                key_data.is_odd.expr()
            }};

            // Calculate the extension node key RLC when in an extension node
            // Currently, the extension node S and extension node C both have the same key
            // RLC - however, sometimes extension node can be replaced by a
            // shorter extension node (in terms of nibbles), this is still to be
            // implemented.
            let key_rlc = key_data.rlc.expr()
                + ext_key_rlc_expr(
                    &mut cb.base,
                    config.rlp_key.key_value.clone(),
                    key_data.mult.expr(),
                    config.is_key_part_odd.expr(),
                    not!(is_key_odd),
                    key_bytes.clone(),
                    &ctx.r,
                );

            // Get the length of the key
            // Unless both parts of the key are odd, subtract 1 from the key length.
            let key_len = config.rlp_key.key_value.len();
            let key_num_bytes_for_mult = key_len
                - ifx! {not!(key_data.is_odd.expr() * config.is_key_part_odd.expr()) => { 1.expr() }};
            // Get the multiplier for this key length
            config.mult_key = cb.base.query_cell();
            require!((FixedTableTag::RMult, key_num_bytes_for_mult, config.mult_key.expr()) => @"fixed");

            // Store the post ext state
            config.post_state = Some(ExtState {
                key_rlc: key_rlc,
                key_mult: key_data.mult.expr() * config.mult_key.expr(),
                num_nibbles,
                is_key_odd,
                branch_rlp_rlc: branch_rlp_rlc.try_into().unwrap(),
            });
        });

        config
    }

    pub(crate) fn get_post_state(&self) -> ExtState<F> {
        self.post_state.as_ref().unwrap().clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        witness: &mut [MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        _pv: &mut MPTState<F>,
        offset: usize,
        idx: usize,
        key_data: &KeyDataWitness<F>,
        key_rlc: &mut F,
        key_mult: &mut F,
        num_nibbles: &mut usize,
        is_key_odd: &mut bool,
    ) -> Result<(), Error> {
        // Data
        let list_rlp_bytes = witness[idx + 17].rlp_bytes.to_owned();
        let key_bytes: [Vec<u8>; 2] = [witness[idx + 17].s(), witness[idx + 18].s()];
        let value_bytes: [Vec<u8>; 2] = [witness[idx + 17].c(), witness[idx + 18].c()];

        let rlp_key =
            self.rlp_key
                .assign(region, offset, &list_rlp_bytes, &key_bytes[true.idx()])?;

        let mut ext_mult = F::one();
        for _ in 0..rlp_key.num_bytes_on_key_row() {
            ext_mult *= mpt_config.r;
        }
        self.mult.assign(region, offset, ext_mult)?;

        let is_key_part_odd = key_bytes[0][rlp_key.key_value.num_rlp_bytes()] >> 4 == 1;
        self.is_key_part_odd
            .assign(region, offset, is_key_part_odd.scalar())?;

        self.is_not_hashed.assign(
            region,
            offset,
            rlp_key.rlp_list.num_bytes().scalar(),
            HASH_WIDTH.scalar(),
        )?;

        let mut key_len_mult = rlp_key.key_value.len();
        if !(*is_key_odd && is_key_part_odd) {
            key_len_mult -= 1;
        }

        // Update number of nibbles
        *num_nibbles += num_nibbles::value(rlp_key.key_value.len(), is_key_part_odd);

        // Update parity
        *is_key_odd = if is_key_part_odd {
            !*is_key_odd
        } else {
            *is_key_odd
        };

        // Key RLC
        let (key_rlc_ext, _) = ext_key_rlc_calc_value(
            rlp_key.key_value.clone(),
            key_data.mult,
            is_key_part_odd,
            !*is_key_odd,
            key_bytes.clone(),
            mpt_config.r,
        );
        *key_rlc = key_data.rlc + key_rlc_ext;

        // Key mult
        let mut mult_key = 1.scalar();
        for _ in 0..key_len_mult {
            mult_key = mult_key * mpt_config.r;
        }
        self.mult_key.assign(region, offset, mult_key)?;
        *key_mult = key_data.mult * mult_key;

        for is_s in [true, false] {
            self.rlp_value[is_s.idx()].assign(region, offset, &value_bytes[is_s.idx()])?;
        }

        Ok(())
    }
}

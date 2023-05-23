use eth_types::Field;
use gadgets::util::{pow, Scalar};
use halo2_proofs::{
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    helpers::{KeyDataWitness, ListKeyGadget, MPTConstraintBuilder},
    rlp_gadgets::RLPItemWitness,
    witness_row::{ExtensionBranchRowType, Node},
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{cell_manager::Cell, constraint_builder::RLCChainable, gadgets::LtGadget, cached_region::{CachedRegion, ChallengeSet}},
    mpt_circuit::{
        helpers::{
            ext_key_rlc_calc_value, ext_key_rlc_expr, num_nibbles, Indexable, KeyData, ParentData,
        },
        param::HASH_WIDTH,
        FixedTableTag, MPTConfig, MPTState,
    },
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

        circuit!([meta, cb], {
            // Data
            let key_items = [
                ctx.rlp_item(meta,cb, ExtensionBranchRowType::KeyS as usize),
                ctx.nibbles(meta, cb, ExtensionBranchRowType::KeyC as usize),
            ];
            let rlp_value = [
                ctx.rlp_item(meta, cb, ExtensionBranchRowType::ValueS as usize),
                ctx.rlp_item(meta, cb, ExtensionBranchRowType::ValueC as usize),
            ];

            config.rlp_key = ListKeyGadget::construct(cb, &key_items[0]);
            // TODO(Brecht): add lookup constraint
            config.is_key_part_odd = cb.query_cell();

            let mut branch_rlp_rlc = vec![0.expr(); 2];
            for is_s in [true, false] {
                // In C we have the key nibbles, we check below only for S.
                if is_s {
                    // RLP encoding checks: [key, branch]
                    // Verify that the lengths are consistent.
                    require!(config.rlp_key.rlp_list.len() => config.rlp_key.key_value.num_bytes() + rlp_value[is_s.idx()].num_bytes());
                }

                // Multiplier after list and key
                let mult = config.rlp_key.rlp_list.rlp_mult(&r) * key_items[true.idx()].mult();

                // Extension node RLC
                let node_rlc = (config.rlp_key.rlc(&r), mult.expr())
                    .rlc_chain(rlp_value[is_s.idx()].rlc_rlp());

                // The branch expected in the extension node
                branch_rlp_rlc[is_s.idx()] = rlp_value[is_s.idx()].rlc_content();

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

            // Calculate the number of bytes
            let key_len = config.rlp_key.key_value.len();
            // Calculate the number of nibbles
            let num_nibbles = num_nibbles::expr(key_len.expr(), config.is_key_part_odd.expr());
            // Make sure the nibble counter is updated correctly
            let num_nibbles = key_data.num_nibbles.expr() + num_nibbles.expr();

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
                    cb,
                    config.rlp_key.key_value.clone(),
                    key_data.mult.expr(),
                    config.is_key_part_odd.expr(),
                    not!(is_key_odd),
                    key_items
                        .iter()
                        .map(|item| item.bytes())
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                    &ctx.r,
                );

            // Get the length of the key
            // Unless both parts of the key are odd, subtract 1 from the key length.
            let key_len = config.rlp_key.key_value.len();
            let key_num_bytes_for_mult = key_len
                - ifx! {not!(key_data.is_odd.expr() * config.is_key_part_odd.expr()) => { 1.expr() }};
            // Get the multiplier for this key length
            config.mult_key = cb.query_cell();
            require!((FixedTableTag::RMult, key_num_bytes_for_mult, config.mult_key.expr()) => @"fixed");

            // Store the post ext state
            config.post_state = Some(ExtState {
                key_rlc,
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

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        _mpt_config: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        key_data: &KeyDataWitness<F>,
        key_rlc: &mut F,
        key_mult: &mut F,
        num_nibbles: &mut usize,
        is_key_odd: &mut bool,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let extension = &node.extension_branch.clone().unwrap().extension;

        // Data
        let key_items = [
            rlp_values[ExtensionBranchRowType::KeyS as usize].clone(),
            rlp_values[ExtensionBranchRowType::KeyC as usize].clone(),
        ];
        let _value_bytes = [
            rlp_values[ExtensionBranchRowType::ValueS as usize].clone(),
            rlp_values[ExtensionBranchRowType::ValueC as usize].clone(),
        ];

        let rlp_key = self.rlp_key.assign(
            region,
            offset,
            &extension.list_rlp_bytes,
            &key_items[true.idx()],
        )?;

        let first_key_byte = key_items[true.idx()].bytes[rlp_key.key_item.num_rlp_bytes()];
        // Compact encoding
        let is_key_part_odd = first_key_byte >> 4 == 1;
        if is_key_part_odd {
            assert!(first_key_byte < 0b10_0000);
        } else {
            assert!(first_key_byte == 0);
        }
        self.is_key_part_odd
            .assign(region, offset, is_key_part_odd.scalar())?;

        self.is_not_hashed.assign(
            region,
            offset,
            rlp_key.rlp_list.num_bytes().scalar(),
            HASH_WIDTH.scalar(),
        )?;

        let mut key_len_mult = rlp_key.key_item.len();
        if !(*is_key_odd && is_key_part_odd) {
            key_len_mult -= 1;
        }

        // Update number of nibbles
        *num_nibbles += num_nibbles::value(rlp_key.key_item.len(), is_key_part_odd);

        // Update parity
        *is_key_odd = if is_key_part_odd {
            !*is_key_odd
        } else {
            *is_key_odd
        };

        // Key RLC
        let (key_rlc_ext, _) = ext_key_rlc_calc_value(
            rlp_key.key_item,
            key_data.mult,
            is_key_part_odd,
            !*is_key_odd,
            key_items
                .iter()
                .map(|item| item.bytes.clone())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            pv.r,
        );
        *key_rlc = key_data.rlc + key_rlc_ext;

        // Key mult
        let mult_key = pow::value(pv.r, key_len_mult);
        self.mult_key.assign(region, offset, mult_key)?;
        *key_mult = key_data.mult * mult_key;

        Ok(())
    }
}

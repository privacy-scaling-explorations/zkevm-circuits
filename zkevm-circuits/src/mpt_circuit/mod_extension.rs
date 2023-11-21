use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::plonk::{Error, VirtualCells};

use super::{
    helpers::{ListKeyGadget, MPTConstraintBuilder, ListKeyWitness, KeyData, ext_key_rlc_calc_value},
    rlp_gadgets::{RLPItemWitness, get_ext_odd_nibble_value},
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion, cell_manager::Cell, constraint_builder::{RLCChainableRev, RLCChainable},
        gadgets::{LtGadget, IsZeroGadget},
    },
    mpt_circuit::{
        helpers::{
            Indexable, ParentData, KECCAK, parent_memory, FIXED, ext_key_rlc_value, key_memory, ext_key_rlc_expr,
        },
        RlpItemType, witness_row::StorageRowType, FixedTableTag, param::{HASH_WIDTH, KEY_PREFIX_EVEN, KEY_LEN_IN_NIBBLES},
    }, matchw,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct ModExtensionGadget<F> {
    rlp_key: [ListKeyGadget<F>; 2],
    is_not_hashed: [LtGadget<F, 2>; 2],
    is_short_branch: IsZeroGadget<F>,
    is_key_part_odd: [Cell<F>; 2], // Whether the number of nibbles is odd or not.
    mult_key: Cell<F>,
}

impl<F: Field> ModExtensionGadget<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        parent_data: &mut [ParentData<F>; 2],
        key_data: &mut [KeyData<F>; 2],
    ) -> Self {
        let mut config = ModExtensionGadget::default();

        circuit!([meta, cb], {
            let key_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeKey as usize,
                    RlpItemType::Key,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeKey as usize,
                    RlpItemType::Key,
                ),
            ];
            let key_nibbles = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeNibbles as usize,
                    RlpItemType::Nibbles,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeNibbles as usize,
                    RlpItemType::Nibbles,
                ),
            ];
            let rlp_value = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeValue as usize,
                    RlpItemType::Value,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeValue as usize,
                    RlpItemType::Value,
                ),
            ];

            let is_insert = parent_data[0].is_placeholder.expr(); // insert or delete

            let lo_s = is_insert.clone() * parent_data[0].hash.lo().expr() + (1.expr() - is_insert.clone()) * parent_data[1].hash.lo().expr();
            let hi_s = is_insert.clone() * parent_data[0].hash.hi().expr() + (1.expr() - is_insert.clone()) * parent_data[1].hash.hi().expr();
            let lo_c = is_insert.clone() * parent_data[0].drifted_parent_hash.lo().expr() + (1.expr() - is_insert.clone()) * parent_data[1].drifted_parent_hash.lo().expr();
            let hi_c = is_insert.clone() * parent_data[0].drifted_parent_hash.hi().expr() + (1.expr() - is_insert.clone()) * parent_data[1].drifted_parent_hash.hi().expr();
            let parent_data_lo = vec![lo_s, lo_c];
            let parent_data_hi = vec![hi_s, hi_c];
            let parent_data_rlc = is_insert.clone() * parent_data[0].rlc.expr() + (1.expr() - is_insert.clone()) * parent_data[1].rlc.expr();

            let key_rlc_before = key_data[0].rlc.expr() * is_insert.clone() + (1.expr() - is_insert.clone()) * key_data[1].rlc.expr();
            let key_mult_before = key_data[0].mult.expr() * is_insert.clone() + (1.expr() - is_insert.clone()) * key_data[1].mult.expr();
            let key_is_odd_before = key_data[0].is_odd.expr() * is_insert.clone() + (1.expr() - is_insert.clone()) * key_data[1].is_odd.expr();

            let middle_key_rlc = key_data[1].drifted_rlc.expr() * is_insert.clone() + (1.expr() - is_insert.clone()) * key_data[0].drifted_rlc.expr();
            let middle_key_mult = key_data[1].mult.expr() * is_insert.clone() + (1.expr() - is_insert.clone()) * key_data[0].mult.expr();
            let middle_key_is_odd = key_data[1].is_odd.expr() * is_insert.clone() + (1.expr() - is_insert.clone()) * key_data[0].is_odd.expr();

            config.rlp_key[0] = ListKeyGadget::construct(cb, &key_items[0]);
            config.rlp_key[1] = ListKeyGadget::construct(cb, &key_items[1]);
 
            let mut key_rlc = vec![];
            for is_s in [true, false] {
                config.is_key_part_odd[is_s.idx()] = cb.query_cell();

                let items = vec![key_items[is_s.idx()].clone(), key_nibbles[is_s.idx()].clone()];
                let rlc = ext_key_rlc_expr(
                        cb,
                        config.rlp_key[is_s.idx()].key_value.clone(),
                        1.expr(),
                        config.is_key_part_odd[is_s.idx()].expr(),
                        false.expr(),
                        items
                            .iter()
                            .map(|item| item.bytes_be())
                            .collect::<Vec<_>>()
                            .try_into()
                            .unwrap(),
                        &cb.key_r.expr(),
                    );
                key_rlc.push(rlc);
            }

            config.is_short_branch = IsZeroGadget::construct(
                &mut cb.base,
                key_rlc[0].expr() - key_rlc[1].expr(),
            );

            for is_s in [true, false] {
                let first_byte = matchx! {(
                    key_items[is_s.idx()].is_short() => key_items[is_s.idx()].bytes_be()[0].expr(),
                    key_items[is_s.idx()].is_long() => key_items[is_s.idx()].bytes_be()[1].expr(),
                    key_items[is_s.idx()].is_very_long() => key_items[is_s.idx()].bytes_be()[2].expr(),
                )};
                require!((FixedTableTag::ExtOddKey.expr(),
                    first_byte, config.is_key_part_odd[is_s.idx()].expr()) =>> @FIXED);
                
                // RLP encoding checks: [key, branch]
                // Verify that the lengths are consistent.
                require!(config.rlp_key[is_s.idx()].rlp_list.len() => config.rlp_key[is_s.idx()].key_value.num_bytes() + rlp_value[is_s.idx()].num_bytes());

                config.is_not_hashed[is_s.idx()] = LtGadget::construct(
                    &mut cb.base,
                    config.rlp_key[is_s.idx()].rlp_list.num_bytes(),
                    HASH_WIDTH.expr(),
                );

                // Extension node RLC
                let node_rlc = config
                    .rlp_key[is_s.idx()]
                    .rlc2(&cb.keccak_r)
                    .rlc_chain_rev(rlp_value[is_s.idx()].rlc_chain_data());

                let (rlc, num_bytes, is_not_hashed) =  
                    (
                        node_rlc.expr(),
                        config.rlp_key[is_s.idx()].rlp_list.num_bytes(),
                        config.is_not_hashed[is_s.idx()].expr(),
                    );
 
                ifx! {config.is_short_branch => {
                    if is_s {
                        ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                            require!((1.expr(), rlc.expr(), num_bytes.expr(), parent_data_lo[is_s.idx()].clone(), parent_data_hi[is_s.idx()].clone()) =>> @KECCAK);
                        } elsex {
                            require!(rlc => parent_data_rlc);
                        }}
                    } else {
                        ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                            let branch_rlp_word = rlp_value[1].word();
                            require!(branch_rlp_word.lo() => parent_data_lo[1]);
                            require!(branch_rlp_word.hi() => parent_data_hi[1]);
                        } elsex {
                            require!(rlp_value[1].rlc_rlp() => parent_data_rlc);
                        }}
                    }
                } elsex {
                    ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                        // Hashed branch hash in long extension is in parent branch
                        require!((1.expr(), rlc.expr(), num_bytes.expr(), parent_data_lo[is_s.idx()].clone(), parent_data_hi[is_s.idx()].clone()) =>> @KECCAK);
                    } elsex {
                        // Non-hashed branch hash in parent branch
                        require!(rlc => parent_data_rlc);
                    }} 
                }} 
            }

            let data0 = [key_items[0].clone(), key_nibbles[0].clone()];
            let nibbles_rlc_long = key_rlc_before
                + ext_key_rlc_expr(
                    cb,
                    config.rlp_key[0].key_value.clone(),
                    key_mult_before,
                    config.is_key_part_odd[0].expr(),
                    key_is_odd_before,
                    data0
                        .iter()
                        .map(|item| item.bytes_be())
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                    &cb.key_r.expr(),
                );

            let data1 = [key_items[1].clone(), key_nibbles[1].clone()];
            let rlc_after_short = middle_key_rlc.clone() + ext_key_rlc_expr(
                cb,
                config.rlp_key[1].key_value.clone(),
                middle_key_mult,
                config.is_key_part_odd[1].expr(),
                middle_key_is_odd,
                data1
                    .iter()
                    .map(|item| item.bytes_be())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
                &cb.key_r.expr(),
            );

            ifx! {config.is_short_branch => {
                require!(middle_key_rlc => nibbles_rlc_long);
            } elsex {
                require!(rlc_after_short => nibbles_rlc_long);
            }}
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        rlp_values: &[RLPItemWitness],
        list_rlp_bytes: [&[u8]; 2],
    ) -> Result<(), Error> {
        let key_items = [
            rlp_values[StorageRowType::LongExtNodeKey as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeKey as usize].clone(),
        ];

        let mut rlp_key = vec![ListKeyWitness::default(); 2];
        let mut key_rlc = vec![];

        let items_s = [
            rlp_values[StorageRowType::LongExtNodeKey as usize].clone(),
            rlp_values[StorageRowType::LongExtNodeNibbles as usize].clone(),
        ];
        let items_c = [
            rlp_values[StorageRowType::ShortExtNodeKey as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeNibbles as usize].clone(),
        ];
        let items = vec![items_s, items_c];

        for is_s in [true, false] {
            rlp_key[is_s.idx()] = self.rlp_key[is_s.idx()].assign(
                region,
                offset,
                &list_rlp_bytes[is_s.idx()],
                &key_items[is_s.idx()],
            )?;

            let first_key_byte =
                key_items[is_s.idx()].bytes[rlp_key[is_s.idx()].key_item.num_rlp_bytes()];

            let is_key_part_odd = first_key_byte >> 4 == 1;
            if is_key_part_odd {
                assert!(first_key_byte < 0b10_0000);
            } else {
                assert!(first_key_byte == 0);
            }

            self.is_key_part_odd[is_s.idx()]
            .assign(region, offset, is_key_part_odd.scalar())?;

            self.is_not_hashed[is_s.idx()].assign(
                region,
                offset,
                rlp_key[is_s.idx()].rlp_list.num_bytes().scalar(),
                HASH_WIDTH.scalar(),
            )?; 

            let (key_rlc_ext, _) = ext_key_rlc_calc_value(
                rlp_key[is_s.idx()].key_item.clone(),
                1.scalar(),
                is_key_part_odd,
                false,
                items[is_s.idx()]
                    .iter()
                    .map(|item| item.bytes.clone())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
                region.key_r,
            );

            key_rlc.push(key_rlc_ext);
        }

        self.is_short_branch.assign(
            region,
            offset,
            key_rlc[0] - key_rlc[1],
        )?;

        Ok(())
    }
}
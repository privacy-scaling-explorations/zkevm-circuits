use std::f32::consts::E;

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
        gadgets::LtGadget,
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
                    RlpItemType::Node,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeValue as usize,
                    RlpItemType::Node,
                ),
            ];

            for is_s in [true, false] {
                config.rlp_key[is_s.idx()] = ListKeyGadget::construct(cb, &key_items[is_s.idx()]);
                config.is_key_part_odd[is_s.idx()] = cb.query_cell();

                let first_byte = matchx! {
                    key_items[is_s.idx()].is_short() => key_items[is_s.idx()].bytes_be()[0].expr(),
                    key_items[is_s.idx()].is_long() => key_items[is_s.idx()].bytes_be()[1].expr(),
                    key_items[is_s.idx()].is_very_long() => key_items[is_s.idx()].bytes_be()[2].expr(),
                };
                require!((FixedTableTag::ExtOddKey.expr(),
                    first_byte, config.is_key_part_odd[is_s.idx()].expr()) => @FIXED);
                
                // RLP encoding checks: [key, branch]
                // Verify that the lengths are consistent.
                require!(config.rlp_key[is_s.idx()].rlp_list.len() => config.rlp_key[is_s.idx()].key_value.num_bytes() + rlp_value[is_s.idx()].num_bytes());

                // Extension node RLC
                let node_rlc = config
                    .rlp_key[is_s.idx()]
                    .rlc2(&cb.keccak_r)
                    .rlc_chain_rev(rlp_value[is_s.idx()].rlc_chain_data());

                config.is_not_hashed[is_s.idx()] = LtGadget::construct(
                    &mut cb.base,
                    config.rlp_key[is_s.idx()].rlp_list.num_bytes(),
                    HASH_WIDTH.expr(),
                );

                let (rlc, num_bytes, is_not_hashed) =  
                    (
                        node_rlc.expr(),
                        config.rlp_key[is_s.idx()].rlp_list.num_bytes(),
                        config.is_not_hashed[is_s.idx()].expr(),
                    );
 
                if is_s {
                    ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                        // Hashed branch hash in parent branch
                        require!(vec![1.expr(), rlc.expr(), num_bytes.expr(), parent_data[is_s.idx()].hash.lo().expr(), parent_data[is_s.idx()].hash.hi().expr()] => @KECCAK);
                    } elsex {
                        // Non-hashed branch hash in parent branch
                        require!(rlc => parent_data[is_s.idx()].rlc);
                    }} 
                } else {
                    ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(is_not_hashed)]) => {
                        // Hashed branch hash in parent branch
                        require!(vec![1.expr(), rlc.expr(), num_bytes.expr(), parent_data[is_s.idx()].drifted_parent_hash.lo().expr(), parent_data[is_s.idx()].drifted_parent_hash.hi().expr()] => @KECCAK);
                    } elsex {
                        // Non-hashed branch hash in parent branch
                        require!(rlc => parent_data[is_s.idx()].rlc);
                    }}
                }
            }

            // TODO: inverse operation (delete)
            (*key_data)[0] = KeyData::load(cb, &ctx.memory[key_memory(true)], 0.expr());

            let nibbles_rlc_long = ext_key_rlc_expr(
                cb,
                config.rlp_key[0].key_value.clone(),
                1.expr(),
                config.is_key_part_odd[0].expr(),
                // Always false because we calculate the RLC of nibbles only (we ignore the key nibbles above the extension):
                false.expr(),
                key_items
                    .iter()
                    .map(|item| item.bytes_be())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
                &cb.key_r.expr(),
            );

            let data = [key_items[1].clone(), key_nibbles[1].clone()];

            let nibbles_rlc_short = ext_key_rlc_expr(
                cb,
                config.rlp_key[1].key_value.clone(),
                1.expr(),
                config.is_key_part_odd[1].expr(),
                // Taking into account the nibbles and the drifted_index:
                not!(config.is_key_part_odd[0]),
                data
                    .iter()
                    .map(|item| item.bytes_be())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
                &cb.key_r.expr(),
            );

            let mult = key_data[0].drifted_mult.expr();
            ifx! {config.is_key_part_odd[0] => {
                let r = cb.key_r.clone();
                let rlc1 = (key_data[0].nibbles_rlc.expr(), mult.clone()).rlc_chain(key_data[0].drifted_index.expr());
                let rlc = (rlc1, mult.clone() * r).rlc_chain(nibbles_rlc_short.clone());

                require!(nibbles_rlc_long => rlc);
            } elsex {
                let rlc2 = key_data[0].drifted_index.expr() * 16.expr() + nibbles_rlc_short; 
                let rlc = (key_data[0].nibbles_rlc.expr(), mult).rlc_chain(rlc2);

                require!(nibbles_rlc_long => rlc);
            }}


            // require!(nibbles_rlc_long => d);
            // require!(debug_check => key_data[0].nibbles_rlc);
            // require!(debug_check1 => d);
 
            /*
            let r = cb.key_r.clone();
            let debug_check = (1.expr() * 16.expr() + 2.expr()) + (3.expr() * 16.expr() + 4.expr()) * r.clone();
            let debug_check1 = (1.expr() * 16.expr() + 2.expr()) + (3.expr() * 16.expr() + 4.expr()) * r.clone()
                + (5.expr() * 16.expr() + 6.expr()) * r.clone() * r.clone();
            require!(debug_check => key_data[0].nibbles_rlc);
            require!(debug_check1 => nibbles_rlc_long);

            require!(config.is_key_part_odd[1] => true.expr());
            require!(config.rlp_key[1].key_value.num_bytes() => 1.expr());

            require!(5.expr() => key_data[0].drifted_index);
            */

            // TODO:
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        rlp_values: &[RLPItemWitness],
        list_rlp_bytes: [Vec<u8>; 2],
    ) -> Result<(), Error> {
        let key_items = [
            rlp_values[StorageRowType::LongExtNodeKey as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeKey as usize].clone(),
        ];
        let key_nibbles = [
            rlp_values[StorageRowType::LongExtNodeNibbles as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeNibbles as usize].clone(),
        ];
        let value_bytes = [
            rlp_values[StorageRowType::LongExtNodeValue as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeValue as usize].clone(),
        ];

        let mut rlp_key = vec![ListKeyWitness::default(); 2];

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

            // Debugging:
            /*
            if !is_s {
                let data = [key_items[1].clone(), key_nibbles[1].clone()];
                let (nibbles_rlc, _) = ext_key_rlc_calc_value(
                    rlp_key[is_s.idx()].key_item.clone(),
                    F::ONE,
                    is_key_part_odd,
                    false,
                    data
                        .iter()
                        .map(|item| item.bytes.clone())
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                    region.key_r,
                );

                println!("{:?}", nibbles_rlc);
                println!("{:?}", F::from(16*6));
                println!("=====");
            }
            */
        }
        
        // TODO

        Ok(())
    }
}

use eth_types::Field;
use gadgets::util::{pow, Scalar};
use halo2_proofs::plonk::{Error, Expression, VirtualCells};

use super::{
    helpers::{KeyDataWitness, ListKeyGadget, MPTConstraintBuilder},
    rlp_gadgets::RLPItemWitness,
    witness_row::{ExtensionBranchRowType, Node},
    MPTContext,
};
use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion, cell_manager::Cell, constraint_builder::RLCChainableRev,
        gadgets::LtGadget,
    },
    mpt_circuit::{
        helpers::{
            ext_key_rlc_calc_value, ext_key_rlc_expr, num_nibbles, Indexable, KeyData, MptCellType,
            ParentData, FIXED, KECCAK, MULT, parent_memory,
        },
        param::HASH_WIDTH,
        FixedTableTag, MPTConfig, MPTState, RlpItemType, witness_row::StorageRowType,
    },
    util::word::Word,
};

#[derive(Clone, Debug)]
pub(crate) struct ExtState<F> {
    pub(crate) key_rlc: Expression<F>,
    pub(crate) key_mult: Expression<F>,
    pub(crate) num_nibbles: Expression<F>,
    pub(crate) is_key_odd: Expression<F>,

    pub(crate) branch_rlp_word: [Word<Expression<F>>; 2],
    pub(crate) branch_rlp_rlc: [Expression<F>; 2],
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ModExtensionGadget<F> {
    rlp_key: [ListKeyGadget<F>; 2],
    is_not_hashed: LtGadget<F, 2>,
    is_key_part_odd: Cell<F>,
    mult_key: Cell<F>,
}

impl<F: Field> ModExtensionGadget<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        parent_data: &mut [ParentData<F>; 2],
    ) -> Self {
        let mut config = ModExtensionGadget::default();

        circuit!([meta, cb], {
            // Data
            let key_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeKey as usize,
                    RlpItemType::Key,
                ),/*
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeKey as usize,
                    RlpItemType::Nibbles,
                ),
                */
            ];
            let rlp_value = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeValue as usize,
                    RlpItemType::Node,
                )/*,
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ShortExtNodeKey as usize,
                    RlpItemType::Node,
                ),
                */
            ];

            config.rlp_key[0] = ListKeyGadget::construct(cb, &key_items[0]);
            /*
            config.is_key_part_odd = cb.query_cell();
            let first_byte = matchx! {
                key_items[true.idx()].is_short() => key_items[true.idx()].bytes_be()[0].expr(),
                key_items[true.idx()].is_long() => key_items[true.idx()].bytes_be()[1].expr(),
                key_items[true.idx()].is_very_long() => key_items[true.idx()].bytes_be()[2].expr(),
            };
            require!((FixedTableTag::ExtOddKey.expr(), first_byte, config.is_key_part_odd.expr()) => @FIXED);
            */

            let long_mod_ext_rlc = config
                .rlp_key[0]
                .rlc2(&cb.keccak_r)
                .rlc_chain_rev(rlp_value[0].rlc_chain_data());
        
            let long_mod_ext_num_bytes = config.rlp_key[0].rlp_list.num_bytes();

            let is_s = true;
            let parent_data = &mut parent_data[is_s.idx()];
            *parent_data =
                ParentData::load("leaf load", cb, &ctx.memory[parent_memory(is_s)], 0.expr());

            require!(vec![1.expr(), long_mod_ext_rlc.expr(), long_mod_ext_num_bytes.expr(), parent_data.hash.lo().expr(), parent_data.hash.hi().expr()] => @KECCAK);


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
        let mod_ext_key_items = [
            rlp_values[StorageRowType::LongExtNodeKey as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeKey as usize].clone(),
        ];
        let mod_ext_value_bytes = [
            rlp_values[StorageRowType::LongExtNodeValue as usize].clone(),
            rlp_values[StorageRowType::ShortExtNodeValue as usize].clone(),
        ];

        self.rlp_key[0].assign(
            region,
            offset,
            &list_rlp_bytes[true.idx()],
            &mod_ext_key_items[true.idx()],
        )?;

        // TODO

        Ok(())
    }
}

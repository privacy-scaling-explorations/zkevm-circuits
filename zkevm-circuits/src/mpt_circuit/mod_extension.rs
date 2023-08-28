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
            ParentData, FIXED, KECCAK, MULT,
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
    rlp_key: ListKeyGadget<F>,
    is_not_hashed: LtGadget<F, 2>,
    is_key_part_odd: Cell<F>,
    mult_key: Cell<F>,
}

impl<F: Field> ModExtensionGadget<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let mut config = ModExtensionGadget::default();

        circuit!([meta, cb], {
            // Data
            let key_items = [
                // Special case, requring string fail tests
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::LongExtNodeKey as usize,
                    RlpItemType::Key,
                )/*,
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

            // config.rlp_key = ListKeyGadget::construct(cb, &key_items[0]);
            /*
            config.is_key_part_odd = cb.query_cell();
            let first_byte = matchx! {
                key_items[true.idx()].is_short() => key_items[true.idx()].bytes_be()[0].expr(),
                key_items[true.idx()].is_long() => key_items[true.idx()].bytes_be()[1].expr(),
                key_items[true.idx()].is_very_long() => key_items[true.idx()].bytes_be()[2].expr(),
            };
            require!((FixedTableTag::ExtOddKey.expr(), first_byte, config.is_key_part_odd.expr()) => @FIXED);
            */

            // TODO:
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        _mpt_config: &MPTConfig<F>,
        _pv: &mut MPTState<F>,
        offset: usize,
    ) -> Result<(), Error> {
        // TODO

        Ok(())
    }
}

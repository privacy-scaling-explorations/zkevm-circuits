use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

use crate::circuit_tools::constraint_builder::{RLCChainable, RLCableValue};
use crate::circuit_tools::gadgets::LtGadget;
use crate::mpt_circuit::helpers::IsEmptyTreeGadget;
use crate::table::ProofType;
use crate::{
    assign, circuit,
    mpt_circuit::{
        helpers::{key_memory, parent_memory, KeyData, MPTConstraintBuilder, ParentData},
        param::{HASH_WIDTH, IS_STORAGE_MOD_POS, KEY_LEN_IN_NIBBLES},
        FixedTableTag,
    },
    mpt_circuit::{witness_row::MptWitnessRow, MPTContext},
    mpt_circuit::{MPTConfig, ProofValues},
};
use crate::{
    circuit_tools::cell_manager::Cell,
    mpt_circuit::helpers::{DriftedGadget, ParentDataWitness},
};

use super::{
    helpers::{Indexable, LeafKeyGadget, WrongGadget},
    param::IS_NON_EXISTING_STORAGE_POS,
    rlp_gadgets::RLPValueGadget,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct StorageLeafConfig<F> {
    key_data: [KeyData<F>; 2],
    parent_data: [ParentData<F>; 2],
    key_mult: [Cell<F>; 2],
    rlp_key: [LeafKeyGadget<F>; 2],
    rlp_value: [RLPValueGadget<F>; 2],
    wrong_rlp_key: LeafKeyGadget<F>,
    is_wrong_leaf: Cell<F>,
    is_not_hashed: [LtGadget<F, 1>; 2],
    is_empty_trie: [IsEmptyTreeGadget<F>; 2],
    drifted: DriftedGadget<F>,
    wrong: WrongGadget<F>,
}

impl<F: Field> StorageLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let r = ctx.r.clone();

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = StorageLeafConfig::default();

        circuit!([meta, cb.base], {
            let key_bytes = [
                ctx.expr(meta, 0)[..36].to_owned(),
                ctx.expr(meta, 2)[..36].to_owned(),
            ];
            let value_bytes = [ctx.expr(meta, 1), ctx.expr(meta, 3)];
            let drifted_bytes = ctx.expr(meta, 4)[..36].to_owned();
            let wrong_bytes = ctx.expr(meta, 5)[..36].to_owned();
            let lookup_offset = 3;
            let wrong_offset = 5;

            let mut key_rlc = vec![0.expr(); 2];
            let mut value_rlc = vec![0.expr(); 2];
            let mut value_rlp_rlc = vec![0.expr(); 2];
            for is_s in [true, false] {
                // Parent data
                let parent_data = &mut config.parent_data[is_s.idx()];
                *parent_data = ParentData::load(
                    "leaf load",
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    0.expr(),
                );
                // Key data
                let key_data = &mut config.key_data[is_s.idx()];
                *key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(is_s)], 0.expr());

                // Placeholder leaf checks
                config.is_empty_trie[is_s.idx()] =
                    IsEmptyTreeGadget::construct(&mut cb.base, parent_data.rlc.expr(), &r);
                let is_placeholder_leaf = config.is_empty_trie[is_s.idx()].expr();

                let rlp_key = &mut config.rlp_key[is_s.idx()];
                *rlp_key = LeafKeyGadget::construct(&mut cb.base, &key_bytes[is_s.idx()]);
                config.rlp_value[is_s.idx()] =
                    RLPValueGadget::construct(&mut cb.base, &value_bytes[is_s.idx()][0..36]);

                config.key_mult[is_s.idx()] = cb.base.query_cell();
                require!((FixedTableTag::RMult, rlp_key.num_bytes_on_key_row(), config.key_mult[is_s.idx()].expr()) => @"fixed");

                // RLC bytes zero check
                cb.set_length(rlp_key.num_bytes_on_key_row());
                cb.set_length_s(config.rlp_value[is_s.idx()].num_bytes());

                (value_rlc[is_s.idx()], value_rlp_rlc[is_s.idx()]) =
                    config.rlp_value[is_s.idx()].rlc(&r);

                let leaf_rlc = (rlp_key.rlc(&r), config.key_mult[is_s.idx()].expr())
                    .rlc_chain(value_rlp_rlc[is_s.idx()].expr());

                // Key
                key_rlc[is_s.idx()] = key_data.rlc.expr()
                    + rlp_key.leaf_key_rlc(
                        &mut cb.base,
                        key_data.mult.expr(),
                        key_data.is_odd.expr(),
                        1.expr(),
                        &r,
                    );
                // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES
                let num_nibbles = rlp_key.num_key_nibbles(key_data.is_odd.expr());
                require!(key_data.num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);

                // Placeholder leaves default to value `0`.
                ifx! {is_placeholder_leaf => {
                    require!(value_rlc[is_s.idx()] => 0);
                }}

                // Make sure the RLP encoding is correct.
                // storage = [key, value]
                require!(rlp_key.num_bytes() => rlp_key.num_bytes_on_key_row() + config.rlp_value[is_s.idx()].num_bytes());

                // Check if the account is in its parent.
                // Check is skipped for placeholder leafs which are dummy leafs
                ifx! {not!(is_placeholder_leaf) => {
                    config.is_not_hashed[is_s.idx()] = LtGadget::construct(&mut cb.base, rlp_key.num_bytes(), 32.expr());
                    ifx!{or::expr(&[parent_data.is_root.expr(), not!(config.is_not_hashed[is_s.idx()])]) => {
                        // Hashed branch hash in parent branch
                        require!((1, leaf_rlc, rlp_key.num_bytes(), parent_data.rlc) => @"keccak");
                    } elsex {
                        // Non-hashed branch hash in parent branch
                        require!(leaf_rlc => parent_data.rlc);
                    }}
                }}

                // Key done, set the default values
                KeyData::store(
                    &mut cb.base,
                    &ctx.memory[key_memory(is_s)],
                    KeyData::default_values(),
                );
                // Store the new parent
                ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [0.expr(), true.expr(), false.expr(), 0.expr()],
                );
            }

            // Drifted leaf handling
            config.drifted = DriftedGadget::construct(
                cb,
                &config.parent_data,
                &config.key_data,
                &key_rlc,
                &value_rlp_rlc,
                &drifted_bytes,
                &ctx.r,
            );

            // Wrong leaf handling
            let is_non_existing = a!(ctx.proof_type.is_non_existing_storage_proof, wrong_offset);
            config.wrong = WrongGadget::construct(
                meta,
                cb,
                ctx.clone(),
                is_non_existing,
                &config.rlp_key,
                &key_rlc,
                &wrong_bytes,
                wrong_offset,
                false,
                &ctx.r,
            );

            // Put the data in the lookup table
            require!(a!(ctx.mpt_table.key_rlc, lookup_offset) => key_rlc[false.idx()]);
            require!(a!(ctx.mpt_table.value_prev, lookup_offset) => value_rlc[true.idx()]);
            require!(a!(ctx.mpt_table.value, lookup_offset) => value_rlc[false.idx()]);
        });

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        ctx: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let base_offset = offset;

        let row_key = [&witness[offset + 0], &witness[offset + 2]];
        let value_bytes = [&witness[offset + 1], &witness[offset + 3]];
        let row_drifted = &witness[offset + 4];
        let row_wrong = &witness[offset + 5];
        let lookup_offset = offset + 3;
        let wrong_offset = offset + 5;

        let mut parent_data = vec![ParentDataWitness::default(); 2];
        let mut key_rlc = vec![0.scalar(); 2];
        let mut value_rlc = vec![0.scalar(); 2];
        for is_s in [true, false] {
            // Key
            let key_row = &row_key[is_s.idx()];

            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                base_offset,
                &mut pv.memory[parent_memory(is_s)],
                0,
            )?;

            let rlp_key_witness =
                self.rlp_key[is_s.idx()].assign(region, base_offset, &key_row.bytes)?;

            let (_, leaf_mult) = rlp_key_witness.rlc_leaf(ctx.r);
            self.key_mult[is_s.idx()].assign(region, base_offset, leaf_mult)?;

            self.is_not_hashed[is_s.idx()].assign(
                region,
                base_offset,
                rlp_key_witness.num_bytes().scalar(),
                32.scalar(),
            )?;

            let key_data = self.key_data[is_s.idx()].witness_load(
                region,
                base_offset,
                &mut pv.memory[key_memory(is_s)],
                0,
            )?;
            self.key_data[is_s.idx()].witness_store(
                region,
                base_offset,
                &mut pv.memory[key_memory(is_s)],
                F::zero(),
                F::one(),
                0,
                false,
                false,
                0,
                false,
                F::zero(),
                F::one(),
            )?;

            // Key
            (key_rlc[is_s.idx()], _) =
                rlp_key_witness.leaf_key_rlc(key_data.rlc, key_data.mult, ctx.r);

            // Value
            let value_row = &value_bytes[is_s.idx()];

            let value_witness =
                self.rlp_value[is_s.idx()].assign(region, base_offset, &value_row.bytes)?;

            value_rlc[is_s.idx()] = value_row.bytes
                [value_witness.num_rlp_bytes() as usize..HASH_WIDTH + 2]
                .rlc_value(ctx.r);

            self.parent_data[is_s.idx()].witness_store(
                region,
                base_offset,
                &mut pv.memory[parent_memory(is_s)],
                F::zero(),
                true,
                false,
                F::zero(),
            )?;

            self.is_empty_trie[is_s.idx()].assign(
                region,
                base_offset,
                parent_data[is_s.idx()].rlc,
                ctx.r,
            )?;
        }

        // Drifted leaf handling
        self.drifted
            .assign(region, base_offset, &parent_data, &row_drifted.bytes, ctx.r)?;

        // Wrong leaf handling
        let is_non_existing = row_wrong.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1;
        self.wrong.assign(
            region,
            base_offset,
            ctx,
            is_non_existing,
            &mut pv.memory,
            &key_rlc,
            &row_wrong.bytes,
            wrong_offset,
            row_key,
            false,
            ProofType::StorageDoesNotExist,
            ctx.r,
        )?;

        // Put the data in the lookup table
        if value_bytes[false.idx()].get_byte_rev(IS_STORAGE_MOD_POS) == 1 {
            assign!(region, (ctx.proof_type.proof_type, lookup_offset) => ProofType::StorageChanged.scalar())?;
        }
        assign!(region, (ctx.mpt_table.key_rlc, lookup_offset) => key_rlc[false.idx()])?;
        assign!(region, (ctx.mpt_table.value_prev, lookup_offset) => value_rlc[true.idx()])?;
        assign!(region, (ctx.mpt_table.value, lookup_offset) => value_rlc[false.idx()])?;

        Ok(())
    }
}

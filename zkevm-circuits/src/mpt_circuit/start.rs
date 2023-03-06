use super::helpers::Indexable;
use super::param::{
    IS_ACCOUNT_DELETE_MOD_POS, IS_BALANCE_MOD_POS, IS_CODEHASH_MOD_POS, IS_NONCE_MOD_POS,
    IS_NON_EXISTING_ACCOUNT_POS, IS_NON_EXISTING_STORAGE_POS, IS_STORAGE_MOD_POS,
};
use crate::circuit_tools::cell_manager::Cell;
use crate::circuit_tools::constraint_builder::{RLCable, RLCableValue};
use crate::mpt_circuit::helpers::{main_memory, MainData};
use crate::table::ProofType;
use crate::{
    assign, circuit,
    mpt_circuit::helpers::{key_memory, parent_memory, KeyData, MPTConstraintBuilder, ParentData},
    mpt_circuit::{witness_row::MptWitnessRow, MPTContext},
    mpt_circuit::{MPTConfig, ProofValues},
};
use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct StartConfig<F> {
    proof_type: Cell<F>,
}

impl<F: Field> StartConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let r = ctx.r.clone();

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = StartConfig::default();

        circuit!([meta, cb.base], {
            let root_bytes = [
                ctx.expr(meta, 0)[..32].to_owned(),
                ctx.expr(meta, 0)[34..66].to_owned(),
            ];

            config.proof_type = cb.base.query_cell();

            let mut root = vec![0.expr(); 2];
            for is_s in [true, false] {
                root[is_s.idx()] = root_bytes[is_s.idx()].rlc(&r);
            }

            MainData::store(
                &mut cb.base,
                &ctx.memory[main_memory()],
                [
                    config.proof_type.expr(),
                    false.expr(),
                    0.expr(),
                    root[true.idx()].expr(),
                    root[false.idx()].expr(),
                ],
            );

            for is_s in [true, false] {
                ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [
                        root[is_s.idx()].expr(),
                        true.expr(),
                        false.expr(),
                        root[is_s.idx()].expr(),
                    ],
                );
                KeyData::store(
                    &mut cb.base,
                    &ctx.memory[key_memory(is_s)],
                    KeyData::default_values_expr(),
                );
            }
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
        idx: usize,
    ) -> Result<(), Error> {
        let row = &witness[idx];

        let root_bytes = [row.s_root_bytes().to_owned(), row.c_root_bytes().to_owned()];
        let columns = [ctx.s_main.bytes.to_owned(), ctx.c_main.bytes.to_owned()];

        // TODO(Brecht): change witness and just get the proof type directly
        let mut i = 0;
        let mut proof_type = None;
        while proof_type.is_none() {
            let row = &witness[idx + i];
            if row.get_byte_rev(IS_STORAGE_MOD_POS) == 1 {
                proof_type = Some(ProofType::StorageChanged);
            }
            if row.get_byte_rev(IS_NONCE_MOD_POS) == 1 {
                proof_type = Some(ProofType::NonceChanged);
            }
            if row.get_byte_rev(IS_BALANCE_MOD_POS) == 1 {
                proof_type = Some(ProofType::BalanceChanged);
            }
            if row.get_byte_rev(IS_CODEHASH_MOD_POS) == 1 {
                proof_type = Some(ProofType::CodeHashExists);
            }
            if row.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) == 1 {
                proof_type = Some(ProofType::AccountDestructed);
            }
            if row.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) == 1 {
                proof_type = Some(ProofType::AccountDoesNotExist);
            }
            if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1 {
                proof_type = Some(ProofType::StorageDoesNotExist);
            }
            i += 1;
        }
        self.proof_type
            .assign(region, offset, proof_type.unwrap().scalar())?;

        let mut root = vec![0.scalar(); 2];
        for is_s in [true, false] {
            root[is_s.idx()] = root_bytes[is_s.idx()].rlc_value(ctx.r);
        }

        MainData::witness_store(
            region,
            offset,
            &mut pv.memory[main_memory()],
            proof_type.unwrap() as usize,
            false,
            0.scalar(),
            root[true.idx()],
            root[false.idx()],
        )?;

        for is_s in [true, false] {
            for (byte, column) in root_bytes[is_s.idx()].iter().zip(columns[is_s.idx()]) {
                assign!(region, (column, offset) => byte.scalar())?;
            }
            ParentData::witness_store(
                region,
                offset,
                &mut pv.memory[parent_memory(is_s)],
                root[is_s.idx()],
                true,
                false,
                root[is_s.idx()],
            )?;
            KeyData::witness_store(
                region,
                offset,
                &mut pv.memory[key_memory(is_s)],
                F::zero(),
                F::one(),
                0,
                false,
                F::zero(),
                F::one(),
            )?;
        }

        Ok(())
    }
}

use bus_mapping::precompile::PrecompileAuxData;
use eth_types::{evm_types::GasCost, word, Field, ToLittleEndian, U256};
use ethers_core::k256::elliptic_curve::PrimeField;
use gadgets::util::{and, not, or, select, sum, Expr};
use halo2_proofs::{circuit::Value, halo2curves::secp256k1::Fq, plonk::Error};

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            from_bytes,
            math_gadget::{IsEqualGadget, IsZeroGadget, IsZeroWordGadget, LtWordGadget},
            CachedRegion, Cell,
        },
    },
    table::CallContextFieldTag,
    util::word::{Word, WordCell, WordExpr},
    witness::{Block, Call, ExecStep, Transaction},
};

#[derive(Clone, Debug)]
pub struct EcrecoverGadget<F> {
    is_recovered: Cell<F>,
    recovered_addr: Cell<F>,

    fq_modulus: WordCell<F>,
    msg_hash: WordCell<F>,
    sig_r: WordCell<F>,
    sig_s: WordCell<F>,
    sig_v: WordCell<F>,

    sig_r_canonical: LtWordGadget<F>,
    sig_s_canonical: LtWordGadget<F>,
    is_zero_sig_r: IsZeroWordGadget<F, WordCell<F>>,
    is_zero_sig_s: IsZeroWordGadget<F, WordCell<F>>,

    is_zero_sig_v_hi: IsZeroGadget<F>,
    is_sig_v_27: IsEqualGadget<F>,
    is_sig_v_28: IsEqualGadget<F>,

    is_success: Cell<F>,
    callee_address: Cell<F>,
    caller_id: Cell<F>,
    // call_data_offset: Cell<F>,
    // call_data_length: Cell<F>,
    // return_data_offset: Cell<F>,
    // return_data_length: Cell<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for EcrecoverGadget<F> {
    const EXECUTION_STATE: ExecutionState = ExecutionState::PrecompileEcrecover;
    const NAME: &'static str = "ECRECOVER";

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let is_recovered = cb.query_bool();
        let recovered_addr = cb.query_cell();

        let fq_modulus = cb.query_word_unchecked();
        let msg_hash = cb.query_word_unchecked();
        let sig_r = cb.query_word_unchecked();
        let sig_s = cb.query_word_unchecked();
        let sig_v = cb.query_word_unchecked();

        // verify sig_r and sig_s
        // the range is 0 < sig_r/sig_s < Fq::MODULUS
        let sig_r_canonical = LtWordGadget::construct(cb, &sig_r.to_word(), &fq_modulus.to_word());
        let sig_s_canonical = LtWordGadget::construct(cb, &sig_s.to_word(), &fq_modulus.to_word());
        let is_zero_sig_r = IsZeroWordGadget::construct(cb, &sig_r);
        let is_zero_sig_s = IsZeroWordGadget::construct(cb, &sig_s);
        let is_valid_r_s = and::expr([
            sig_r_canonical.expr(),
            sig_s_canonical.expr(),
            not::expr(or::expr([is_zero_sig_r.expr(), is_zero_sig_s.expr()])),
        ]);

        // sig_v is valid if sig_v == 27 || sig_v == 28
        let is_zero_sig_v_hi = IsZeroGadget::construct(cb, sig_v.hi().expr());
        let is_sig_v_27 = IsEqualGadget::construct(cb, sig_v.lo().expr(), 27.expr());
        let is_sig_v_28 = IsEqualGadget::construct(cb, sig_v.lo().expr(), 28.expr());
        let is_valid_sig_v = and::expr([
            or::expr([is_sig_v_27.expr(), is_sig_v_28.expr()]),
            is_zero_sig_v_hi.expr(),
        ]);

        let [is_success, callee_address, caller_id] = [
            CallContextFieldTag::IsSuccess,
            CallContextFieldTag::CalleeAddress,
            CallContextFieldTag::CallerId,
        ]
        .map(|tag| cb.call_context(None, tag));

        for (field_tag, value) in [
            (CallContextFieldTag::CallDataOffset, 0.expr()),
            (CallContextFieldTag::CallDataLength, 128.expr()),
            (CallContextFieldTag::ReturnDataOffset, 128.expr()),
            (
                CallContextFieldTag::ReturnDataLength,
                select::expr(is_success.expr(), 32.expr(), 0.expr()),
            ),
        ] {
            cb.call_context_lookup_read(None, field_tag, Word::from_lo_unchecked(value));
        }

        let gas_cost = select::expr(
            is_success.expr(),
            GasCost::PRECOMPILE_ECRECOVER_BASE.expr(),
            cb.curr.state.gas_left.expr(),
        );

        // lookup to the sign_verify table:
        let is_valid_sig = and::expr([is_valid_r_s.expr(), is_valid_sig_v.expr()]);
        cb.condition(is_valid_sig.expr(), |cb| {
            cb.sig_table_lookup(
                msg_hash.to_word(),
                sig_v.limbs[0].expr() - 27.expr(),
                sig_r.to_word(),
                sig_s.to_word(),
                select::expr(is_recovered.expr(), recovered_addr.expr(), 0.expr()),
                is_recovered.expr(),
            );
        });
        cb.condition(not::expr(is_valid_sig.expr()), |cb| {
            cb.require_zero(
                "is_recovered == false if r, s or v not canonical",
                is_recovered.expr(),
            );
        });

        cb.condition(not::expr(is_recovered.expr()), |cb| {
            cb.require_zero(
                "address == 0 if address could not be recovered",
                recovered_addr.expr(),
            );
        });

        cb.precompile_info_lookup(
            cb.execution_state().as_u64().expr(),
            callee_address.expr(),
            cb.execution_state().precompile_base_gas_cost().expr(),
        );

        let restore_context = RestoreContextGadget::construct2(
            cb,
            is_success.expr(),
            gas_cost.expr(),
            0.expr(),
            0.expr(),
            select::expr(is_success.expr(), 32.expr(), 0.expr()),
            0.expr(),
            0.expr(),
        );

        Self {
            is_recovered,
            recovered_addr,
            fq_modulus,

            msg_hash,
            sig_r,
            sig_s,
            sig_v,

            sig_r_canonical,
            sig_s_canonical,
            is_zero_sig_v_hi,
            is_zero_sig_r,
            is_zero_sig_s,
            is_sig_v_27,
            is_sig_v_28,

            is_success,
            callee_address,
            caller_id,
            // call_data_offset,
            // call_data_length,
            // return_data_offset,
            // return_data_length,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        if let Some(PrecompileAuxData::Ecrecover(aux_data)) = &step.aux_data {
            let recovered = !aux_data.recovered_addr.is_zero();
            self.is_recovered
                .assign(region, offset, Value::known(F::from(recovered as u64)))?;
            let mut recovered_addr = aux_data.recovered_addr.to_fixed_bytes();
            recovered_addr.reverse();
            self.recovered_addr.assign(
                region,
                offset,
                Value::known(from_bytes::value(&recovered_addr)),
            )?;

            let sig_r = U256::from(aux_data.sig_r.to_le_bytes());
            let sig_s = U256::from(aux_data.sig_s.to_le_bytes());
            let msg_hash = U256::from(aux_data.msg_hash.to_le_bytes());
            self.msg_hash.assign_u256(region, offset, msg_hash)?;
            self.sig_v.assign_u256(region, offset, aux_data.sig_v)?;
            self.sig_r.assign_u256(region, offset, sig_r)?;
            self.sig_s.assign_u256(region, offset, sig_s)?;

            self.fq_modulus
                .assign_u256(region, offset, word!(Fq::MODULUS))?;

            self.sig_r_canonical
                .assign(region, offset, sig_r, word!(Fq::MODULUS))?;
            self.sig_s_canonical
                .assign(region, offset, sig_s, word!(Fq::MODULUS))?;
            self.is_zero_sig_r.assign_u256(region, offset, sig_r)?;
            self.is_zero_sig_s.assign_u256(region, offset, sig_s)?;

            self.is_zero_sig_v_hi.assign(
                region,
                offset,
                from_bytes::value(&aux_data.sig_v.to_le_bytes()[16..31]),
            )?;
            self.is_sig_v_27.assign(
                region,
                offset,
                F::from(aux_data.sig_v.to_le_bytes()[0] as u64),
                F::from(27),
            )?;
            self.is_sig_v_28.assign(
                region,
                offset,
                F::from(aux_data.sig_v.to_le_bytes()[0] as u64),
                F::from(28),
            )?;
        }

        self.is_success.assign(
            region,
            offset,
            Value::known(F::from(u64::from(call.is_success))),
        )?;

        self.callee_address.assign(
            region,
            offset,
            Value::known(from_bytes::value(
                &call.address.to_low_u64_be().to_le_bytes(),
            )),
        )?;
        self.caller_id
            .assign(region, offset, Value::known(F::from(call.caller_id as u64)))?;
        // self.call_data_offset.assign(
        //     region,
        //     offset,
        //     Value::known(F::from(call.call_data_offset)),
        // )?;
        // self.call_data_length.assign(
        //     region,
        //     offset,
        //     Value::known(F::from(call.call_data_length)),
        // )?;
        // self.return_data_offset.assign(
        //     region,
        //     offset,
        //     Value::known(F::from(call.return_data_offset)),
        // )?;
        // self.return_data_length.assign(
        //     region,
        //     offset,
        //     Value::known(F::from(call.return_data_length)),
        // )?;
        self.restore_context
            .assign(region, offset, block, call, step, 7)
    }
}

#[cfg(test)]
mod test {
    use bus_mapping::{
        evm::{OpcodeId, PrecompileCallArgs},
        precompile::PrecompileCalls,
    };
    use eth_types::{bytecode, word, ToWord};
    use mock::TestContext;
    // use rayon::{iter::ParallelIterator, prelude::IntoParallelRefIterator};

    use crate::test_util::CircuitTestBuilder;

    lazy_static::lazy_static! {
        static ref TEST_VECTOR: Vec<PrecompileCallArgs> = {
            vec![
                // PrecompileCallArgs {
                //     name: "ecrecover (padded bytes, addr recovered)",
                //     setup_code: bytecode! {
                //         // msg hash from 0x00
                //         PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                //         PUSH1(0x00)
                //         MSTORE
                //         // signature v from 0x20
                //         PUSH1(28)
                //         PUSH1(0x20)
                //         MSTORE
                //         // signature r from 0x40
                //         PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                //         PUSH1(0x40)
                //         MSTORE
                //         // signature s from 0x60
                //         PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                //         PUSH1(0x60)
                //         MSTORE
                //     },
                //     // copy 101 bytes from memory addr 0. This should be sufficient to recover an
                //     // address, but the signature is invalid (ecrecover does not care about this
                //     // though)
                //     call_data_offset: 0x00.into(),
                //     call_data_length: 0x65.into(),
                //     // return 32 bytes and write from memory addr 128
                //     ret_offset: 0x80.into(),
                //     ret_size: 0x20.into(),
                //     address: PrecompileCalls::Ecrecover.address().to_word(),
                //     ..Default::default()
                // },
                PrecompileCallArgs {
                    name: "ecrecover (valid sig, addr recovered)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(28)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    // copy 128 bytes from memory addr 0. Address is recovered and the signature is
                    // valid.
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    // return 32 bytes and write from memory addr 128
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                /*
                PrecompileCallArgs {
                    name: "ecrecover (valid sig, addr recovered, extra input bytes)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(28)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    // copy 133 bytes from memory addr 0. Address is recovered and the signature is
                    // valid. The 5 bytes after the first 128 bytes are ignored.
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x85.into(),
                    // return 32 bytes and write from memory addr 128
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (overflowing msg_hash)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(28)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (overflowing sig_r)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(28)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (overflowing sig_s)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(28)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (invalid v > 28, single byte)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(29)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (invalid v < 27, single byte)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(26)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (invalid v, multi-byte, last byte == 28)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20, 1c == 28 (but not single byte)
                        PUSH32(word!("0x010000000000000000000000000000000000000000000000000000000000001c"))
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                PrecompileCallArgs {
                    name: "ecrecover (v == 1)",
                    setup_code: bytecode! {
                        // msg hash from 0x00
                        PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                        PUSH1(0x00)
                        MSTORE
                        // signature v from 0x20
                        PUSH1(0x01)
                        PUSH1(0x20)
                        MSTORE
                        // signature r from 0x40
                        PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                        PUSH1(0x40)
                        MSTORE
                        // signature s from 0x60
                        PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                        PUSH1(0x60)
                        MSTORE
                    },
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x80.into(),
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
                */
            ]
        };
    }

    lazy_static::lazy_static! {
        static ref OOG_TEST_VECTOR: Vec<PrecompileCallArgs> = {
            vec![PrecompileCallArgs {
                name: "ecrecover (oog)",
                setup_code: bytecode! {
                    // msg hash from 0x00
                    PUSH32(word!("0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"))
                    PUSH1(0x00)
                    MSTORE
                    // signature v from 0x20
                    PUSH1(28)
                    PUSH1(0x20)
                    MSTORE
                    // signature r from 0x40
                    PUSH32(word!("0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"))
                    PUSH1(0x40)
                    MSTORE
                    // signature s from 0x60
                    PUSH32(word!("0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"))
                    PUSH1(0x60)
                    MSTORE
                },
                // copy 128 bytes from memory addr 0. Address is recovered and the signature is
                // valid.
                call_data_offset: 0x00.into(),
                call_data_length: 0x80.into(),
                // return 32 bytes and write from memory addr 128
                ret_offset: 0x80.into(),
                ret_size: 0x20.into(),
                gas: 0.into(),
                value: 2.into(),
                address: PrecompileCalls::Ecrecover.address().to_word(),
                ..Default::default()
            }]
        };
    }

    #[test]
    fn precompile_ecrecover_test() {
        let call_kinds = vec![
            OpcodeId::CALL,
            // OpcodeId::STATICCALL,
            // OpcodeId::DELEGATECALL,
            // OpcodeId::CALLCODE,
        ];

        TEST_VECTOR.iter().for_each(|test_vector| {
            for &call_kind in &call_kinds {
                let bytecode = test_vector.with_call_op(call_kind);

                CircuitTestBuilder::new_from_test_ctx(
                    TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                )
                .run();
            }
        });
    }

    #[test]
    fn precompile_ecrecover_oog_test() {
        let call_kinds = vec![
            OpcodeId::CALL,
            OpcodeId::STATICCALL,
            OpcodeId::DELEGATECALL,
            OpcodeId::CALLCODE,
        ];

        OOG_TEST_VECTOR.iter().for_each(|test_vector| {
            for &call_kind in &call_kinds {
                let bytecode = test_vector.with_call_op(call_kind);

                CircuitTestBuilder::new_from_test_ctx(
                    TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                )
                .run();
            }
        })
    }
}

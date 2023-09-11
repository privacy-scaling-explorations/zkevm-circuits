use bus_mapping::precompile::PrecompileAuxData;
use eth_types::{evm_types::GasCost, word, Field, ToLittleEndian, ToScalar, U256};
use gadgets::util::{and, not, select, Expr};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_WORD},
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            from_bytes,
            math_gadget::{LtWordGadget, ModGadget},
            rlc, CachedRegion, Cell, RandomLinearCombination, Word,
        },
    },
    table::CallContextFieldTag,
    witness::{Block, Call, ExecStep, Transaction},
};

lazy_static::lazy_static! {
    static ref FQ_MODULUS: U256 = {
        word!("0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141")
    };
}

#[derive(Clone, Debug)]
pub struct EcrecoverGadget<F> {
    recovered: Cell<F>,
    msg_hash_keccak_rlc: Cell<F>,
    sig_v_keccak_rlc: Cell<F>,
    sig_r_keccak_rlc: Cell<F>,
    sig_s_keccak_rlc: Cell<F>,
    recovered_addr_keccak_rlc: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,

    msg_hash_raw: Word<F>,
    msg_hash: Word<F>,
    fq_modulus: Word<F>,
    msg_hash_mod: ModGadget<F, true>,

    sig_r: Word<F>,
    sig_r_canonical: LtWordGadget<F>,
    sig_s: Word<F>,
    sig_s_canonical: LtWordGadget<F>,

    is_success: Cell<F>,
    callee_address: Cell<F>,
    caller_id: Cell<F>,
    call_data_offset: Cell<F>,
    call_data_length: Cell<F>,
    return_data_offset: Cell<F>,
    return_data_length: Cell<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for EcrecoverGadget<F> {
    const EXECUTION_STATE: ExecutionState = ExecutionState::PrecompileEcrecover;

    const NAME: &'static str = "ECRECOVER";

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let (
            recovered,
            msg_hash_keccak_rlc,
            sig_v_keccak_rlc,
            sig_r_keccak_rlc,
            sig_s_keccak_rlc,
            recovered_addr_keccak_rlc,
        ) = (
            cb.query_bool(),
            cb.query_cell_phase2(),
            cb.query_cell_phase2(),
            cb.query_cell_phase2(),
            cb.query_cell_phase2(),
            cb.query_keccak_rlc(),
        );

        let msg_hash_raw = cb.query_word_rlc();
        let msg_hash = cb.query_word_rlc();
        let fq_modulus = cb.query_word_rlc();
        let msg_hash_mod = ModGadget::construct(cb, [&msg_hash_raw, &fq_modulus, &msg_hash]);

        let sig_r = cb.query_word_rlc();
        let sig_r_canonical = LtWordGadget::construct(cb, &sig_r, &fq_modulus);
        let sig_s = cb.query_word_rlc();
        let sig_s_canonical = LtWordGadget::construct(cb, &sig_s, &fq_modulus);
        let r_s_canonical = and::expr([sig_r_canonical.expr(), sig_s_canonical.expr()]);

        cb.require_equal(
            "msg hash cells assigned incorrectly",
            msg_hash_keccak_rlc.expr(),
            cb.keccak_rlc::<N_BYTES_WORD>(
                msg_hash_raw
                    .cells
                    .iter()
                    .map(Expr::expr)
                    .collect::<Vec<Expression<F>>>()
                    .try_into()
                    .expect("msg hash is 32 bytes"),
            ),
        );
        cb.require_equal(
            "sig_r cells assigned incorrectly",
            sig_r_keccak_rlc.expr(),
            cb.keccak_rlc::<N_BYTES_WORD>(
                sig_r
                    .cells
                    .iter()
                    .map(Expr::expr)
                    .collect::<Vec<Expression<F>>>()
                    .try_into()
                    .expect("msg hash is 32 bytes"),
            ),
        );
        cb.require_equal(
            "sig_s cells assigned incorrectly",
            sig_s_keccak_rlc.expr(),
            cb.keccak_rlc::<N_BYTES_WORD>(
                sig_s
                    .cells
                    .iter()
                    .map(Expr::expr)
                    .collect::<Vec<Expression<F>>>()
                    .try_into()
                    .expect("msg hash is 32 bytes"),
            ),
        );
        cb.require_equal(
            "Secp256k1::Fq modulus assigned correctly",
            fq_modulus.expr(),
            cb.word_rlc::<N_BYTES_WORD>(FQ_MODULUS.to_le_bytes().map(|b| b.expr())),
        );

        let [is_success, callee_address, caller_id, call_data_offset, call_data_length, return_data_offset, return_data_length] =
            [
                CallContextFieldTag::IsSuccess,
                CallContextFieldTag::CalleeAddress,
                CallContextFieldTag::CallerId,
                CallContextFieldTag::CallDataOffset,
                CallContextFieldTag::CallDataLength,
                CallContextFieldTag::ReturnDataOffset,
                CallContextFieldTag::ReturnDataLength,
            ]
            .map(|tag| cb.call_context(None, tag));

        let gas_cost = select::expr(
            is_success.expr(),
            GasCost::PRECOMPILE_ECRECOVER_BASE.expr(),
            cb.curr.state.gas_left.expr(),
        );

        // lookup to the sign_verify table:
        //
        // || msg_hash | v | r | s | recovered_addr | recovered ||
        cb.condition(r_s_canonical.expr(), |cb| {
            cb.sig_table_lookup(
                msg_hash.expr(),
                sig_v_keccak_rlc.expr() - 27.expr(),
                sig_r.expr(),
                sig_s.expr(),
                select::expr(
                    recovered.expr(),
                    from_bytes::expr(&recovered_addr_keccak_rlc.cells),
                    0.expr(),
                ),
                recovered.expr(),
            );
        });
        cb.condition(not::expr(r_s_canonical.expr()), |cb| {
            cb.require_zero(
                "recovered == false if r or s not canonical",
                recovered.expr(),
            );
        });
        cb.condition(not::expr(recovered.expr()), |cb| {
            cb.require_zero(
                "address == 0 if address could not be recovered",
                recovered_addr_keccak_rlc.expr(),
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
            0x00.expr(),                                              // ReturnDataOffset
            select::expr(recovered.expr(), 0x20.expr(), 0x00.expr()), // ReturnDataLength
            0.expr(),
            0.expr(),
        );

        Self {
            recovered,
            msg_hash_keccak_rlc,
            sig_v_keccak_rlc,
            sig_r_keccak_rlc,
            sig_s_keccak_rlc,
            recovered_addr_keccak_rlc,

            msg_hash_raw,
            msg_hash,
            fq_modulus,
            msg_hash_mod,

            sig_r,
            sig_r_canonical,
            sig_s,
            sig_s_canonical,

            is_success,
            callee_address,
            caller_id,
            call_data_offset,
            call_data_length,
            return_data_offset,
            return_data_length,
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
            self.recovered
                .assign(region, offset, Value::known(F::from(recovered as u64)))?;
            self.msg_hash_keccak_rlc.assign(
                region,
                offset,
                region
                    .challenges()
                    .keccak_input()
                    .map(|r| rlc::value(&aux_data.msg_hash.to_le_bytes(), r)),
            )?;
            self.sig_v_keccak_rlc.assign(
                region,
                offset,
                region
                    .challenges()
                    .keccak_input()
                    .map(|r| rlc::value(&aux_data.sig_v.to_le_bytes(), r)),
            )?;
            self.sig_r_keccak_rlc.assign(
                region,
                offset,
                region
                    .challenges()
                    .keccak_input()
                    .map(|r| rlc::value(&aux_data.sig_r.to_le_bytes(), r)),
            )?;
            self.sig_s_keccak_rlc.assign(
                region,
                offset,
                region
                    .challenges()
                    .keccak_input()
                    .map(|r| rlc::value(&aux_data.sig_s.to_le_bytes(), r)),
            )?;
            for (word_rlc, value) in [
                (&self.msg_hash_raw, aux_data.msg_hash),
                (&self.sig_r, aux_data.sig_r),
                (&self.sig_s, aux_data.sig_s),
            ] {
                word_rlc.assign(region, offset, Some(value.to_le_bytes()))?;
            }
            let (quotient, remainder) = aux_data.msg_hash.div_mod(*FQ_MODULUS);
            self.msg_hash
                .assign(region, offset, Some(remainder.to_le_bytes()))?;
            self.fq_modulus
                .assign(region, offset, Some(FQ_MODULUS.to_le_bytes()))?;
            self.msg_hash_mod.assign(
                region,
                offset,
                aux_data.msg_hash,
                *FQ_MODULUS,
                remainder,
                quotient,
            )?;
            self.sig_r_canonical
                .assign(region, offset, aux_data.sig_r, *FQ_MODULUS)?;
            self.sig_s_canonical
                .assign(region, offset, aux_data.sig_s, *FQ_MODULUS)?;
            self.recovered_addr_keccak_rlc.assign(
                region,
                offset,
                Some({
                    let mut recovered_addr = aux_data.recovered_addr.to_fixed_bytes();
                    recovered_addr.reverse();
                    recovered_addr
                }),
            )?;
        } else {
            log::error!("unexpected aux_data {:?} for ecrecover", step.aux_data);
            return Err(Error::Synthesis);
        }

        self.is_success.assign(
            region,
            offset,
            Value::known(F::from(u64::from(call.is_success))),
        )?;
        self.callee_address.assign(
            region,
            offset,
            Value::known(call.code_address.unwrap().to_scalar().unwrap()),
        )?;
        self.caller_id
            .assign(region, offset, Value::known(F::from(call.caller_id as u64)))?;
        self.call_data_offset.assign(
            region,
            offset,
            Value::known(F::from(call.call_data_offset)),
        )?;
        self.call_data_length.assign(
            region,
            offset,
            Value::known(F::from(call.call_data_length)),
        )?;
        self.return_data_offset.assign(
            region,
            offset,
            Value::known(F::from(call.return_data_offset)),
        )?;
        self.return_data_length.assign(
            region,
            offset,
            Value::known(F::from(call.return_data_length)),
        )?;
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
    use itertools::Itertools;
    use mock::TestContext;
    use rayon::iter::{ParallelBridge, ParallelIterator};

    use crate::test_util::CircuitTestBuilder;

    lazy_static::lazy_static! {
        static ref TEST_VECTOR: Vec<PrecompileCallArgs> = {
            vec![
                PrecompileCallArgs {
                    name: "ecrecover (padded bytes, addr recovered)",
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
                    // copy 101 bytes from memory addr 0. This should be sufficient to recover an
                    // address, but the signature is invalid (ecrecover does not care about this
                    // though)
                    call_data_offset: 0x00.into(),
                    call_data_length: 0x65.into(),
                    // return 32 bytes and write from memory addr 128
                    ret_offset: 0x80.into(),
                    ret_size: 0x20.into(),
                    address: PrecompileCalls::Ecrecover.address().to_word(),
                    ..Default::default()
                },
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
            ]
        };

        static ref OOG_TEST_VECTOR: Vec<PrecompileCallArgs> = {
            vec![
                PrecompileCallArgs {
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
                },
            ]
        };
    }

    #[test]
    fn precompile_ecrecover_test() {
        let call_kinds = vec![
            OpcodeId::CALL,
            OpcodeId::STATICCALL,
            OpcodeId::DELEGATECALL,
            OpcodeId::CALLCODE,
        ];

        TEST_VECTOR
            .iter()
            .cartesian_product(&call_kinds)
            .par_bridge()
            .for_each(|(test_vector, &call_kind)| {
                let bytecode = test_vector.with_call_op(call_kind);

                CircuitTestBuilder::new_from_test_ctx(
                    TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                )
                .run();
            })
    }

    #[test]
    fn precompile_ecrecover_oog_test() {
        let call_kinds = vec![
            OpcodeId::CALL,
            OpcodeId::STATICCALL,
            OpcodeId::DELEGATECALL,
            OpcodeId::CALLCODE,
        ];

        OOG_TEST_VECTOR
            .iter()
            .cartesian_product(&call_kinds)
            .par_bridge()
            .for_each(|(test_vector, &call_kind)| {
                let bytecode = test_vector.with_call_op(call_kind);

                CircuitTestBuilder::new_from_test_ctx(
                    TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                )
                .run();
            })
    }
}

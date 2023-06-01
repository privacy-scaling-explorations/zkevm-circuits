#![allow(missing_docs)]
//! wrapping of mpt-circuit
use crate::{
    table::{MptTable, PoseidonTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem, Error, Expression},
};
use hash_circuit::hash::Hashable;
use itertools::Itertools;
use mpt_zktrie::mpt_circuits::{
    constraint_builder::SelectorColumn,
    gadgets::{
        byte_bit::ByteBitGadget,
        byte_representation::{ByteRepresentationConfig, BytesLookup, RlcLookup},
        canonical_representation::CanonicalRepresentationConfig,
        is_zero::IsZeroGadget,
        key_bit::{KeyBitConfig, KeyBitLookup},
        mpt_update::{
            byte_representations, hash_traces, key_bit_lookups, mpt_update_keys, MptUpdateConfig,
        },
        one_hot::OneHot,
        poseidon::PoseidonLookup,
        rlc_randomness::RlcRandomness,
    },
    serde::SMTTrace,
    types::Proof,
    MPTProofType,
};

/// re-wrapping for mpt circuit
#[derive(Clone)]
pub struct MptCircuitConfig {
    pub mpt_update: MptUpdateConfig,
    pub canonical_representation: CanonicalRepresentationConfig,
    pub key_bit: KeyBitConfig,
    pub byte_bit: ByteBitGadget,
    pub byte_representation: ByteRepresentationConfig,
    /// PoseidonTable
    pub poseidon_table: PoseidonTable,
}

/// Circuit configuration arguments
pub struct MptCircuitConfigArgs {
    /// PoseidonTable
    pub poseidon_table: PoseidonTable,
    /// MptTable
    pub mpt_table: MptTable,
    /// Challenges
    pub challenges: Challenges,
}

impl SubCircuitConfig<Fr> for MptCircuitConfig {
    type ConfigArgs = MptCircuitConfigArgs;

    fn new(
        cs: &mut ConstraintSystem<Fr>,
        Self::ConfigArgs {
            poseidon_table,
            mpt_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        // TODO: connect mpt_table with mpt_circuit?
        let mpt_table = (
            mpt_table.q_enable,
            [
                mpt_table.address,
                mpt_table.storage_key,
                mpt_table.proof_type,
                mpt_table.new_root,
                mpt_table.old_root,
                mpt_table.new_value,
                mpt_table.old_value,
            ],
        );
        let rlc_randomness = RlcRandomness(challenges.evm_word());
        let mut cb = mpt_zktrie::mpt_circuits::constraint_builder::ConstraintBuilder::new(
            SelectorColumn(mpt_table.0),
        );

        let byte_bit = ByteBitGadget::configure(cs, &mut cb);
        let byte_representation =
            ByteRepresentationConfig::configure(cs, &mut cb, &byte_bit, &rlc_randomness);
        let canonical_representation =
            CanonicalRepresentationConfig::configure(cs, &mut cb, &byte_bit);
        let key_bit = KeyBitConfig::configure(
            cs,
            &mut cb,
            &canonical_representation,
            &byte_bit,
            &byte_bit,
            &byte_bit,
        );

        let mpt_update = MptUpdateConfig::configure(
            cs,
            &mut cb,
            &poseidon_table,
            &key_bit,
            &byte_representation,
            &byte_representation,
            &rlc_randomness,
        );

        cb.build(cs);

        Self {
            mpt_update,
            key_bit,
            byte_bit,
            canonical_representation,
            byte_representation,
            poseidon_table,
        }
    }
}

/// ...
#[derive(Clone, Debug, Default)]
pub struct MptCircuit {
    traces: Vec<(MPTProofType, SMTTrace)>,
}

#[cfg(any(feature = "test", test))]
impl SubCircuit<Fr> for MptCircuit {
    type Config = MptCircuitConfig;

    fn new_from_block(block: &witness::Block<Fr>) -> Self {
        Self {
            traces: block
                .mpt_updates
                .proof_types
                .iter()
                .cloned()
                .zip_eq(block.mpt_updates.smt_traces.iter().cloned())
                .collect(),
        }
    }

    fn min_num_rows_block(block: &witness::Block<Fr>) -> (usize, usize) {
        // FIXME
        (
            block.circuits_params.max_mpt_rows,
            block.circuits_params.max_mpt_rows,
        )
    }

    /// Make the assignments to the MptCircuit, notice it fill mpt table
    /// but not fill hash table
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let proofs: Vec<Proof> = self.traces.iter().cloned().map(Proof::from).collect();

        let (u64s, u128s, frs) = byte_representations(&proofs);

        layouter.assign_region(
            || "",
            |mut region| {
                // TODO: selector?
                config
                    .mpt_update
                    .assign(&mut region, &proofs, challenges.evm_word());
                config
                    .canonical_representation
                    .assign(&mut region, &mpt_update_keys(&proofs));
                config
                    .key_bit
                    .assign(&mut region, &key_bit_lookups(&proofs));
                config.byte_bit.assign(&mut region);
                config.byte_representation.assign(
                    &mut region,
                    &u64s,
                    &u128s,
                    &frs,
                    challenges.evm_word(),
                );
                Ok(())
            },
        )?;

        Ok(())
    }

    /// powers of randomness for instance columns
    fn instance(&self) -> Vec<Vec<Fr>> {
        vec![]
    }
}

#[cfg(any(feature = "test", test))]
impl Circuit<Fr> for MptCircuit {
    type Config = (MptCircuitConfig, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { traces: vec![] }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let poseidon_table = PoseidonTable::dev_construct(meta);
        let mpt_table = MptTable::construct(meta);

        let config = {
            //let challenges = challenges.exprs(meta);

            MptCircuitConfig::new(
                meta,
                MptCircuitConfigArgs {
                    poseidon_table,
                    mpt_table,
                    challenges,
                },
            )
        };

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&layouter);
        //let proofs: Vec<Proof> = self.traces.iter().map(Proof::from).collect();
        //config.poseidon_table.dev_load(&mut layouter, &hash_traces(&proofs));
        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

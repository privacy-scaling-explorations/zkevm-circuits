// PI CIRCUIT
//
// pub struct Transform {
// pub typ: ProofType,
// pub key: H256,
// pub value: U256,
// pub address: Address,
// pub nonce: U64,
// pub balance: U256,
// pub code_hash: H256,
// }
//
// pub struct MptTable {
// Account address
// pub address: Column<Advice>,
// Storage address
// pub storage_key: word::Word<Column<Advice>>,
// Proof type
// pub proof_type: Column<Advice>,
// New MPT root
// pub new_root: word::Word<Column<Advice>>,
// Previous MPT root
// pub old_root: word::Word<Column<Advice>>,
// New value
// pub new_value: word::Word<Column<Advice>>,
// Old value
// pub old_value: word::Word<Column<Advice>>,
// }
//
// PICIRCUIT
//
// PI
// ------------------
// last_state_root
// next_state_root
/// len
// | proof_type
// | address
// | value_hi
// | value_lo
// | storage_hi
// | storage_lo
//
// start  proof_type  address value_hi value_lo storage_hi storage_lo  old_root new_root
// -----  ---------- -------- -------- -------- ---------- ---------- --------- ----------
// 1      -                                                                      r1
// 0      BalChange   a1       0        0        0          0          r1        r2
// 0      BalChange   a2       0        0        0          0          r2        r3
// 0      0
// 0      0
// 0      0
//
// check first state root
// if start.current == 1 => new_root.current == PI.last_state_root
//
// check last state root
// if proof_type.curr != 0 and proof_type.next == 0 => new_root.current == PI.next_state_root
//
// check state_root_propagation
// if start ==  1 || proof_type != 0 => old_root.next == new_root.current
//
// proof type = 0 propagation a
// if proof_type.current == 0 => proof_type.next == 0
//
// lookup (proof_type  address value_hi value_lo storage_hi storage_lo  old_root new_root) into
// MPTTable
//

// =========================================================================================

use eth_types::{Address, Field, Word, H256, U256};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance, Advice, Fixed},
};
use zkevm_circuits::{
    mpt_circuit::{MPTCircuit, MPTCircuitParams, MPTConfig},
    table::{KeccakTable, MPTProofType, MptTable},
    util::{Challenges, word},
};

///
#[derive(Clone)]
pub struct LightClientCircuitConfig<F: Field> {
    pub mpt_config: MPTConfig<F>,

    pub pi_mpt : MptTable,
    pub pi_instance: Column<Instance>,
    pub first: Column<Fixed>,
    pub count : Column<Advice>,
}

/// MPT Circuit for proving the storage modification is valid.
#[derive(Default)]
pub struct LightClientCircuit<F: Field> {
    ///
    pub mpt_circuit: MPTCircuit<F>,
    ///
    pub pi: Vec<F>,
}

/// MPT Circuit configuration parameters
#[derive(Copy, Clone, Debug, Default)]
pub struct LightClientCircuitParams {
    ///
    mpt: MPTCircuitParams,
}

impl<F: Field> Circuit<F> for LightClientCircuit<F> {
    type Config = (LightClientCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = LightClientCircuitParams;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn params(&self) -> Self::Params {
        LightClientCircuitParams {
            mpt: MPTCircuitParams {
                degree: self.mpt_circuit.degree,
                disable_preimage_check: self.mpt_circuit.disable_preimage_check,
            },
        }
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenges_expr = challenges.exprs(meta);
        let keccak_table = KeccakTable::construct(meta);

        let mpt_config = MPTConfig::new(meta, challenges_expr, keccak_table, params.mpt);

        let config = LightClientCircuitConfig {
            mpt_config,
            first: meta.fixed_column(),
            count: meta.advice_column(),
            pi_instance: meta.instance_column(),
            pi_mpt : MptTable {
                address: meta.advice_column(),
                storage_key:  word::Word::new([meta.advice_column(), meta.advice_column()]),
                proof_type: meta.advice_column(),
                new_root:  word::Word::new([meta.advice_column(), meta.advice_column()]),
                old_root:  word::Word::new([meta.advice_column(), meta.advice_column()]),
                new_value:  word::Word::new([meta.advice_column(), meta.advice_column()]),
                old_value:  word::Word::new([meta.advice_column(), meta.advice_column()]),
            }
        };

        (config, challenges)
    }

    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!();
    }

    fn synthesize(
        &self,
        (config, _challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = _challenges.values(&mut layouter);
        let height = config
            .mpt_config
            .assign(&mut layouter, &self.mpt_circuit.nodes, &challenges)?;
        config.mpt_config.load_fixed_table(&mut layouter)?;
        config
            .mpt_config
            .load_mult_table(&mut layouter, &challenges, height)?;
        config.mpt_config.keccak_table.dev_load(
            &mut layouter,
            &self.mpt_circuit.keccak_data,
            &challenges,
        )?;

        // -------

        layouter.assign_region(
            || "pi",
            |mut region| {
                region.assign_fixed(|| "", config.first, 0,  || Value::known(F::ONE))?;

                Ok(())
            }
        )?;


        // layouter.constrain_instance(digest_word_assigned.lo().cell(), config.pi_instance, 0)?;


        Ok(())
    }
}

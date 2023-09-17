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
use crate::transforms::LightClientWitness;
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
use gadgets::{is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction}, util::{Expr, not::{expr, self}, and}};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector, Expression},
    poly::Rotation,
};
use zkevm_circuits::{
    mpt_circuit::{MPTCircuit, MPTCircuitParams, MPTConfig},
    table::{KeccakTable, MPTProofType, MptTable},
    util::{word, Challenges},
};

// A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
pub fn xif<F: Field>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    and::expr([a, not::expr(b)])
}

///
#[derive(Clone)]
pub struct LightClientCircuitConfig<F: Field> {
    pub mpt_config: MPTConfig<F>,

    pub pi_mpt: MptTable,
    pub pi_instance: Column<Instance>,
    pub first: Column<Fixed>,
    pub count: Column<Advice>,
    pub count_decrement_less_one_is_zero : IsZeroConfig<F>,
    pub count_is_zero: IsZeroConfig<F>,
    pub q_enable: Selector,
}

/// MPT Circuit for proving the storage modification is valid.
#[derive(Default)]
pub struct LightClientCircuit<F: Field> {
    ///
    pub mpt_circuit: MPTCircuit<F>,
    ///
    pub lc_witness: LightClientWitness<F>,
}

/// MPT Circuit configuration parameters
#[derive(Copy, Clone, Debug, Default)]
pub struct LightClientCircuitParams {
    ///
    mpt: MPTCircuitParams,
}

const PI_ROW_OLD_ROOT_LO: usize = 0;
const PI_ROW_OLD_ROOT_HI: usize = 1;
const PI_ROW_NEW_ROOT_LO: usize = 2;
const PI_ROW_NEW_ROOT_HI: usize = 3;
const PI_ROW_PROOF_COUNT: usize = 4;

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

        let first = meta.fixed_column();
        let count = meta.advice_column();
        let q_enable = meta.selector();
        let pi_instance = meta.instance_column();
        let pi_mpt = MptTable {
            address: meta.advice_column(),
            storage_key: word::Word::new([meta.advice_column(), meta.advice_column()]),
            proof_type: meta.advice_column(),
            new_root: word::Word::new([meta.advice_column(), meta.advice_column()]),
            old_root: word::Word::new([meta.advice_column(), meta.advice_column()]),
            new_value: word::Word::new([meta.advice_column(), meta.advice_column()]),
            old_value: word::Word::new([meta.advice_column(), meta.advice_column()]),
        };

        meta.enable_equality(pi_instance);
        meta.enable_equality(count);

        let count_inv = meta.advice_column();
        let count_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(count, Rotation::cur()),
            count_inv,
        );
        let count_decrement_less_one_inv = meta.advice_column();

        let count_decrement_less_one_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                let count_next = meta.query_advice(count, Rotation::next());
                let count_cur = meta.query_advice(count, Rotation::cur());
                count_cur - count_next - 1.expr()
            },
            count_decrement_less_one_inv,
        );

        meta.create_gate("if not zero, count descreases monotonically", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let if_not_zero_count_decreased_monotocally = xif(not::expr(count_is_zero.expr()), count_decrement_less_one_is_zero.expr());

            vec![ q_enable * if_not_zero_count_decreased_monotocally ]
        });

        // first count entry is
        //
        // This verifies is_zero is calculated correctly
        // let expect_is_zero = meta.query_advice(config.expect_is_zero, Rotation::cur());
        // let is_zero = meta.query_advice(config.is_zero.is_zero, Rotation::cur());
        // vec![q_enable * (is_zero - expect_is_zero)]
        // });
        let config = LightClientCircuitConfig {
            mpt_config,
            first,
            count,
            count_is_zero,
            count_decrement_less_one_is_zero,
            q_enable,
            pi_instance,
            pi_mpt,
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
        let height =
            config
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

        let MAX_PROOF_COUNT = 10;



        // -------
        let starting_count_cell = layouter.assign_region(
            || "pi",
            |mut region| {

                region.name_column(|| "LC_first", config.first);
                region.name_column(|| "LC_count", config.count);
                region.name_column(|| "LC_count_inv", config.count_is_zero.value_inv);
                region.name_column(|| "LC_count_monodec_inv", config.count_decrement_less_one_is_zero.value_inv);
                region.name_column(|| "LC_pi_instance", config.pi_instance);

                region.assign_fixed(|| "", config.first, 0, || Value::known(F::ONE))?;

                let mut starting_count_cell = None;

                for offset in 0..self.lc_witness.0.len() {
                    //println!("****** offset {}", offset);
                    config.q_enable.enable(&mut region, offset)?;

                    let count = Value::known(F::from((self.lc_witness.0.len() - offset) as u64));

                    IsZeroChip::construct(config.count_is_zero.clone()).assign(&mut region, offset, count)?;
                    IsZeroChip::construct(config.count_decrement_less_one_is_zero.clone()).assign(&mut region, offset, Value::known(1.into()))?;

                    let cell = region.assign_advice(
                        || "",
                        config.count,
                        offset,
                        || count,
                    )?;
                    if offset == 0 {
                        starting_count_cell = Some(cell);
                    }
                }

                // fill in the rest of the count cells with 0
                for offset in self.lc_witness.0.len()..MAX_PROOF_COUNT {
                    region.assign_advice(
                        || "",
                        config.count,
                        offset,
                        || Value::known(F::ZERO),
                    )?;
                }

                Ok(starting_count_cell.unwrap())
            },
        )?;

        layouter.constrain_instance(
            starting_count_cell.cell(),
            config.pi_instance,
            PI_ROW_PROOF_COUNT,
        )?;

        Ok(())
    }
}

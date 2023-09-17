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
use crate::transforms::{LightClientProof, LightClientWitness};
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

const MAX_PROOF_COUNT: usize = 10;

use eth_types::{Address, Field, Word, H256, U256};
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    util::{
        and,
        not::{self, expr},
        or, Expr,
    },
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Any, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance,
        Selector, TableColumn,
    },
    poly::Rotation,
};
use zkevm_circuits::{
    mpt_circuit::{MPTCircuit, MPTCircuitParams, MPTConfig},
    table::{KeccakTable, LookupTable, MPTProofType, MptTable},
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

    pub is_first: Column<Fixed>,
    pub is_padding: IsZeroConfig<F>,
    pub is_last: IsZeroConfig<F>,

    pub new_root_propagation: IsZeroConfig<F>,

    pub count: Column<Advice>,
    pub count_decrement_less_one_is_zero: IsZeroConfig<F>,

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

        let is_first = meta.fixed_column();
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

        for col in [
            pi_mpt.address,
            pi_mpt.storage_key.lo(),
            pi_mpt.storage_key.hi(),
            pi_mpt.proof_type,
            pi_mpt.new_root.lo(),
            pi_mpt.new_root.hi(),
            pi_mpt.old_root.lo(),
            pi_mpt.old_root.hi(),
            pi_mpt.new_value.lo(),
            pi_mpt.new_value.hi(),
            pi_mpt.old_value.lo(),
            pi_mpt.old_value.hi(),
        ]
        .iter()
        {
            meta.enable_equality(*col);
        }

        meta.enable_equality(pi_instance);
        meta.enable_equality(count);

        let is_padding_inv = meta.advice_column();
        let is_padding = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(count, Rotation::cur()),
            is_padding_inv,
        );

        let is_last_inv = meta.advice_column();
        let is_last = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(count, Rotation::cur()) - 1.expr(),
            is_last_inv,
        );

        let new_root_propagation_inv = meta.advice_column();
        let new_root_propagation = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                (meta.query_advice(pi_mpt.new_root.lo(), Rotation::cur())
                    - meta.query_advice(pi_mpt.new_root.lo(), Rotation::next()))
                    + (meta.query_advice(pi_mpt.new_root.hi(), Rotation::cur())
                        - meta.query_advice(pi_mpt.new_root.hi(), Rotation::next()))
            },
            new_root_propagation_inv,
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

        meta.create_gate("if not padding, count descreases monotonically", |meta| {
            let q_enable = meta.query_selector(q_enable);
            vec![
                q_enable
                    * xif(
                        not::expr(is_padding.expr()),
                        count_decrement_less_one_is_zero.expr(),
                    ),
            ]
        });

        meta.create_gate("if last or padding, new_root is propagated ", |meta| {
            let q_enable = meta.query_selector(q_enable);
            vec![q_enable * xif(is_padding.expr(), new_root_propagation.expr())]
        });

        meta.create_gate(
            "if not padding and not last row, roots should be chanined",
            |meta| {
                let q_enable = meta.query_selector(q_enable);

                let one_if_not_padding_and_not_last_rot =
                    or::expr([is_padding.expr(), is_last.expr()]);

                // TODO: quite ugly, need to compare with zero
                let zero_if_roots_are_chanined = (meta
                    .query_advice(pi_mpt.new_root.lo(), Rotation::cur())
                    - meta.query_advice(pi_mpt.old_root.lo(), Rotation::next()))
                    + (meta.query_advice(pi_mpt.new_root.hi(), Rotation::cur())
                        - meta.query_advice(pi_mpt.old_root.hi(), Rotation::next()));

                vec![
                    q_enable
                        * xif(
                            not::expr(one_if_not_padding_and_not_last_rot),
                            not::expr(zero_if_roots_are_chanined),
                        ),
                ]
            },
        );

        meta.lookup_any("lc_mpt_updates lookups into mpt_table", |meta| {
            vec![
                (
                    meta.query_advice(pi_mpt.proof_type, Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.proof_type, Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.address, Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.address, Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.new_value.lo(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.new_value.lo(), Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.new_value.hi(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.new_value.hi(), Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.storage_key.lo(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.storage_key.lo(), Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.storage_key.hi(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.storage_key.hi(), Rotation::cur()),
                ),
                // (meta.query_advice(pi_mpt.old_root.lo(), Rotation::cur()),
                // meta.query_advice(mpt_config.mpt_table.old_root.lo(), Rotation::cur())),
                // (meta.query_advice(pi_mpt.old_root.hi(), Rotation::cur()),
                // meta.query_advice(mpt_config.mpt_table.old_root.hi(), Rotation::cur())),
                // (meta.query_advice(pi_mpt.new_root.lo(), Rotation::cur()),
                // meta.query_advice(mpt_config.mpt_table.new_root.lo(), Rotation::cur())),
                // (meta.query_advice(pi_mpt.new_root.hi(), Rotation::cur()),
                // meta.query_advice(mpt_config.mpt_table.new_root.hi(), Rotation::cur())),
            ]
        });

        let config = LightClientCircuitConfig {
            mpt_config,
            is_first,
            count,
            is_padding,
            is_last,
            count_decrement_less_one_is_zero,
            new_root_propagation,
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

        let pi = layouter.assign_region(
            || "pi",
            |mut region| {
                let is_padding = IsZeroChip::construct(config.is_padding.clone());
                let is_last =
                    IsZeroChip::construct(config.is_last.clone());
                let count_decrement_less_one_is_zero =
                    IsZeroChip::construct(config.count_decrement_less_one_is_zero.clone());
                    let new_root_propagation =
                    IsZeroChip::construct(config.new_root_propagation.clone());

                region.name_column(|| "LC_first", config.is_first);
                region.name_column(|| "LC_count", config.count);
                region.name_column(|| "LC_padding_inv", config.is_padding.value_inv);
                region.name_column(|| "LC_last_inv", config.is_last.value_inv);
                region.name_column(
                    || "LC_count_monodec_inv",
                    config.count_decrement_less_one_is_zero.value_inv,
                );
                region.name_column(|| "LC_pi_instance", config.pi_instance);

                region.assign_fixed(|| "", config.is_first, 0, || Value::known(F::ONE))?;

                let mut pi = Vec::new();

                for offset in 0..MAX_PROOF_COUNT {
                    if offset < MAX_PROOF_COUNT - 1 {
                        config.q_enable.enable(&mut region, offset)?;
                    }

                    let count_usize = self.lc_witness.0.len().saturating_sub(offset);
                    let padding = count_usize == 0;
                    let count = Value::known(F::from(count_usize as u64));

                    is_padding.assign(&mut region, offset, count)?;
                    is_last.assign(
                        &mut region,
                        offset,
                        Value::known(F::from(count_usize as u64) - F::ONE),
                    )?;
                    count_decrement_less_one_is_zero.assign(
                        &mut region,
                        offset,
                        Value::known(if padding { F::ZERO - F::ONE } else { F::ZERO }),
                    )?;

                    let mpt = self.lc_witness.0.get(offset).cloned().unwrap_or(LightClientProof {
                        new_root: self.lc_witness.0.last().unwrap().new_root,
                        ..Default::default()
                    });
                    let mpt_next = self.lc_witness.0.get(offset+1).cloned().unwrap_or(LightClientProof {
                        new_root: self.lc_witness.0.last().unwrap().new_root,
                        ..Default::default()
                    });

                    new_root_propagation.assign(&mut region, offset,
                        Value::known(mpt.new_root.lo() - mpt_next.new_root.lo() + mpt.new_root.hi() - mpt_next.new_root.hi())
                    )?;

                    let count_cell = region.assign_advice(|| "", config.count, offset, || count)?;

                    let mpt = self.lc_witness.0.get(offset).cloned().unwrap_or(LightClientProof {
                        new_root: self.lc_witness.0.last().unwrap().new_root,
                        ..Default::default()
                    });

                    let [typ, addr, value_lo, value_hi,
                         key_lo, key_hi, old_root_lo, old_root_hi,
                         new_root_lo, new_root_hi] =

                        [(config.pi_mpt.proof_type,mpt.typ), (config.pi_mpt.address,mpt.address),(config.pi_mpt.new_value.lo(),mpt.value.lo()),
                        (config.pi_mpt.new_value.hi(),mpt.value.hi()),(config.pi_mpt.storage_key.lo(),mpt.key.lo()), (config.pi_mpt.storage_key.hi(),
                        mpt.key.hi()), (config.pi_mpt.old_root.lo(),mpt.old_root.lo()),(config.pi_mpt.old_root.hi(), mpt.old_root.hi()),
                        (config.pi_mpt.new_root.lo(), mpt.new_root.lo()),(config.pi_mpt.new_root.hi(), mpt.new_root.hi())]
                        .map(|(col, value)|
                                region.assign_advice(
                                    || "",
                                    col,
                                    offset,
                                    || Value::known(value),
                                ).unwrap()
                            );

                    if offset == 0 {
                        pi.push(Some(old_root_lo));
                        pi.push(Some(old_root_hi));
                        pi.push(None);
                        pi.push(None);
                        pi.push(Some(count_cell));
                    }

                    pi.append(vec![Some(typ), Some(addr), Some(value_lo), Some(value_hi), Some(key_lo), Some(key_hi)].as_mut());

                    if offset == MAX_PROOF_COUNT -1 {
                        pi[2] = Some(new_root_lo);
                        pi[3] = Some(new_root_hi);
                    }

                }
                Ok(pi)
            },
        )?;

        // check that state updates to lookup are the same that the specified in the public inputs
        for (n, value) in pi.into_iter().enumerate() {
            layouter.constrain_instance(value.unwrap().cell(), config.pi_instance, n)?;
        }

        Ok(())
    }
}

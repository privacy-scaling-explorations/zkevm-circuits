use super::equal_words::EqualWordsConfig;
use eth_types::Field;
use eyre::Result;
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    util::{
        and,
        not::{self},
        or, Expr,
    },
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::bn256::Fr,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};

use zkevm_circuits::{
    keccak_circuit::{KeccakCircuit, KeccakCircuitConfig, KeccakCircuitConfigArgs},
    mpt_circuit::{MPTCircuit, MPTCircuitParams, MPTConfig},
    table::{KeccakTable, MptTable},
    util::{word, Challenges, SubCircuit, SubCircuitConfig},
};

pub const DEFAULT_MAX_PROOF_COUNT: usize = 20;
pub const DEFAULT_CIRCUIT_DEGREE: usize = 14;

use super::witness::{
    SingleTrieModification, SingleTrieModifications, StateUpdateWitness, Transforms,
};

// A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
fn xif<F: Field>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    and::expr([a, not::expr(b)])
}

///
#[derive(Clone)]
pub struct StateUpdateCircuitConfig<F: Field> {
    #[cfg(not(feature = "disable-keccak"))]
    pub keccak_config: KeccakCircuitConfig<F>,
    pub mpt_config: MPTConfig<F>,

    pub pi_mpt: MptTable,
    pub pi_instance: Column<Instance>,

    pub is_first: Column<Fixed>,
    pub is_padding: IsZeroConfig<F>,
    pub is_last: IsZeroConfig<F>,

    pub new_root_propagation: EqualWordsConfig<F>,
    pub root_chained: EqualWordsConfig<F>,

    pub count: Column<Advice>,
    pub count_decrement: IsZeroConfig<F>,

    pub q_enable: Selector,
}

/// MPT Circuit for proving the storage modification is valid.
#[derive(Default)]
pub struct StateUpdateCircuit<F: Field> {
    pub transforms: Transforms,
    #[cfg(not(feature = "disable-keccak"))]
    pub keccak_circuit: KeccakCircuit<F>,
    pub mpt_circuit: MPTCircuit<F>,
    pub lc_witness: SingleTrieModifications<F>,
    pub degree: usize,
    pub max_proof_count: usize,
}

impl<F: Field> Circuit<F> for StateUpdateCircuit<F> {
    type Config = (StateUpdateCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = MPTCircuitParams;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn params(&self) -> Self::Params {
        MPTCircuitParams {
            degree: self.mpt_circuit.degree,
            disable_preimage_check: self.mpt_circuit.disable_preimage_check,
        }
    }

    fn configure_with_params(meta: &mut ConstraintSystem<F>, params: Self::Params) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenges_expr = challenges.exprs(meta);

        let keccak_table = KeccakTable::construct(meta);

        #[cfg(not(feature = "disable-keccak"))]
        let keccak_config = KeccakCircuitConfig::new(
            meta,
            KeccakCircuitConfigArgs {
                keccak_table: keccak_table.clone(),
                challenges: challenges_expr.clone(),
            },
        );
        let mpt_config = MPTConfig::new(meta, challenges_expr, keccak_table, params);

        let is_first = meta.fixed_column();
        let count = meta.advice_column();
        let q_enable = meta.complex_selector();
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

        let new_root_propagation = EqualWordsConfig::configure(
            meta,
            q_enable,
            (pi_mpt.new_root, Rotation::cur()),
            (pi_mpt.new_root, Rotation::next()),
        );

        let root_chained = EqualWordsConfig::configure(
            meta,
            q_enable,
            (pi_mpt.new_root, Rotation::cur()),
            (pi_mpt.old_root, Rotation::next()),
        );

        let count_decrement_less_one_inv = meta.advice_column();
        let count_decrement = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                let count_next = meta.query_advice(count, Rotation::next());
                let count_cur = meta.query_advice(count, Rotation::cur());
                count_cur - count_next - 1.expr()
            },
            count_decrement_less_one_inv,
        );

        meta.create_gate("if not padding, count decreases monotonically", |meta| {
            let q_enable = meta.query_selector(q_enable);
            vec![q_enable * xif(not::expr(is_padding.expr()), count_decrement.expr())]
        });

        meta.create_gate("if last or padding, new_root is propagated ", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_last_or_padding = or::expr([is_padding.expr(), is_last.expr()]);
            vec![q_enable * xif(is_last_or_padding.expr(), new_root_propagation.expr())]
        });

        meta.create_gate(
            "if not padding and not last row, roots should be chained",
            |meta| {
                let q_enable = meta.query_selector(q_enable);

                let one_if_not_padding_and_not_last_rot =
                    or::expr([is_padding.expr(), is_last.expr()]);

                vec![
                    q_enable
                        * xif(
                            not::expr(one_if_not_padding_and_not_last_rot),
                            root_chained.expr(),
                        ),
                ]
            },
        );

        meta.lookup_any("lc_mpt_updates lookups into mpt_table", |meta| {
            let is_not_padding = 1.expr() - is_padding.expr();

            let lookups = vec![
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
                // TODO: MPT_table new/old roots are reversed
                (
                    meta.query_advice(pi_mpt.old_root.lo(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.new_root.lo(), Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.old_root.hi(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.new_root.hi(), Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.new_root.lo(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.old_root.lo(), Rotation::cur()),
                ),
                (
                    meta.query_advice(pi_mpt.new_root.hi(), Rotation::cur()),
                    meta.query_advice(mpt_config.mpt_table.old_root.hi(), Rotation::cur()),
                ),
            ];

            lookups
                .into_iter()
                .map(|(from, to)| (from * is_not_padding.clone(), to))
                .collect()
        });

        let config = StateUpdateCircuitConfig {
            #[cfg(not(feature = "disable-keccak"))]
            keccak_config,
            mpt_config,
            is_first,
            count,
            is_padding,
            is_last,
            count_decrement,
            new_root_propagation,
            root_chained,
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

        // assign MPT witness

        let height =
            config
                .mpt_config
                .assign(&mut layouter, &self.mpt_circuit.nodes, &challenges)?;
        config.mpt_config.load_fixed_table(&mut layouter)?;
        config
            .mpt_config
            .load_mult_table(&mut layouter, &challenges, height)?;

        #[cfg(feature = "disable-keccak")]
        config.mpt_config.keccak_table.dev_load(
            &mut layouter,
            &self.mpt_circuit.keccak_data,
            &challenges,
        )?;

        #[cfg(not(feature = "disable-keccak"))]
        self.keccak_circuit
            .synthesize_sub(&config.keccak_config, &challenges, &mut layouter)?;

        // assign LC witness

        let pi = layouter.assign_region(
            || "lc witness",
            |mut region| {

                assert!(self.lc_witness.len() < self.max_proof_count);

                let is_padding = IsZeroChip::construct(config.is_padding.clone());
                let is_last =
                    IsZeroChip::construct(config.is_last.clone());
                let count_decrement =
                    IsZeroChip::construct(config.count_decrement.clone());

                region.name_column(|| "LC_first", config.is_first);
                region.name_column(|| "LC_count", config.count);
                region.name_column(|| "LC_padding_inv", config.is_padding.value_inv);
                region.name_column(|| "LC_last_inv", config.is_last.value_inv);
                region.name_column(
                    || "LC_count_monodec_inv",
                    config.count_decrement.value_inv,
                );
                region.name_column(|| "LC_pi_instance", config.pi_instance);

                region.assign_fixed(|| "", config.is_first, 0, || Value::known(F::ONE))?;

                let mut pi = Vec::new();

                for offset in 0..self.max_proof_count {

                    let count_usize = self.lc_witness.len().saturating_sub(offset);
                    let padding = count_usize == 0;
                    let count = Value::known(F::from(count_usize as u64));

                    // do not enable the last row, to avoid errors in constraints that involves next rotation
                    if offset < self.max_proof_count - 1 {
                        config.q_enable.enable(&mut region, offset)?;
                    }

                    // assign is_padding, is_last, count_decrement

                    is_padding.assign(&mut region, offset, count)?;
                    is_last.assign(
                        &mut region,
                        offset,
                        Value::known(F::from(count_usize as u64) - F::ONE),
                    )?;
                    count_decrement.assign(
                        &mut region,
                        offset,
                        Value::known(if padding { F::ZERO - F::ONE } else { F::ZERO }),
                    )?;

                    // assign set the value for entries to do the lookup propagating ending root in padding
                    // and collect cells for checking public inputs.

                    let stm = self.lc_witness.get(offset).cloned().unwrap_or(SingleTrieModification {
                        new_root: self.lc_witness.last().cloned().unwrap_or_default().new_root,
                        ..Default::default()
                    });
                    let stm_next = self.lc_witness.get(offset+1).cloned().unwrap_or(SingleTrieModification {
                        new_root: self.lc_witness.last().cloned().unwrap_or_default().new_root,
                        ..Default::default()
                    });

                    config.new_root_propagation.assign(&mut region, offset,
                        "new_root_propagation",  &stm.new_root, &stm_next.new_root
                    )?;

                    config.root_chained.assign(&mut region, offset,
                        "root_chained",
                        &stm.new_root, &stm_next.old_root
                    )?;

                    let count_cell = region.assign_advice(|| "", config.count, offset, || count)?;

                    let [typ,
                         addr,
                         value_lo,
                         value_hi,
                         key_lo,
                         key_hi,
                         old_root_lo,
                         old_root_hi,
                         new_root_lo,
                         new_root_hi] =

                        [
                            (config.pi_mpt.proof_type,stm.typ),
                            (config.pi_mpt.address,stm.address),
                            (config.pi_mpt.new_value.lo(),stm.value.lo()),
                            (config.pi_mpt.new_value.hi(),stm.value.hi()),
                            (config.pi_mpt.storage_key.lo(),stm.key.lo()),
                            (config.pi_mpt.storage_key.hi(), stm.key.hi()),
                            (config.pi_mpt.old_root.lo(),stm.old_root.lo()),
                            (config.pi_mpt.old_root.hi(), stm.old_root.hi()),
                            (config.pi_mpt.new_root.lo(), stm.new_root.lo()),
                            (config.pi_mpt.new_root.hi(), stm.new_root.hi())
                        ]
                        .map(|(col, value)|
                                region.assign_advice(
                                    || "",
                                    col,
                                    offset,
                                    || Value::known(value),
                                ).unwrap()
                            );

                    // at beggining, set the old root and number of proofs

                    if offset == 0 {
                        pi.push(Some(old_root_lo));
                        pi.push(Some(old_root_hi));
                        pi.push(None);
                        pi.push(None);
                        pi.push(Some(count_cell));
                    }

                    pi.append(vec![Some(typ), Some(addr), Some(value_lo), Some(value_hi), Some(key_lo), Some(key_hi)].as_mut());

                    // at ending, set the last root in the last row (valid since we are propagating it)

                    if offset == self.max_proof_count -1 {
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

impl StateUpdateCircuit<Fr> {
    pub fn new(
        witness: StateUpdateWitness<Fr>,
        degree: usize,
        max_proof_count: usize,
    ) -> Result<StateUpdateCircuit<Fr>> {
        let StateUpdateWitness {
            mpt_witness,
            transforms,
            lc_witness,
        } = witness;

        // populate the keccak data
        let mut keccak_data = vec![];
        for node in mpt_witness.iter() {
            for k in node.keccak_data.iter() {
                keccak_data.push(k.to_vec());
            }
        }

        // verify the circuit
        let disable_preimage_check = mpt_witness[0].start.clone().unwrap().disable_preimage_check;

        let mpt_circuit = zkevm_circuits::mpt_circuit::MPTCircuit::<Fr> {
            nodes: mpt_witness,
            keccak_data: keccak_data.clone(),
            degree,
            disable_preimage_check,
            _marker: std::marker::PhantomData,
        };

        #[cfg(not(feature = "disable-keccak"))]
        let keccak_circuit = KeccakCircuit::<Fr>::new(2usize.pow(degree as u32), keccak_data);

        let lc_circuit = StateUpdateCircuit::<Fr> {
            transforms,
            #[cfg(not(feature = "disable-keccak"))]
            keccak_circuit,
            mpt_circuit,
            lc_witness,
            degree,
            max_proof_count,
        };

        Ok(lc_circuit)
    }
}

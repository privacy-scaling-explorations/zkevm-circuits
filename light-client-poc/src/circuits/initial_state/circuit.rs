use eth_types::{keccak256, Field, H256};
use eyre::Result;
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    util::{
        not::{self},
        or, Expr,
    },
};

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::bn256::Fr,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, SecondPhase,
        Selector,
    },
    poly::Rotation,
};

use zkevm_circuits::{
    mpt_circuit::{MPTCircuit, MPTCircuitParams, MPTConfig},
    table::{KeccakTable, MptTable},
    util::{
        word::{self, Word},
        Challenges,
    },
};

use crate::witness::{
    SingleTrieModification, SingleTrieModifications, Transforms, Witness,
};

#[cfg(not(feature = "disable-keccak"))]
use zkevm_circuits::{
    keccak_circuit::{KeccakCircuit, KeccakCircuitConfig, KeccakCircuitConfigArgs},
    util::{SubCircuit, SubCircuitConfig},
};

pub const DEFAULT_MAX_PROOF_COUNT: usize = 20;
pub const DEFAULT_CIRCUIT_DEGREE: usize = 14;

use crate::circuits::utils::{xif, xnif, EqualWordsConfig, FixedRlcConfig};

pub trait STMHelper<F> {
    fn get_padded_values(&self, max_proof_count: usize) -> Vec<(F, usize)>;
    fn first_root(&self) -> Word<F>;
    fn last_root(&self) -> Word<F>;
    fn initial_values_len(&self) -> usize;
    fn initial_values_bytes(&self) -> Vec<u8>;
    fn initial_values_hash(&self) -> Word<F>;
}

impl<F: Field> STMHelper<F> for SingleTrieModifications<F> {
    fn first_root(&self) -> Word<F> {
        self.0.first().cloned().unwrap().old_root
    }

    fn last_root(&self) -> Word<F> {
        self.0.last().cloned().unwrap().new_root
    }

    fn get_padded_values(&self, len: usize) -> Vec<(F, usize)> {
        assert!(self.0.len() <= len);

        let first_root = self.first_root();
        let last_root = self.last_root();

        let mut rlc_values = vec![
            (first_root.lo(), 16),
            (first_root.hi(), 16),
            (last_root.lo(), 16),
            (last_root.hi(), 16),
        ];
        for i in 0..len {
            if let Some(w) = self.0.get(i) {
                rlc_values.push((w.typ, 1));
                rlc_values.push((w.address, 20));
                rlc_values.push((w.value.lo(), 16));
                rlc_values.push((w.value.hi(), 16));
                rlc_values.push((w.key.lo(), 16));
                rlc_values.push((w.key.hi(), 16));
            } else {
                rlc_values.push((0u64.into(), 1));
                rlc_values.push((0u64.into(), 20));
                rlc_values.push((0u64.into(), 16));
                rlc_values.push((0u64.into(), 16));
                rlc_values.push((0u64.into(), 16));
                rlc_values.push((0u64.into(), 16));
            }
        }
        rlc_values
    }

    fn initial_values_len(&self) -> usize {
        self.0
            .iter()
            .enumerate()
            .find(|(_, t)| t.old_root != t.new_root)
            .unwrap()
            .0
    }

    fn initial_values_bytes(&self) -> Vec<u8> {
        let values = self.get_padded_values(self.0.len());
        let initial_values_len = self.initial_values_len();

        values
            .iter()
            .take(initial_values_len)
            .flat_map(|(f, len)| f.to_repr()[0..*len].to_vec())
            .collect()
    }
    fn initial_values_hash(&self) -> Word<F> {
        let initial_values_bytes = self.initial_values_bytes();
        let initial_values_hash = keccak256(&initial_values_bytes);
        Word::from(H256(initial_values_hash))
    }
}

///
#[derive(Clone)]
pub struct InitialStateCircuitConfig<F: Field> {
    #[cfg(not(feature = "disable-keccak"))]
    pub keccak_config: KeccakCircuitConfig<F>,
    pub mpt_config: MPTConfig<F>,

    pub pi_mpt: MptTable,
    pub pi_instance: Column<Instance>,
    pub lookup_pi_keccak: Word<Column<Advice>>,
    pub lookup_pi_rlc_value: Column<Advice>,
    pub lookup_pi_rlc_len: Column<Advice>,

    pub is_first: Column<Fixed>,
    pub is_padding: IsZeroConfig<F>,
    pub is_last: IsZeroConfig<F>,

    pub new_root_propagation: EqualWordsConfig<F>,

    pub no_state_change_cur: EqualWordsConfig<F>,
    pub no_state_change_next: EqualWordsConfig<F>,

    pub root_chained: EqualWordsConfig<F>,

    pub count: Column<Advice>,
    pub count_decrement: IsZeroConfig<F>,

    pub q_enable: Selector,

    pub fixed_rlc: FixedRlcConfig<F>,
}

/// MPT Circuit for proving the storage modification is valid.
#[derive(Default)]
pub struct InitialStateCircuit<F: Field> {
    pub transforms: Transforms,
    #[cfg(not(feature = "disable-keccak"))]
    pub keccak_circuit: KeccakCircuit<F>,
    pub mpt_circuit: MPTCircuit<F>,
    pub lc_witness: SingleTrieModifications<F>,
    pub degree: usize,
    pub max_proof_count: usize,
}

impl<F: Field> Circuit<F> for InitialStateCircuit<F> {
    type Config = (InitialStateCircuitConfig<F>, Challenges);
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
        let mpt_config =
            MPTConfig::new(meta, challenges_expr.clone(), keccak_table.clone(), params);

        let is_first = meta.fixed_column();
        let count = meta.advice_column();
        let q_enable = meta.complex_selector();
        let pi_instance = meta.instance_column();
        let lookup_pi_keccak = word::Word::new([meta.advice_column(), meta.advice_column()]);
        let lookup_pi_rlc_value = meta.advice_column_in(SecondPhase);
        let lookup_pi_rlc_len = meta.advice_column();

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
            lookup_pi_keccak.lo(),
            lookup_pi_keccak.hi(),
            lookup_pi_rlc_value,
            lookup_pi_rlc_len,
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

        let no_state_change_cur = EqualWordsConfig::configure(
            meta,
            q_enable,
            (pi_mpt.old_root, Rotation::cur()),
            (pi_mpt.new_root, Rotation::cur()),
        );

        let no_state_change_next = EqualWordsConfig::configure(
            meta,
            q_enable,
            (pi_mpt.old_root, Rotation::next()),
            (pi_mpt.new_root, Rotation::next()),
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
            vec![q_enable * xnif(not::expr(is_padding.expr()), count_decrement.expr())]
        });

        let not_padding_nor_last_row = or::expr([is_padding.expr(), is_last.expr()]);

        meta.create_gate("if last or padding, new_root is propagated ", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_last_or_padding = or::expr([is_padding.expr(), is_last.expr()]);
            vec![q_enable * xnif(is_last_or_padding.expr(), new_root_propagation.expr())]
        });

        meta.create_gate(
            "if not last or padding, if state changed in cur row, next row must change state also",
            |meta| {
                let q_enable = meta.query_selector(q_enable);

                let if_cur_state_changes_next_too = xif(
                    not::expr(no_state_change_cur.expr()),
                    not::expr(no_state_change_next.expr()),
                );

                vec![
                    q_enable
                        * xnif(
                            not::expr(not_padding_nor_last_row.clone()),
                            if_cur_state_changes_next_too,
                        ),
                ]
            },
        );

        meta.create_gate(
            "if not padding and not last row, roots should be chained",
            |meta| {
                let q_enable = meta.query_selector(q_enable);

                vec![q_enable * xnif(not::expr(not_padding_nor_last_row), root_chained.expr())]
            },
        );

        meta.lookup_any("lc_mpt_updates lookups into mpt_table", |meta| {
            let is_not_padding = 1.expr() - is_padding.expr();

            let lookups = vec![
                (pi_mpt.proof_type, mpt_config.mpt_table.proof_type),
                (pi_mpt.address, mpt_config.mpt_table.address),
                (pi_mpt.new_value.lo(), mpt_config.mpt_table.new_value.lo()),
                (pi_mpt.new_value.hi(), mpt_config.mpt_table.new_value.hi()),
                (
                    pi_mpt.storage_key.lo(),
                    mpt_config.mpt_table.storage_key.lo(),
                ),
                (
                    pi_mpt.storage_key.hi(),
                    mpt_config.mpt_table.storage_key.hi(),
                ),
                // TODO: MPT_table new/old roots are reversed
                (pi_mpt.old_root.lo(), mpt_config.mpt_table.new_root.lo()),
                (pi_mpt.old_root.hi(), mpt_config.mpt_table.new_root.hi()),
                (pi_mpt.new_root.lo(), mpt_config.mpt_table.old_root.lo()),
                (pi_mpt.new_root.hi(), mpt_config.mpt_table.old_root.hi()),
            ];

            lookups
                .into_iter()
                .map(|(from, to)| {
                    (
                        meta.query_advice(from, Rotation::cur()) * is_not_padding.clone(),
                        meta.query_advice(to, Rotation::cur()),
                    )
                })
                .collect()
        });

        let fixed_rlc =
            FixedRlcConfig::configure(meta, &[1, 16, 20], challenges_expr.keccak_input());

        meta.lookup_any("lookup keccak from public inputs", |meta| {
            let lookups = vec![
                (lookup_pi_rlc_value, keccak_table.input_rlc),
                (lookup_pi_rlc_len, keccak_table.input_len),
                (lookup_pi_keccak.lo(), keccak_table.output.lo()),
                (lookup_pi_keccak.hi(), keccak_table.output.hi()),
            ];

            lookups
                .into_iter()
                .map(|(from, to)| {
                    (
                        meta.query_advice(from, Rotation::cur())
                            * meta.query_fixed(is_first, Rotation::cur()),
                        meta.query_advice(to, Rotation::cur()),
                    )
                })
                .collect()
        });

        let config = InitialStateCircuitConfig {
            #[cfg(not(feature = "disable-keccak"))]
            keccak_config,
            mpt_config,
            is_first,
            count,
            is_padding,
            is_last,
            count_decrement,
            new_root_propagation,
            no_state_change_cur,
            no_state_change_next,
            root_chained,
            q_enable,
            pi_instance,
            lookup_pi_keccak,
            lookup_pi_rlc_value,
            lookup_pi_rlc_len,
            pi_mpt,
            fixed_rlc,
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
        assert!(self.lc_witness.len() < self.max_proof_count);

        let challenges = _challenges.values(&mut layouter);

        // keccak value

        let (keccak_lo, keccak_hi) = layouter.assign_region(
            || "keccak value",
            |mut region| {
                let hash = self.lc_witness.initial_values_hash();
                let lo = region.assign_advice(
                    || "keccak_lo",
                    config.lookup_pi_keccak.lo(),
                    0,
                    || Value::known(hash.lo()),
                )?;
                let hi = region.assign_advice(
                    || "keccak_hi",
                    config.lookup_pi_keccak.hi(),
                    0,
                    || Value::known(hash.hi()),
                )?;
                Ok((lo, hi))
            },
        )?;
        layouter.constrain_instance(keccak_lo.cell(), config.pi_instance, 0)?;
        layouter.constrain_instance(keccak_hi.cell(), config.pi_instance, 1)?;

        // assign LC witness

        let (rlc_acc_cell, initial_value_cells) = config.fixed_rlc.assign(
            &mut layouter,
            self.lc_witness.get_padded_values(self.max_proof_count),
            self.lc_witness.initial_values_len(),
            challenges.keccak_input(),
        )?;

        layouter.assign_region(
            || "rlc",
            |mut region| {
                let rlc_acc = region.assign_advice(
                    || "rlc acc",
                    config.lookup_pi_rlc_value,
                    0,
                    || rlc_acc_cell.value().map(|v| *v),
                )?;
                region.constrain_equal(rlc_acc_cell.cell(), rlc_acc.cell())?;

                let len = F::from(self.lc_witness.initial_values_bytes().len() as u64);
                region.assign_advice(
                    || "rlc len",
                    config.lookup_pi_rlc_len,
                    0,
                    || Value::known(len),
                )
            },
        )?;

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

        layouter.assign_region(
            || "lc witness",
            |mut region| {


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

                region.name_column(|| "LC_old_root_hi", config.pi_mpt.old_root.hi());
                region.name_column(|| "LC_old_root_lo", config.pi_mpt.old_root.lo());
                region.name_column(|| "LC_new_root_hi", config.pi_mpt.new_root.hi());
                region.name_column(|| "LC_new_root_lo", config.pi_mpt.new_root.lo());
                region.name_column(|| "LC_address", config.pi_mpt.address);
                region.name_column(|| "LC_proof_type", config.pi_mpt.proof_type);
                region.name_column(|| "LC_old_value_hi", config.pi_mpt.old_value.hi());
                region.name_column(|| "LC_old_value_lo", config.pi_mpt.old_value.lo());
                region.name_column(|| "LC_new_value_hi", config.pi_mpt.new_value.hi());
                region.name_column(|| "LC_new_value_lo", config.pi_mpt.new_value.lo());
                region.name_column(|| "LC_storagekey_hi", config.pi_mpt.storage_key.hi());
                region.name_column(|| "LC_storagekey_lo", config.pi_mpt.storage_key.lo());


                let mut values = vec![];
                for offset in 0..self.max_proof_count {

                    region.assign_fixed(|| "LC_first", config.is_first, offset, || Value::known(if offset==0 { F::ONE } else { F::ZERO }))?;

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

                    config.no_state_change_cur.assign(&mut region, offset,
                        "no_state_change_cur",
                        &stm.old_root, &stm.new_root
                    )?;

                    config.no_state_change_next.assign(&mut region, offset,
                        "no_state_change_next",
                        &stm_next.old_root, &stm_next.new_root
                    )?;

                    // assign SMT inputs

                    region.assign_advice(|| "", config.count, offset, || count)?;

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


                    // at beggining, set the old root
                    if offset == 0 {
                        values.push(old_root_lo.clone());
                        values.push(old_root_hi.clone());
                        values.push(old_root_lo); // dummy values, to be replaced at the end
                        values.push(old_root_hi);
                    }

                    values.append(&mut vec![typ,addr,value_lo,value_hi, key_lo, key_hi]);

                    // at ending, set the last root in the last row (valid since we are propagating it)
                    if offset == self.max_proof_count -1 {
                        values[2] = new_root_lo;
                        values[3] = new_root_hi;
                    }

                }

                for (pos, value) in values.iter().enumerate() {
                    region.constrain_equal(value.cell(), initial_value_cells[pos].cell())?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

impl InitialStateCircuit<Fr> {
    pub fn new(
        witness: Witness<Fr>,
        degree: usize,
        max_proof_count: usize,
    ) -> Result<InitialStateCircuit<Fr>> {
        let Witness {
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
        keccak_data.push(lc_witness.initial_values_bytes());

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

        let lc_circuit = InitialStateCircuit::<Fr> {
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

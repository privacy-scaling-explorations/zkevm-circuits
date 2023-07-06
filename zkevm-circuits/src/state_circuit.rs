//! The state circuit implementation.
mod constraint_builder;
mod lexicographic_ordering;
mod lookups;
mod multiple_precision_integer;
mod param;

#[cfg(any(test, feature = "test-circuits"))]
mod dev;
#[cfg(test)]
mod test;
use bus_mapping::operation::Target;
#[cfg(feature = "test-circuits")]
pub use dev::StateCircuit as TestStateCircuit;

use self::{
    constraint_builder::{MptUpdateTableQueries, RwTableQueries},
    lexicographic_ordering::LimbIndex,
};
use crate::{
    table::{AccountFieldTag, LookupTable, MPTProofType, MptTable, RwTable, UXTable},
    util::{word, Challenges, Expr, SubCircuit, SubCircuitConfig},
    witness::{self, MptUpdates, Rw, RwMap},
};
use constraint_builder::{ConstraintBuilder, Queries};
use eth_types::{Address, Field, Word};
use gadgets::{
    batched_is_zero::{BatchedIsZeroChip, BatchedIsZeroConfig},
    binary_number::{BinaryNumberChip, BinaryNumberConfig},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, FirstPhase, Fixed, SecondPhase,
        VirtualCells,
    },
    poly::Rotation,
};
use lexicographic_ordering::Config as LexicographicOrderingConfig;
use lookups::{Chip as LookupsChip, Config as LookupsConfig, Queries as LookupsQueries};
use multiple_precision_integer::{Chip as MpiChip, Config as MpiConfig, Queries as MpiQueries};
use param::*;
use std::marker::PhantomData;

#[cfg(test)]
use std::collections::HashMap;

/// Config for StateCircuit
#[derive(Clone)]
pub struct StateCircuitConfig<F> {
    // Figure out why you get errors when this is Selector.
    selector: Column<Fixed>,
    // https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/407
    rw_table: RwTable,
    sort_keys: SortKeysConfig,
    // Assigned value at the start of the block. For Rw::Account and
    // Rw::AccountStorage rows this is the committed value in the MPT, for
    // others, it is 0.
    initial_value: word::Word<Column<Advice>>,
    // For Rw::AccountStorage, identify non-existing if both committed value and
    // new value are zero. Will do lookup for MPTProofType::NonExistingStorageProof if
    // non-existing, otherwise do lookup for MPTProofType::StorageMod.
    is_non_exist: BatchedIsZeroConfig,
    // Intermediary witness used to reduce mpt lookup expression degree
    mpt_proof_type: Column<Advice>,
    state_root: word::Word<Column<Advice>>,
    lexicographic_ordering: LexicographicOrderingConfig,
    not_first_access: Column<Advice>,
    lookups: LookupsConfig,
    // External tables
    mpt_table: MptTable,
    // External U8Table
    u8_table: UXTable<8>,
    // External U10Table
    u10_table: UXTable<10>,
    // External U16Table
    u16_table: UXTable<16>,
    _marker: PhantomData<F>,
}

/// Circuit configuration arguments
pub struct StateCircuitConfigArgs<F: Field> {
    /// RwTable
    pub rw_table: RwTable,
    /// MptTable
    pub mpt_table: MptTable,
    /// U8Table
    pub u8_table: UXTable<8>,
    /// U10Table
    pub u10_table: UXTable<10>,
    /// U16Table
    pub u16_table: UXTable<16>,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for StateCircuitConfig<F> {
    type ConfigArgs = StateCircuitConfigArgs<F>;

    /// Return a new StateCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            rw_table,
            mpt_table,
            u8_table,
            u10_table,
            u16_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        let selector = meta.fixed_column();
        let lookups = LookupsChip::configure(meta, u8_table, u10_table, u16_table);

        let rw_counter = MpiChip::configure(meta, selector, [rw_table.rw_counter], lookups);
        let tag = BinaryNumberChip::configure(meta, selector, Some(rw_table.tag));
        let id = MpiChip::configure(meta, selector, [rw_table.id], lookups);

        let address = MpiChip::configure(meta, selector, [rw_table.address], lookups);

        let storage_key = MpiChip::configure(
            meta,
            selector,
            [rw_table.storage_key.lo(), rw_table.storage_key.hi()],
            lookups,
        );
        let initial_value = word::Word::new([meta.advice_column(), meta.advice_column()]);

        let is_non_exist = BatchedIsZeroChip::configure(
            meta,
            (FirstPhase, FirstPhase),
            |meta| meta.query_fixed(selector, Rotation::cur()),
            |meta| {
                [
                    meta.query_advice(initial_value.lo(), Rotation::cur()),
                    meta.query_advice(initial_value.hi(), Rotation::cur()),
                    meta.query_advice(rw_table.value.lo(), Rotation::cur()),
                    meta.query_advice(rw_table.value.hi(), Rotation::cur()),
                ]
            },
        );
        let mpt_proof_type = meta.advice_column_in(SecondPhase);
        let state_root = word::Word::new([meta.advice_column(), meta.advice_column()]);

        let sort_keys = SortKeysConfig {
            tag,
            id,
            field_tag: rw_table.field_tag,
            address,
            storage_key,
            rw_counter,
        };

        let power_of_randomness: [Expression<F>; 31] = challenges.keccak_powers_of_randomness();
        let lexicographic_ordering =
            LexicographicOrderingConfig::configure(meta, sort_keys, lookups, power_of_randomness);

        // annotate columns
        rw_table.annotate_columns(meta);
        mpt_table.annotate_columns(meta);
        u8_table.annotate_columns(meta);
        u10_table.annotate_columns(meta);
        u16_table.annotate_columns(meta);

        let config = Self {
            selector,
            sort_keys,
            initial_value,
            is_non_exist,
            mpt_proof_type,
            state_root,
            lexicographic_ordering,
            not_first_access: meta.advice_column(),
            lookups,
            rw_table,
            mpt_table,
            u8_table,
            u10_table,
            u16_table,
            _marker: PhantomData::default(),
        };

        let mut constraint_builder = ConstraintBuilder::new();
        meta.create_gate("state circuit constraints", |meta| {
            let queries = queries(meta, &config);
            constraint_builder.build(&queries);
            constraint_builder.gate(queries.selector)
        });
        for (name, lookup) in constraint_builder.lookups() {
            meta.lookup_any(name, |_| lookup);
        }

        config
    }
}

impl<F: Field> StateCircuitConfig<F> {
    /// load fixed tables
    pub(crate) fn load_aux_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        LookupsChip::construct(self.lookups).load(layouter)
    }

    /// Make the assignments to the StateCircuit
    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        rows: &[Rw],
        n_rows: usize, // 0 means dynamically calculated from `rows`.
    ) -> Result<(), Error> {
        let updates = MptUpdates::mock_from(rows);
        layouter.assign_region(
            || "state circuit",
            |mut region| self.assign_with_region(&mut region, rows, &updates, n_rows),
        )
    }

    fn assign_with_region(
        &self,
        region: &mut Region<'_, F>,
        rows: &[Rw],
        updates: &MptUpdates,
        n_rows: usize, // 0 means dynamically calculated from `rows`.
    ) -> Result<(), Error> {
        let tag_chip = BinaryNumberChip::construct(self.sort_keys.tag);

        let (rows, padding_length) = RwMap::table_assignments_prepad(rows, n_rows);
        let rows_len = rows.len();

        let mut state_root = updates.old_root();

        // annotate columns
        self.annotate_circuit_in_region(region);

        for (offset, row) in rows.iter().enumerate() {
            if offset >= padding_length {
                log::trace!("state circuit assign offset:{} row:{:#?}", offset, row);
            }

            region.assign_fixed(
                || "selector",
                self.selector,
                offset,
                || Value::known(F::ONE),
            )?;

            tag_chip.assign(region, offset, &row.tag())?;

            self.sort_keys
                .rw_counter
                .assign(region, offset, row.rw_counter() as u32)?;

            if let Some(id) = row.id() {
                self.sort_keys.id.assign(region, offset, id as u32)?;
            }

            if let Some(address) = row.address() {
                self.sort_keys.address.assign(region, offset, address)?;
            }

            if let Some(storage_key) = row.storage_key() {
                self.sort_keys
                    .storage_key
                    .assign(region, offset, storage_key)?;
            }

            if offset > 0 {
                let prev_row = &rows[offset - 1];
                let index = self
                    .lexicographic_ordering
                    .assign(region, offset, row, prev_row)?;
                let is_first_access =
                    !matches!(index, LimbIndex::RwCounter0 | LimbIndex::RwCounter1);

                region.assign_advice(
                    || "not_first_access",
                    self.not_first_access,
                    offset,
                    || Value::known(if is_first_access { F::ZERO } else { F::ONE }),
                )?;

                if is_first_access {
                    // If previous row was a last access, we need to update the state root.
                    if let Some(update) = updates.get(prev_row) {
                        let (new_root, old_root) = update.root_assignments();
                        assert_eq!(state_root, old_root);
                        state_root = new_root;
                    }
                    if matches!(row.tag(), Target::CallContext) && !row.is_write() {
                        assert_eq!(row.value_assignment(), 0.into(), "{:?}", row);
                    }
                }
            }

            // The initial value can be determined from the mpt updates or is 0.
            let initial_value = word::Word::<F>::from(
                updates
                    .get(row)
                    .map(|u| u.value_assignments().1)
                    .unwrap_or_default(),
            );

            initial_value.into_value().assign_advice(
                region,
                || "initial_value",
                self.initial_value,
                offset,
            )?;

            // Identify non-existing if both committed value and new value are zero.
            let (committed_value, value) = {
                let (_, committed_value) = updates
                    .get(row)
                    .map(|u| u.value_assignments())
                    .unwrap_or_default();
                let value = row.value_assignment();
                (
                    word::Word::<F>::from(committed_value),
                    word::Word::<F>::from(value),
                )
            };

            BatchedIsZeroChip::construct(self.is_non_exist.clone()).assign(
                region,
                offset,
                Value::known([
                    committed_value.lo(),
                    committed_value.hi(),
                    value.lo(),
                    value.hi(),
                ]),
            )?;

            let mpt_proof_type = match row {
                Rw::AccountStorage { .. } => {
                    if committed_value.is_zero_vartime() && value.is_zero_vartime() {
                        MPTProofType::NonExistingStorageProof as u64
                    } else {
                        MPTProofType::StorageMod as u64
                    }
                }
                Rw::Account { field_tag, .. } => {
                    if committed_value.is_zero_vartime()
                        && value.is_zero_vartime()
                        && matches!(field_tag, AccountFieldTag::CodeHash)
                    {
                        MPTProofType::NonExistingAccountProof as u64
                    } else {
                        *field_tag as u64
                    }
                }
                _ => 0,
            };

            region.assign_advice(
                || "mpt_proof_type",
                self.mpt_proof_type,
                offset,
                || Value::known(F::from(mpt_proof_type)),
            )?;

            // TODO: Switch from Rw::Start -> Rw::Padding to simplify this logic.
            // State root assignment is at previous row (offset - 1) because the state root
            // changes on the last access row.
            if offset != 0 {
                word::Word::<F>::from(state_root)
                    .into_value()
                    .assign_advice(region, || "state root", self.state_root, offset - 1)?;
            }

            if offset == rows_len - 1 {
                // The last row is always a last access, so we need to handle the case where the
                // state root changes because of an mpt lookup on the last row.
                if let Some(update) = updates.get(row) {
                    state_root = {
                        let (new_root, old_root) = update.root_assignments();
                        assert_eq!(state_root, old_root);
                        new_root
                    };
                }
                word::Word::<F>::from(state_root)
                    .into_value()
                    .assign_advice(region, || "last row state_root", self.state_root, offset)?;
            }
        }

        Ok(())
    }

    fn annotate_circuit_in_region(&self, region: &mut Region<F>) {
        self.rw_table.annotate_columns_in_region(region);
        self.mpt_table.annotate_columns_in_region(region);
        self.is_non_exist
            .annotate_columns_in_region(region, "STATE");
        self.lexicographic_ordering
            .annotate_columns_in_region(region, "STATE");
        self.sort_keys.annotate_columns_in_region(region, "STATE");
        region.name_column(|| "STATE_selector", self.selector);
        region.name_column(|| "STATE_not_first_access", self.not_first_access);
        region.name_column(|| "STATE_initial_value lo", self.initial_value.lo());
        region.name_column(|| "STATE_initial_value hi", self.initial_value.hi());
        region.name_column(|| "STATE_mpt_proof_type", self.mpt_proof_type);
        region.name_column(|| "STATE_state_root lo", self.state_root.lo());
        region.name_column(|| "STATE_state_root hi", self.state_root.hi());
    }
}

/// Keys for sorting the rows of the state circuit
#[derive(Clone, Copy)]
pub struct SortKeysConfig {
    tag: BinaryNumberConfig<Target, 4>,
    id: MpiConfig<u32, N_LIMBS_ID>,
    address: MpiConfig<Address, N_LIMBS_ACCOUNT_ADDRESS>,
    field_tag: Column<Advice>,
    storage_key: MpiConfig<Word, N_LIMBS_WORD>,
    rw_counter: MpiConfig<u32, N_LIMBS_RW_COUNTER>,
}

impl SortKeysConfig {
    /// Annotates this config within a circuit region.
    pub fn annotate_columns_in_region<F: Field>(&self, region: &mut Region<F>, prefix: &str) {
        self.tag.annotate_columns_in_region(region, prefix);
        self.address.annotate_columns_in_region(region, prefix);
        self.id.annotate_columns_in_region(region, prefix);
        self.storage_key.annotate_columns_in_region(region, prefix);
        self.rw_counter.annotate_columns_in_region(region, prefix);
        region.name_column(|| format!("{}_field_tag", prefix), self.field_tag);
    }
}

type Lookup<F> = (&'static str, Expression<F>, Expression<F>);

/// State Circuit for proving RwTable is valid
#[derive(Default, Clone, Debug)]
pub struct StateCircuit<F> {
    /// Rw rows
    pub rows: Vec<Rw>,
    updates: MptUpdates,
    pub(crate) n_rows: usize,
    #[cfg(test)]
    overrides: HashMap<(dev::AdviceColumn, isize), F>,
    _marker: PhantomData<F>,
}

impl<F: Field> StateCircuit<F> {
    /// make a new state circuit from an RwMap
    pub fn new(rw_map: RwMap, n_rows: usize) -> Self {
        let rows = rw_map.table_assignments();
        let updates = MptUpdates::mock_from(&rows);
        Self {
            rows,
            updates,
            n_rows,
            #[cfg(test)]
            overrides: HashMap::new(),
            _marker: PhantomData::default(),
        }
    }
}

impl<F: Field> SubCircuit<F> for StateCircuit<F> {
    type Config = StateCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        Self::new(block.rws.clone(), block.circuits_params.max_rws)
    }

    fn unusable_rows() -> usize {
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            block.rws.0.values().flatten().count() + 1,
            block.circuits_params.max_rws,
        )
    }

    /// Make the assignments to the StateCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        _challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load_aux_tables(layouter)?;

        // Assigning to same columns in different regions should be avoided.
        // Here we use one single region to assign `overrides` to both rw table and
        // other parts.
        layouter.assign_region(
            || "state circuit",
            |mut region| {
                config
                    .rw_table
                    .load_with_region(&mut region, &self.rows, self.n_rows)?;

                config.assign_with_region(&mut region, &self.rows, &self.updates, self.n_rows)?;
                #[cfg(test)]
                {
                    let first_non_padding_index = if self.rows.len() < self.n_rows {
                        RwMap::padding_len(self.rows.len(), self.n_rows)
                    } else {
                        1 // at least 1 StartOp padding in idx 0, so idx 1 is first non-padding row
                    };

                    for ((column, row_offset), &f) in &self.overrides {
                        let advice_column = column.value(config);
                        let offset = usize::try_from(
                            isize::try_from(first_non_padding_index).unwrap() + *row_offset,
                        )
                        .unwrap();
                        region.assign_advice(
                            || "override",
                            advice_column,
                            offset,
                            || Value::known(f),
                        )?;
                    }
                }

                Ok(())
            },
        )
    }

    /// powers of randomness for instance columns
    fn instance(&self) -> Vec<Vec<F>> {
        vec![]
    }
}

fn queries<F: Field>(meta: &mut VirtualCells<'_, F>, c: &StateCircuitConfig<F>) -> Queries<F> {
    let first_different_limb = c.lexicographic_ordering.first_different_limb;
    let final_bits_sum = meta.query_advice(first_different_limb.bits[3], Rotation::cur())
        + meta.query_advice(first_different_limb.bits[4], Rotation::cur());
    let mpt_update_table_expressions = c.mpt_table.table_exprs(meta);
    assert_eq!(mpt_update_table_expressions.len(), 12);

    let meta_query_word =
        |metap: &mut VirtualCells<'_, F>, word_column: word::Word<Column<Advice>>, at: Rotation| {
            word::Word::new([
                metap.query_advice(word_column.lo(), at),
                metap.query_advice(word_column.hi(), at),
            ])
        };

    Queries {
        selector: meta.query_fixed(c.selector, Rotation::cur()),
        // TODO: use LookupTable trait here.
        rw_table: RwTableQueries {
            rw_counter: meta.query_advice(c.rw_table.rw_counter, Rotation::cur()),
            prev_rw_counter: meta.query_advice(c.rw_table.rw_counter, Rotation::prev()),
            is_write: meta.query_advice(c.rw_table.is_write, Rotation::cur()),
            tag: meta.query_advice(c.rw_table.tag, Rotation::cur()),
            id: meta.query_advice(c.rw_table.id, Rotation::cur()),
            prev_id: meta.query_advice(c.rw_table.id, Rotation::prev()),
            address: meta.query_advice(c.rw_table.address, Rotation::cur()),
            prev_address: meta.query_advice(c.rw_table.address, Rotation::prev()),
            field_tag: meta.query_advice(c.rw_table.field_tag, Rotation::cur()),
            storage_key: meta_query_word(meta, c.rw_table.storage_key, Rotation::cur()),
            value: meta_query_word(meta, c.rw_table.value, Rotation::cur()),
            value_prev: meta_query_word(meta, c.rw_table.value, Rotation::prev()),
            value_prev_column: meta_query_word(meta, c.rw_table.value_prev, Rotation::cur()),
        },
        // TODO: clean this up
        mpt_update_table: MptUpdateTableQueries {
            address: mpt_update_table_expressions[0].clone(),
            storage_key: word::Word::new([
                mpt_update_table_expressions[1].clone(),
                mpt_update_table_expressions[2].clone(),
            ]),
            proof_type: mpt_update_table_expressions[3].clone(),
            new_root: word::Word::new([
                mpt_update_table_expressions[4].clone(),
                mpt_update_table_expressions[5].clone(),
            ]),
            old_root: word::Word::new([
                mpt_update_table_expressions[6].clone(),
                mpt_update_table_expressions[7].clone(),
            ]),
            new_value: word::Word::new([
                mpt_update_table_expressions[8].clone(),
                mpt_update_table_expressions[9].clone(),
            ]),
            old_value: word::Word::new([
                mpt_update_table_expressions[10].clone(),
                mpt_update_table_expressions[11].clone(),
            ]),
        },
        lexicographic_ordering_selector: meta
            .query_fixed(c.lexicographic_ordering.selector, Rotation::cur()),
        rw_counter: MpiQueries::new(meta, c.sort_keys.rw_counter),
        tag_bits: c
            .sort_keys
            .tag
            .bits
            .map(|bit| meta.query_advice(bit, Rotation::cur())),
        id: MpiQueries::new(meta, c.sort_keys.id),
        // this isn't binary! only 0 if most significant 3 bits are all 0 and at most 1 of the two
        // least significant bits is 1.
        // TODO: this can mask off just the top 3 bits if you want, since the 4th limb index is
        // Address9, which is always 0 for Rw::Stack rows.
        is_tag_and_id_unchanged: 4.expr()
            * (meta.query_advice(first_different_limb.bits[0], Rotation::cur())
                + meta.query_advice(first_different_limb.bits[1], Rotation::cur())
                + meta.query_advice(first_different_limb.bits[2], Rotation::cur()))
            + final_bits_sum.clone() * (1.expr() - final_bits_sum),
        address: MpiQueries::new(meta, c.sort_keys.address),
        storage_key: MpiQueries::new(meta, c.sort_keys.storage_key),
        initial_value: meta_query_word(meta, c.initial_value, Rotation::cur()),
        initial_value_prev: meta_query_word(meta, c.initial_value, Rotation::prev()),
        is_non_exist: meta.query_advice(c.is_non_exist.is_zero, Rotation::cur()),
        mpt_proof_type: meta.query_advice(c.mpt_proof_type, Rotation::cur()),
        lookups: LookupsQueries::new(meta, c.lookups),
        first_different_limb: [0, 1, 2, 3]
            .map(|idx| meta.query_advice(first_different_limb.bits[idx], Rotation::cur())),
        not_first_access: meta.query_advice(c.not_first_access, Rotation::cur()),
        last_access: 1.expr() - meta.query_advice(c.not_first_access, Rotation::next()),
        state_root: meta_query_word(meta, c.state_root, Rotation::cur()),
        state_root_prev: meta_query_word(meta, c.state_root, Rotation::prev()),
    }
}

//! The state circuit implementation.
mod constraint_builder;
mod lexicographic_ordering;
mod lookups;
mod multiple_precision_integer;
mod random_linear_combination;
#[cfg(test)]
mod state_tests;

use crate::{
    evm_circuit::{
        param::N_BYTES_WORD,
        util::RandomLinearCombination,
        witness::{Rw, RwMap, RwRow},
    },
    rw_table::RwTable,
};
use constraint_builder::{ConstraintBuilder, Queries};
use eth_types::{Address, Field, ToLittleEndian};
use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, VirtualCells,
    },
    poly::Rotation,
};
use lexicographic_ordering::{
    Chip as LexicographicOrderingChip, Config as LexicographicOrderingConfig,
};
use lookups::{Chip as LookupsChip, Config as LookupsConfig, Queries as LookupsQueries};
use multiple_precision_integer::{Chip as MpiChip, Config as MpiConfig, Queries as MpiQueries};
use random_linear_combination::{Chip as RlcChip, Config as RlcConfig, Queries as RlcQueries};

const N_LIMBS_RW_COUNTER: usize = 2;
const N_LIMBS_ACCOUNT_ADDRESS: usize = 10;
const N_LIMBS_ID: usize = 2;

/// Config for StateCircuit
#[derive(Clone)]
pub struct StateConfig<F: Field> {
    // Figure out why you get errors when this is Selector.
    // https://github.com/appliedzkp/zkevm-circuits/issues/407
    selector: Column<Fixed>,

    rw_table: RwTable,

    rw_counter_mpi: MpiConfig<u32, N_LIMBS_RW_COUNTER>,
    //is_write: Column<Advice>,
    //tag: Column<Advice>,
    id_mpi: MpiConfig<u32, N_LIMBS_ID>,
    address_mpi: MpiConfig<Address, N_LIMBS_ACCOUNT_ADDRESS>,
    //field_tag: Column<Advice>,
    storage_key_rlc: RlcConfig<N_BYTES_WORD>,
    //value: Column<Advice>,
    is_storage_key_unchanged: IsZeroConfig<F>,
    lookups: LookupsConfig,
    power_of_randomness: [Column<Instance>; N_BYTES_WORD - 1],
    lexicographic_ordering: LexicographicOrderingConfig<F>,
}

type Lookup<F> = (&'static str, Expression<F>, Expression<F>);

/// State Circuit for proving RwTable is valid
#[derive(Default)]
pub struct StateCircuit<F: Field> {
    pub(crate) randomness: F,
    pub(crate) rows: Vec<Rw>,
}

impl<F: Field> StateCircuit<F> {
    /// make a new state circuit
    pub fn new(randomness: F, rw_map: RwMap) -> Self {
        let mut rows: Vec<_> = rw_map.0.into_values().flatten().collect();
        rows.sort_by_key(|row| {
            (
                row.tag() as u64,
                row.field_tag().unwrap_or_default(),
                row.id().unwrap_or_default(),
                row.address().unwrap_or_default(),
                row.storage_key().unwrap_or_default(),
                row.rw_counter(),
            )
        });
        Self { randomness, rows }
    }

    /// powers of randomness for instance columns
    pub fn instance(&self) -> Vec<Vec<F>> {
        (1..32)
            .map(|exp| vec![self.randomness.pow(&[exp, 0, 0, 0]); self.rows.len()])
            .collect()
    }

    fn assign_row(
        &self,
        config: &StateConfig<F>,
        region: &mut Region<F>,
        is_storage_key_unchanged: &IsZeroChip<F>,
        lexicographic_ordering_chip: &LexicographicOrderingChip<F>,
        offset: usize,
        row: RwRow<F>,
        prev_row: Option<RwRow<F>>,
    ) -> Result<(), Error> {
        // step 1: assign selector
        if offset != 0 {
            region.assign_fixed(|| "selector", config.selector, offset, || Ok(F::one()))?;
        }
        // step 2: assign lexicographic_ordering_chip
        // we deliberately don't reuse the "offset == 0" if clause
        if offset != 0 {
            let rw_keys = row.rw_keys();
            let prev_rw_keys = prev_row
                .expect("prev_row is empty only for first row")
                .rw_keys();
            lexicographic_ordering_chip.assign(region, offset, &rw_keys, &prev_rw_keys)?;
        }

        config
            .rw_table
            .assign(region, offset, self.randomness, &row)?;

        config
            .rw_counter_mpi
            .assign(region, offset, row.rw_counter as u32)?;
        config.id_mpi.assign(region, offset, row.id as u32)?;
        config.address_mpi.assign(region, offset, row.address)?;

        config
            .storage_key_rlc
            .assign(region, offset, self.randomness, row.storage_key)?;
        let cur_storage_key = RandomLinearCombination::random_linear_combine(
            row.storage_key.to_le_bytes(),
            self.randomness,
        );
        let prev_storage_key = RandomLinearCombination::random_linear_combine(
            prev_row.unwrap_or_default().storage_key.to_le_bytes(),
            self.randomness,
        );
        is_storage_key_unchanged.assign(
            region,
            offset,
            Some(cur_storage_key - prev_storage_key),
        )?;

        Ok(())
    }
}

impl<F: Field> Circuit<F> for StateCircuit<F> {
    type Config = StateConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let selector = meta.fixed_column();
        let lookups = LookupsChip::configure(meta);
        let power_of_randomness = [0; N_BYTES_WORD - 1].map(|_| meta.instance_column());

        let rw_table = RwTable::construct(meta);
        let is_zero_chip_advice_column = meta.advice_column();
        let id_mpi = MpiChip::configure(meta, rw_table.id, selector);
        let address_mpi = MpiChip::configure(meta, rw_table.address, selector);
        let storage_key_rlc = RlcChip::configure(
            meta,
            selector,
            rw_table.storage_key,
            lookups.u8,
            power_of_randomness,
        );
        let rw_counter_mpi = MpiChip::configure(meta, rw_table.rw_counter, selector);

        let is_storage_key_unchanged = IsZeroChip::configure(
            meta,
            |meta| meta.query_fixed(selector, Rotation::cur()),
            |meta| {
                meta.query_advice(rw_table.storage_key, Rotation::cur())
                    - meta.query_advice(rw_table.storage_key, Rotation::prev())
            },
            is_zero_chip_advice_column,
        );

        let config = Self::Config {
            selector,
            address_mpi,
            id_mpi,
            rw_counter_mpi,
            storage_key_rlc,
            lexicographic_ordering: LexicographicOrderingChip::configure(
                meta,
                selector,
                rw_table.tag,
                rw_table.field_tag,
                id_mpi.limbs,
                address_mpi.limbs,
                storage_key_rlc.bytes,
                rw_counter_mpi.limbs,
                //lookups.u16,
            ),
            is_storage_key_unchanged,
            lookups,
            power_of_randomness,
            rw_table,
        };

        let mut constraint_builder = ConstraintBuilder::new();
        meta.create_gate("state circuit constraints", |meta| {
            let queries = queries(meta, &config);
            constraint_builder.build(&queries);
            constraint_builder.gate(queries.selector)
        });
        for (name, expressions) in constraint_builder.lookups() {
            meta.lookup_any(name, |_| vec![expressions]);
        }

        config
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        println!("synthesize begin");
        LookupsChip::construct(config.lookups).load(&mut layouter)?;
        let is_storage_key_unchanged =
            IsZeroChip::construct(config.is_storage_key_unchanged.clone());

        let lexicographic_ordering_chip =
            LexicographicOrderingChip::construct(config.lexicographic_ordering.clone());

        layouter.assign_region(
            || "assign rw table",
            |mut region| {
                let mut prev_row: Option<RwRow<F>> = None;
                let mut offset = 0;

                for row in self.rows.iter() {
                    println!("offset {} row {:#?}", offset, row);

                    let row: RwRow<F> = row.table_assignment(self.randomness);

                    // check if we need to insert an initial row before the real row
                    if prev_row.is_none()
                        || !row.rw_keys().is_same_access(&prev_row.unwrap().rw_keys())
                    {
                        // need to insert a initial row
                        let mut initial_row = row;
                        // TODO: set default value correctly
                        // rw_counter == 0 means this is an "initial row"
                        initial_row.rw_counter = 0;

                        // assign this initial row
                        self.assign_row(
                            &config,
                            &mut region,
                            &is_storage_key_unchanged,
                            &lexicographic_ordering_chip,
                            offset,
                            initial_row,
                            prev_row,
                        )?;
                        offset += 1;
                        prev_row = Some(initial_row);
                    }

                    self.assign_row(
                        &config,
                        &mut region,
                        &is_storage_key_unchanged,
                        &lexicographic_ordering_chip,
                        offset,
                        row,
                        prev_row,
                    )?;
                    prev_row = Some(row);
                    offset += 1;
                }
                Ok(())
            },
        )
    }
}

fn queries<F: Field>(meta: &mut VirtualCells<'_, F>, c: &StateConfig<F>) -> Queries<F> {
    Queries {
        selector: meta.query_fixed(c.selector, Rotation::cur()),
        rw_counter: MpiQueries::new(meta, c.rw_counter_mpi),
        is_write: meta.query_advice(c.rw_table.is_write, Rotation::cur()),
        tag: meta.query_advice(c.rw_table.tag, Rotation::cur()),
        prev_tag: meta.query_advice(c.rw_table.tag, Rotation::prev()),
        id: MpiQueries::new(meta, c.id_mpi),
        address: MpiQueries::new(meta, c.address_mpi),
        field_tag: meta.query_advice(c.rw_table.field_tag, Rotation::cur()),
        storage_key: RlcQueries::new(meta, c.storage_key_rlc),
        value: meta.query_advice(c.rw_table.value, Rotation::cur()),
        lookups: LookupsQueries::new(meta, c.lookups),
        power_of_randomness: c
            .power_of_randomness
            .map(|c| meta.query_instance(c, Rotation::cur())),
        is_storage_key_unchanged: c.is_storage_key_unchanged.is_zero_expression.clone(),
        lexicographic_ordering_upper_limb_difference_is_zero: c
            .lexicographic_ordering
            .upper_limb_difference_is_zero
            .is_zero_expression
            .clone(),
    }
}

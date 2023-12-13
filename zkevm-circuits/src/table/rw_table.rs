use bus_mapping::operation::OperationContainer;
use halo2_proofs::{
    self,
    circuit::{AssignedCell, SimpleFloorPlanner},
    halo2curves::ff::{BatchInvert, WithSmallOrderMulGroup},
};

use halo2_proofs::{
    halo2curves::{bn256::Fr, group::Curve, CurveAffine},
    plonk::{Advice, Assigned, Assignment, Challenge, Fixed, FloorPlanner, Instance, Selector},
    poly::{
        commitment::{Blind, CommitmentScheme, Params},
        EvaluationDomain, LagrangeCoeff, Polynomial,
    },
};
use snark_verifier::util::arithmetic::PrimeCurveAffine;

use super::*;

/// The RwTable shared between EVM Circuit and State Circuit, which contains
/// traces of the EVM state operations.
#[derive(Clone, Copy, Debug)]
pub struct RwTable {
    /// Read Write Counter
    pub rw_counter: Column<Advice>,
    /// Is Write
    pub is_write: Column<Advice>,
    /// Tag
    pub tag: Column<Advice>,
    /// Key1 (Id)
    pub id: Column<Advice>,
    /// Key2 (Address)
    pub address: Column<Advice>,
    /// Key3 (FieldTag)
    pub field_tag: Column<Advice>,
    /// Key3 (StorageKey)
    pub storage_key: word::Word<Column<Advice>>,
    /// Value
    pub value: word::Word<Column<Advice>>,
    /// Value Previous
    pub value_prev: word::Word<Column<Advice>>,
    /// InitVal (Committed Value)
    pub init_val: word::Word<Column<Advice>>,
}

impl<F: Field> LookupTable<F> for RwTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.rw_counter.into(),
            self.is_write.into(),
            self.tag.into(),
            self.id.into(),
            self.address.into(),
            self.field_tag.into(),
            self.storage_key.lo().into(),
            self.storage_key.hi().into(),
            self.value.lo().into(),
            self.value.hi().into(),
            self.value_prev.lo().into(),
            self.value_prev.hi().into(),
            self.init_val.lo().into(),
            self.init_val.hi().into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("rw_counter"),
            String::from("is_write"),
            String::from("tag"),
            String::from("id"),
            String::from("address"),
            String::from("field_tag"),
            String::from("storage_key_lo"),
            String::from("storage_key_hi"),
            String::from("value_lo"),
            String::from("value_hi"),
            String::from("value_prev_lo"),
            String::from("value_prev_hi"),
            String::from("init_val_lo"),
            String::from("init_val_hi"),
        ]
    }
}

impl RwTable {
    /// Construct a new RwTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            // TODO upgrade halo2 to use `unblinded_advice_column`
            // https://github.com/privacy-scaling-explorations/halo2/blob/main/halo2_proofs/examples/vector-ops-unblinded.rs
            // rw_counter: meta.unblinded_advice_column(),
            // is_write: meta.unblinded_advice_column(),
            // tag: meta.unblinded_advice_column(),
            // id: meta.unblinded_advice_column(),
            // address: meta.unblinded_advice_column(),
            // field_tag: meta.unblinded_advice_column(),
            // storage_key: word::Word::new([meta.unblinded_advice_column(),
            // meta.unblinded_advice_column()]), value: word::Word::new([meta.
            // unblinded_advice_column(), meta.unblinded_advice_column()]), value_prev:
            // word::Word::new([meta.unblinded_advice_column(), meta.unblinded_advice_column()]),
            // init_val: word::Word::new([meta.unblinded_advice_column(),
            // meta.unblinded_advice_column()]),
            rw_counter: meta.advice_column(),
            is_write: meta.advice_column(),
            tag: meta.advice_column(),
            id: meta.advice_column(),
            address: meta.advice_column(),
            field_tag: meta.advice_column(),
            storage_key: word::Word::new([meta.advice_column(), meta.advice_column()]),
            value: word::Word::new([meta.advice_column(), meta.advice_column()]),
            value_prev: word::Word::new([meta.advice_column(), meta.advice_column()]),
            init_val: word::Word::new([meta.advice_column(), meta.advice_column()]),
        }
    }
    fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &RwRow<Value<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let mut assigned_cells = vec![];
        for (column, value) in [
            (self.rw_counter, row.rw_counter),
            (self.is_write, row.is_write),
            (self.tag, row.tag),
            (self.id, row.id),
            (self.address, row.address),
            (self.field_tag, row.field_tag),
        ] {
            assigned_cells.push(region.assign_advice(
                || "assign rw row on rw table",
                column,
                offset,
                || value,
            )?);
        }
        for (column, value) in [
            (self.storage_key, row.storage_key),
            (self.value, row.value),
            (self.value_prev, row.value_prev),
            (self.init_val, row.init_val),
        ] {
            assigned_cells.extend(
                value
                    .assign_advice(region, || "assign rw row on rw table", column, offset)?
                    .limbs
                    .clone(),
            );
        }

        Ok(assigned_cells)
    }

    /// Assign the `RwTable` from a `RwMap`, following the same
    /// table layout that the State Circuit uses.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        rws: &[Rw],
        n_rows: usize,
        is_first_row_padding: bool,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "rw table",
            |mut region| self.load_with_region(&mut region, rws, n_rows, is_first_row_padding),
        )
    }

    pub(crate) fn load_with_region<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        rws: &[Rw],
        n_rows: usize,
        is_first_row_padding: bool,
    ) -> Result<(), Error> {
        let (rows, _) = RwMap::table_assignments_padding(rws, n_rows, is_first_row_padding);
        for (offset, row) in rows.iter().enumerate() {
            self.assign(region, offset, &row.table_assignment())?;
        }
        Ok(())
    }
}

/// get rw table column commitment
/// implementation snippet from halo2 `create_proof` https://github.com/privacy-scaling-explorations/halo2/blob/9b33f9ce524dbb9133fc8b9638b2afd0571659a8/halo2_proofs/src/plonk/prover.rs#L37
pub fn get_rwtable_cols_commitment<'params, Scheme: CommitmentScheme>(
    degree: usize,
    rws: &[Rw],
    n_rows: usize,
    params_prover: &'params Scheme::ParamsProver,
    is_first_row_padding: bool,
) -> Vec<<Scheme as CommitmentScheme>::Curve>
where
    <Scheme as CommitmentScheme>::Scalar: WithSmallOrderMulGroup<3> + Field,
{
    struct WitnessCollection<F: Field> {
        k: u32,
        advice: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
        _marker: std::marker::PhantomData<F>,
    }

    impl<'a, F: Field> Assignment<F> for WitnessCollection<F> {
        fn enter_region<NR, N>(&mut self, _: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            // Do nothing; we don't care about regions in this context.
        }

        fn exit_region(&mut self) {
            // Do nothing; we don't care about regions in this context.
        }

        fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            // We only care about advice columns here

            Ok(())
        }

        fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
        where
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            // Do nothing
        }

        fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
            Err(Error::BoundsFailure)
        }

        fn assign_advice<V, VR, A, AR>(
            &mut self,
            _: A,
            column: Column<Advice>,
            row: usize,
            to: V,
        ) -> Result<(), Error>
        where
            V: FnOnce() -> Value<VR>,
            VR: Into<Assigned<F>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            to().into_field().map(|v| {
                *self
                    .advice
                    .get_mut(column.index())
                    .and_then(|v| v.get_mut(row))
                    .ok_or(Error::BoundsFailure)
                    .unwrap() = v;
            });
            Ok(())
        }

        fn assign_fixed<V, VR, A, AR>(
            &mut self,
            _: A,
            _: Column<Fixed>,
            _: usize,
            _: V,
        ) -> Result<(), Error>
        where
            V: FnOnce() -> Value<VR>,
            VR: Into<Assigned<F>>,
            A: FnOnce() -> AR,
            AR: Into<String>,
        {
            // We only care about advice columns here

            Ok(())
        }

        fn copy(
            &mut self,
            _: Column<Any>,
            _: usize,
            _: Column<Any>,
            _: usize,
        ) -> Result<(), Error> {
            // We only care about advice columns here

            Ok(())
        }

        fn fill_from_row(
            &mut self,
            _: Column<Fixed>,
            _: usize,
            _: Value<Assigned<F>>,
        ) -> Result<(), Error> {
            Ok(())
        }

        fn get_challenge(&self, challenge: Challenge) -> Value<F> {
            Value::unknown()
        }

        fn push_namespace<NR, N>(&mut self, _: N)
        where
            NR: Into<String>,
            N: FnOnce() -> NR,
        {
            // Do nothing; we don't care about namespaces in this context.
        }

        fn pop_namespace(&mut self, _: Option<String>) {
            // Do nothing; we don't care about namespaces in this context.
        }
    }

    let rw_map = RwMap::from(&OperationContainer {
        ..Default::default()
    });
    let rows = rw_map.table_assignments(false);
    let rwtable_circuit = RwTableCircuit::new(&rows, 1, false);

    let domain = EvaluationDomain::<<Scheme as CommitmentScheme>::Scalar>::new(
        degree as u32,
        params_prover.k(),
    );

    let mut cs = ConstraintSystem::default();
    let rwtable_circuit_config = RwTableCircuit::configure(&mut cs);
    // TODO adjust domain.empty_lagrange_assigned() visibility in halo2 library to public
    let mut witness = WitnessCollection {
        k: params_prover.k(),
        advice: vec![
            domain.empty_lagrange_assigned();
            rwtable_circuit_config.rw_table.advice_columns().len()
        ],
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain the witness and other information.
    <RwTableCircuit<'_> as Circuit<Fr>>::FloorPlanner::synthesize(
        &mut witness,
        &rwtable_circuit,
        rwtable_circuit_config,
        cs.constants().clone(),
    )
    .unwrap();

    let mut advice_values =
        batch_invert_assigned::<Scheme::Scalar>(domain, witness.advice.into_iter().collect());

    // Compute commitments to advice column polynomials
    let blinds = vec![Blind::default(); witness.advice.len()];
    let advice_commitments_projective: Vec<_> = advice_values
        .iter()
        .zip(blinds.iter())
        .map(|(poly, blind)| params_prover.commit_lagrange(poly, *blind))
        .collect();
    let mut advice_commitments =
        vec![Scheme::Curve::identity(); advice_commitments_projective.len()];

    <Scheme::Curve as CurveAffine>::CurveExt::batch_normalize(
        &advice_commitments_projective,
        &mut advice_commitments,
    );

    advice_commitments
}

struct RwTableCircuit<'a> {
    rws: &'a [Rw],
    n_rows: usize,
    is_first_row_padding: bool,
}

impl<'a> RwTableCircuit<'a> {
    #[allow(dead_code)]
    pub(crate) fn new(rws: &'a [Rw], n_rows: usize, is_first_row_padding: bool) -> Self {
        Self {
            rws,
            n_rows,
            is_first_row_padding,
        }
    }
}

#[derive(Clone)]
struct RwTableCircuitConfig {
    pub rw_table: RwTable,
}

impl<'a> RwTableCircuitConfig {}

impl<'a, F: Field> Circuit<F> for RwTableCircuit<'a> {
    type Config = RwTableCircuitConfig;

    type FloorPlanner = SimpleFloorPlanner;

    type Params = ();

    fn without_witnesses(&self) -> Self {
        todo!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        RwTableCircuitConfig {
            rw_table: RwTable::construct(meta),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "XXXX",
            |mut region| {
                config.rw_table.load_with_region(
                    &mut region,
                    self.rws,
                    self.n_rows,
                    self.is_first_row_padding,
                )
            },
        )?;
        Ok(())
    }
}

// migrate from halo2 library
fn batch_invert_assigned<F: Field + WithSmallOrderMulGroup<3>>(
    domain: EvaluationDomain<F>,
    assigned: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
) -> Vec<Polynomial<F, LagrangeCoeff>> {
    let mut assigned_denominators: Vec<_> = assigned
        .iter()
        .map(|f| {
            f.iter()
                .map(|value| value.denominator())
                .collect::<Vec<_>>()
        })
        .collect();

    assigned_denominators
        .iter_mut()
        .flat_map(|f| {
            f.iter_mut()
                // If the denominator is trivial, we can skip it, reducing the
                // size of the batch inversion.
                .filter_map(|d| d.as_mut())
        })
        .batch_invert();

    assigned
        .iter()
        .zip(assigned_denominators.into_iter())
        .map(|(poly, inv_denoms)| {
            let inv_denoms = inv_denoms.into_iter().map(|d| d.unwrap_or(F::ONE));
            domain.lagrange_from_vec(
                poly.iter()
                    .zip(inv_denoms.into_iter())
                    .map(|(a, inv_den)| a.numerator() * inv_den)
                    .collect(),
            )
        })
        .collect()
}

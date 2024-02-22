//! Utility functions and types to get circuit stats from any halo2 circuit

use eth_types::Field;
use halo2_proofs::plonk::ConstraintSystem;
use std::collections::BTreeSet;

// From Scroll https://github.com/scroll-tech/zkevm-circuits/blob/7d9bc181953cfc6e7baf82ff0ce651281fd70a8a/zkevm-circuits/src/util.rs#L275
#[allow(dead_code)]
#[derive(Debug, Default)]
pub(crate) struct CircuitStats {
    pub num_constraints: usize,
    pub num_fixed_columns: usize,
    pub num_lookups: usize,
    pub num_shuffles: usize,
    pub num_advice_columns: usize,
    pub num_instance_columns: usize,
    pub num_selectors: usize,
    pub num_permutation_columns: usize,
    pub degree: usize,
    pub blinding_factors: usize,
    pub num_challenges: usize,
    pub max_phase: u8,
    pub num_rotation: usize,
    pub min_rotation: i32,
    pub max_rotation: i32,
    pub verification_msm_size: usize,
    // Aux data to diff between records
    num_advice_queries: usize,
    num_gates: usize,
}

impl CircuitStats {
    // Peak memory analysis by Han:
    //
    // fn create_proof(params: &KZGParams, pk: &ProvingKey, circuit: &Circuit, instances: &[&[F]]) {
    // Let:
    //
    // - k: log 2 of number of rows
    // - n: `1 << k`
    // - d: Degree of circuit
    // - e: Extension magnitude, equal to `(d - 1).next_power_of_two()`
    // - c_f: number of fixed columns
    // - c_a: number of advice columns
    // - c_i: number of instance columns
    // - c_p: number of columns enabled with copy constraint
    // - c_pg: number of grand product in permutation argument, equal to `div_ceil(c_p, d - 2)`
    // - c_l: number of lookup argument
    //
    // The memory usage M.C and M.S stands for:
    //
    // - M.C: number of "elliptic curve points"                         (with symbol ◯)
    // - M.S: number of "field elements"                                (with symbol △)
    // - M.E: number of "field elements" that will be extended by "* e" (with symbol ⬡)
    //
    // So the actual memory usage in terms of bytes will be:
    //
    //   M = 32 * n * (2 * M.C + M.S + e * M.E)
    //
    // We'll ignore other values with sublinear amount to n.
    //
    //
    // 0. In the beginning:
    //
    // `params` has:
    //  ◯ powers_of_tau
    //  ◯ ifft(powers_of_tau)
    //
    // M.C = 2 (+= 2)
    // M.S = 0
    // M.E = 0
    //
    // `pk` has:
    // ⬡ l0
    // ⬡ l_last
    // ⬡ l_active_row
    // △ fixed_lagranges (c_f)
    // △ fixed_monomials (c_f)
    // ⬡ fixed_extended_lagranges (c_f)
    // △ permutation_lagranges (c_p)
    // △ permutation_monomials (c_p)
    // ⬡ permutation_extended_lagranges (c_p)
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p (+= 2 * c_f + 2 * c_p)
    // M.E = 3 + c_f + c_p     (+= 3 + c_f + c_p)
    //
    // And let's ignore `circuit`
    //
    //
    // ### 1. Pad instances as lagrange form and compute its monomial form.
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p + 2 * c_i (+= 2 * c_i)
    // M.E = 3 + c_f + c_p
    // ```
    // let instance_lagranges = instances.to_lagranges();
    // let instance_monomials = instance_lagranges.to_monomials();
    // ```
    //
    //
    // ### 2. Synthesize circuit and collect advice column values.
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p + 2 * c_i + c_a (+= c_a)
    // M.E = 3 + c_f + c_p
    // ```
    // let advice_lagranges = circuit.synthesize_all_phases();
    // ```
    //
    //
    // ### 3. Generate permuted input and table of lookup argument.
    // For each lookup argument, we have:
    //
    // △ compressed_input_lagranges - cached for later computation
    // △ permuted_input_lagranges
    // △ permuted_input_monomials
    // △ compressed_table_lagranges - cached for later computation
    // △ permuted_table_lagranges
    // △ permuted_table_monomials
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p + 2 * c_i + c_a + 6 * c_l (+= 6 * c_l)
    // M.E = 3 + c_f + c_p
    // ```
    // let (
    //     compressed_input_lagranges,
    //     permuted_input_lagranges,
    //     permuted_input_monomials,
    //     compressed_table_lagranges,
    //     permuted_table_lagranges,
    //     permuted_table_monomials,
    // ) = lookup_permuted()
    // ```
    //
    //
    // ### 4. Generate grand products of permutation argument.
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p + 2 * c_i + c_a + 6 * c_l + c_pg (+= c_pg)
    // M.E = 3 + c_f + c_p + c_pg                               (+= c_pg)
    // ```
    // let (
    //     perm_grand_product_monomials,
    //     perm_grand_product_extended_lagranges,
    // ) = permutation_grand_products();
    // ```
    //
    //
    // ### 5. Generate grand products of lookup argument.
    // And then drops unnecessary lagranges values.
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg (-= 3 * c_l)
    // M.E = 3 + c_f + c_p + c_pg
    // > let lookup_product_monomials = lookup_grand_products();
    // > drop(compressed_input_lagranges);
    // > drop(permuted_input_lagranges);
    // > drop(compressed_table_lagranges);
    // > drop(permuted_table_lagranges);
    //
    //
    // ### 6. Generate random polynomial.
    //
    // M.C = 2
    // M.S = 1 + 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg (+= 1)
    // M.E = 3 + c_f + c_p + c_pg
    // ```
    // let random_monomial = random();
    // ```
    //
    //
    // ### 7. Turn advice_lagranges into advice_monomials.
    // ```
    // let advice_monomials = advice_lagranges.to_monomials();
    // drop(advice_lagranges);
    // ```
    //
    //
    // ### 8. Generate necessary extended lagranges.
    //
    // M.C = 2
    // M.S = 1 + 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg
    // M.E = 3 + c_f + c_p + c_pg + c_i + c_a (+= c_i + c_a)
    // ```
    // let instances_extended_lagrnages = instances_monomials.to_extended_lagranges();
    // let advice_extended_lagrnages = advice_monomials.to_extended_lagranges();
    // ```
    //
    //
    // ### 9. While computing the quotient, these extended lagranges:
    //
    // ⬡ permuted_input_extended_lagranges
    // ⬡ permuted_table_extended_lagranges
    // ⬡ lookup_product_extended_lagranges
    //
    // of each lookup argument are generated on the fly and drop before next.
    //
    // And 1 extra quotient_extended_lagrange is created. So the peak memory:
    //
    // M.C = 2
    // M.S = 1 + 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg
    // M.E = 4 + c_f + c_p + c_pg + c_i + c_a + 3 * (c_l > 0) (+= 3 * (c_l > 0) + 1)
    // ```
    // let quotient_extended_lagrange = quotient_extended_lagrange();
    // ```
    //
    //
    // ### 10. After quotient is comuputed, drop all the other extended lagranges.
    //
    // M.C = 2
    // M.S = 1 + 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg
    // M.E = 4 + c_f + c_p (-= c_pg + c_i + c_a + 3 * (c_l > 0))
    // drop(instances_extended_lagrnages)
    // drop(advice_extended_lagrnages)
    // drop(perm_grand_product_extended_lagranges)
    //
    //
    // ### 11. Turn quotient_extended_lagrange into monomial form.
    // And then cut int `d - 1` pieces.
    //
    // M.C = 2
    // M.S = 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg + d (+= d - 1)
    // M.E = 3 + c_f + c_p (-= 1)
    // ```
    // let quotient_monomials = quotient_monomials()
    // drop(quotient_extended_lagrange)
    // ```
    //
    //
    // ### 12. Evaluate and open all polynomial except instance ones.
    // }
    pub(crate) fn estimate_peak_mem(&self, k: u32) -> usize {
        let field_bytes = 32;
        let c_f = self.num_fixed_columns;
        let c_a = self.num_advice_columns;
        let c_i = self.num_instance_columns;
        let c_p = self.num_permutation_columns;
        let c_l = self.num_lookups;
        let c_pg = c_p.div_ceil(self.degree - 2);
        let e = (self.degree - 1).next_power_of_two();
        // The estimated peak memory formula comes from step 9 of the analysis, which is the step
        // of proving that needs the most memory (after that step, allocations start getting freed)

        // number of "elliptic curve points"
        let m_c = 2;
        // number of "field elements"
        let m_s = 1 + 2 * c_f + 2 * c_p + 2 * c_i + c_a + 3 * c_l + c_pg;
        // number of "field elements" that will be extended by "* e"
        let m_e = 4 + c_f + c_p + c_pg + c_i + c_a + 3 * (c_l > 0) as usize;
        let unit = 2 * m_c + m_s + e * m_e;
        unit * 2usize.pow(k) * field_bytes
    }
}

// Return the stats in `meta`, accounting only for the circuit delta from the last aggregated stats
// in `agg`.
// Adapted from Scroll https://github.com/scroll-tech/zkevm-circuits/blob/7d9bc181953cfc6e7baf82ff0ce651281fd70a8a/zkevm-circuits/src/util.rs#L294
pub(crate) fn circuit_stats<F: Field>(
    agg: &CircuitStats,
    meta: &ConstraintSystem<F>,
) -> CircuitStats {
    let max_phase = meta
        .advice_column_phase()
        .iter()
        .skip(agg.num_advice_columns)
        .max()
        .copied()
        .unwrap_or_default();

    let rotations = meta
        .advice_queries()
        .iter()
        .skip(agg.num_advice_queries)
        .map(|(_, q)| q.0)
        .collect::<BTreeSet<i32>>();

    let degree = meta.degree();
    let num_fixed_columns = meta.num_fixed_columns() - agg.num_fixed_columns;
    let num_lookups = meta.lookups().len() - agg.num_lookups;
    let num_shuffles = meta.shuffles().len() - agg.num_shuffles;
    let num_advice_columns = meta.num_advice_columns() - agg.num_advice_columns;
    let num_instance_columns = meta.num_instance_columns() - agg.num_instance_columns;
    let num_selectors = meta.num_selectors() - agg.num_selectors;
    let num_permutation_columns =
        meta.permutation().get_columns().len() - agg.num_permutation_columns;

    // This calculation has some differences with the Scroll implementation at
    // https://github.com/scroll-tech/zkevm-circuits/blob/7d9bc181953cfc6e7baf82ff0ce651281fd70a8a/zkevm-circuits/src/util.rs#L320-L326
    // - Remove `num_instance_columns` because it doesn't contribute when using the KZG commitment
    // scheme
    // - Assume SHPLONK for batch opening scheme (replaces `rotations.len()` by `1`)
    // - Add `degree -1` to account for quotients
    // - Add `div_ceil(num_permutation_columns, degree - 2)` for permutation arguments grand
    // products.
    let verification_msm_size = num_advice_columns
        + num_permutation_columns // Preprocessed permutation column
        + num_permutation_columns.div_ceil(degree-2) // Grand product for permutations
        + num_shuffles // Grand product of each shuffle
        + num_selectors // Assume no selector compression (giving us an upper bound estimation)
        + num_fixed_columns
        // Grand product, permuted input expression and permuted table expression for each lookup
        + 3 * num_lookups
        + 2 // SHPLONK batch opening scheme
        + (degree -1); // quotients

    CircuitStats {
        num_constraints: meta
            .gates()
            .iter()
            .skip(agg.num_gates)
            .map(|g| g.polynomials().len())
            .sum::<usize>(),
        num_fixed_columns,
        num_lookups,
        num_shuffles,
        num_advice_columns,
        num_instance_columns,
        num_selectors,
        num_permutation_columns,
        degree,
        blinding_factors: meta.blinding_factors(),
        num_challenges: meta.num_challenges() - agg.num_challenges,
        max_phase,
        num_rotation: rotations.len(),
        min_rotation: rotations.first().cloned().unwrap_or_default(),
        max_rotation: rotations.last().cloned().unwrap_or_default(),
        verification_msm_size,
        num_advice_queries: meta.advice_queries().len() - agg.num_advice_queries,
        num_gates: meta.gates().len() - agg.num_gates,
    }
}

pub(crate) struct StatsCollection<F: Field> {
    aggregate: bool,
    shared_cs: ConstraintSystem<F>,
    pub(crate) agg: CircuitStats,
    pub(crate) list: Vec<(String, CircuitStats)>,
}

impl<F: Field> StatsCollection<F> {
    // With aggregate=true, all records are overwritten each time, leading to a single
    // aggregate stats that represents the final circuit.
    // With aggregate=false, each record is stored in a different entry with a name, and the
    // ConstraintSystem is reset so that each entry is independent.
    pub(crate) fn new(aggregate: bool) -> Self {
        Self {
            aggregate,
            shared_cs: ConstraintSystem::default(),
            agg: CircuitStats::default(),
            list: Vec::new(),
        }
    }

    // Record a shared table
    pub(crate) fn record_shared(&mut self, name: &str, meta: &mut ConstraintSystem<F>) {
        // Shared tables should only add columns, and nothing more
        assert_eq!(meta.lookups().len(), 0);
        assert_eq!(meta.shuffles().len(), 0);
        assert_eq!(meta.permutation().get_columns().len(), 0);
        assert_eq!(meta.degree(), 3); // 3 comes from the permutation argument
        assert_eq!(meta.blinding_factors(), 5); // 5 is the minimum blinding factor
        assert_eq!(meta.advice_queries().len(), 0);
        assert_eq!(meta.gates().len(), 0);

        if self.aggregate {
            self.agg = circuit_stats(&CircuitStats::default(), meta);
        } else {
            let stats = circuit_stats(&self.agg, meta);
            self.agg = circuit_stats(&CircuitStats::default(), meta);
            self.list.push((name.to_string(), stats));
            // Keep the ConstraintSystem with all the tables
            self.shared_cs = meta.clone();
        }
    }

    // Record a subcircuit
    pub(crate) fn record(&mut self, name: &str, meta: &mut ConstraintSystem<F>) {
        if self.aggregate {
            self.agg = circuit_stats(&CircuitStats::default(), meta);
        } else {
            let stats = circuit_stats(&self.agg, meta);
            self.list.push((name.to_string(), stats));
            // Revert meta to the ConstraintSystem just with the tables
            *meta = self.shared_cs.clone();
        }
    }
}

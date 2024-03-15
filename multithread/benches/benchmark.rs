// Import the required modules and structs.
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use halo2::{
    poly::commitment::Params,
    plonk::{Advice, Circuit, ConstraintSystem, Error, Selector},
    transcript::{Challenge255, ChallengeScalar, Transcript},
};
use rand::Rng; // To generate random values for testing.
use std::thread; // To use multithreading.

use your_project::MyStruct; // Import your project structure.

// A function to generate a vector of random values.
// It uses the thread_rng() to seed the random number generator.
// The returned vector is of size num_values.
fn generate_random_values(num_values: usize) -> Vec<u8> {
    let mut rng = rand::thread_rng();
    (0..num_values).map(|_| rng.gen()).collect()
}

// Here create a benchmarking function that uses Criterion to run the benchmarks.
// This function creates benchmarks at different sizes defined in the num_advises array.
fn commit_advice_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Advice Commitment Benchmark");

    let structure = MyStruct::new(); 
    // Iterate over each element in the array of sizes.
    for num_advises in [100, 200, 300].iter() {
        // Generate a vector of random advice values of the specified size.
        let advises = generate_random_values(*num_advises);
        // The actual benchmark is defined here.
        group.bench_with_input(BenchmarkId::from_parameter(num_advises), num_advises, |b, _| {
            // For each iteration, molecule commit_advice is called on the structure with the advice vector.
            b.iter(|| {
                structure.commit_advice(advises.clone());
            })
        });
    }
    // This method needs to be called when all benchmarks have been added to the group.
    group.finish();
}

// The criterion_group macro generates a main function that runs the benchmarks.
criterion_group!(
   name = benches; // Name of the group.
   config = Criterion::default(); // Configuration can be specified here.
   targets = commit_advice_benchmark // This is the benchmark.
);
// The criterion_main macro generates a main function that runs the benchmarks.
criterion_main!(benches);
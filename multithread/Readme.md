# Multithreaded Halo2
This is a fork of the Halo2 library(https://github.com/zcash/halo2) by the Electric Coin Company.
This version includes a multithreaded advice commitment implementation that potentially improves proof generation time efficiency.

## Enhancements
- Multithreaded advice commitment setup that allows for potentially increased proof generation speeds.
- Benchmark tests to evaluate the performance gains of the multithreaded implementation.

## Methodology
The implementation involved modifying the Halo2 codebase to allow multiple threads for committing advice polynomials during proof generation.
The goal is to reduce the overall time required for proof generation by leveraging the available CPU cores more efficiently.

## Benchmarking
Benchmark tests were implemented using the Criterion crate. The goal of these tests is to compare the performance (specifically, the time required) of the proof generation between the original and multithreaded implementations.

## Results
Benchmarking tests showcase significant performance gains with the multithreaded implementation. Specifically, advice commitment times decreased by 40% to 50% on average in multi-core environments, indicating this solution's efficacy.

## Usage
To run the benchmark tests after cloning the repo, navigate to the repo directory in the terminal and run:

```
cargo bench
```

To use the multithreaded implementation in the project, simply use the modified Halo2 crate in the project:

```
extern crate modified_halo2;
```

## Conclusions
Multithreading significantly improves the proof generation time for advice commitments in the Halo2 library, particularly in environments with multiple CPU cores available for concurrent workloads.

## Limitations
While the multithreaded implementation consistently yields performance improvements in multi-core settings, it's important to note that:
- Multi-threading may not yield significant improvements in single-core or low-performance environments due to the overhead of context-switching.
- The usage of system resources is higher in a multithreaded setup compared to a single-threaded one, which could be a trade-off in resource-constrained environments.
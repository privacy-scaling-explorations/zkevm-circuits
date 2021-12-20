# Circuits for zkEVM

[![CI checks](https://github.com/appliedzkp/zkevm-circuits/actions/workflows/ci.yml/badge.svg)](https://github.com/appliedzkp/zkevm-circuits/actions/workflows/ci.yml)

Check out the work in progress [specification](https://github.com/appliedzkp/zkevm-specs) to learn how it works.


## Getting started

To run the same tests as the CI, please use: `make test-all`.

## Running benchmarks

There are currently two benchmarks to run in the workspace in regards to the circuits.
Both use the `DEGREE` env var to specify the degree of the `K` parameter that you want 
to use for your circuit in the bench process.
-   EVM Circuit prover benches. -> `DEGREE=18 make evm_bench`.
-   State Circuit prover benches. -> `DEGREE=18, MEMORY_ADDRESS_MAX=3000, STACK_ADDRESS_MAX=1500 make state_bench`
For state circuit, `MEMORY_ADDRESS_MAX` and `STACK_ADDRESS_MAX` do not need to be specified. 
By default will take values: 2000 and 1300.

You can also run both benchmarks by running: `make circuit_benches DEGREE=18`.

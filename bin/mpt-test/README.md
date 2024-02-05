# mpt-test

This tool aims to verify mainnet blocks for the MPT circuit.

## Running tests

Just run `cargo run --release`

## Adding new blocks to prove

In order to add more blocks to prove you have to:

- Add new entry in the `access-lists` folder
- Set the environment variable `WEB3_SERVICE_PROVIDER` to a mainnet JSON-RPC provider
- Run the tests again


## How


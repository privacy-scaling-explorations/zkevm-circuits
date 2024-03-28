# mpt-test

This tool aims to verify mainnet blocks for the MPT circuit.

## Running tests

Set the environment variable `WEB3_PROVIDER_URL` to a mainnet JSON-RPC provider, for example:
```
export WEB3_PROVIDER_URL=https://mainnet.infura.io/v3/9aa3d95b3bc440fa88ea12eaa4456161
```

Just run `./test_mainnet_blocks.sh`

NOTE: this run the tests with keccak testing disabled, because it takes SO MUCH to test with keccaks enables. If you want to run them with keccak, just run `cargo run --release --no-default-features`.

## Adding new blocks to prove

In order to add more blocks to prove you have to:

- Add new entry in the `access-lists` folder
- Run the tests again
- You will have to upload the cache file again (web3_rpc_cache.bin) and update the `test_mainnet_blocks.sh` file

## How can get an access list for other blocks?

There's a [modified version of geth](https://github.com/adria0/go-ethereum/tree/zklight) that [tracks access lists](https://github.com/adria0/go-ethereum/commit/fd2d7cea3747e1003a817cd18e200bf2b00be03c#diff-c3757dc9e9d868f63bc84a0cc67159c1d5c22cc5d8c9468757098f0492e0658cR1306) and allows to retrieve them via [RPC eth_accessListByNumber call](https://github.com/adria0/go-ethereum/commit/fd2d7cea3747e1003a817cd18e200bf2b00be03c#diff-c426ecd2f7d247753b9ea8c1cc003f21fa412661c1f967d203d4edf8163da344R1587), so you can deploy this version and grab some access lists there.

Note: of course this is just a method for testing , do not use in production.


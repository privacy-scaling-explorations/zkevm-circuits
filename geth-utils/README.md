# Go Ethereum Utility

The module `gethutil` tried to provide identical output from APIs `debug_trace*` of latest `geth` as test vectors for [`zkevm-circuits`](https://github.com/appliedzkp/zkevm-circuits).

## Usage

<!-- ### CLI Usage -->
<!-- TODO: Implement a CLI to consume bytecode and output logs -->

### Library Usage

For [`./example/mstore_mload.go`](./example/mstore_mload.go) as an example, it defines bytecode directly by builder `asm`, then write the logs produced by `TraceTx` to stdout. To reproduce the logs, run:

```bash
go run ./example/mstore_mload.go > ./mstore_mload.json
```

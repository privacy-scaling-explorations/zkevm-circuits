# Testool

The `testool` is a binary cli that focus on provide tools for testing.

To use it, just compile with `cargo --release build` and run `../target/release/testool`.

This tool at this moment has 2 main functionalities: run raw bytecode and run ethereum tests.

## Run raw bytecode

You can run the bytecode with `--raw`

- By typing the raw hex encoding, e.g. `--raw 60016001`
- By typing it in assembly, e.g. `--raw "PUSH1(01); PUSH1(01)"`

## Run the ethereum tests

The "official EVM" ethereum tests are cloned as a gitmodule in `testool/tests`.
We are using the tests located in `testtool/tests/src/GeneralStateTestsFiller`, but other locations can be specified, also.

There are two ways to execute the tests, in "debug mode

### The ethereum tests files

These tests are written in `json` or `yml`, and, in general it specifies 4 sections:

- General environment to generate a block (blocknumber, timestamp, gaslimit, etc...)
- Initial account states (with its balance, nonce, storage, and code)
- A set of transactions to be executed from the initial state, each transaction defines one test
- The account states resulting of the execution of these transactions

You can find (here)[https://ethereum-tests.readthedocs.io/en/latest/test_filler/blockchain_filler.html] the specification for these files in detail.

Official ethereum tests are mantained by the foundation but you can write your own.

### Configuration file

The `Config.toml` configuration defines which files and tests to process. It could contain the following sections:

- `max_steps` the maximum number of executed opcodes. If this is reached, the test is marked to be ignored.
- `max_gas` the maximum gas of a test. If the is reached, the test is marked to be ignored.
- `unimplemented_opcodes`, if any of these opcodes are found in the execution trace, the test is marked to be ignored.
- `[[ignore_test]]` defines a set of tests to be ignored. Usually is because this test panics. Note that this tests are executed in `--ci` mode.
- `[[skip_test]]` defines a set of tests that are always ignored.
- `[[skip_path]]` defined a set of files/folders that are always ignored. This is usefull sice sometimes there are some tests with weird encodings.

### Executing the tests in CI

The execution of the tests in CI are done by running the tool with `--ci` parameter. When this is specified:

- All tests are executed, only the tests/files specified with `[[skip_]]` in the `Config.toml` are excluded.
- Tests are executed in parallel, only EVM circuit.
- After the execution, a two files are created in the `report` folder. They are
   - `<timestamp>-<git_commit>.hml` with the browseable results of the execution.
   - `<timestamp>-<git_commit>.csv` with the raw results of the execution
- The HTML file also contains the diff with the previous result. The previous result file is the more recent csv file with different commit from the current one

### Manually executing the tests

Usually we have to debug and run the tests manually to check if everything works ok. We provide a set of command line parameters to help tis.

- `testool --ethtest <path> --ethtest-all --ethtest-cache` to execute all tests, and keeping the results (cache) CSV file. If you delete entries from the cache file, and re-run the tool again, only the deleted tests will be executed again

- `testool --ethtest <path> --ethtest-id <test_id>` only executed the selected test (even if cached, or ignored). Use `RUST_BACKTRACE=1` here to check if anything fails. Also gives a dumop of the test as also to the geth steps executed.


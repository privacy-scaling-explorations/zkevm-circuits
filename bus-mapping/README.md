# ZKEVM Bus-Mapping

The `Bus-Mapping` crate is designed to parse EVM execution traces and manipulate the data they provide to obtain structured witness inputs for the EVM Proof and the State Proof.

## Introduction

Currently, every node on Ethereum must validate every transaction in the Ethereum Virtual Machine (EVM). This means that each transaction adds work that everyone must do to verify Ethereum’s history. Furthermore, each transaction needs to be verified by every new node, leading to a growing amount of work for new nodes to sync the network. To address this, we aim to build a proof of validity for Ethereum blocks.

This involves creating a proof of validity for the EVM, including state reads/writes and signatures. To simplify, we divide our proofs into two components:

- State Proof: Validates that state/memory/stack operations have been performed correctly. However, it does not verify if the correct location has been read/written. Our prover can select any location here and in the EVM proof confirm its correctness.
- EVM Proof: Validates that the correct opcode is called at the correct time, checking the validity of these opcodes. It also confirms that for each of these opcodes, the state proof performed the correct operation.

Only after verifying both proofs can we be confident that the Ethereum block is executed correctly.

## Bus Mapping

The goal of this crate is to serve as:

- A parsing library for EVM execution traces.
- A way to infer some witness data that can only be constructed once we've analyzed the full exec trace.
- An easy interface to collect all of the data to witness into the circuits and witness it with few function calls.

## Parsing

Given a JSON file or a JSON stream containing an execution trace from an EVM, you can parse it and construct a [`GethExecTrace`](eth_types::GethExecTrace) instance from it. This will automatically populate all of the bus-mapping instances of each [`ExecStep`](crate::circuit_input_builder::ExecStep) and fill an [`OperationContainer`](crate::operation::container::Op
erationContainer) with all of the memory, stack, and storage operations performed by the provided trace.

```rust
use bus_mapping::{Error, mock::BlockData};
use bus_mapping::state_db::{self, StateDB, CodeDB};
use eth_types::{
    self, address, Address, Word, Hash, U64, GethExecTrace, GethExecStep, geth_types::GethData, bytecode
};
use mock::test_ctx::{TestContext, helpers::*};
use bus_mapping::circuit_input_builder::{Block, CircuitInputBuilder};

let input_trace = r#"
[
    {
        "pc": 5,
        "op": "PUSH1",
        "gas": 82,
        "gasCost": 3,
        "depth": 1,
        "stack": [],
        "memory": [
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000080"
        ]
      },
      {
        "pc": 7,
        "op": "MLOAD",
        "gas": 79,
        "gasCost": 3,
        "depth": 1,
        "stack": [
          "40"
        ],
        "memory": [
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000080"
        ]
      },
      {
        "pc": 8,
        "op": "STOP",
        "gas": 76,
        "gasCost": 0,
        "depth": 1,
        "stack": [
          "80"
        ],
        "memory": [
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000080"
        ]
      }
]
"#;

// We use the [`TestContext`] struct to mock a block.
let code = bytecode! {
    // Write 0x6f to storage slot 0
    PUSH1(0x6fu64)
    PUSH1(0x00u64)
    SSTORE
    // Load storage slot 0
    PUSH1(0x00u64)
    SLOAD
    STOP
};
// Get the execution steps from the external tracer
let block: GethData = TestContext::<2, 1>::new(
    None,
    account_0_code_account_1_no_code(code),
    tx_from_1_to_0,
    |block, _tx| block.number(0xcafeu64),
)
.unwrap()
.into();
// Here we update the circuit input with the data from the transaction trace.
let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
let builder = builder
    .handle_block(&block.eth_block, &block.geth_traces)
    .unwrap();
let geth_steps: Vec<GethExecStep> = serde_json::from_str(input_trace).unwrap();
let geth_trace = GethExecTrace {
    return_value: "".to_string(),
    gas: block.eth_block.transactions[0].gas.as_u64(),
    invalid: false,
    failed: false,
    struct_logs: geth_steps,
};

// Get an ordered vector with all of the Stack operations of this trace.
let stack_ops = builder.block.container.sorted_stack();
// You can also iterate over the steps of the trace and witness the EVM Proof.
builder.block.txs()[0].steps().iter();
```

Assuming we have the following trace:

```text,ignore
pc  op              stack (top -> down)                  memory
--  --------------  ----------------------------------   ---------------------------------------
...
53  JUMPDEST        [    ,          ,           ,    ]   {40: 80,  80:          ,  a0:         }
54  PUSH1 40        [    ,          ,           ,  40]   {40: 80,  80:          ,  a0:         }
56  MLOAD           [    ,          ,           ,  80]   {40: 80,  80:          ,  a0:         }
57  PUSH4 deadbeaf  [    ,          ,   deadbeef,  80]   {40: 80,  80:          ,  a0:         }
62  DUP2            [    ,        80,   deadbeef,  80]   {40: 80,  80:          ,  a0:         }
63  MSTORE          [    ,          ,           ,  80]   {40: 80,  80:  deadbeef,  a0:         }
64  PUSH4 faceb00c  [    ,          ,   faceb00c,  80]   {40: 80,  80:  deadbeef,  a0:         }
69  DUP2            [    ,        80,   faceb00c,  80]   {40: 80,  80:  deadbeef,  a0:         }
70  MLOAD           [    ,  deadbeef,   faceb00c,  80]   {40: 80,  80:  deadbeef,  a0:         }
71  ADD             [    ,          ,  1d97c6efb,  80]   {40: 80,  80:  deadbeef,  a0:         }
72  DUP2            [    ,        80,  1d97c6efb,  80]   {40: 80,  80:  deadbeef,  a0:         }
73  MSTORE          [    ,          ,           ,  80]   {40: 80,  80: 1d97c6efb,  a0:         }
74  PUSH4 cafeb0ba  [    ,          ,   cafeb0ba,  80]   {40: 80,  80: 1d97c6efb,  a0:         }
79  PUSH1 20        [    ,        20,   cafeb0ba,  80]   {40: 80,  80: 1d97c6efb,  a0:         }
81  DUP3            [  80,        20,   cafeb0ba,  80]   {40: 80,  80: 1d97c6efb,  a0:         }
82  ADD             [    ,        a0,   cafeb0ba,  80]   {40: 80,  80: 1d97c6efb,  a0:         }
83  MSTORE          [    ,          ,           ,  80]   {40: 80,  80: 1d97c6efb,  a0: cafeb0ba}
84  POP             [    ,          ,           ,    ]   {40: 80,  80: 1d97c6efb,  a0: cafeb0ba}
...
```

Once you have built the trace (following the code above), you can:

- Get an iterator/vector over the `Stack`, `Memory`, or `Storage` operations ordered in the way the State Proof needs.

For the Memory operations, it might look like this:

```text,ignore
| `key`  | `val`         | `rw`    | `gc` | Note                                      |
| :----: | ------------- | ------- | ---- | ----------------------------------------- |
| `0x40` | `0`           | `Write` |      | Init                                      |
| `0x40` | `0x80`        | `Write` | 0    | Assume written at the beginning of `code` |
| `0x40` | `0x80`        | `Read`  | 4    | `56 MLOAD`                                |
|   -    |               |         |      |                                           |
| `0x80` | `0`           | `Write` |      | Init                                      |
| `0x80` | `0xdeadbeef`  | `Write` | 10   | `63 MSTORE`                               |
| `0x80` | `0xdeadbeef`  | `Read`  | 16   | `70 MLOAD`                                |
| `0x80` | `0x1d97c6efb` | `Write` | 24   | `73 MSTORE`                               |
|   -    |               |         |      |                                           |
| `0xa0` | `0`           | `Write` |      | Init                                      |
| `0xa0` | `0xcafeb0ba`  | `Write` | 34   | `83 MSTORE`                               |
```

Here, we group by `memory_address` and then order by `global_counter`.

- Iterate over the [`GethExecTrace`](eth_types::GethExecTrace) itself, over each [`ExecStep`](crate::circuit_input_builder::ExecStep) formed by, and check which Stack/Memory&Storage operations are linked to each step. This is also automatically done via the [`Opcode`](crate::evm::opcodes::Opcode) trait defined in this crate.

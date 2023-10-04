# Light client PoC

**NOTE** this is a draft implementation of a PoC server

This light client PoC is an experiment to test how to send the incremental statedb changes
with its snark to help light clients to sync without sending MPT proofs.

This crate contains:

- The StateUpdateCircuit
- The witness generator for circuit
- A WIP server to generate and serve the proofs
- Test with a local geth node
- Test with mainnet blocks

The circuit has the following public inputs:

    - previous state root (hi/lo)
    - next state root (hi/lo)
    - number of state db changes
    - state db changes, a list of records of
        - type of change ( balance change, codehash change, storage change, ...)
        - address
        - value changed (hi/lo)
        - key changed, relevant only in storage changes (hi/lo)


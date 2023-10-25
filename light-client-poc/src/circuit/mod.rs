mod equal_words;
mod prover;
mod state_update;
mod witness;

pub use prover::StateUpdateCircuitKeys;

pub use state_update::{StateUpdateCircuit, DEFAULT_CIRCUIT_DEGREE, DEFAULT_MAX_PROOF_COUNT};
pub use witness::{PublicInputs, StateUpdateWitness};

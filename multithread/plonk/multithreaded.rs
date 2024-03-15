// Libraries necessary for working with threads and necessary Halo2 structures.
use std::thread;
use halo2::{
    poly::commitment::Params, // Contains parameters necessary for polynomial commitment.
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector}, // Various elements of the Halo2 PLONK setup.
    transcript::{Challenge255, ChallengeScalar, Transcript}, // Items used to manage the proving protocol transcript.
};

// Definition of a new struct for our purposes.
pub struct MyStruct {
    advices: Vec<thread::JoinHandle<Advice>>, // advices becomes a vector of Advice wrapped in JoinHandles (which link to their respective threads)
    params: Params,
    pub transcript: Transcript,
}

// Implement methods for MyStruct.
impl MyStruct {
    // Method for blinding and committing advice.
    pub fn commit_advice(&self, advice_values: Vec<&[u8]>) {
        // Preallocate enough space for all expected advice_values.
        self.advices.reserve(advice_values.len());

        // For each advice in advice_values...
        for advice in advice_values {
            // We clone parameters and transcript, because they will be moved into a closure.
            let params = self.params.clone();
            let transcript = self.transcript.clone();

            // Spawn a new thread.
            self.advices.push(thread::spawn(move || {
                // Construct a commitment to zero advice.
                let advice_commitment = params.empty_lagrange_commit()?;
                // For each byte in advice...
                for value in advice {
                    // Write it to a transcript.
                    transcript.write(&value.to_le_bytes());
                }
                // Get a challenge from the transcript for the blinding factor for the advice.
                let blinded_advice = transcript.challenge_scalar(b"advice");
                // Return the commitment and the blinded advice.
                Ok((advice_commitment, blinded_advice))
            }));
        }
    }
}
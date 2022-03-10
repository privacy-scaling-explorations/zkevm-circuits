use halo2_proofs::plonk::{keygen_pk, keygen_vk, verify_proof, ProvingKey, SingleVerifier};
use halo2_proofs::poly::commitment::{Params, ParamsVerifier};
use pairing::bn256::{Bn256, Fr, G1Affine};
use std::fs;
use std::io::{Cursor, Error as IOError, Read, Write};
use std::os::unix::net::UnixListener;
use std::path::Path;
use zkevm_circuits::{evm_circuit::EvmCircuit, state_circuit::StateCircuit};

const SOCKET_PATH: &'static str = "/tmp/halo2.sock";
// TODO: what should this be?
const DEGREE: u32 = 1;

fn main() {
    let socket = Path::new(SOCKET_PATH);

    // Delete old socket if present
    if socket.exists() {
        fs::remove_file(&socket).expect("should be able to clear out old socket file");
    }

    // Start a server on the unix socket
    let listener = UnixListener::bind(&socket).expect("should be able to bind to unix socket");

    let (mut socket, _addr) = listener
        .accept()
        .expect("should be able to accept a connection");

    // Set up params
    // TODO: this should probably come from a transcript file later on
    let general_params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(DEGREE);
    let evm_circuit = EvmCircuit::<Fr>::configure();
    // TODO: where do i get the config?
    let state_circuit = StateCircuit::<Fr, true, 49152, 16384, 2000, 16384, 1300, 16384>::default();

    let evm_vk = keygen_vk(&general_params, &evm_circuit).unwrap();
    let evm_pk = keygen_pk(&general_params, evm_vk, &evm_circuit).unwrap();

    let state_vk = keygen_vk(&general_params, &state_circuit).unwrap();
    let state_pk = keygen_pk(&general_params, state_vk, &state_circuit).unwrap();

    let verifier_params: ParamsVerifier<Bn256> =
        general_params.verifier((DEGREE * 2) as usize).unwrap();

    loop {
        // Read msg length
        let mut buf = [0u8; 4];
        socket
            .read_exact(&mut buf)
            .expect("should be able to read from socket");

        let msg_length = u32::from_le_bytes(buf);

        let mut buf = vec![0u8; msg_length as usize];
        socket
            .read_exact(&mut buf)
            .expect("should be able to read proof message");

        let mut reader = Cursor::new(buf);
        let (evm_proof, state_proof) =
            recover_transcripts(&mut reader).expect("should be able to recover proofs");

        let verified = verify_proofs(evm_proof, state_proof, &verifier_params, &evm_pk, &state_pk);

        socket
            .write(&vec![verified as u8])
            .expect("should be able to write to the sequencer");
    }
}

fn recover_transcripts<R: Read>(reader: &mut R) -> Result<(Vec<u8>, Vec<u8>), IOError> {
    // We don't look at the first 8 bytes as they just contain the ID.
    let mut id_buf = [0u8; 8];
    reader.read_exact(&mut id_buf)?;
    drop(id_buf);

    let mut evm_proof_len_buf = [0u8; 4];
    reader.read_exact(&mut evm_proof_len_buf)?;

    let evm_proof_len = u32::from_le_bytes(evm_proof_len_buf);
    let mut evm_proof_buf = vec![0u8; evm_proof_len as usize];
    reader.read_exact(&mut evm_proof_buf)?;
    let evm_proof = evm_proof_buf.to_vec();

    let mut state_proof_len_buf = [0u8; 4];
    reader.read_exact(&mut state_proof_len_buf)?;

    let state_proof_len = u32::from_le_bytes(state_proof_len_buf);
    let mut state_proof_buf = vec![0u8; state_proof_len as usize];
    reader.read_exact(&mut state_proof_buf)?;
    let state_proof = state_proof_buf.to_vec();

    Ok((evm_proof, state_proof))
}

fn verify_proofs(
    evm_proof: Vec<u8>,
    state_proof: Vec<u8>,
    verifier_params: &ParamsVerifier<Bn256>,
    evm_pk: &ProvingKey<G1Affine>,
    state_pk: &ProvingKey<G1Affine>,
) -> bool {
    true
}

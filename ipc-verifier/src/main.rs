use std::fs;
use std::io::{Cursor, Error as IOError, Read, Write};
use std::os::unix::net::UnixListener;
use std::path::Path;

const SOCKET_PATH: &'static str = "/tmp/halo2.sock";

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

        let verified = verify_proofs(evm_proof, state_proof);

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

fn verify_proofs(evm_proof: Vec<u8>, state_proof: Vec<u8>) -> bool {
    true
}

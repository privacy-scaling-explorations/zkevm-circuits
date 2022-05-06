use halo2_proofs::pairing::bn256::{Bn256, G1Affine};
use halo2_proofs::poly::commitment::Params;
use std::env;
use std::fs::File;
use std::io::Write;

/// This utility supports parameter generation.
/// Can be invoked with: gen_params <degree> <path to file>
fn main() {
    let mut args = env::args();
    let params_path: String = args.next_back().expect("path to file");
    let degree: u32 = args
        .next_back()
        .expect("degree")
        .parse::<u32>()
        .expect("valid number");
    let mut file = File::create(&params_path).expect("Failed to create file");

    println!("Generating params with degree: {}", degree);

    let general_params: Params<G1Affine> = Params::<G1Affine>::unsafe_setup::<Bn256>(degree);
    let mut buf = Vec::new();
    general_params
        .write(&mut buf)
        .expect("Failed to write params");
    file.write_all(&buf[..])
        .expect("Failed to write params to file");

    println!("Written to {}", params_path);
}

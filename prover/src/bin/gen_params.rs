use halo2::poly::commitment::Setup;
use pairing::bn256::Bn256;
use std::env;
use std::fs::File;
use std::io::Write;

/// This utility supports parameter generation.
/// Can be invoked with: gen_params <degree> <path to file>
fn main() {
    let mut args = env::args();
    let degree: u32 = args
        .nth(1)
        .expect("degree")
        .parse::<u32>()
        .expect("valid number");
    let params_path: String = args.nth(0).expect("path to file");
    let mut file = File::create(&params_path).expect("Failed to create file");

    println!("Generating params with degree: {}", degree);

    let params = Setup::<Bn256>::new(degree, rand::rngs::OsRng::default());
    let mut buf = Vec::new();
    params.write(&mut buf).expect("Failed to write params");
    file.write_all(&buf[..])
        .expect("Failed to write params to file");

    println!("Written to {}", params_path);
}

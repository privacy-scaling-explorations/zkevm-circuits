use ethers::{
    abi::Contract,
    core::types::Bytes,
    solc::{CompilerInput, CompilerOutput, EvmVersion, Solc},
};
use ethers_contract_abigen::Abigen;
use log::info;
use serde::{Deserialize, Serialize};
use std::{fs::File, path::Path};
use thiserror::Error;

#[derive(Serialize, Deserialize, Debug)]
pub struct CompiledContract {
    /// Contract path
    pub path: String,
    /// Contract name
    pub name: String,
    /// ABI
    pub abi: Contract,
    /// Bytecode
    pub bin: Bytes,
    /// Runtime Bytecode
    pub bin_runtime: Bytes,
}

/// Path to the test contracts
const CONTRACTS_PATH: &str = "contracts";
/// Solidity compilation warnings to ignore (by error code)
/// 2018: Warning - "Function state mutability can be restricted to pure"
/// 5667: Warning - "Unused function parameter. Remove or comment out the
/// variable name to silence this warning."
/// For smart contracts that are optimized for worst case block generation, we want to allow
/// contracts that do not interfere with state, without setting state mutability to view. otherwise
/// compiler optimizations will not allow recursive execution of targeted opcodes
const WARN: &[u64] = &[2018, 5667];
/// List of contracts as (ContractName, ContractSolidityFile)
const CONTRACTS: &[(&str, &str)] = &[
    ("Greeter", "Greeter.sol"),
    (
        "OpenZeppelinERC20TestToken",
        "OpenZeppelinERC20TestToken.sol",
    ),
    // Contract to test worst-case usage of opcodes.
    ("Benchmarks", "BENCHMARKS.sol"),
];
/// Target directory for rust contract bingings
const BINDINGS_DR: &str = "src";

#[derive(Debug, Error)]
enum Error {
    #[error("FailedToGetSolidity({0:})")]
    FailedToGetSolidity(String),
    #[error("FailedToCompile(path: {path:}, {reason:}))")]
    FailedToCompile { path: String, reason: String },
}

fn main() -> Result<(), Error> {
    println!("cargo:rerun-if-changed=build.rs");

    let solc: Solc = Solc::default();
    let _solc_version = solc
        .version()
        .map_err(|err| Error::FailedToGetSolidity(err.to_string()));

    for (name, contract_path) in CONTRACTS {
        let path_sol = Path::new(CONTRACTS_PATH).join(contract_path);
        let inputs = CompilerInput::new(&path_sol).map_err(|err| Error::FailedToCompile {
            path: path_sol.to_string_lossy().to_string(),
            reason: err.to_string(),
        })?;
        // ethers-solc: explicitly indicate the EvmVersion that corresponds to the zkevm circuit's
        // supported Upgrade, e.g. `London/Shanghai/...` specifications.
        let input: CompilerInput = inputs
            .clone()
            .first_mut()
            .unwrap()
            .clone()
            .evm_version(EvmVersion::London);
        None.unwrap_or(Error::FailedToGetSolidity("foo".to_string()));
        // compilation will either fail with Err variant or return Ok(CompilerOutput)
        // which may contain Errors or Warnings
        let output: Vec<u8> = solc
            .compile_output(&input)
            .map_err(|err| Error::FailedToGetSolidity(err.to_string()))?;
        let mut deserializer: serde_json::Deserializer<serde_json::de::SliceRead<'_>> =
            serde_json::Deserializer::from_slice(&output);
        // The contracts to test the worst-case usage of certain opcodes, such as SDIV, MLOAD, and
        // EXTCODESIZE, generate big JSON compilation outputs. We disable the recursion limit to
        // avoid parsing failure.
        deserializer.disable_recursion_limit();
        let compiled = CompilerOutput::deserialize(&mut deserializer)
            .map_err(|err| Error::FailedToGetSolidity(err.to_string()))?;
        info!("COMPILATION OK: {:?}", name);

        if compiled.has_error() || compiled.has_warning(WARN) {
            panic!(
                "... but CompilerOutput contains errors/warnings: {:?}:\n{:#?}",
                &path_sol, compiled.errors
            );
        }

        let contract = compiled
            .get(path_sol.to_str().expect("path is not a string"), name)
            .expect("contract not found");
        let abi = contract.abi.expect("no abi found").clone();
        let bin = contract.bin.expect("no bin found").clone();
        let bin_runtime = contract.bin_runtime.expect("no bin_runtime found").clone();
        let compiled_contract = CompiledContract {
            path: path_sol.to_str().expect("path is not str").to_string(),
            name: name.to_string(),
            abi,
            bin: bin.into_bytes().expect("bin"),
            bin_runtime: bin_runtime.into_bytes().expect("bin_runtime"),
        };

        // Save CompiledContract object to json files in "contracts" folder
        let mut path_json = path_sol.clone();
        path_json.set_extension("json");
        serde_json::to_writer(
            &File::create(&path_json).expect("cannot create file"),
            &compiled_contract,
        )
        .expect("cannot serialize json into file");
    }
    // Generate contract binding for compiled contracts
    for entry in glob::glob("./contracts/*.json").unwrap() {
        match entry {
            Ok(path) => {
                generate_rust_contract_bindings(BINDINGS_DR, &path);
            }
            Err(e) => eprintln!("{:#?}", e),
        }
    }
    Ok(())
}

fn generate_rust_contract_bindings(bindings_dir: &str, file: &Path) {
    const SLASH: char = '/';
    const DOT: char = '.';

    let abi_source = file.to_path_buf();
    let tempbinding = file
        .to_path_buf()
        .into_os_string()
        .into_string()
        .expect("FAILED CONVERSION TO STRING");
    let filenamevec: Vec<&str> = tempbinding.split(SLASH).collect();
    let filename = filenamevec[1];

    let contractnamevector: Vec<&str> = filename.split(DOT).collect();
    let contractname = contractnamevector[0].to_lowercase();
    let destpath = format!("{}{}{}", "bindings_", contractname, ".rs");
    let destpath =
        // Path::new(&bindings_dir).join([contractname.clone(), "rs".to_string()].join("."));
        Path::new(&bindings_dir).join(destpath);
    let _ = Abigen::new(
        contractname,
        abi_source.into_os_string().into_string().expect("error"),
    )
    .expect("error")
    .generate()
    .expect("error")
    .write_to_file(destpath);
}

use ethers::{
    abi::Contract,
    core::types::Bytes,
    solc::{
        artifacts::{CompactContractRef, Error as SolcArtifactError},
        CompilerInput, CompilerOutput, EvmVersion, Solc,
    },
};
use ethers_contract_abigen::Abigen;
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

#[derive(Error, Debug)]
enum BuildError {
    /// Failed to detect solidity compiler or compiler version.
    #[error("FailedToGetSolidity({0:})")]
    FailedToGetSolidity(String),
    /// Failed to create CompilerInput artifact for given contract  
    #[error("FailedToComposeCompilerInputs(path: {path:}, {reason:}))")]
    FailedToComposeCompilerInputs { path: String, reason: String },
    /// Errors or non-ignored warnings exist in the CompilerOutpu struct
    #[error("CompilerOutputContainsErrors(path: {path:}, errors: {errors:#?})")]
    CompilerOutputContainsErrors {
        path: String,
        errors: Vec<SolcArtifactError>,
    },
    /// Vec<CompilerInput> is empty
    #[error("ArtifactError")]
    ArtifactError,
    /// Functon compile_output failed to encode CompilerInput to Vec<u8>
    #[error("CompileOutputFailure({0:})")]
    CompileOutputFailure(String),
    /// Could not convert Vec<u8> to CompilerOutput
    #[error("CompilerOutputDeSerError({0:})")]
    CompilerOutputDeSerError(String),
    /// Failed loading Abi from CompactContractRef
    #[error("ErrorLoadingContractAbi")]
    ErrorLoadingContractAbi,
    /// Failed loading Bin from CompactContractRef
    #[error("ErrorLoadingContractBin({0:})")]
    ErrorLoadingContractBin(String),
    /// Failed loading BinRuntime from CompactContractRef
    #[error("ErrorLoadingContractBinRuntime({0:})")]
    ErrorLoadingContractBinRuntime(String),
    /// Failed to convert PathBuff to String
    #[error("StringConversionError({0:})")]
    StringConversionError(String),
    /// Failed to create CompactContractRef from path + name
    #[error("FailedToLoadCompactContractRef")]
    FailedToLoadCompactContractRef,
    /// Failed Bytecode to Bytes conversion
    #[error("ByteCodeToBytesError({0:})")]
    ByteCodeToBytesError(String),
    /// Error serializing json to file
    #[error("JsonSerializatonError({0:})")]
    JsonSerializatonError(String),
    /// Errors from Abigen
    #[error("GenerateContractBindingsError({0:})")]
    GenerateContractBindingsError(String),
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

fn main() -> Result<(), BuildError> {
    println!("cargo:rerun-if-changed=build.rs");

    let solc: Solc = Solc::default();
    let _solc_version = solc
        .version()
        .map_err(|err| BuildError::FailedToGetSolidity(err.to_string()))?;

    for (name, contract_path) in CONTRACTS {
        let path_sol = Path::new(CONTRACTS_PATH).join(contract_path);
        let input = CompilerInput::new(&path_sol)
            .map_err(|err| BuildError::FailedToComposeCompilerInputs {
                path: path_sol.to_string_lossy().to_string(),
                reason: err.to_string(),
            })?
            .pop()
            .ok_or(BuildError::ArtifactError)?
            // ethers-solc: explicitly indicate the EvmVersion that corresponds to the zkevm
            // circuit's supported Upgrade, e.g. `London/Shanghai/...` specifications.
            .evm_version(EvmVersion::London);

        // compilation will either fail with Err variant or return Ok(CompilerOutput)
        // which may contain Errors or Warnings
        let output: Vec<u8> = solc
            .compile_output(&input)
            .map_err(|err| BuildError::CompileOutputFailure(err.to_string()))?;
        let mut deserializer: serde_json::Deserializer<serde_json::de::SliceRead<'_>> =
            serde_json::Deserializer::from_slice(&output);
        // The contracts to test the worst-case usage of certain opcodes, such as SDIV, MLOAD, and
        // EXTCODESIZE, generate big JSON compilation outputs. We disable the recursion limit to
        // avoid parsing failure.
        deserializer.disable_recursion_limit();

        let p = path_sol.to_str().ok_or_else(|| {
            BuildError::StringConversionError(
                "Failed to convert provided path to string".to_string(),
            )
        })?;

        let compiled = CompilerOutput::deserialize(&mut deserializer)
            .map_err(|err| BuildError::CompilerOutputDeSerError(err.to_string()))?;
        let compiled_binding = compiled.clone();

        let error_free = !{ compiled.has_error() || compiled.has_warning(WARN) };

        let _ = error_free.then_some(|| ()).ok_or_else(|| {
            BuildError::CompilerOutputContainsErrors {
                path: p.to_string(),
                errors: compiled.errors,
            }
        })?;

        let contract: CompactContractRef = compiled_binding.get(p, name).ok_or(
            BuildError::FailedToLoadCompactContractRef
        )?;

        let abi = contract
            .abi
            .ok_or(
                BuildError::ErrorLoadingContractAbi
            )?
            .clone();

        let bin = contract
            .bin
            .ok_or_else(|| {
                BuildError::ErrorLoadingContractBin("Failed to get contract Bin".to_string())
            })?
            .clone()
            .into_bytes()
            .ok_or_else(|| {
                BuildError::ByteCodeToBytesError("Could not convert bin to bytes".to_string())
            })?;

        let bin_runtime = contract
            .bin_runtime
            .ok_or_else(|| {
                BuildError::ErrorLoadingContractBinRuntime(
                    "Failed to get contract bin-runtime".to_string(),
                )
            })?
            .clone()
            .into_bytes()
            .ok_or_else(|| {
                BuildError::ByteCodeToBytesError(
                    "Could not convert bin-runtime to bytes".to_string(),
                )
            })?;

        let compiled_contract = CompiledContract {
            path: p.to_string(),
            name: name.to_string(),
            abi,
            bin,
            bin_runtime,
        };

        // Save CompiledContract object to json files in "contracts" folder
        let mut path_json = path_sol.clone();
        path_json.set_extension("json");
        serde_json::to_writer(
            &File::create(&path_json).expect("cannot create file"),
            &compiled_contract,
        )
        .map_err(|err| BuildError::JsonSerializatonError(err.to_string()))?;
    }
    // Generate contract binding for compiled contracts
    for entry in glob::glob("./contracts/*.json").unwrap() {
        match entry {
            Ok(path) => {
                let _ = generate_rust_contract_bindings(BINDINGS_DR, &path);
            }
            Err(e) => eprintln!("{:#?}", e),
        }
    }
    Ok(())
}

fn generate_rust_contract_bindings(bindings_dir: &str, file: &Path) -> Result<(), BuildError> {
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
    let destpath = Path::new(&bindings_dir).join(destpath);
    let _ = Abigen::new(
        contractname,
        abi_source
            .into_os_string()
            .into_string()
            .expect("FAILED CONVERSION TO STRING"),
    )
    .map_err(|err| BuildError::GenerateContractBindingsError(err.to_string()))?
    .generate()
    .map_err(|err| BuildError::GenerateContractBindingsError(err.to_string()))?
    .write_to_file(destpath);
    Ok(())
}

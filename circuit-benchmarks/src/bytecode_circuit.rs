//! State circuit benchmarks

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use eth_types::Field;
    use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof};
    use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG};
    use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
    use halo2_proofs::poly::kzg::strategy::SingleStrategy;
    use halo2_proofs::{
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        poly::commitment::ParamsProver,
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use hex;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::env::var;
    use zkevm_circuits::bytecode_circuit::bytecode_unroller::{unroll, UnrolledBytecode};
    use zkevm_circuits::bytecode_circuit::dev::{get_randomness, BytecodeCircuitTester};

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_bytecode_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or_else(|_| "12")
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let bytecodes_len: u32 = var("DATASCALE")
            .unwrap_or_else(|_| "0")
            .parse()
            .expect("Cannot parse NOC env var as u32");

        let randomness = get_randomness();
        // Create the circuit
        let bytecode_circuit = BytecodeCircuitTester::<Fr>::new(
            generate_code_bytes(bytecodes_len, randomness),
            2usize.pow(degree),
            randomness,
        );

        let num_rows = 1 << degree;
        const NUM_BLINDING_ROWS: usize = 7 - 1;
        let instance = vec![randomness; num_rows - NUM_BLINDING_ROWS];

        // Initialize the polynomial commitment parameters
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Bench setup generation
        let setup_message = format!("Setup generation with degree = {}", degree);
        let start1 = start_timer!(|| setup_message);
        let general_params = ParamsKZG::<Bn256>::setup(degree, &mut rng);
        let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();
        end_timer!(start1);

        // Initialize the proving key
        let vk = keygen_vk(&general_params, &bytecode_circuit).expect("keygen_vk should not fail");
        let pk =
            keygen_pk(&general_params, vk, &bytecode_circuit).expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!("Bytecode Proof generation with {} rows", degree);
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            XorShiftRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            BytecodeCircuitTester<Fr>,
        >(
            &general_params,
            &pk,
            &[bytecode_circuit],
            &[&[instance.as_slice()][..]][..],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "Bytecode Proof verification");
        let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&general_params);

        verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(
            &verifier_params,
            pk.get_vk(),
            strategy,
            &[&[instance.as_slice()][..]][..],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }

    fn generate_code_bytes<F: Field>(
        bytecodes_len: u32,
        randomness: F,
    ) -> Vec<UnrolledBytecode<F>> {
        let sample_hexbytes: &str = "608060405260405162000f6238038062000f6283398101604081905262000026\
                                     9162000519565b82816200005560017f360894a13ba1a3210667c828492db98d\
                                     ca3e2076cc3735a920a3ca505d382bbd620005f9565b60008051602062000f1b\
                                     833981519152146200007557620000756200061f565b62000083828260006200\
                                     00e7565b50620000b3905060017fb53127684a568b3173ae13b9f8a6016e243e\
                                     63b6e8ee1178d6a717850b5d6104620005f9565b60008051602062000efb8339\
                                     8151915214620000d357620000d36200061f565b620000de8262000124565b50\
                                     505062000688565b620000f2836200017f565b60008251118062000100575080\
                                     5b156200011f576200011d8383620001c160201b620002601760201c565b505b\
                                     505050565b7f7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832d\
                                     c59e38c9798f6200014f620001f0565b604080516001600160a01b0392831681\
                                     5291841660208301520160405180910390a16200017c8162000229565b50565b\
                                     6200018a81620002de565b6040516001600160a01b038216907fbc7cd75a20ee\
                                     27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b90600090a250\
                                     565b6060620001e9838360405180606001604052806027815260200162000f3b\
                                     6027913962000381565b9392505050565b60006200021a60008051602062000e\
                                     fb83398151915260001b6200046760201b620002081760201c565b5460016001\
                                     60a01b0316919050565b6001600160a01b038116620002945760405162461bcd\
                                     60e51b815260206004820152602660248201527f455243313936373a206e6577\
                                     2061646d696e20697320746865207a65726f2061604482015265646472657373\
                                     60d01b60648201526084015b60405180910390fd5b80620002bd600080516020\
                                     62000efb83398151915260001b6200046760201b620002081760201c565b8054\
                                     6001600160a01b0319166001600160a01b039290921691909117905550565b62\
                                     0002f4816200046a60201b6200028c1760201c565b620003585760405162461b\
                                     cd60e51b815260206004820152602d60248201527f455243313936373a206e65\
                                     7720696d706c656d656e746174696f6e206973206e60448201526c1bdd081848\
                                     18dbdb9d1c9858dd609a1b60648201526084016200028b565b80620002bd6000\
                                     8051602062000f1b83398151915260001b6200046760201b620002081760201c\
                                     565b60606001600160a01b0384163b620003eb5760405162461bcd60e51b8152\
                                     60206004820152602660248201527f416464726573733a2064656c6567617465\
                                     2063616c6c20746f206e6f6e2d636f6044820152651b9d1c9858dd60d21b6064\
                                     8201526084016200028b565b600080856001600160a01b031685604051620004\
                                     08919062000635565b600060405180830381855af49150503d80600081146200\
                                     0445576040519150601f19603f3d011682016040523d82523d6000602084013e\
                                     6200044a565b606091505b5090925090506200045d82828662000479565b9695\
                                     505050505050565b90565b6001600160a01b03163b151590565b606083156200\
                                     048a575081620001e9565b8251156200049b5782518084602001fd5b81604051\
                                     62461bcd60e51b81526004016200028b919062000653565b80516001600160a0\
                                     1b0381168114620004cf57600080fd5b919050565b634e487b7160e01b600052\
                                     604160045260246000fd5b60005b838110156200050757818101518382015260\
                                     2001620004ed565b838111156200011d5750506000910152565b600080600060\
                                     6084860312156200052f57600080fd5b6200053a84620004b7565b9250620005\
                                     4a60208501620004b7565b60408501519092506001600160401b038082111562\
                                     00056857600080fd5b818601915086601f8301126200057d57600080fd5b8151\
                                     81811115620005925762000592620004d4565b604051601f8201601f19908116\
                                     603f01168101908382118183101715620005bd57620005bd620004d4565b8160\
                                     4052828152896020848701011115620005d757600080fd5b620005ea83602083\
                                     0160208801620004ea565b80955050505050509250925092565b600082821015\
                                     6200061a57634e487b7160e01b600052601160045260246000fd5b500390565b\
                                     634e487b7160e01b600052600160045260246000fd5b60008251620006498184\
                                     60208701620004ea565b9190910192915050565b602081526000825180602084\
                                     015262000674816040850160208701620004ea565b601f01601f191691909101\
                                     60400192915050565b61086380620006986000396000f3fe6080604052600436\
                                     1061004e5760003560e01c80633659cfe6146100655780634f1ef28614610085\
                                     5780635c60da1b146100985780638f283970146100c9578063f851a440146100\
                                     e95761005d565b3661005d5761005b6100fe565b005b61005b6100fe565b3480\
                                     1561007157600080fd5b5061005b6100803660046106ed565b610118565b6100\
                                     5b610093366004610708565b61015f565b3480156100a457600080fd5b506100\
                                     ad6101d0565b6040516001600160a01b03909116815260200160405180910390\
                                     f35b3480156100d557600080fd5b5061005b6100e43660046106ed565b61020b\
                                     565b3480156100f557600080fd5b506100ad610235565b61010661029b565b61\
                                     011661011161033a565b610344565b565b610120610368565b6001600160a01b\
                                     0316336001600160a01b03161415610157576101548160405180602001604052\
                                     806000815250600061039b565b50565b6101546100fe565b610167610368565b\
                                     6001600160a01b0316336001600160a01b031614156101c8576101c383838380\
                                     80601f0160208091040260200160405190810160405280939291908181526020\
                                     018383808284376000920191909152506001925061039b915050565b50505056\
                                     5b6101c36100fe565b60006101da610368565b6001600160a01b031633600160\
                                     0160a01b03161415610200576101fb61033a565b905090565b6102086100fe56\
                                     5b90565b610213610368565b6001600160a01b0316336001600160a01b031614\
                                     1561015757610154816103c6565b600061023f610368565b6001600160a01b03\
                                     16336001600160a01b03161415610200576101fb610368565b60606102858383\
                                     6040518060600160405280602781526020016108076027913961041a565b9392\
                                     505050565b6001600160a01b03163b151590565b6102a3610368565b60016001\
                                     60a01b0316336001600160a01b031614156101165760405162461bcd60e51b81\
                                     5260206004820152604260248201527f5472616e73706172656e745570677261\
                                     646561626c6550726f78793a2061646d60448201527f696e2063616e6e6f7420\
                                     66616c6c6261636b20746f2070726f78792074617267606482015261195d60f2\
                                     1b608482015260a4015b60405180910390fd5b60006101fb6104f5565b366000\
                                     8037600080366000845af43d6000803e808015610363573d6000f35b3d6000fd\
                                     5b60007fb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a71785\
                                     0b5d61035b546001600160a01b0316919050565b6103a48361051d565b600082\
                                     5111806103b15750805b156101c3576103c08383610260565b50505050565b7f\
                                     7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f\
                                     6103ef610368565b604080516001600160a01b03928316815291841660208301\
                                     520160405180910390a16101548161055d565b60606104258461028c565b6104\
                                     805760405162461bcd60e51b815260206004820152602660248201527f416464\
                                     726573733a2064656c65676174652063616c6c20746f206e6f6e2d636f604482\
                                     0152651b9d1c9858dd60d21b6064820152608401610331565b60008085600160\
                                     0160a01b03168560405161049b91906107b7565b600060405180830381855af4\
                                     9150503d80600081146104d6576040519150601f19603f3d011682016040523d\
                                     82523d6000602084013e6104db565b606091505b50915091506104eb82828661\
                                     0606565b9695505050505050565b60007f360894a13ba1a3210667c828492db9\
                                     8dca3e2076cc3735a920a3ca505d382bbc61038c565b6105268161063f565b60\
                                     40516001600160a01b038216907fbc7cd75a20ee27fd9adebab32041f755214d\
                                     bc6bffa90cc0225b39da2e5c2d3b90600090a250565b6001600160a01b038116\
                                     6105c25760405162461bcd60e51b815260206004820152602660248201527f45\
                                     5243313936373a206e65772061646d696e20697320746865207a65726f206160\
                                     448201526564647265737360d01b6064820152608401610331565b807fb53127\
                                     684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d61035b8054\
                                     6001600160a01b0319166001600160a01b039290921691909117905550565b60\
                                     608315610615575081610285565b8251156106255782518084602001fd5b8160\
                                     405162461bcd60e51b815260040161033191906107d3565b6106488161028c56\
                                     5b6106aa5760405162461bcd60e51b815260206004820152602d60248201527f\
                                     455243313936373a206e657720696d706c656d656e746174696f6e206973206e\
                                     60448201526c1bdd08184818dbdb9d1c9858dd609a1b60648201526084016103\
                                     31565b807f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca\
                                     505d382bbc6105e5565b80356001600160a01b03811681146106e857600080fd\
                                     5b919050565b6000602082840312156106ff57600080fd5b610285826106d156\
                                     5b60008060006040848603121561071d57600080fd5b610726846106d1565b92\
                                     50602084013567ffffffffffffffff8082111561074357600080fd5b81860191\
                                     5086601f83011261075757600080fd5b81358181111561076657600080fd5b87\
                                     602082850101111561077857600080fd5b602083019450809350505050925092\
                                     5092565b60005b838110156107a657818101518382015260200161078e565b83\
                                     8111156103c05750506000910152565b600082516107c981846020870161078b\
                                     565b9190910192915050565b60208152600082518060208401526107f2816040\
                                     85016020870161078b565b601f01601f1916919091016040019291505056fe41\
                                     6464726573733a206c6f772d6c6576656c2064656c65676174652063616c6c20\
                                     6661696c6564a2646970667358221220fb0d75414bd881ce16381528bf0b9b2c\
                                     1bea4c3e27069fcb6981b67d1535643064736f6c63430008090033b53127684a\
                                     568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103360894a13b\
                                     a1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc4164647265\
                                     73733a206c6f772d6c6576656c2064656c65676174652063616c6c206661696c\
                                     6564000000000000000000000000320bb4633bb62027d4b1d7827ddc81cc7345\
                                     863900000000000000000000000071d78dc7ccc0e037e12de1e50f5470903ce3\
                                     7148000000000000000000000000000000000000000000000000000000000000\
                                     0060000000000000000000000000000000000000000000000000000000000000\
                                     00000000000000000000000000000000000000000000";
        let bytes = hex::decode(sample_hexbytes).expect("hex decode failed");
        (0..bytecodes_len)
            .map(|_| unroll(bytes.clone(), randomness))
            .collect::<Vec<UnrolledBytecode<F>>>()
    }
}

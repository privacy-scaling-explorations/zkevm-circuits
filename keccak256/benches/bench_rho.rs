#[macro_use]
extern crate criterion;

use halo2::circuit::Layouter;
use halo2::circuit::SimpleFloorPlanner;
use halo2::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
    ConstraintSystem, Error,
};
use halo2::poly::commitment::Params;
use halo2::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use itertools::Itertools;
use keccak256::arith_helpers::*;
use keccak256::common::*;
use keccak256::gates::gate_helpers::*;
use keccak256::gates::rho::RhoConfig;
use keccak256::gates::rho_checks::RhoAdvices;
use keccak256::keccak_arith::*;

use pasta_curves::arithmetic::FieldExt;
use pasta_curves::pallas;
use std::convert::TryInto;

use criterion::Criterion;
use halo2::pasta::EqAffine;

/// run cargo bench bench_rho_gate
fn bench_rho_gate(c: &mut Criterion) {
    let mut group = c.benchmark_group("Rho gate bench");
    group.sample_size(10);
    #[derive(Default, Clone)]
    struct MyCircuit<F> {
        in_state: [F; 25],
        out_state: [F; 25],
    }
    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = RhoConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let state: [Column<Advice>; 25] = (0..25)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            let cols: [Column<Advice>; 7] = state[0..7].try_into().unwrap();
            let adv = RhoAdvices::from(cols);
            let axiliary = [state[8], state[9]];

            let base13_to_9 = [
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
            ];
            let special = [meta.fixed_column(), meta.fixed_column()];
            RhoConfig::configure(
                meta,
                state,
                &adv,
                axiliary,
                base13_to_9,
                special,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.load(&mut layouter)?;
            let state = layouter.assign_region(
                || "assign input state",
                |mut region| {
                    let offset = 0;
                    let state: [Lane<F>; 25] = self
                        .in_state
                        .iter()
                        .enumerate()
                        .map(|(idx, value)| {
                            let cell = region
                                .assign_advice(
                                    || format!("lane {}", idx),
                                    config.state[idx],
                                    offset,
                                    || Ok(*value),
                                )
                                .unwrap();
                            Lane {
                                cell,
                                value: *value,
                            }
                        })
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap();
                    Ok(state)
                },
            )?;
            let next_state =
                config.assign_rotation_checks(&mut layouter, state)?;
            assert_eq!(
                next_state.clone().map(|lane| lane.value),
                self.out_state
            );
            layouter.assign_region(
                || "assign output state",
                |mut region| {
                    let offset = 1;
                    config.assign_region(
                        &mut region,
                        offset,
                        next_state.clone(),
                    )?;
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    let input1: State = [
        [102, 111, 111, 98, 97],
        [114, 0, 5, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 5, 0],
        [0, 0, 0, 0, 0],
    ];
    let mut in_biguint = StateBigInt::default();
    let mut in_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];

    for (x, y) in (0..5).cartesian_product(0..5) {
        in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
    }
    let s0_arith = KeccakFArith::theta(&in_biguint);
    for (x, y) in (0..5).cartesian_product(0..5) {
        in_state[5 * x + y] = biguint_to_f(&s0_arith[(x, y)]).unwrap();
    }
    let s1_arith = KeccakFArith::rho(&s0_arith);
    let mut out_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];
    for (x, y) in (0..5).cartesian_product(0..5) {
        out_state[5 * x + y] = biguint_to_f(&s1_arith[(x, y)]).unwrap();
    }
    let circuit = MyCircuit::<pallas::Base> {
        in_state,
        out_state,
    };
    let k = 15;
    let params: Params<EqAffine> = Params::new(k);

    // Initialize the proving key
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    // proving key takes 3 mins
    let pk =
        keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    let name = "rho";

    let prover_name = name.to_string() + "-prover";
    let verifier_name = name.to_string() + "-verifier";

    group.bench_function(&prover_name, |b| {
        b.iter(|| {
            // Create a proof
            let mut transcript =
                Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            create_proof(&params, &pk, &[circuit.clone()], &[], &mut transcript)
                .expect("proof generation should not fail")
        });
    });

    // Create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(&params, &pk, &[circuit], &[], &mut transcript)
        .expect("proof generation should not fail");
    let proof = transcript.finalize();
    group.bench_function(&verifier_name, |b| {
        b.iter(|| {
            let msm = params.empty_msm();
            let mut transcript =
                Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
            let guard =
                verify_proof(&params, pk.get_vk(), msm, &[], &mut transcript)
                    .unwrap();
            let msm = guard.clone().use_challenges();
            assert!(msm.eval());
        });
    });
    group.finish();
}

criterion_group!(benches, bench_rho_gate);
criterion_main!(benches);

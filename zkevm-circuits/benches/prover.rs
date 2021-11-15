use halo2::arithmetic::FieldExt;
use halo2::circuit::{Cell, Layouter, SimpleFloorPlanner};
use halo2::plonk::*;
use halo2::poly::{commitment::Setup, Rotation};
use halo2::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use pairing::bn256::{Bn256, Fr as Fp};

use std::marker::PhantomData;

#[derive(Clone)]
struct PlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,
}

trait StandardCs<FF: FieldExt> {
    fn raw_multiply<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Result<(FF, FF, FF), Error>;
    fn raw_add<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Result<(FF, FF, FF), Error>;
    fn copy(
        &self,
        layouter: &mut impl Layouter<FF>,
        a: Cell,
        b: Cell,
    ) -> Result<(), Error>;
}

#[derive(Clone)]
struct MyCircuit<F: FieldExt> {
    a: Option<F>,
    zero: Option<F>,
    k: u32,
}

struct StandardPlonk<F: FieldExt> {
    config: PlonkConfig,
    _marker: PhantomData<F>,
}

impl<FF: FieldExt> StandardPlonk<FF> {
    fn new(config: PlonkConfig) -> Self {
        StandardPlonk {
            config,
            _marker: PhantomData,
        }
    }
}

impl<FF: FieldExt> StandardCs<FF> for StandardPlonk<FF> {
    fn raw_multiply<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        mut f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Result<(FF, FF, FF), Error>,
    {
        layouter.assign_region(
            || "mul",
            |mut region| {
                let mut values = None;
                let lhs = region.assign_advice(
                    || "lhs",
                    self.config.a,
                    0,
                    || {
                        values = Some(f()?);
                        Ok(values.ok_or(Error::SynthesisError)?.0)
                    },
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    self.config.b,
                    0,
                    || Ok(values.ok_or(Error::SynthesisError)?.1),
                )?;

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || Ok(values.ok_or(Error::SynthesisError)?.2),
                )?;

                region.assign_fixed(
                    || "a",
                    self.config.sa,
                    0,
                    || Ok(FF::zero()),
                )?;
                region.assign_fixed(
                    || "b",
                    self.config.sb,
                    0,
                    || Ok(FF::zero()),
                )?;
                region.assign_fixed(
                    || "c",
                    self.config.sc,
                    0,
                    || Ok(FF::one()),
                )?;
                region.assign_fixed(
                    || "a * b",
                    self.config.sm,
                    0,
                    || Ok(FF::one()),
                )?;

                Ok((lhs, rhs, out))
            },
        )
    }

    fn raw_add<F>(
        &self,
        layouter: &mut impl Layouter<FF>,
        mut f: F,
    ) -> Result<(Cell, Cell, Cell), Error>
    where
        F: FnMut() -> Result<(FF, FF, FF), Error>,
    {
        layouter.assign_region(
            || "mul",
            |mut region| {
                let mut values = None;
                let lhs = region.assign_advice(
                    || "lhs",
                    self.config.a,
                    0,
                    || {
                        values = Some(f()?);
                        Ok(values.ok_or(Error::SynthesisError)?.0)
                    },
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    self.config.b,
                    0,
                    || Ok(values.ok_or(Error::SynthesisError)?.1),
                )?;

                let out = region.assign_advice(
                    || "out",
                    self.config.c,
                    0,
                    || Ok(values.ok_or(Error::SynthesisError)?.2),
                )?;

                region.assign_fixed(
                    || "a",
                    self.config.sa,
                    0,
                    || Ok(FF::one()),
                )?;
                region.assign_fixed(
                    || "b",
                    self.config.sb,
                    0,
                    || Ok(FF::one()),
                )?;
                region.assign_fixed(
                    || "c",
                    self.config.sc,
                    0,
                    || Ok(FF::one()),
                )?;
                region.assign_fixed(
                    || "a * b",
                    self.config.sm,
                    0,
                    || Ok(FF::zero()),
                )?;

                Ok((lhs, rhs, out))
            },
        )
    }

    fn copy(
        &self,
        layouter: &mut impl Layouter<FF>,
        left: Cell,
        right: Cell,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "copy",
            |mut region| {
                region.constrain_equal(left, right)?;
                region.constrain_equal(left, right)
            },
        )
    }
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            a: None,
            zero: None,
            k: self.k,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> PlonkConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        meta.enable_equality(a.into());
        meta.enable_equality(b.into());
        meta.enable_equality(c.into());

        let sm = meta.fixed_column();
        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();

        meta.create_gate("mini plonk", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let sm = meta.query_fixed(sm, Rotation::cur());

            vec![
                a.clone() * sa
                    + b.clone() * sb
                    + a * b * sm
                    + (c * sc * (-F::one())),
            ]
        });

        PlonkConfig {
            a,
            b,
            c,
            sa,
            sb,
            sc,
            sm,
            // perm,
        }
    }

    fn synthesize(
        &self,
        config: PlonkConfig,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let cs = StandardPlonk::new(config);

        for _ in 0..1 << ((self.k - 1) - 3) {
            let mut a_squared = None;
            let (a0, _, c0) = cs.raw_multiply(&mut layouter, || {
                a_squared = self.a.map(|a| a.square());
                Ok((
                    self.a.ok_or(Error::SynthesisError)?,
                    self.a.ok_or(Error::SynthesisError)?,
                    a_squared.ok_or(Error::SynthesisError)?,
                ))
            })?;
            let (a1, b1, _) = cs.raw_add(&mut layouter, || {
                let fin = a_squared.and_then(|a2| self.a.map(|a| a + a2));
                Ok((
                    self.a.ok_or(Error::SynthesisError)?,
                    a_squared.ok_or(Error::SynthesisError)?,
                    fin.ok_or(Error::SynthesisError)?,
                ))
            })?;
            cs.copy(&mut layouter, a0, a1)?;
            cs.copy(&mut layouter, b1, c0)?;
        }

        Ok(())
    }
}

fn main() {
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    let k = 8;
    let public_inputs_size = 0;

    let empty_circuit: MyCircuit<Fp> = MyCircuit {
        a: None,
        zero: None,
        k,
    };

    // Initialize the polynomial commitment parameters
    let rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32,
        0x54, 0x06, 0xbc, 0xe5,
    ]);

    let params = Setup::<Bn256>::new(k, rng);
    let verifier_params =
        Setup::<Bn256>::verifier_params(&params, public_inputs_size).unwrap();

    // Initialize the proving key
    let vk =
        keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit)
        .expect("keygen_pk should not fail");

    let circuit: MyCircuit<Fp> = MyCircuit {
        a: Some(Fp::from(5)),
        zero: Some(Fp::zero()),
        k,
    };

    // Create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    use std::time::Instant;
    let _dur = Instant::now();

    create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
        .expect("proof generation should not fail");

    println!("proving period: {:?}", _dur.elapsed());

    let proof = transcript.finalize();

    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(bool::from(
        verify_proof(&verifier_params, pk.get_vk(), &[&[]], &mut transcript)
            .unwrap()
    ));
}

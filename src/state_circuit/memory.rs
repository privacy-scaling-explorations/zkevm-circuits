use crate::gadget::Variable;
use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use pasta_curves::{arithmetic::FieldExt, pallas};
use std::marker::PhantomData;

/*
Example memory table:

| address | step | value | flag |
---------------------------------
|    0    |   0  |   0   |   1  |
|    0    |  12  |  12   |   1  |
|    0    |  24  |  12   |   0  |
|    1    |   0  |   0   |   1  |
|    1    |  17  |  32   |   1  |
|    1    |  89  |  32   |   0  |
*/

/*
Example bus mapping:

| step | memory_flag | memory_address | memory_value |
------------------------------------------------------
|  12  |      1      |        0       |      12      |
|  17  |      1      |        1       |      32      |
|  24  |      0      |        0       |      12      |
|  89  |      0      |        1       |      32      |
*/

/// In the state proof, memory operations are ordered first by address, and then by step.
/// Memory is initialised at 0 for each new address.
/// Memory is a word-addressed byte array, i.e. a mapping from a 253-bit word -> u8.
#[derive(Copy, Clone, Debug)]
struct MemoryAddress<F: FieldExt>(F);

/// Global counter
#[derive(Copy, Clone, Debug)]
struct Step(usize);

/// TODO: In the EVM we can only read memory values in 32 bytes, but can write either
/// single-byte or 32-byte chunks. In zkEVM:
/// - Are we reading single bytes or 32-byte chunks? TBD
/// - We are writing a single field element (253 bits)
#[derive(Copy, Clone, Debug)]
struct Value<F: FieldExt>(F);

#[derive(Clone, Debug)]
enum ReadWrite<F: FieldExt> {
    // flag == 0
    Read(Step, Value<F>),
    // flag == 1
    Write(Step, Value<F>),
}

impl<F: FieldExt> ReadWrite<F> {
    fn step(&self) -> Step {
        match self {
            Self::Read(step, _) | Self::Write(step, _) => *step,
        }
    }

    fn value(&self) -> Value<F> {
        match self {
            Self::Read(_, value) | Self::Write(_, value) => *value,
        }
    }

    fn flag(&self) -> bool {
        match self {
            Self::Read(..) => false,
            Self::Write(..) => true,
        }
    }
}

#[derive(Clone, Debug)]
/// All the read/write operations that happen at this address.
pub(crate) struct MemoryOp<F: FieldExt> {
    address: MemoryAddress<F>,
    steps: Vec<Option<ReadWrite<F>>>,
}

/*
Example bus mapping:

| step | memory_flag | memory_address | memory_value |
------------------------------------------------------
|  12  |      1      |       0        |      12      |
|  17  |      1      |       1        |      32      |
|  24  |      0      |       0        |      12      |
|  89  |      0      |       1        |      32      |
*/

/// A mapping derived from witnessed memory operations.
/// TODO: The complete version of this mapping will involve storage, stack,
/// and opcode details as well.
#[derive(Clone, Debug)]
pub(crate) struct BusMapping<F: FieldExt> {
    step: Variable<usize, F>,
    memory_flag: Variable<bool, F>,
    memory_address: Variable<F, F>,
    memory_value: Variable<F, F>,
}

#[derive(Clone, Debug)]
pub(crate) struct Config<F: FieldExt, const NUM_STEPS: usize> {
    q_memory: Selector,
    q_memory_init: Selector,
    q_same_value: Selector,
    address: Column<Advice>,
    step: Column<Advice>,
    value: Column<Advice>,
    flag: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const NUM_STEPS: usize> Config<F, NUM_STEPS> {
    /// Set up custom gates and lookup arguments for this configuration.
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_memory = meta.selector();
        let q_memory_init = meta.selector();
        let q_same_value = meta.selector();
        let address = meta.advice_column();
        let step = meta.advice_column();
        let value = meta.advice_column();
        let flag = meta.advice_column();

        // Constraints for each step. These are activated when q_memory is nonzero.
        meta.create_gate("Memory operation", |meta| {
            let q_memory = meta.query_selector(q_memory);
            let q_memory_init = meta.query_selector(q_memory_init);
            let q_same_value = meta.query_selector(q_same_value);

            // If address_cur != address_prev, this is an `init`. We must constrain:
            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - steps[0] == 0

            let value_expr = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let step = meta.query_advice(step, Rotation::cur());

            let check_flag_init = {
                let one = Expression::Constant(F::one());
                one - flag.clone()
            };

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = {
                let one = Expression::Constant(F::one());
                flag.clone() * (one - flag.clone())
            };

            // If flag == 0 (read), and step != 0, value_prev == value_cur
            let value_prev = meta.query_advice(value, Rotation::prev());
            let same_value_check = { value_expr.clone() - value_prev };

            // step_prev < step_cur
            // TODO: Figure out how to enforce this. Suggestion: lookup step_cur, step_prev,
            // and their difference `step_cur - step_prev` in a table.

            // TODO: address[i] == address[i + 1] == ... == address[i + NUM_STEPS - 1]

            vec![
                q_memory * bool_check_flag,
                q_memory_init.clone() * value_expr,
                q_memory_init.clone() * check_flag_init,
                q_memory_init.clone() * step,
                q_same_value * same_value_check,
            ]
        });

        Config {
            q_memory,
            q_memory_init,
            q_same_value,
            address,
            step,
            value,
            flag,
            _marker: PhantomData,
        }
    }

    /// Load lookup table / other fixed constants for this configuration.
    pub(crate) fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        todo!()
    }

    /// Assign cells.
    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        ops: Vec<MemoryOp<F>>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        layouter.assign_region(
            || "Memory operations",
            |mut region| {
                let mut offset = 0;
                for op in ops.iter() {
                    let address = op.address;

                    for (step_offset, step) in op.steps.iter().enumerate() {
                        let bus_mapping =
                            self.step(step_offset, &mut region, offset, address, step)?;

                        offset += 1;

                        // TODO: order by step
                        bus_mappings.push(bus_mapping);
                    }
                }

                // FIXME
                // dummy:
                let value = ops[0].steps[0]
                    .as_ref()
                    .map(|read_write| read_write.value().0);
                region.assign_advice(
                    || "value",
                    self.value,
                    31,
                    || value.ok_or(Error::SynthesisError),
                )?;

                Ok(())
            },
        )?;

        Ok(bus_mappings)
    }

    /// Assign cells for each step in an operation.
    fn step(
        &self,
        step_offset: usize,
        region: &mut Region<'_, F>,
        offset: usize,
        address: MemoryAddress<F>,
        read_write: &Option<ReadWrite<F>>,
    ) -> Result<BusMapping<F>, Error> {
        if step_offset == 0 {
            self.q_memory_init.enable(region, offset)?;
        } else {
            self.q_memory.enable(region, offset)?;
        }

        // Assign `address`
        let memory_address = {
            let cell =
                region.assign_advice(|| "address", self.address, offset, || Ok(address.0))?;
            Variable::<F, F> {
                cell,
                field_elem: Some(address.0),
                value: Some(address.0),
            }
        };

        // Assign `step`
        let step = {
            let value = read_write.as_ref().map(|read_write| read_write.step().0);
            let field_elem = value.map(|value| F::from_u64(value as u64));

            let cell = region.assign_advice(
                || "step",
                self.step,
                offset,
                || field_elem.ok_or(Error::SynthesisError),
            )?;

            Variable::<usize, F> {
                cell,
                field_elem,
                value,
            }
        };

        // Assign `value`
        let memory_value = {
            let value = read_write.as_ref().map(|read_write| read_write.value().0);
            let cell = region.assign_advice(
                || "value",
                self.value,
                offset,
                || value.ok_or(Error::SynthesisError),
            )?;

            Variable::<F, F> {
                cell,
                field_elem: value,
                value,
            }
        };

        // Assign memory_flag
        let memory_flag = {
            let value = read_write.as_ref().map(|read_write| read_write.flag());
            let field_elem = value.map(|value| F::from_u64(value as u64));
            let cell = region.assign_advice(
                || "flag",
                self.flag,
                offset,
                || field_elem.ok_or(Error::SynthesisError),
            )?;

            Variable::<bool, F> {
                cell,
                field_elem,
                value,
            }
        };

        if step_offset > 0 && !memory_flag.value.unwrap() {
            self.q_same_value.enable(region, offset)?;
        }

        Ok(BusMapping {
            step,
            memory_flag,
            memory_address,
            memory_value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Config, MemoryAddress, MemoryOp, ReadWrite, Step, Value};
    use halo2::{
        circuit::layouter::SingleChipLayouter,
        dev::MockProver,
        plonk::{Assignment, Circuit, ConstraintSystem, Error},
    };

    use pasta_curves::{arithmetic::FieldExt, pallas};
    use std::marker::PhantomData;

    #[test]
    fn memory_circuit() {
        struct MemoryCircuit<F: FieldExt, const NUM_STEPS: usize> {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt, const NUM_STEPS: usize> Circuit<F> for MemoryCircuit<F, NUM_STEPS> {
            type Config = Config<F, NUM_STEPS>;

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Config::configure(meta)
            }

            fn synthesize(
                &self,
                cs: &mut impl Assignment<F>,
                config: Self::Config,
            ) -> Result<(), Error> {
                let layouter = SingleChipLayouter::new(cs)?;

                config.assign(layouter, self.ops.clone())?;

                Ok(())
            }
        }

        let op_0 = MemoryOp {
            address: MemoryAddress(pallas::Base::zero()),
            steps: vec![
                Some(ReadWrite::Write(Step(0), Value(pallas::Base::from_u64(0)))),
                Some(ReadWrite::Write(
                    Step(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(Step(24), Value(pallas::Base::from_u64(12)))),
            ],
        };

        let op_1 = MemoryOp {
            address: MemoryAddress(pallas::Base::one()),
            steps: vec![
                Some(ReadWrite::Write(Step(0), Value(pallas::Base::from_u64(0)))),
                Some(ReadWrite::Write(
                    Step(17),
                    Value(pallas::Base::from_u64(32)),
                )),
                Some(ReadWrite::Read(Step(89), Value(pallas::Base::from_u64(32)))),
            ],
        };

        let circuit = MemoryCircuit::<pallas::Base, 4> {
            ops: vec![op_0, op_1],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(5, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}

use crate::gadget::Variable;
use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;

use std::marker::PhantomData;

/*
Example memory table:

| address | global_counter | value | flag |
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

| global_counter | memory_flag | memory_address | memory_value |
------------------------------------------------------
|  12  |      1      |        0       |      12      |
|  17  |      1      |        1       |      32      |
|  24  |      0      |        0       |      12      |
|  89  |      0      |        1       |      32      |
*/

/// In the state proof, memory operations are ordered first by address, and then by global_counter.
/// Memory is initialised at 0 for each new address.
/// Memory is a word-addressed byte array, i.e. a mapping from a 253-bit word -> u8.
#[derive(Copy, Clone, Debug)]
struct MemoryAddress<F: FieldExt>(F);

/// Global counter
#[derive(Copy, Clone, Debug)]
struct GlobalCounter(usize);

/// TODO: In the EVM we can only read memory values in 32 bytes, but can write either
/// single-byte or 32-byte chunks. In zkEVM:
/// - Are we reading single bytes or 32-byte chunks? TBD
/// - We are writing a single field element (253 bits)
#[derive(Copy, Clone, Debug)]
struct Value<F: FieldExt>(F);

#[derive(Clone, Debug)]
enum ReadWrite<F: FieldExt> {
    // flag == 0
    Read(GlobalCounter, Value<F>),
    // flag == 1
    Write(GlobalCounter, Value<F>),
}

impl<F: FieldExt> ReadWrite<F> {
    fn global_counter(&self) -> GlobalCounter {
        match self {
            Self::Read(global_counter, _) | Self::Write(global_counter, _) => *global_counter,
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
    global_counters: Vec<Option<ReadWrite<F>>>,
}

/*
Example bus mapping:

| global_counter | memory_flag | memory_address | memory_value |
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
    global_counter: Variable<usize, F>,
    memory_flag: Variable<bool, F>,
    memory_address: Variable<F, F>,
    memory_value: Variable<F, F>,
}

#[derive(Clone, Debug)]
pub(crate) struct Config<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> {
    q_memory: Column<Fixed>,
    address: Column<Advice>,
    global_counter: Column<Advice>,
    value: Column<Advice>,
    flag: Column<Advice>,
    global_counter_table: Column<Fixed>,
    address_table: Column<Fixed>,
    address_table_zero: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize>
    Config<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
{
    /// Set up custom gates and lookup arguments for this configuration.
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_memory = meta.fixed_column();
        let address = meta.advice_column();
        let global_counter = meta.advice_column();
        let value = meta.advice_column();
        let flag = meta.advice_column();
        let global_counter_table = meta.fixed_column();
        let address_table = meta.fixed_column();
        let address_table_zero = meta.fixed_column();

        // Note:
        // q_memory = 0: for rows for which we do not set any column
        // q_memory = 1: first row
        // q_memory = 2: init rows (except the first row)
        // q_memory = 3: all rows (for which we do not set any column) except init rows

        // A gate for the first operation (does not need Rotation::prev).
        meta.create_gate("Memory first row operation", |meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());
            let two = Expression::Constant(F::one() + F::one());
            let three = Expression::Constant(F::one() + F::one() + F::one());
            let is_first_row = q_memory.clone() * (two - q_memory.clone()) * (three - q_memory);

            let value = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0

            // Note: is_first_row is either 0 or 2 (when q_memory is 1).
            // Having 2 in the constraints below is ok, we don't need to normalize it.
            vec![
                is_first_row.clone() * value,
                is_first_row.clone() * (Expression::Constant(F::one()) - flag.clone()),
                is_first_row * global_counter,
            ]
        });

        meta.create_gate("Memory operation", |meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());

            // If address_cur != address_prev, this is an `init`. We must constrain:
            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0

            let address_diff = {
                let address_prev = meta.query_advice(address, Rotation::prev());
                let address_cur = meta.query_advice(address, Rotation::cur());
                address_cur - address_prev
            };

            let value_cur = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            let one = Expression::Constant(F::one());
            let is_not_first_row = q_memory.clone() * (q_memory.clone() - one);

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

            let value_prev = meta.query_advice(value, Rotation::prev());
            // If flag == 0 (read), and global_counter != 0, value_prev == value_cur
            let q_read = {
                let one = Expression::Constant(F::one());
                one - flag.clone()
            };

            // Note: is_not_first_row is either 0 or 2 (when q_memory is 2) or 6 (when q_memory is 3).
            // Having 2 or 6 in the constraints below is ok, we don't need to normalize it.
            vec![
                is_not_first_row.clone() * bool_check_flag,
                is_not_first_row.clone() * address_diff.clone() * value_cur.clone(),
                is_not_first_row.clone() * address_diff.clone() * check_flag_init,
                is_not_first_row.clone() * address_diff * global_counter,
                is_not_first_row * q_read * (value_cur - value_prev),
            ]
        });

        // global_counter monotonicity:
        meta.lookup(|meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());

            let global_counter_table = meta.query_fixed(global_counter_table, Rotation::cur());

            let global_counter_prev = meta.query_advice(global_counter, Rotation::prev());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::one() + F::one());
            let is_not_init = q_memory.clone()
                * (q_memory.clone() - one.clone())
                * (q_memory.clone() - two.clone());

            let inv = F::from_u64(6 as u64).invert().unwrap();
            let i = Expression::Constant(inv);

            vec![(
                // Note: is_not_init can only be 6 (when q_memory is 3) or 0 - we multiply it by 1/6 to get 1
                is_not_init.clone() * i.clone() * (global_counter.clone() - global_counter_prev)
                    + (Expression::Constant(F::one()) - is_not_init * i), // default to 1 when is_not_init is 0
                global_counter_table,
            )]
        });

        // TODO: figure out why checks fail when put in the vec of the same meta.lookup call
        // (for some cases having a vector with more than one tuple works though)

        // address is in the allowed range - for q_memory = 1:
        meta.lookup(|meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());
            let address_cur = meta.query_advice(address, Rotation::cur());
            let address_table_zero = meta.query_fixed(address_table_zero, Rotation::cur());

            let two = Expression::Constant(F::one() + F::one());
            let three = Expression::Constant(F::one() + F::one() + F::one());
            let is_first_row =
                q_memory.clone() * (two - q_memory.clone()) * (three.clone() - q_memory.clone());

            let inv = F::from_u64(2 as u64).invert().unwrap();
            let i = Expression::Constant(inv);

            vec![(
                // when q_memory is 1, is_first_row is 2 - multiply by 1/2
                is_first_row.clone() * address_cur.clone() * i.clone(),
                address_table_zero,
            )]
        });

        // address is in the allowed range - for q_memory = 2:
        meta.lookup(|meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());
            let address_cur = meta.query_advice(address, Rotation::cur());
            let address_table_zero = meta.query_fixed(address_table_zero, Rotation::cur());

            let one = Expression::Constant(F::one());
            let three = Expression::Constant(F::one() + F::one() + F::one());
            let is_init_and_not_first_row =
                q_memory.clone() * (q_memory.clone() - one) * (three - q_memory);

            let inv = F::from_u64(2 as u64).invert().unwrap();
            let i = Expression::Constant(inv);

            vec![(
                // when q_memory is 2, is_init_and_not_first_row is 2 - multiply by 1/2
                is_init_and_not_first_row.clone() * address_cur.clone() * i.clone(),
                address_table_zero,
            )]
        });

        // address is in the allowed range - for q_memory = 3:
        meta.lookup(|meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());
            let address_table_zero = meta.query_fixed(address_table_zero, Rotation::cur());
            let address_cur = meta.query_advice(address, Rotation::cur());

            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::one() + F::one());
            let is_not_init = q_memory.clone()
                * (q_memory.clone() - one.clone())
                * (q_memory.clone() - two.clone());

            let inv = F::from_u64(6 as u64).invert().unwrap();
            let i = Expression::Constant(inv);

            vec![
                // when q_memory is 3, is_not_init is 6 - multiply by 1/6
                (is_not_init.clone() * address_cur * i, address_table_zero),
            ]
        });

        // if address_prev != address_cur, address_prev < address_cur;
        meta.lookup(|meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());
            let address_table = meta.query_fixed(address_table, Rotation::cur());

            let address_cur = meta.query_advice(address, Rotation::cur());
            let address_prev = meta.query_advice(address, Rotation::prev());
            let address_diff = address_cur.clone() - address_prev;

            let one = Expression::Constant(F::one());
            let three = Expression::Constant(F::one() + F::one() + F::one());
            let is_init_and_not_first_row =
                q_memory.clone() * (q_memory.clone() - one.clone()) * (three - q_memory.clone());

            let inv = F::from_u64(2 as u64).invert().unwrap();
            let i = Expression::Constant(inv);

            vec![(
                // Note: is_init_and_not_first_row can only be 2 (when q_memory is 2) or 0 - we multiply it by 1/2 to get 1
                is_init_and_not_first_row.clone() * address_diff.clone() * i.clone()
                    + (Expression::Constant(F::one()) - is_init_and_not_first_row.clone() * i), // default to 1 when is_init_and_not_first_row is 0
                address_table,
            )]
        });

        // global_counter is in the allowed range:
        meta.lookup(|meta| {
            let q_memory = meta.query_fixed(q_memory, Rotation::cur());

            let global_counter_table = meta.query_fixed(global_counter_table, Rotation::cur());

            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::one() + F::one());
            let qs_lookup = q_memory.clone() * (q_memory.clone() - one) * (q_memory.clone() - two);

            let inv = F::from_u64(6 as u64).invert().unwrap();
            let i = Expression::Constant(inv);

            vec![(
                // We only need to check global_counter is in some range when q_memory is 3.
                // When q_memory is 1 and 2, the global counter must be 0 and this is checked
                // by create_gate "Memory first row operation" and "Memory operation"
                qs_lookup.clone() * i.clone() * global_counter
                    + (Expression::Constant(F::one()) - qs_lookup * i), // default to 1 when qs_lookup is 0
                global_counter_table,
            )]
        });

        Config {
            q_memory,
            address,
            global_counter,
            value,
            flag,
            global_counter_table,
            address_table,
            address_table_zero,
            _marker: PhantomData,
        }
    }

    /// Load lookup table / other fixed constants for this configuration.
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter
            .assign_region(
                || "global counter table",
                |mut region| {
                    // generate range table [1, GLOBAL_COUNTER_MAX-1]
                    for idx in 0..GLOBAL_COUNTER_MAX.next_power_of_two() {
                        let to = if idx > 0 && idx < GLOBAL_COUNTER_MAX {
                            F::from_u64(idx as u64)
                        } else {
                            // padding with 1
                            F::one()
                        };
                        region.assign_fixed(
                            || "global counter table",
                            self.global_counter_table,
                            idx,
                            || Ok(to),
                        )?;
                    }
                    Ok(())
                },
            )
            .ok();

        layouter
            .assign_region(
                || "address table",
                |mut region| {
                    for idx in 0..ADDRESS_MAX.next_power_of_two() {
                        let to = if idx > 0 && idx < ADDRESS_MAX {
                            F::from_u64(idx as u64)
                        } else {
                            // padding with 1
                            F::one()
                        };
                        region.assign_fixed(
                            || "address table",
                            self.address_table,
                            idx,
                            || Ok(to),
                        )?;
                    }
                    Ok(())
                },
            )
            .ok();

        layouter.assign_region(
            || "address table with zero",
            |mut region| {
                for idx in 0..ADDRESS_MAX.next_power_of_two() {
                    let to = if idx < ADDRESS_MAX {
                        F::from_u64(idx as u64)
                    } else {
                        // padding with 1
                        F::one()
                    };
                    region.assign_fixed(
                        || "address table with zero",
                        self.address_table_zero,
                        idx,
                        || Ok(to),
                    )?;
                }
                Ok(())
            },
        )
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

                for (index, op) in ops.iter().enumerate() {
                    let address = op.address;

                    self.init(&mut region, offset, address)?;

                    let mut selector_value = F::one();
                    if index > 0 {
                        selector_value = F::one() + F::one();
                    }
                    region.assign_fixed(
                        || "Memory selector",
                        self.q_memory,
                        offset,
                        || Ok(selector_value),
                    )?;

                    // Increase offset by 1 after initialising.
                    offset += 1;

                    for global_counter in op.global_counters.iter() {
                        let bus_mapping =
                            self.assign_per_counter(&mut region, offset, address, global_counter)?;

                        region.assign_fixed(
                            || "Memory selector",
                            self.q_memory,
                            offset,
                            || Ok(F::one() + F::one() + F::one()),
                        )?;
                        offset += 1;

                        // TODO: order by global_counter
                        bus_mappings.push(bus_mapping);
                    }
                }

                Ok(())
            },
        )?;

        Ok(bus_mappings)
    }

    /// Initialise first row for a new operation.
    fn init(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: MemoryAddress<F>,
    ) -> Result<(), Error> {
        // Assign `address`
        region.assign_advice(|| "init address", self.address, offset, || Ok(address.0))?;

        // Assign `global_counter`
        region.assign_advice(
            || "init global counter",
            self.global_counter,
            offset,
            || Ok(F::zero()),
        )?;

        // Assign `value`
        region.assign_advice(|| "init value", self.value, offset, || Ok(F::zero()))?;

        // Assign memory_flag
        region.assign_advice(|| "init memory", self.flag, offset, || Ok(F::one()))?;

        Ok(())
    }

    /// Assign cells for each global counter in an operation.
    fn assign_per_counter(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: MemoryAddress<F>,
        read_write: &Option<ReadWrite<F>>,
    ) -> Result<BusMapping<F>, Error> {
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

        // Assign `global_counter`
        let global_counter = {
            let value = read_write
                .as_ref()
                .map(|read_write| read_write.global_counter().0);
            let field_elem = value.map(|value| F::from_u64(value as u64));

            let cell = region.assign_advice(
                || "global counter",
                self.global_counter,
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

        Ok(BusMapping {
            global_counter,
            memory_flag,
            memory_address,
            memory_value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Config, GlobalCounter, MemoryAddress, MemoryOp, ReadWrite, Value};
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure::ConstraintNotSatisfied, VerifyFailure::Lookup},
        plonk::{Circuit, ConstraintSystem, Error},
    };

    use pasta_curves::{arithmetic::FieldExt, pallas};
    use std::marker::PhantomData;

    #[test]
    fn memory_circuit() {
        #[derive(Default)]
        struct MemoryCircuit<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> Circuit<F>
            for MemoryCircuit<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;
                config.assign(layouter, self.ops.clone())?;

                Ok(())
            }
        }

        let op_0 = MemoryOp {
            address: MemoryAddress(pallas::Base::zero()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(24),
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let op_1 = MemoryOp {
            address: MemoryAddress(pallas::Base::one()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(17),
                    Value(pallas::Base::from_u64(32)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(87),
                    Value(pallas::Base::from_u64(32)),
                )),
            ],
        };

        let circuit = MemoryCircuit::<pallas::Base, 100, 100> {
            ops: vec![op_0, op_1],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(14, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn same_address_read() {
        #[derive(Default)]
        struct MemoryCircuit<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> Circuit<F>
            for MemoryCircuit<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;
                config.assign(layouter, self.ops.clone())?;

                Ok(())
            }
        }

        let op_0 = MemoryOp {
            address: MemoryAddress(pallas::Base::zero()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(24),
                    Value(pallas::Base::from_u64(13)), // This should fail as it not the same value as in previous write op
                )),
            ],
        };

        let circuit = MemoryCircuit::<pallas::Base, 100, 100> {
            ops: vec![op_0],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(14, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![ConstraintNotSatisfied {
                constraint: ((1, "Memory operation").into(), 4, "").into(),
                row: 2
            },])
        );
    }

    #[test]
    fn max_values() {
        #[derive(Default)]
        struct MemoryCircuit<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> Circuit<F>
            for MemoryCircuit<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;
                config.assign(layouter, self.ops.clone())?;

                Ok(())
            }
        }

        const ADDRESS_MAX: usize = 100;

        let op_0 = MemoryOp {
            address: MemoryAddress(pallas::Base::from_u64((ADDRESS_MAX - 1) as u64)),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(24),
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let op_1 = MemoryOp {
            address: MemoryAddress(pallas::Base::from_u64(ADDRESS_MAX as u64)),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(24),
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let circuit = MemoryCircuit::<pallas::Base, 100, ADDRESS_MAX> {
            ops: vec![op_0, op_1],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(14, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![
                Lookup {
                    lookup_index: 2,
                    row: 3,
                },
                Lookup {
                    lookup_index: 3,
                    row: 4,
                },
                Lookup {
                    lookup_index: 3,
                    row: 5,
                }
            ])
        );
    }

    #[test]
    fn non_monotone_global_counter() {
        #[derive(Default)]
        struct MemoryCircuit<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADRESS_MAX: usize> {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt, const GLOBAL_COUNTER_MAX: usize, const ADDRESS_MAX: usize> Circuit<F>
            for MemoryCircuit<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;
                config.assign(layouter, self.ops.clone())?;

                Ok(())
            }
        }

        let op_0 = MemoryOp {
            address: MemoryAddress(pallas::Base::zero()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(1352),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(1255),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(1155),
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let op_1 = MemoryOp {
            address: MemoryAddress(pallas::Base::one()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(1788),
                    Value(pallas::Base::from_u64(32)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(8712),
                    Value(pallas::Base::from_u64(32)),
                )),
            ],
        };

        let circuit = MemoryCircuit::<pallas::Base, 10000, 10000> {
            ops: vec![op_0, op_1],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(15, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![
                Lookup {
                    lookup_index: 0,
                    row: 2,
                },
                Lookup {
                    lookup_index: 0,
                    row: 3,
                }
            ])
        );
    }
}

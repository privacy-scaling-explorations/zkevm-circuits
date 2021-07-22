use crate::gadget::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    monotone::{MonotoneChip, MonotoneConfig},
    Variable,
};
use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
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
pub(crate) struct Config<
    F: FieldExt,
    const MAX_MEMORY_ROWS: usize,
    const GLOBAL_COUNTER_MAX: usize,
    const ADDRESS_MAX: usize,
> {
    q_first: Selector,
    q_not_first: Selector,
    address: Column<Advice>,
    global_counter: Column<Advice>,
    value: Column<Advice>,
    flag: Column<Advice>,
    global_counter_table: Column<Fixed>,
    address_table_zero: Column<Fixed>,
    is_zero: IsZeroConfig<F>,
    mono_incr: MonotoneConfig,
    _marker: PhantomData<F>,
}

impl<
        F: FieldExt,
        const MAX_MEMORY_ROWS: usize,
        const GLOBAL_COUNTER_MAX: usize,
        const ADDRESS_MAX: usize,
    > Config<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
{
    /// Set up custom gates and lookup arguments for this configuration.
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_first = meta.selector();
        let q_not_first = meta.selector();
        let address = meta.advice_column();
        let global_counter = meta.advice_column();
        let value = meta.advice_column();
        let flag = meta.advice_column();
        let global_counter_table = meta.fixed_column();
        let address_table_zero = meta.fixed_column();

        let is_zero = IsZeroChip::configure(meta, q_not_first, |meta| {
            let value_a = meta.query_advice(address, Rotation::cur());
            let value_b = meta.query_advice(address, Rotation::prev());
            value_a - value_b
        });

        let mono_incr = MonotoneChip::<F, ADDRESS_MAX, true, false>::configure(
            meta,
            |meta| meta.query_selector(q_not_first),
            address,
        );

        // A gate for the first operation (does not need Rotation::prev).
        meta.create_gate("Memory first row operation", |meta| {
            let q_first = meta.query_selector(q_first);

            let value = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0

            vec![
                q_first.clone() * value,
                q_first.clone() * (Expression::Constant(F::one()) - flag),
                q_first * global_counter,
            ]
        });

        meta.create_gate("Memory operation", |meta| {
            let q_not_first = meta.query_selector(q_not_first);
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
            let check_flag_init = one.clone() - flag.clone();

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = flag.clone() * (one.clone() - flag.clone());

            // If flag == 0 (read), and global_counter != 0, value_prev == value_cur
            let value_prev = meta.query_advice(value, Rotation::prev());
            let q_read = one - flag;

            vec![
                q_not_first.clone() * address_diff.clone() * value_cur.clone(),
                q_not_first.clone() * address_diff.clone() * check_flag_init,
                q_not_first.clone() * address_diff * global_counter,
                q_not_first.clone() * bool_check_flag,
                q_not_first * q_read * (value_cur - value_prev),
            ]
        });

        // global_counter monotonicity:
        meta.lookup(|meta| {
            let q_not_first = meta.query_selector(q_not_first);
            let global_counter_table = meta.query_fixed(global_counter_table, Rotation::cur());
            let global_counter_prev = meta.query_advice(global_counter, Rotation::prev());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            vec![(
                q_not_first
                    * is_zero.clone().is_zero_expression
                    * (global_counter - global_counter_prev)
                    + (Expression::Constant(F::one()) - is_zero.clone().is_zero_expression), // default to 1 when is_zero_expression is 0
                global_counter_table,
            )]
        });

        // TODO: figure out why checks fail when put in the vec of the same meta.lookup call
        // (for some cases having a vector with more than one tuple works though)

        // address is in the allowed range
        meta.lookup(|meta| {
            let q_first = meta.query_selector(q_first);
            let q_not_first = meta.query_selector(q_not_first);
            let address_cur = meta.query_advice(address, Rotation::cur());
            let address_table_zero = meta.query_fixed(address_table_zero, Rotation::cur());

            vec![((q_first + q_not_first) * address_cur, address_table_zero)]
        });

        // global_counter is in the allowed range:
        meta.lookup(|meta| {
            let q_first = meta.query_selector(q_first);
            let q_not_first = meta.query_selector(q_not_first);
            let global_counter = meta.query_advice(global_counter, Rotation::cur());
            let global_counter_table = meta.query_fixed(global_counter_table, Rotation::cur());

            vec![(
                (q_first.clone() + q_not_first.clone()) * global_counter
                    + (Expression::Constant(F::one()) - (q_first + q_not_first)), // default to 1 when (q_first + q_not_first) is 0
                global_counter_table,
            )]
        });

        Config {
            q_first,
            q_not_first,
            address,
            global_counter,
            value,
            flag,
            global_counter_table,
            address_table_zero,
            is_zero,
            mono_incr,
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
                    for idx in 1..GLOBAL_COUNTER_MAX {
                        region.assign_fixed(
                            || "global counter table",
                            self.global_counter_table,
                            idx,
                            || Ok(F::from_u64(idx as u64)),
                        )?;
                    }
                    Ok(())
                },
            )
            .ok();

        layouter.assign_region(
            || "address table with zero",
            |mut region| {
                for idx in 0..ADDRESS_MAX {
                    region.assign_fixed(
                        || "address table with zero",
                        self.address_table_zero,
                        idx,
                        || Ok(F::from_u64(idx as u64)),
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

        let chip = IsZeroChip::construct(self.is_zero.clone());
        let monotone_chip =
            MonotoneChip::<F, ADDRESS_MAX, true, false>::construct(self.mono_incr.clone());
        monotone_chip.load(&mut layouter)?;

        layouter.assign_region(
            || "Memory operations",
            |mut region| {
                let mut offset = 0;

                for (index, op) in ops.iter().enumerate() {
                    let address = op.address;
                    let mut address_prev = ops.first().unwrap().address;
                    if index > 0 {
                        address_prev = ops[index - 1].address;
                    }

                    if index == 0 {
                        self.q_first.enable(&mut region, offset)?;
                    } else {
                        self.q_not_first.enable(&mut region, offset)?;
                    }
                    self.init(&mut region, offset, address)?;
                    chip.assign(&mut region, offset, Some(address.0 - address_prev.0))?;

                    // Increase offset by 1 after initialising.
                    offset += 1;

                    for global_counter in op.global_counters.iter() {
                        self.q_not_first.enable(&mut region, offset)?;
                        let bus_mapping =
                            self.assign_per_counter(&mut region, offset, address, global_counter)?;
                        chip.assign(&mut region, offset, Some(F::zero()))?;

                        offset += 1;

                        // TODO: order by global_counter
                        bus_mappings.push(bus_mapping);
                    }
                }

                let last_address = ops.last().unwrap().address;
                let last_gc = ops.last().unwrap().global_counters.last().unwrap();
                let mut last_counter = last_gc.as_ref().unwrap().global_counter().0;

                // We pad all remaining memory rows to avoid the check at the first unused row.
                // Without padding, (address_cur - address_prev) would not be zero at the first unused row
                // and some checks would be triggered.
                for i in offset..MAX_MEMORY_ROWS {
                    self.q_not_first.enable(&mut region, i)?;

                    // Assign `address`
                    region.assign_advice(
                        || "init address",
                        self.address,
                        i,
                        || Ok(last_address.0),
                    )?;

                    chip.assign(&mut region, i, Some(F::zero()))?;

                    // Assign `global_counter`
                    region.assign_advice(
                        || "init global counter",
                        self.global_counter,
                        i,
                        || Ok(F::from_u64(last_counter as u64)),
                    )?;
                    // To not break the global counter monotonicity
                    last_counter += 1;

                    // Assign `value`
                    region.assign_advice(|| "init value", self.value, i, || Ok(F::zero()))?;

                    // Assign memory_flag
                    region.assign_advice(|| "init memory", self.flag, i, || Ok(F::one()))?;
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
        struct MemoryCircuit<
            F: FieldExt,
            const MAX_MEMORY_ROWS: usize,
            const GLOBAL_COUNTER_MAX: usize,
            const ADDRESS_MAX: usize,
        > {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<
                F: FieldExt,
                const MAX_MEMORY_ROWS: usize,
                const GLOBAL_COUNTER_MAX: usize,
                const ADDRESS_MAX: usize,
            > Circuit<F> for MemoryCircuit<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
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

        // Note: be careful when setting MAX_MEMORY_ROWS and GLOBAL_COUNTER_MAX -
        // GLOBAL_COUNTER_MAX needs to be big enough for padded rows (unused memory rows
        // that are filled with dummy values)
        let circuit = MemoryCircuit::<pallas::Base, 1000, 2000, 100> {
            ops: vec![op_0, op_1],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(14, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn same_address_read() {
        #[derive(Default)]
        struct MemoryCircuit<
            F: FieldExt,
            const MAX_MEMORY_ROWS: usize,
            const GLOBAL_COUNTER_MAX: usize,
            const ADDRESS_MAX: usize,
        > {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<
                F: FieldExt,
                const MAX_MEMORY_ROWS: usize,
                const GLOBAL_COUNTER_MAX: usize,
                const ADDRESS_MAX: usize,
            > Circuit<F> for MemoryCircuit<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
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

        let circuit = MemoryCircuit::<pallas::Base, 1000, 2000, 100> {
            ops: vec![op_0],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(14, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![ConstraintNotSatisfied {
                constraint: ((2, "Memory operation").into(), 4, "").into(),
                row: 2
            },])
        );
    }

    #[test]
    fn max_values() {
        #[derive(Default)]
        struct MemoryCircuit<
            F: FieldExt,
            const MAX_MEMORY_ROWS: usize,
            const GLOBAL_COUNTER_MAX: usize,
            const ADDRESS_MAX: usize,
        > {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<
                F: FieldExt,
                const MAX_MEMORY_ROWS: usize,
                const GLOBAL_COUNTER_MAX: usize,
                const ADDRESS_MAX: usize,
            > Circuit<F> for MemoryCircuit<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
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

        // Small MAX_MEMORY_ROWS is set to avoid having padded rows (all padded rows would
        // fail because of the address they would have - the address of the last unused row)
        const MAX_MEMORY_ROWS: usize = 7;
        const ADDRESS_MAX: usize = 100;
        const GLOBAL_COUNTER_MAX: usize = 60000;

        let op_0 = MemoryOp {
            address: MemoryAddress(pallas::Base::from_u64((ADDRESS_MAX - 1) as u64)),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(GLOBAL_COUNTER_MAX - 1),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Write(
                    GlobalCounter(GLOBAL_COUNTER_MAX), // this global counter value is not in the allowed range
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let op_1 = MemoryOp {
            address: MemoryAddress(pallas::Base::from_u64(ADDRESS_MAX as u64)), // this address is not in the allowed range
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

        let circuit =
            MemoryCircuit::<pallas::Base, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX> {
                ops: vec![op_0, op_1],
                _marker: PhantomData,
            };

        let prover = MockProver::<pallas::Base>::run(16, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![
                Lookup {
                    lookup_index: 2,
                    row: 4,
                },
                Lookup {
                    lookup_index: 2,
                    row: 5,
                },
                Lookup {
                    lookup_index: 2,
                    row: 6,
                },
                Lookup {
                    lookup_index: 3,
                    row: 3,
                }
            ])
        );
    }

    #[test]
    fn non_monotone_global_counter() {
        #[derive(Default)]
        struct MemoryCircuit<
            F: FieldExt,
            const MAX_MEMORY_ROWS: usize,
            const GLOBAL_COUNTER_MAX: usize,
            const ADDRESS_MAX: usize,
        > {
            ops: Vec<MemoryOp<F>>,
            _marker: PhantomData<F>,
        }

        impl<
                F: FieldExt,
                const MAX_MEMORY_ROWS: usize,
                const GLOBAL_COUNTER_MAX: usize,
                const ADDRESS_MAX: usize,
            > Circuit<F> for MemoryCircuit<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>
        {
            type Config = Config<F, MAX_MEMORY_ROWS, GLOBAL_COUNTER_MAX, ADDRESS_MAX>;
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

        let circuit = MemoryCircuit::<pallas::Base, 100, 10000, 10000> {
            ops: vec![op_0, op_1],
            _marker: PhantomData,
        };

        let prover = MockProver::<pallas::Base>::run(15, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![
                Lookup {
                    lookup_index: 1,
                    row: 2,
                },
                Lookup {
                    lookup_index: 1,
                    row: 3,
                }
            ])
        );
    }
}

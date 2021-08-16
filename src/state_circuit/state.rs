use crate::gadget::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    monotone::{MonotoneChip, MonotoneConfig},
    Variable,
};
use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;

/*
Example memory table:

| address | global_counter | value | flag |
-------------------------------------------
|    0    |        0       |   0   |   1  |
|    0    |       12       |  12   |   1  |
|    0    |       24       |  12   |   0  |
|    1    |        0       |   0   |   1  |
|    1    |       17       |  32   |   1  |
|    1    |       89       |  32   |   0  |
*/

/*
Example bus mapping:

| global_counter | memory_flag | memory_address | memory_value |
----------------------------------------------------------------
|       12       |      1      |        0       |      12      |
|       17       |      1      |        1       |      32      |
|       24       |      0      |        0       |      12      |
|       89       |      0      |        1       |      32      |
*/

// target:
// 1 - first row of either target (Note: only the first row, not all init rows)
// 2 - memory
// 3 - stack
// 4 - storage

/// In the state proof, memory operations are ordered first by address, and then by global_counter.
/// Memory is initialised at 0 for each new address.
/// Memory is a word-addressed byte array, i.e. a mapping from a 253-bit word -> u8.
/// TODO: Confirm if we are using 253- or 256-bit memory addresses.
#[derive(Copy, Clone, Debug)]
struct Address<F: FieldExt>(F);

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
pub(crate) struct Op<F: FieldExt> {
    address: Address<F>,
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
    const GLOBAL_COUNTER_MAX: usize,
    const MEMORY_ROWS_MAX: usize,
    const MEMORY_ADDRESS_MAX: usize,
    const STACK_ROWS_MAX: usize,
    const STACK_ADDRESS_MAX: usize,
> {
    q_target: Column<Fixed>,
    address: Column<Advice>,
    address_diff_inv: Column<Advice>,
    global_counter: Column<Advice>,
    value: Column<Advice>,
    flag: Column<Advice>,
    padding: Column<Advice>,
    global_counter_table: Column<Fixed>,
    memory_address_table_zero: Column<Fixed>,
    stack_address_table_zero: Column<Fixed>,
    memory_value_table: Column<Fixed>,
    address_diff_is_zero: IsZeroConfig<F>,
    memory_address_monotone: MonotoneConfig,
    stack_address_monotone: MonotoneConfig,
    address_padding_monotone: MonotoneConfig,
    stack_padding_monotone: MonotoneConfig,
}

impl<
        F: FieldExt,
        const GLOBAL_COUNTER_MAX: usize,
        const MEMORY_ROWS_MAX: usize,
        const MEMORY_ADDRESS_MAX: usize,
        const STACK_ROWS_MAX: usize,
        const STACK_ADDRESS_MAX: usize,
    >
    Config<
        F,
        GLOBAL_COUNTER_MAX,
        MEMORY_ROWS_MAX,
        MEMORY_ADDRESS_MAX,
        STACK_ROWS_MAX,
        STACK_ADDRESS_MAX,
    >
{
    /// Set up custom gates and lookup arguments for this configuration.
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_target = meta.fixed_column();
        let address = meta.advice_column();
        let address_diff_inv = meta.advice_column();
        let global_counter = meta.advice_column();
        let value = meta.advice_column();
        let flag = meta.advice_column();
        let padding = meta.advice_column();
        let global_counter_table = meta.fixed_column();
        let memory_address_table_zero = meta.fixed_column();
        let stack_address_table_zero = meta.fixed_column();
        let memory_value_table = meta.fixed_column();

        let address_diff_is_zero = IsZeroChip::configure(
            meta,
            |meta| {
                let padding = meta.query_advice(padding, Rotation::cur());
                let one = Expression::Constant(F::one());
                let is_not_padding = one - padding;

                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let one = Expression::Constant(F::one());
                let q_not_first = q_target.clone() * (q_target - one);

                q_not_first * is_not_padding
            },
            |meta| {
                let address_cur = meta.query_advice(address, Rotation::cur());
                let address_prev = meta.query_advice(address, Rotation::prev());
                address_cur - address_prev
            },
            address_diff_inv,
        );

        let memory_address_monotone = MonotoneChip::<F, MEMORY_ADDRESS_MAX, true, false>::configure(
            meta,
            |meta| {
                let padding = meta.query_advice(padding, Rotation::cur());
                let one = Expression::Constant(F::one());
                let is_not_padding = one - padding;

                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let one = Expression::Constant(F::one());
                let three = Expression::Constant(F::from_u64(3));
                let four = Expression::Constant(F::from_u64(4));
                let q_memory = q_target.clone()
                    * (q_target.clone() - one.clone())
                    * (three - q_target.clone())
                    * (four.clone() - q_target.clone());

                // q_memory is 4 when target is 2, we use 1/4 to normalize the value
                let inv = F::from_u64(4 as u64).invert().unwrap_or(F::zero());
                let i = Expression::Constant(inv);

                q_memory * i * is_not_padding
            },
            address,
        );

        // todo: only one Monotone gadget could be used (with MEMORY_ADDRESS_MAX as it is bigger)
        // if the normalization is somehow solved
        let stack_address_monotone = MonotoneChip::<F, STACK_ADDRESS_MAX, true, false>::configure(
            meta,
            |meta| {
                let padding = meta.query_advice(padding, Rotation::cur());
                let one = Expression::Constant(F::one());
                let is_not_padding = one - padding;

                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let one = Expression::Constant(F::one());
                let two = Expression::Constant(F::from_u64(2));
                let four = Expression::Constant(F::from_u64(4));
                let q_stack = q_target.clone()
                    * (q_target.clone() - one)
                    * (q_target.clone() - two)
                    * (four - q_target);

                // q_stack is 6 when target is 3, we use 1/6 to normalize the value
                let inv = F::from_u64(6 as u64).invert().unwrap_or(F::zero());
                let i = Expression::Constant(inv);

                q_stack * i * is_not_padding
            },
            address,
        );

        let address_padding_monotone = MonotoneChip::<F, 1, true, false>::configure(
            meta,
            |meta| {
                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let one = Expression::Constant(F::one());
                let three = Expression::Constant(F::from_u64(3));
                let four = Expression::Constant(F::from_u64(4));
                let q_memory = q_target.clone()
                    * (q_target.clone() - one.clone())
                    * (three - q_target.clone())
                    * (four.clone() - q_target.clone());

                // q_memory is 4 when target is 2, we use 1/4 to normalize the value
                let inv = F::from_u64(4 as u64).invert().unwrap_or(F::zero());
                let i = Expression::Constant(inv);

                q_memory * i
            },
            padding,
        );

        let stack_padding_monotone = MonotoneChip::<F, 1, true, false>::configure(
            meta,
            |meta| {
                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let one = Expression::Constant(F::one());
                let two = Expression::Constant(F::from_u64(2));
                let four = Expression::Constant(F::from_u64(4));
                let q_stack = q_target.clone()
                    * (q_target.clone() - one)
                    * (q_target.clone() - two)
                    * (four - q_target);

                // q_stack is 6 when target is 3, we use 1/6 to normalize the value
                let inv = F::from_u64(6 as u64).invert().unwrap_or(F::zero());
                let i = Expression::Constant(inv);

                // first stack row shouldn't be checked as the address would be compared with
                // the last memory address

                q_stack * i
            },
            padding,
        );

        // A gate for the first row (does not need Rotation::prev).
        meta.create_gate("First memory row operation", |meta| {
            // First row is memory row (fixed by q_target fixed column), so we check whether
            // q_target_next = 2
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::from_u64(2));
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));
            // q_target_cur must be 1
            // q_target_next must be 2
            let q_memory_first = q_target_cur.clone()
                * (two - q_target_cur.clone())
                * (three.clone() - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one)
                * (three - q_target_next.clone())
                * (four - q_target_next);

            let value = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0

            let one = Expression::Constant(F::one());

            vec![
                q_memory_first.clone() * value,
                q_memory_first.clone() * (one - flag),
                q_memory_first * global_counter,
            ]
        });

        meta.create_gate("Memory operation", |meta| {
            // If address_cur != address_prev, this is an `init`. We must constrain:
            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0

            let q_target = meta.query_fixed(q_target, Rotation::cur());
            let one = Expression::Constant(F::one());
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));
            let q_memory = q_target.clone()
                * (q_target.clone() - one)
                * (three - q_target.clone())
                * (four - q_target);

            let address_diff = {
                let address_prev = meta.query_advice(address, Rotation::prev());
                let address_cur = meta.query_advice(address, Rotation::cur());
                address_cur - address_prev
            };

            let value_cur = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());

            let one = Expression::Constant(F::one());

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = flag.clone() * (one.clone() - flag.clone());

            // If flag == 0 (read), and global_counter != 0, value_prev == value_cur
            let value_prev = meta.query_advice(value, Rotation::prev());
            let q_read = one - flag;

            vec![
                q_memory.clone() * address_diff.clone() * value_cur.clone(), // when address changes, the write value is 0
                q_memory.clone() * address_diff.clone() * q_read.clone(), // when address changes, the flag is 1 (write)
                q_memory.clone() * address_diff * global_counter, // when address changes, global_counter is 0
                q_memory.clone() * bool_check_flag,               // flag is either 0 or 1
                q_memory * q_read * (value_cur - value_prev), // when reading, the value is the same as at the previous op
            ]
        });

        meta.create_gate("First stack row operation", |meta| {
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::from_u64(2));
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));
            let q_stack_first = q_target_cur.clone()
                * (two.clone() - q_target_cur.clone())
                * (three - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one.clone())
                * (q_target_next.clone() - two)
                * (four - q_target_next);

            let flag = meta.query_advice(flag, Rotation::cur());
            let q_read = one - flag;

            vec![
                q_stack_first.clone() * q_read.clone(), // first stack op has to be write (flag = 1)
            ]
        });

        meta.create_gate("Stack operation", |meta| {
            let q_target = meta.query_fixed(q_target, Rotation::cur());
            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::from_u64(2));
            let four = Expression::Constant(F::from_u64(4));
            let q_stack = q_target.clone()
                * (q_target.clone() - one)
                * (q_target.clone() - two)
                * (four - q_target);

            let address_diff = {
                let address_prev = meta.query_advice(address, Rotation::prev());
                let address_cur = meta.query_advice(address, Rotation::cur());
                address_cur - address_prev
            };

            let value_cur = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());

            let one = Expression::Constant(F::one());

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = flag.clone() * (one.clone() - flag.clone());

            // If flag == 0 (read), and global_counter != 0, value_prev == value_cur
            let value_prev = meta.query_advice(value, Rotation::prev());
            let q_read = one - flag;

            vec![
                q_stack.clone() * address_diff.clone() * q_read.clone(), // when address changes, the flag is 1 (write)
                q_stack.clone() * bool_check_flag,                       // flag is either 0 or 1
                q_stack * q_read * (value_cur - value_prev), // when reading, the value is the same as at the previous op
            ]
        });

        // global_counter monotonicity is only checked when address_cur == address_prev.
        // (Recall that operations are ordered first by address, and then by global_counter.)
        meta.lookup(|meta| {
            let global_counter_table = meta.query_fixed(global_counter_table, Rotation::cur());
            let global_counter_prev = meta.query_advice(global_counter, Rotation::prev());
            let global_counter = meta.query_advice(global_counter, Rotation::cur());
            let one = Expression::Constant(F::one());

            let padding = meta.query_advice(padding, Rotation::cur());
            let is_not_padding = one.clone() - padding;

            let q_target = meta.query_fixed(q_target, Rotation::cur());
            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::from_u64(2));
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));

            // q_memory_not_first is 4 when target is 2, we use 1/4 to normalize the value
            let inv = F::from_u64(4 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);
            let q_memory_not_first = q_target.clone()
                * (q_target.clone() - one.clone())
                * (three - q_target.clone())
                * (four.clone() - q_target.clone())
                * i;

            // q_stack_not_first is 6 when target is 3, we use 1/6 to normalize the value
            let inv = F::from_u64(6 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);
            let q_stack_not_first = q_target.clone()
                * (q_target.clone() - one.clone())
                * (q_target.clone() - two)
                * (four - q_target)
                * i;

            let q_not_first = q_memory_not_first + q_stack_not_first;

            vec![(
                q_not_first
                    * is_not_padding
                    * address_diff_is_zero.clone().is_zero_expression
                    * (global_counter - global_counter_prev - one.clone()), // - 1 because it needs to be strictly monotone
                global_counter_table,
            )]
        });

        // Memory address is in the allowed range.
        meta.lookup(|meta| {
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::from_u64(2));
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));

            // q_memory is 4 when target is 2, we use 1/4 to normalize the value
            let inv = F::from_u64(4 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);

            let q_memory_not_first = q_target_cur.clone()
                * (q_target_cur.clone() - one.clone())
                * (three.clone() - q_target_cur.clone())
                * (four.clone() - q_target_cur.clone())
                * i;

            // q_memory_first is 12 when q_target_cur is 1 and q_target_next is 2,
            // we use 1/12 to normalize the value
            let inv = F::from_u64(12 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);

            // q_target_cur must be 1
            // q_target_next must be 2
            let q_memory_first = q_target_cur.clone()
                * (two - q_target_cur.clone())
                * (three.clone() - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one)
                * (three - q_target_next.clone())
                * (four - q_target_next)
                * i;

            let q_memory = q_memory_first + q_memory_not_first;

            let address_cur = meta.query_advice(address, Rotation::cur());
            let memory_address_table_zero =
                meta.query_fixed(memory_address_table_zero, Rotation::cur());

            vec![(q_memory * address_cur, memory_address_table_zero)]
        });

        // Stack address is in the allowed range.
        meta.lookup(|meta| {
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            let one = Expression::Constant(F::one());
            let two = Expression::Constant(F::from_u64(2));
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));

            // q_stack_not_first is 6 when target is 3, we use 1/6 to normalize the value
            let inv = F::from_u64(6 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);

            let q_stack_not_first = q_target_cur.clone()
                * (q_target_cur.clone() - one.clone())
                * (q_target_cur.clone() - two.clone())
                * (four.clone() - q_target_cur.clone())
                * i;

            // q_stack_first is 12, we use 1/12 to normalize the value
            let inv = F::from_u64(12 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);

            let q_stack_first = q_target_cur.clone()
                * (two.clone() - q_target_cur.clone())
                * (three - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one)
                * (q_target_next.clone() - two)
                * (four - q_target_next)
                * i;

            let address_cur = meta.query_advice(address, Rotation::cur());
            let stack_address_table_zero =
                meta.query_fixed(stack_address_table_zero, Rotation::cur());

            let q_stack = q_stack_first + q_stack_not_first;

            vec![(q_stack * address_cur, stack_address_table_zero)]
        });

        // global_counter is in the allowed range:
        meta.lookup(|meta| {
            let global_counter = meta.query_advice(global_counter, Rotation::cur());
            let global_counter_table = meta.query_fixed(global_counter_table, Rotation::cur());

            vec![(global_counter, global_counter_table)]
        });

        // Memory value (for non-first rows) is in the allowed range.
        // Memory first row value doesn't need to be checked - it is checked above
        // where memory init row value has to be 0.
        meta.lookup(|meta| {
            let q_target = meta.query_fixed(q_target, Rotation::cur());
            let one = Expression::Constant(F::one());
            let three = Expression::Constant(F::from_u64(3));
            let four = Expression::Constant(F::from_u64(4));
            let q_memory = q_target.clone()
                * (q_target.clone() - one)
                * (three - q_target.clone())
                * (four - q_target);

            let value = meta.query_advice(value, Rotation::cur());
            let memory_value_table = meta.query_fixed(memory_value_table, Rotation::cur());

            // q_memory is 4 when target is 2, we use 1/4 to normalize the value
            let inv = F::from_u64(4 as u64).invert().unwrap_or(F::zero());
            let i = Expression::Constant(inv);

            vec![(q_memory * i * value, memory_value_table)]
        });

        Config {
            q_target,
            address,
            address_diff_inv,
            global_counter,
            value,
            flag,
            padding,
            global_counter_table,
            memory_address_table_zero,
            stack_address_table_zero,
            memory_value_table,
            address_diff_is_zero,
            memory_address_monotone,
            stack_address_monotone,
            address_padding_monotone,
            stack_padding_monotone,
        }
    }

    /// Load lookup table / other fixed constants for this configuration.
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter
            .assign_region(
                || "global counter table",
                |mut region| {
                    for idx in 0..=GLOBAL_COUNTER_MAX {
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

        layouter
            .assign_region(
                || "memory value table",
                |mut region| {
                    for idx in 0..=255 {
                        region.assign_fixed(
                            || "memory value table",
                            self.memory_value_table,
                            idx,
                            || Ok(F::from_u64(idx as u64)),
                        )?;
                    }
                    Ok(())
                },
            )
            .ok();

        layouter
            .assign_region(
                || "address table with zero",
                |mut region| {
                    for idx in 0..=MEMORY_ADDRESS_MAX {
                        region.assign_fixed(
                            || "address table with zero",
                            self.memory_address_table_zero,
                            idx,
                            || Ok(F::from_u64(idx as u64)),
                        )?;
                    }
                    Ok(())
                },
            )
            .ok();

        layouter.assign_region(
            || "stack address table with zero",
            |mut region| {
                for idx in 0..=STACK_ADDRESS_MAX {
                    region.assign_fixed(
                        || "stack address table with zero",
                        self.stack_address_table_zero,
                        idx,
                        || Ok(F::from_u64(idx as u64)),
                    )?;
                }
                Ok(())
            },
        )
    }

    fn assign_operations(
        &self,
        ops: Vec<Op<F>>,
        max_rows: usize,
        target: F,
        address_diff_is_zero_chip: &IsZeroChip<F>,
        start_offset: usize,
        region: &mut Region<F>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        let mut ops_num = 0;
        if target == F::from_u64(2 as u64) {
            // init rows need to be counted
            ops_num = ops
                .clone()
                .into_iter()
                .fold(0, |acc, x| acc + x.global_counters.len() + 1);
        } else if target == F::from_u64(2 as u64) {
            ops_num = ops
                .clone()
                .into_iter()
                .fold(0, |acc, x| acc + x.global_counters.len())
        }

        if ops_num > max_rows {
            panic!("too many operations for the specified fixed value of operations");
        }

        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        let mut offset = start_offset;
        for (index, op) in ops.iter().enumerate() {
            let address = op.address;
            let mut address_prev = ops.first().unwrap().address;
            if index > 0 {
                address_prev = ops[index - 1].address;
            }

            if target == F::from_u64(2 as u64) {
                // println!("{} {}", index, offset);
                // memory ops have init row
                if index == 0 {
                    self.init(region, offset, address, F::one())?;
                } else {
                    self.init(region, offset, address, target)?;
                }
                address_diff_is_zero_chip.assign(
                    region,
                    offset,
                    Some(address.0 - address_prev.0),
                )?;
                offset += 1;
            }

            for (internal_ind, global_counter) in op.global_counters.iter().enumerate() {
                if target == F::from_u64(2 as u64) {
                    let bus_mapping =
                        self.assign_per_counter(region, offset, address, global_counter, target)?;
                    bus_mappings.push(bus_mapping);
                    address_diff_is_zero_chip.assign(region, offset, Some(F::zero()))?;
                } else if target == F::from_u64(3 as u64) {
                    if internal_ind == 0 {
                        if index == 0 {
                            let bus_mapping = self.assign_per_counter(
                                region,
                                offset,
                                address,
                                global_counter,
                                F::one(),
                            )?;
                            bus_mappings.push(bus_mapping);
                            // set some non-zero diff for the first stack op
                            address_diff_is_zero_chip.assign(region, offset, Some(F::one()))?;
                        } else {
                            let bus_mapping = self.assign_per_counter(
                                region,
                                offset,
                                address,
                                global_counter,
                                target,
                            )?;
                            bus_mappings.push(bus_mapping);
                            address_diff_is_zero_chip.assign(
                                region,
                                offset,
                                Some(address.0 - address_prev.0),
                            )?;
                        }
                    } else {
                        // println!("{}", "---------");
                        let bus_mapping = self.assign_per_counter(
                            region,
                            offset,
                            address,
                            global_counter,
                            target,
                        )?;
                        bus_mappings.push(bus_mapping);

                        address_diff_is_zero_chip.assign(region, offset, Some(F::zero()))?;
                    }
                }

                // println!("{} {} ++", index, offset);

                offset += 1;
            }
        }

        // We pad all remaining rows to avoid the check at the first unused row.
        // Without padding, (address_cur - address_prev) would not be zero at the first unused row
        // and some checks would be triggered.

        // todo: edge cases
        for i in offset..start_offset + max_rows {
            if i == start_offset {
                region.assign_fixed(|| "target", self.q_target, i, || Ok(F::one()))?;
            } else {
                region.assign_fixed(|| "target", self.q_target, i, || Ok(target))?;
            }

            // println!("{} ++ --", i);

            region.assign_advice(|| "padding", self.padding, i, || Ok(F::one()))?;

            address_diff_is_zero_chip.assign(region, i, Some(F::zero()))?;

            // Assign `address`
            region.assign_advice(|| "init address", self.address, i, || Ok(F::zero()))?;

            // Assign `value`
            region.assign_advice(|| "value", self.value, i, || Ok(F::zero()))?;

            // Assign `global_counter`
            region.assign_advice(
                || "init global counter",
                self.global_counter,
                i,
                || Ok(F::zero()),
            )?;

            // Assign memory_flag
            region.assign_advice(|| "memory", self.flag, i, || Ok(F::one()))?;
        }

        Ok(bus_mappings)
    }

    /// Assign cells.
    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        memory_ops: Vec<Op<F>>,
        stack_ops: Vec<Op<F>>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        let address_diff_is_zero_chip = IsZeroChip::construct(self.address_diff_is_zero.clone());

        let memory_address_monotone_chip =
            MonotoneChip::<F, MEMORY_ADDRESS_MAX, true, false>::construct(
                self.memory_address_monotone.clone(),
            );
        memory_address_monotone_chip.load(&mut layouter)?;

        let stack_address_monotone_chip =
            MonotoneChip::<F, STACK_ADDRESS_MAX, true, false>::construct(
                self.stack_address_monotone.clone(),
            );
        stack_address_monotone_chip.load(&mut layouter)?;

        let address_padding_monotone_chip =
            MonotoneChip::<F, 1, true, false>::construct(self.address_padding_monotone.clone());
        address_padding_monotone_chip.load(&mut layouter)?;

        let stack_padding_monotone_chip =
            MonotoneChip::<F, 1, true, false>::construct(self.stack_padding_monotone.clone());
        stack_padding_monotone_chip.load(&mut layouter)?;

        layouter.assign_region(
            || "State operations",
            |mut region| {
                let memory_mappings = self.assign_operations(
                    memory_ops.clone(),
                    MEMORY_ROWS_MAX,
                    F::from_u64(2 as u64),
                    &address_diff_is_zero_chip,
                    0,
                    &mut region,
                );
                bus_mappings.extend(memory_mappings.unwrap());

                // println!("{}", "===========================");

                let stack_mappings = self.assign_operations(
                    stack_ops.clone(),
                    STACK_ROWS_MAX,
                    F::from_u64(3 as u64),
                    &address_diff_is_zero_chip,
                    MEMORY_ROWS_MAX,
                    &mut region,
                );
                bus_mappings.extend(stack_mappings.unwrap());

                Ok(bus_mappings.clone())
            },
        )

        // Ok(bus_mappings)
    }

    /// Initialise first row for a new operation.
    fn init(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: Address<F>,
        target: F,
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

        // Assign padding
        region.assign_advice(|| "padding", self.padding, offset, || Ok(F::zero()))?;

        // Assign target
        region.assign_fixed(|| "target", self.q_target, offset, || Ok(target))?;

        Ok(())
    }

    /// Assign cells for each global counter in an operation.
    fn assign_per_counter(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: Address<F>,
        read_write: &Option<ReadWrite<F>>,
        target: F,
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

        // Assign padding
        region.assign_advice(|| "padding", self.padding, offset, || Ok(F::zero()))?;

        // Assign target
        region.assign_fixed(|| "target", self.q_target, offset, || Ok(target))?;

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
    use super::{Address, Config, GlobalCounter, Op, ReadWrite, Value};
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure::ConstraintNotSatisfied, VerifyFailure::Lookup},
        plonk::{Circuit, ConstraintSystem, Error},
    };

    extern crate test;
    use test::Bencher;

    use pasta_curves::{arithmetic::FieldExt, pallas};

    macro_rules! test_state_circuit {
        ($k:expr, $global_counter_max:expr, $memory_rows_max:expr, $memory_address_max:expr, $stack_rows_max:expr, $stack_address_max:expr, $memory_ops:expr, $stack_ops:expr, $result:expr) => {{
            #[derive(Default)]
            struct StateCircuit<
                F: FieldExt,
                const GLOBAL_COUNTER_MAX: usize,
                const MEMORY_ROWS_MAX: usize,
                const MEMORY_ADDRESS_MAX: usize,
                const STACK_ROWS_MAX: usize,
                const STACK_ADDRESS_MAX: usize,
            > {
                memory_ops: Vec<Op<F>>,
                stack_ops: Vec<Op<F>>,
            }

            impl<
                    F: FieldExt,
                    const GLOBAL_COUNTER_MAX: usize,
                    const MEMORY_ROWS_MAX: usize,
                    const MEMORY_ADDRESS_MAX: usize,
                    const STACK_ROWS_MAX: usize,
                    const STACK_ADDRESS_MAX: usize,
                > Circuit<F>
                for StateCircuit<
                    F,
                    GLOBAL_COUNTER_MAX,
                    MEMORY_ROWS_MAX,
                    MEMORY_ADDRESS_MAX,
                    STACK_ROWS_MAX,
                    STACK_ADDRESS_MAX,
                >
            {
                type Config = Config<
                    F,
                    GLOBAL_COUNTER_MAX,
                    MEMORY_ROWS_MAX,
                    MEMORY_ADDRESS_MAX,
                    STACK_ROWS_MAX,
                    STACK_ADDRESS_MAX,
                >;
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
                    config.assign(layouter, self.memory_ops.clone(), self.stack_ops.clone())?;

                    Ok(())
                }
            }

            let circuit = StateCircuit::<
                pallas::Base,
                $global_counter_max,
                $memory_rows_max,
                $memory_address_max,
                $stack_rows_max,
                $stack_address_max,
            > {
                memory_ops: $memory_ops,
                stack_ops: $stack_ops,
            };

            let prover = MockProver::<pallas::Base>::run($k, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    fn constraint_not_satisfied(
        row: usize,
        gate_index: usize,
        gate_name: &'static str,
        index: usize,
    ) -> halo2::dev::VerifyFailure {
        ConstraintNotSatisfied {
            constraint: ((gate_index, gate_name).into(), index, "").into(),
            row,
        }
    }

    fn lookup_fail(row: usize, lookup_index: usize) -> halo2::dev::VerifyFailure {
        Lookup { lookup_index, row }
    }

    #[test]
    fn state_circuit() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::zero()),
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

        let memory_op_1 = Op {
            address: Address(pallas::Base::one()),
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

        let stack_op_0 = Op {
            address: Address(pallas::Base::one()),
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

        test_state_circuit!(
            14,
            2000,
            100,
            2,
            100,
            1023,
            vec![memory_op_0, memory_op_1],
            vec![stack_op_0],
            Ok(())
        );
    }

    #[test]
    fn no_stack_padding() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::zero()),
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

        const STACK_ROWS_MAX: usize = 2;
        let memory_op_1 = Op {
            address: Address(pallas::Base::one()),
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

        let stack_op_0 = Op {
            address: Address(pallas::Base::one()),
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

        test_state_circuit!(
            14,
            2000,
            100,
            STACK_ROWS_MAX,
            100,
            1023,
            vec![memory_op_0, memory_op_1],
            vec![stack_op_0],
            Ok(())
        );
    }

    #[test]
    fn same_address_read() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::zero()),
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
        let stack_op_0 = Op {
            address: Address(pallas::Base::zero()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(19),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(28),
                    Value(pallas::Base::from_u64(13)), // This should fail as it not the same value as in previous write op
                )),
            ],
        };

        const MEMORY_ROWS_MAX: usize = 7;
        test_state_circuit!(
            14,
            2000,
            MEMORY_ROWS_MAX,
            1000,
            100,
            1023,
            vec![memory_op_0],
            vec![stack_op_0],
            Err(vec![
                constraint_not_satisfied(2, 2, "Memory operation", 4),
                constraint_not_satisfied(MEMORY_ROWS_MAX + 1, 4, "Stack operation", 2)
            ])
        );
    }

    #[test]
    fn stack_first_write() {
        // first stack op when address changes is write
        let stack_op_0 = Op {
            address: Address(pallas::Base::zero()),
            global_counters: vec![Some(ReadWrite::Read(
                GlobalCounter(28),
                Value(pallas::Base::from_u64(13)), // This should fail as it is read op
            ))],
        };

        const MEMORY_ROWS_MAX: usize = 2;
        test_state_circuit!(
            14,
            2000,
            MEMORY_ROWS_MAX,
            1000,
            3,
            1023,
            vec![],
            vec![stack_op_0],
            Err(vec![constraint_not_satisfied(
                MEMORY_ROWS_MAX,
                3,
                "First stack row operation",
                0
            )])
        );
    }

    #[test]
    fn max_values() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::from_u64(MEMORY_ADDRESS_MAX as u64)),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(12),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(GLOBAL_COUNTER_MAX),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Write(
                    GlobalCounter(GLOBAL_COUNTER_MAX + 1), // this global counter value is not in the allowed range
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let memory_op_1 = Op {
            address: Address(pallas::Base::from_u64((MEMORY_ADDRESS_MAX + 1) as u64)), // this address is not in the allowed range
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

        let stack_op_0 = Op {
            address: Address(pallas::Base::from_u64(STACK_ADDRESS_MAX as u64)),
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

        let stack_op_1 = Op {
            address: Address(pallas::Base::from_u64((STACK_ADDRESS_MAX + 1) as u64)),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(17),
                    Value(pallas::Base::from_u64(12)),
                )),
                Some(ReadWrite::Write(
                    GlobalCounter(GLOBAL_COUNTER_MAX + 1),
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        // Small MEMORY_MAX_ROWS is set to avoid having padded rows (all padded rows would
        // fail because of the address they would have - the address of the last unused row)
        const MEMORY_ROWS_MAX: usize = 7;
        const STACK_ROWS_MAX: usize = 7;
        const GLOBAL_COUNTER_MAX: usize = 60000;
        const MEMORY_ADDRESS_MAX: usize = 100;
        const STACK_ADDRESS_MAX: usize = 1023;

        test_state_circuit!(
            16,
            GLOBAL_COUNTER_MAX,
            MEMORY_ROWS_MAX,
            MEMORY_ADDRESS_MAX,
            STACK_ROWS_MAX,
            STACK_ADDRESS_MAX,
            vec![memory_op_0, memory_op_1],
            vec![stack_op_0, stack_op_1],
            Err(vec![
                lookup_fail(4, 5),
                lookup_fail(5, 5),
                lookup_fail(6, 5),
                lookup_fail(9, 6),
                lookup_fail(10, 6),
                lookup_fail(3, 7),
                lookup_fail(10, 7)
            ])
        );
    }

    #[test]
    fn max_values_first_row() {
        // first row of a target needs to be checked for address to be in range too
        let memory_op_0 = Op {
            address: Address(pallas::Base::from_u64((MEMORY_ADDRESS_MAX + 1) as u64)), // this address is not in the allowed range
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(12),
                Value(pallas::Base::from_u64(12)),
            ))],
        };

        let stack_op_0 = Op {
            address: Address(pallas::Base::from_u64((STACK_ADDRESS_MAX + 1) as u64)),
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

        // Small MEMORY_MAX_ROWS is set to avoid having padded rows (all padded rows would
        // fail because of the address they would have - the address of the last unused row)
        const MEMORY_ROWS_MAX: usize = 2;
        const STACK_ROWS_MAX: usize = 2;
        const GLOBAL_COUNTER_MAX: usize = 60000;
        const MEMORY_ADDRESS_MAX: usize = 100;
        const STACK_ADDRESS_MAX: usize = 1023;

        test_state_circuit!(
            16,
            GLOBAL_COUNTER_MAX,
            MEMORY_ROWS_MAX,
            MEMORY_ADDRESS_MAX,
            STACK_ROWS_MAX,
            STACK_ADDRESS_MAX,
            vec![memory_op_0],
            vec![stack_op_0],
            Err(vec![
                lookup_fail(0, 5),
                lookup_fail(1, 5),
                lookup_fail(2, 6),
                lookup_fail(3, 6),
            ])
        );
    }

    #[test]
    fn non_monotone_global_counter() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::zero()),
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
                    GlobalCounter(1255), // fails because it needs to be strictly monotone
                    Value(pallas::Base::from_u64(12)),
                )),
            ],
        };

        let stack_op_0 = Op {
            address: Address(pallas::Base::one()),
            global_counters: vec![
                Some(ReadWrite::Write(
                    GlobalCounter(228),
                    Value(pallas::Base::from_u64(32)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(217),
                    Value(pallas::Base::from_u64(32)),
                )),
                Some(ReadWrite::Read(
                    GlobalCounter(217), // fails because it needs to be strictly monotone
                    Value(pallas::Base::from_u64(32)),
                )),
            ],
        };

        const MEMORY_ROWS_MAX: usize = 100;
        test_state_circuit!(
            15,
            10000,
            MEMORY_ROWS_MAX,
            10000,
            100,
            1023,
            vec![memory_op_0],
            vec![stack_op_0],
            Err(vec![
                lookup_fail(2, 4),
                lookup_fail(3, 4),
                lookup_fail(MEMORY_ROWS_MAX + 1, 4),
                lookup_fail(MEMORY_ROWS_MAX + 2, 4),
            ])
        );
    }

    #[test]
    fn non_monotone_address() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::zero()),
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(1352),
                Value(pallas::Base::from_u64(12)),
            ))],
        };

        let memory_op_1 = Op {
            address: Address(pallas::Base::one()),
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(42),
                Value(pallas::Base::from_u64(12)),
            ))],
        };

        let memory_op_2 = Op {
            address: Address(pallas::Base::zero()), // this fails because the address is not monotone
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(135),
                Value(pallas::Base::from_u64(12)),
            ))],
        };

        let stack_op_0 = Op {
            address: Address(pallas::Base::zero()),
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(228),
                Value(pallas::Base::from_u64(32)),
            ))],
        };
        let stack_op_1 = Op {
            address: Address(pallas::Base::one()),
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(229),
                Value(pallas::Base::from_u64(32)),
            ))],
        };
        let stack_op_2 = Op {
            address: Address(pallas::Base::zero()), // this fails because the address is not monotone
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(230),
                Value(pallas::Base::from_u64(32)),
            ))],
        };

        const MEMORY_ROWS_MAX: usize = 10;
        test_state_circuit!(
            14,
            10000,
            MEMORY_ROWS_MAX,
            10000,
            10,
            1023,
            vec![memory_op_0, memory_op_1, memory_op_2],
            vec![stack_op_0, stack_op_1, stack_op_2],
            Err(vec![lookup_fail(4, 0), lookup_fail(MEMORY_ROWS_MAX + 2, 1)])
        );
    }

    #[test]
    fn memory_values() {
        let memory_op_0 = Op {
            address: Address(pallas::Base::zero()),
            global_counters: vec![Some(ReadWrite::Write(
                GlobalCounter(1352),
                Value(pallas::Base::from_u64(256)),
            ))],
        };

        const MEMORY_ROWS_MAX: usize = 100;
        test_state_circuit!(
            15,
            10000,
            MEMORY_ROWS_MAX,
            10000,
            100,
            1023,
            vec![memory_op_0],
            vec![],
            Err(vec![lookup_fail(1, 8),])
        );
    }

    fn state() {
        const GLOBAL_COUNTER_MAX: usize = 60000;
        const MEMORY_ROWS_MAX: usize = 2000;
        const MEMORY_ADDRESS_MAX: usize = 100;
        const STACK_ROWS_MAX: usize = 2000;
        const STACK_ADDRESS_MAX: usize = 1023;

        let mut memory_operations = Vec::new();
        let gcs_per_address = 10;
        for id in 0..100 {
            let mut global_counters = Vec::new();
            for id_int in 0..gcs_per_address {
                let gc = Some(ReadWrite::Write(
                    GlobalCounter(id + id_int + 1), // + 1, otherwise the first gc will be the same as for init row
                    Value(pallas::Base::from_u64(0)),
                ));
                global_counters.push(gc);
            }

            let memory_op = Op {
                address: Address(pallas::Base::from_u64(id as u64)),
                global_counters: global_counters,
            };

            memory_operations.push(memory_op);
        }

        let mut stack_operations = Vec::new();
        let gcs_per_address = 10;
        for id in 0..100 {
            let mut global_counters = Vec::new();
            for id_int in 0..gcs_per_address {
                let gc = Some(ReadWrite::Write(
                    GlobalCounter(id + id_int), // no need for +1 as stack operations don't have init row
                    Value(pallas::Base::from_u64(0)),
                ));
                global_counters.push(gc);
            }

            let stack_op = Op {
                address: Address(pallas::Base::from_u64(id as u64)),
                global_counters: global_counters,
            };

            stack_operations.push(stack_op);
        }

        test_state_circuit!(
            16,
            GLOBAL_COUNTER_MAX,
            MEMORY_ROWS_MAX,
            MEMORY_ADDRESS_MAX,
            STACK_ROWS_MAX,
            STACK_ADDRESS_MAX,
            memory_operations,
            stack_operations,
            Ok(())
        );
    }

    #[bench]
    fn bench_state(b: &mut Bencher) {
        b.iter(|| state());
    }
}

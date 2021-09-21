use crate::gadget::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    monotone::{MonotoneChip, MonotoneConfig},
    Variable,
};
use bus_mapping::operation::{MemoryOp, StackOp, StorageOp};
use halo2::{
    circuit::{Layouter, Region},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Fixed,
        VirtualCells,
    },
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;

/*
Example state table:

| q_target | address | global_counter | value | flag | padding | storage_key | value_prev |
-------------------------------------------------------------------------------------------
|    1     |    0    |       0        |  0    |   1  |    0    |             |            |   // init row (write value 0)
|    2     |    0    |       12       |  12   |   1  |    0    |             |            |
|    2     |    0    |       24       |  12   |   0  |    0    |             |            |
|    2     |    1    |       0        |  0    |   1  |    0    |             |            |   // init row (write value 0)
|    2     |    1    |       2        |  12   |   0  |    0    |             |            |
|    2     |         |                |       |      |    1    |             |            |   // padding
|    2     |         |                |       |      |    1    |             |            |   // padding
|    1     |    0    |       3        |  4    |   1  |    0    |             |            |   // first stack op at the new address has to be write
|    3     |    0    |       17       |  32   |   1  |    0    |             |            |
|    3     |    0    |       89       |  32   |   0  |    0    |             |            |
|    3     |    1    |       48       |  32   |   1  |    0    |             |            |   // first stack op at the new address has to be write
|    3     |    1    |       49       |  32   |   0  |    0    |             |            |
|    3     |         |                |       |      |    1    |             |            |   // padding
|    1     |    1    |       55       |  32   |   1  |    0    |      5      |     0      |   // first storage op at the new address has to be write
|    4     |    1    |       56       |  33   |   1  |    0    |      8      |     32     |
|    4     |         |                |       |      |    1    |             |            |   // padding
*/

// q_target:
// 1 - first row of either target (Note: only the first row, not all init rows)
// 2 - memory
// 3 - stack
// 4 - storage

// address presents memory address, stack pointer, and account address for
// memory, stack, and storage ops respectively two columns are not displayed:
// address_diff and storage_key_diff (needed to check whether the address or
// storage_key changed) storage_key and value_prev are needed for storage ops
// only padding specifies whether the row is just a padding to fill all the rows
// that are intended for a particular target

/*
Example bus mapping:
// TODO: this is going to change

| target | address | global_counter | value | storage_key | value_prev | flag |
-------------------------------------------------------------------------------
|    2   |    0    |       12       |  12   |             |            |  1   |
|    2   |    0    |       24       |  12   |             |            |  0   |
|    2   |    1    |       2        |  12   |             |            |  0   |
|    1   |    0    |       3        |  4    |             |            |  1   |
|    3   |    0    |       17       |  32   |             |            |  1   |
|    3   |    0    |       89       |  32   |             |            |  0   |
|    3   |    1    |       48       |  32   |             |            |  1   |
|    3   |    1    |       49       |  32   |             |            |  0   |
*/

/// A mapping derived from witnessed memory operations.
/// TODO: The complete version of this mapping will involve storage, stack,
/// and opcode details as well.
#[derive(Clone, Debug)]
pub(crate) struct BusMapping<F: FieldExt> {
    global_counter: Variable<usize, F>,
    target: Variable<usize, F>,
    flag: Variable<bool, F>,
    address: Variable<F, F>,
    value: Variable<F, F>,
    storage_key: Variable<F, F>,
    value_prev: Variable<F, F>,
}

#[derive(Clone, Debug)]
pub(crate) struct Config<
    F: FieldExt,
    const GLOBAL_COUNTER_MAX: usize,
    const MEMORY_ROWS_MAX: usize,
    const MEMORY_ADDRESS_MAX: usize,
    const STACK_ROWS_MAX: usize,
    const STACK_ADDRESS_MAX: usize,
    const STORAGE_ROWS_MAX: usize,
> {
    q_target: Column<Fixed>,
    address: Column<Advice>, /* used for memory address, stack pointer, and
                              * account address (for storage) */
    address_diff_inv: Column<Advice>,
    global_counter: Column<Advice>,
    value: Column<Advice>,
    flag: Column<Advice>,
    padding: Column<Advice>,
    storage_key: Column<Advice>,
    storage_key_diff_inv: Column<Advice>,
    value_prev: Column<Advice>,
    global_counter_table: Column<Fixed>,
    memory_address_table_zero: Column<Fixed>,
    stack_address_table_zero: Column<Fixed>,
    memory_value_table: Column<Fixed>,
    address_diff_is_zero: IsZeroConfig<F>,
    address_monotone: MonotoneConfig,
    padding_monotone: MonotoneConfig,
    storage_key_diff_is_zero: IsZeroConfig<F>,
}

impl<
        F: FieldExt,
        const GLOBAL_COUNTER_MAX: usize,
        const MEMORY_ROWS_MAX: usize,
        const MEMORY_ADDRESS_MAX: usize,
        const STACK_ROWS_MAX: usize,
        const STACK_ADDRESS_MAX: usize,
        const STORAGE_ROWS_MAX: usize,
    >
    Config<
        F,
        GLOBAL_COUNTER_MAX,
        MEMORY_ROWS_MAX,
        MEMORY_ADDRESS_MAX,
        STACK_ROWS_MAX,
        STACK_ADDRESS_MAX,
        STORAGE_ROWS_MAX,
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
        let storage_key = meta.advice_column();
        let storage_key_diff_inv = meta.advice_column();
        let value_prev = meta.advice_column();
        let global_counter_table = meta.fixed_column();
        let memory_address_table_zero = meta.fixed_column();
        let stack_address_table_zero = meta.fixed_column();
        let memory_value_table = meta.fixed_column();

        let one = Expression::Constant(F::one());
        let two = Expression::Constant(F::from_u64(2));
        let three = Expression::Constant(F::from_u64(3));
        let four = Expression::Constant(F::from_u64(4));

        let q_memory_first = |meta: &mut VirtualCells<F>| {
            // For first memory row it holds q_target_cur = 1 and q_target_next
            // = 2.
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            // q_target_cur must be 1
            // q_target_next must be 2

            q_target_cur.clone()
                * (two.clone() - q_target_cur.clone())
                * (three.clone() - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one.clone())
                * (three.clone() - q_target_next.clone())
                * (four.clone() - q_target_next)
        };

        let q_memory_first_norm = |meta: &mut VirtualCells<F>| {
            let e = q_memory_first(meta);
            // q_memory_first is 12 when q_target_cur is 1 and q_target_next is
            // 2, we use 1/12 to normalize the value
            let inv = F::from_u64(12_u64).invert().unwrap();
            let i = Expression::Constant(inv);

            e * i
        };

        let q_memory_not_first = |meta: &mut VirtualCells<F>| {
            let q_target = meta.query_fixed(q_target, Rotation::cur());

            q_target.clone()
                * (q_target.clone() - one.clone())
                * (three.clone() - q_target.clone())
                * (four.clone() - q_target)
        };

        let q_memory_not_first_norm = |meta: &mut VirtualCells<F>| {
            let e = q_memory_not_first(meta);
            // q_memory_not_first is 4 when target is 2, we use 1/4 to normalize
            // the value
            let inv = F::from_u64(4_u64).invert().unwrap();
            let i = Expression::Constant(inv);

            e * i
        };

        let q_stack_first = |meta: &mut VirtualCells<F>| {
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            q_target_cur.clone()
                * (two.clone() - q_target_cur.clone())
                * (three.clone() - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one.clone())
                * (q_target_next.clone() - two.clone())
                * (four.clone() - q_target_next)
        };

        let q_stack_first_norm = |meta: &mut VirtualCells<F>| {
            let e = q_stack_first(meta);
            // q_stack_first is 12, we use 1/12 to normalize the value
            let inv = F::from_u64(12_u64).invert().unwrap();
            let i = Expression::Constant(inv);

            e * i
        };

        let q_stack_not_first = |meta: &mut VirtualCells<F>| {
            let q_target = meta.query_fixed(q_target, Rotation::cur());

            q_target.clone()
                * (q_target.clone() - one.clone())
                * (q_target.clone() - two.clone())
                * (four.clone() - q_target)
        };

        let q_stack_not_first_norm = |meta: &mut VirtualCells<F>| {
            let e = q_stack_not_first(meta);
            // q_stack_not_first is 6 when target is 3, we use 1/6 to normalize
            // the value
            let inv = F::from_u64(6_u64).invert().unwrap();
            let i = Expression::Constant(inv);

            e * i
        };

        let q_storage_not_first = |meta: &mut VirtualCells<F>| {
            let q_target = meta.query_fixed(q_target, Rotation::cur());
            q_target.clone()
                * (q_target.clone() - one.clone())
                * (q_target.clone() - two.clone())
                * (q_target - three.clone())
        };

        let q_storage_not_first_norm = |meta: &mut VirtualCells<F>| {
            let e = q_storage_not_first(meta);
            // q_storage_not_first is 24 when target is 4, we use 1/24 to
            // normalize the value
            let inv = F::from_u64(24_u64).invert().unwrap();
            let i = Expression::Constant(inv);

            e * i
        };

        let address_diff_is_zero = IsZeroChip::configure(
            meta,
            |meta| {
                let padding = meta.query_advice(padding, Rotation::cur());
                let is_not_padding = one.clone() - padding;
                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let q_not_first = q_target.clone() * (q_target - one.clone());

                q_not_first * is_not_padding
            },
            |meta| {
                let address_cur = meta.query_advice(address, Rotation::cur());
                let address_prev = meta.query_advice(address, Rotation::prev());
                address_cur - address_prev
            },
            address_diff_inv,
        );

        // Only one monotone gadget is used for memory and stack (with
        // MEMORY_ADDRESS_MAX as it is bigger)
        let address_monotone =
            MonotoneChip::<F, MEMORY_ADDRESS_MAX, true, false>::configure(
                meta,
                |meta| {
                    let padding = meta.query_advice(padding, Rotation::cur());
                    let is_not_padding = one.clone() - padding;
                    // Since q_memory_not_first and q_stack_non_first are
                    // mutually exclusive, q_not_first is binary.
                    let q_not_first = q_memory_not_first_norm(meta)
                        + q_stack_not_first_norm(meta);

                    q_not_first * is_not_padding
                },
                address,
            );

        // Padding monotonicity could be checked using gates (as padding only
        // takes values 0 and 1), but it's much slower than using a
        // lookup.
        let padding_monotone = MonotoneChip::<F, 1, true, false>::configure(
            meta,
            |meta| q_memory_not_first_norm(meta) + q_stack_not_first_norm(meta),
            padding,
        );

        // A gate for the first row (does not need Rotation::prev).
        meta.create_gate("First memory row operation", |meta| {
            let value = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter =
                meta.query_advice(global_counter, Rotation::cur());
            let q_memory_first = q_memory_first(meta);

            //
            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0

            vec![
                q_memory_first.clone() * value,
                q_memory_first.clone() * (one.clone() - flag),
                q_memory_first * global_counter,
            ]
        });

        meta.create_gate("Memory operation + padding", |meta| {
            // If address_cur != address_prev, this is an `init`. We must
            // constrain:
            //      - values[0] == [0]
            //      - flags[0] == 1
            //      - global_counters[0] == 0
            let q_memory_not_first = q_memory_not_first(meta);
            let address_diff = {
                let address_prev = meta.query_advice(address, Rotation::prev());
                let address_cur = meta.query_advice(address, Rotation::cur());
                address_cur - address_prev
            };

            let value_cur = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());
            let global_counter =
                meta.query_advice(global_counter, Rotation::cur());

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = flag.clone() * (one.clone() - flag.clone());

            // If flag == 0 (read), and global_counter != 0, value_prev ==
            // value_cur
            let value_prev = meta.query_advice(value, Rotation::prev());
            let q_read = one.clone() - flag;

            let q_target = meta.query_fixed(q_target, Rotation::cur());
            let padding = meta.query_advice(padding, Rotation::cur());
            let bool_check_padding = padding.clone() * (one.clone() - padding);

            vec![
                q_memory_not_first.clone()
                    * address_diff.clone()
                    * value_cur.clone(), // when address changes, the write value is 0
                q_memory_not_first.clone()
                    * address_diff.clone()
                    * q_read.clone(), // when address changes, the flag is 1 (write)
                q_memory_not_first.clone() * address_diff * global_counter, // when address changes, global_counter is 0
                q_memory_not_first.clone() * bool_check_flag, // flag is either 0 or 1
                q_memory_not_first * q_read * (value_cur - value_prev), // when reading, the value is the same as at the previous op
                // Note that this last constraint needs to hold only when address doesn't change,
                // but we don't need to check this as the first operation at the address always
                // has to be write - that means q_read is 1 only when
                // the address and storage key don't change.
                q_target * bool_check_padding, // padding is 0 or 1
            ]
        });

        meta.create_gate("First stack row operation", |meta| {
            let q_stack_first = q_stack_first(meta);
            let flag = meta.query_advice(flag, Rotation::cur());

            vec![
                q_stack_first * (one.clone() - flag), /* first stack op has to be
                                                       * write (flag = 1) */
            ]
        });

        meta.create_gate("Stack operation", |meta| {
            let q_stack_not_first = q_stack_not_first(meta);
            let address_diff = {
                let address_prev = meta.query_advice(address, Rotation::prev());
                let address_cur = meta.query_advice(address, Rotation::cur());
                address_cur - address_prev
            };

            let value_cur = meta.query_advice(value, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = flag.clone() * (one.clone() - flag.clone());

            // If flag == 0 (read), and global_counter != 0, value_prev == value_cur
            let value_prev = meta.query_advice(value, Rotation::prev());
            let q_read = one.clone() - flag;

            vec![
                q_stack_not_first.clone() * address_diff * q_read.clone(), // when address changes, the flag is 1 (write)
                q_stack_not_first.clone() * bool_check_flag, // flag is either 0 or 1
                q_stack_not_first * q_read * (value_cur - value_prev), // when reading, the value is the same as at the previous op
            ]
        });

        // global_counter monotonicity is checked for memory and stack when
        // address_cur == address_prev. (Recall that operations are
        // ordered first by address, and then by global_counter.)
        meta.lookup(|meta| {
            let global_counter_table =
                meta.query_fixed(global_counter_table, Rotation::cur());
            let global_counter_prev =
                meta.query_advice(global_counter, Rotation::prev());
            let global_counter =
                meta.query_advice(global_counter, Rotation::cur());
            let padding = meta.query_advice(padding, Rotation::cur());
            let is_not_padding = one.clone() - padding;
            let q_not_first =
                q_memory_not_first_norm(meta) + q_stack_not_first_norm(meta);

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
            let q_memory =
                q_memory_first_norm(meta) + q_memory_not_first_norm(meta);
            let address_cur = meta.query_advice(address, Rotation::cur());
            let memory_address_table_zero =
                meta.query_fixed(memory_address_table_zero, Rotation::cur());

            vec![(q_memory * address_cur, memory_address_table_zero)]
        });

        // Stack address is in the allowed range.
        meta.lookup(|meta| {
            let q_stack =
                q_stack_first_norm(meta) + q_stack_not_first_norm(meta);
            let address_cur = meta.query_advice(address, Rotation::cur());
            let stack_address_table_zero =
                meta.query_fixed(stack_address_table_zero, Rotation::cur());

            vec![(q_stack * address_cur, stack_address_table_zero)]
        });

        // global_counter is in the allowed range:
        meta.lookup(|meta| {
            let global_counter =
                meta.query_advice(global_counter, Rotation::cur());
            let global_counter_table =
                meta.query_fixed(global_counter_table, Rotation::cur());

            vec![(global_counter, global_counter_table)]
        });

        // Memory value (for non-first rows) is in the allowed range.
        // Memory first row value doesn't need to be checked - it is checked
        // above where memory init row value has to be 0.
        meta.lookup(|meta| {
            let q_memory_not_first = q_memory_not_first_norm(meta);
            let value = meta.query_advice(value, Rotation::cur());
            let memory_value_table =
                meta.query_fixed(memory_value_table, Rotation::cur());

            vec![(q_memory_not_first * value, memory_value_table)]
        });

        let storage_key_diff_is_zero = IsZeroChip::configure(
            meta,
            |meta| {
                let padding = meta.query_advice(padding, Rotation::cur());
                let is_not_padding = one.clone() - padding;

                let q_target = meta.query_fixed(q_target, Rotation::cur());
                let q_not_first = q_target.clone() * (q_target - one.clone());

                q_not_first * is_not_padding
            },
            |meta| {
                let storage_key_cur =
                    meta.query_advice(storage_key, Rotation::cur());
                let storage_key_prev =
                    meta.query_advice(storage_key, Rotation::prev());
                storage_key_cur - storage_key_prev
            },
            storage_key_diff_inv,
        );

        meta.create_gate("First storage row operation", |meta| {
            let q_target_cur = meta.query_fixed(q_target, Rotation::cur());
            let q_target_next = meta.query_fixed(q_target, Rotation::next());
            let q_storage_first = q_target_cur.clone()
                * (two.clone() - q_target_cur.clone())
                * (three.clone() - q_target_cur.clone())
                * (four.clone() - q_target_cur)
                * (q_target_next.clone() - one.clone())
                * (q_target_next.clone() - two.clone())
                * (q_target_next - three.clone());

            let flag = meta.query_advice(flag, Rotation::cur());
            let q_read = one.clone() - flag;

            vec![
                q_storage_first * q_read, /* first storage op has to be
                                           * write (flag = 1) */
            ]
        });

        meta.create_gate("Storage operation", |meta| {
            let q_storage_not_first = q_storage_not_first(meta);
            let address_diff = {
                let address_prev = meta.query_advice(address, Rotation::prev());
                let address_cur = meta.query_advice(address, Rotation::cur());
                address_cur - address_prev
            };

            let storage_key_diff = {
                let storage_key_prev =
                    meta.query_advice(storage_key, Rotation::prev());
                let storage_key_cur =
                    meta.query_advice(storage_key, Rotation::cur());
                storage_key_cur - storage_key_prev
            };

            let value_cur = meta.query_advice(value, Rotation::cur());
            let value_prev_cur = meta.query_advice(value_prev, Rotation::cur());
            let flag = meta.query_advice(flag, Rotation::cur());

            // flag == 0 or 1
            // (flag) * (1 - flag)
            let bool_check_flag = flag.clone() * (one.clone() - flag.clone());

            // If flag == 0 (read), and global_counter != 0, value_prev == value_cur
            let value_previous = meta.query_advice(value, Rotation::prev());
            let q_read = one.clone() - flag.clone();

            let padding = meta.query_advice(padding, Rotation::cur());
            let is_not_padding = one.clone() - padding;

            vec![
                q_storage_not_first.clone() * address_diff * q_read.clone(), // when address changes, the flag is 1 (write)
                q_storage_not_first.clone() * storage_key_diff * q_read.clone(), // when storage_key_diff changes, the flag is 1 (write)
                q_storage_not_first.clone() * bool_check_flag, // flag is either 0 or 1
                q_storage_not_first.clone()
                    * q_read
                    * (value_cur - value_previous.clone()), // when reading, the value is the same as at the previous op
                // Note that this last constraint needs to hold only when address and storage key don't change,
                // but we don't need to check this as the first operation at new address and
                // new storage key always has to be write - that means q_read is 1 only when
                // the address and storage key doesn't change.
                is_not_padding
                    * q_storage_not_first
                    * flag
                    * address_diff_is_zero.clone().is_zero_expression
                    * storage_key_diff_is_zero.clone().is_zero_expression
                    * (value_prev_cur - value_previous), // when writing, value_prev_cur = value_previous
            ]
        });

        // global_counter monotonicity is checked for storage when address_cur
        // == address_prev and storage_key_cur = storage_key_prev.
        // (Recall that storage operations are ordered first by account address,
        // then by storage_key, and finally by global_counter.)
        meta.lookup(|meta| {
            let global_counter_table =
                meta.query_fixed(global_counter_table, Rotation::cur());
            let global_counter_prev =
                meta.query_advice(global_counter, Rotation::prev());
            let global_counter =
                meta.query_advice(global_counter, Rotation::cur());
            let padding = meta.query_advice(padding, Rotation::cur());
            let is_not_padding = one.clone() - padding;
            let q_storage_not_first = q_storage_not_first_norm(meta);

            vec![(
                q_storage_not_first
                    * is_not_padding
                    * address_diff_is_zero.clone().is_zero_expression
                    * storage_key_diff_is_zero.clone().is_zero_expression
                    * (global_counter - global_counter_prev - one.clone()), // - 1 because it needs to be strictly monotone
                global_counter_table,
            )]
        });

        // TODO: monotone address for storage

        Config {
            q_target,
            address,
            address_diff_inv,
            global_counter,
            value,
            flag,
            padding,
            storage_key,
            storage_key_diff_inv,
            value_prev,
            global_counter_table,
            memory_address_table_zero,
            stack_address_table_zero,
            memory_value_table,
            address_diff_is_zero,
            address_monotone,
            padding_monotone,
            storage_key_diff_is_zero,
        }
    }

    /// Load lookup table / other fixed constants for this configuration.
    pub(crate) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
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
                || "memory address table with zero",
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

    fn assign_memory_ops(
        &self,
        region: &mut Region<F>,
        ops: Vec<MemoryOp>,
        address_diff_is_zero_chip: &IsZeroChip<F>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        let mut init_rows_num = 0;
        for (index, op) in ops.iter().enumerate() {
            if index > 0 {
                if op.address() != ops[index - 1].address() {
                    init_rows_num += 1;
                }
            } else {
                init_rows_num += 1;
            }
        }

        if ops.len() + init_rows_num > MEMORY_ROWS_MAX {
            panic!("too many memory operations");
        }

        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        let mut address_prev = F::zero();
        let mut offset = 0;
        for (index, op) in ops.iter().enumerate() {
            let address = F::from_bytes(&op.address().to_bytes()).unwrap();
            let gc = usize::from(op.gc());
            let v_bytes = op.value().to_bytes();
            let val = F::from_bytes(&v_bytes).unwrap();

            let mut target = 1;
            if index > 0 {
                target = 2;
            }

            // memory ops have init row
            if index == 0 || address != address_prev {
                self.init(region, offset, address, target)?;
                address_diff_is_zero_chip.assign(
                    region,
                    offset,
                    Some(address - address_prev),
                )?;
                target = 2;
                offset += 1;
            }

            let bus_mapping = self.assign_op(
                region,
                offset,
                address,
                gc,
                val,
                op.rw().is_write(),
                target,
                F::zero(),
                F::zero(),
            )?;
            bus_mappings.push(bus_mapping);

            address_prev = address;
            offset += 1;
        }

        self.pad_rows(region, offset, 0, MEMORY_ROWS_MAX, 2)?;

        Ok(bus_mappings)
    }

    fn assign_stack_ops(
        &self,
        region: &mut Region<F>,
        ops: Vec<StackOp>,
        address_diff_is_zero_chip: &IsZeroChip<F>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        if ops.len() > STACK_ROWS_MAX {
            panic!("too many stack operations");
        }
        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        let mut address_prev = F::zero();
        let mut offset = MEMORY_ROWS_MAX;
        for (index, op) in ops.iter().enumerate() {
            let address = F::from_u64(usize::from(*op.address()) as u64);
            let gc = usize::from(op.gc());
            let v_bytes = op.value().to_bytes();
            let val = F::from_bytes(&v_bytes).unwrap();

            let mut target = 1;
            if index > 0 {
                target = 3;
            }

            let bus_mapping = self.assign_op(
                region,
                offset,
                address,
                gc,
                val,
                op.rw().is_write(),
                target,
                F::zero(),
                F::zero(),
            )?;
            bus_mappings.push(bus_mapping);

            address_diff_is_zero_chip.assign(
                region,
                offset,
                Some(address - address_prev),
            )?;

            address_prev = address;
            offset += 1;
        }

        self.pad_rows(region, offset, MEMORY_ROWS_MAX, STACK_ROWS_MAX, 3)?;

        Ok(bus_mappings)
    }

    fn assign_storage_ops(
        &self,
        region: &mut Region<F>,
        ops: Vec<StorageOp>,
        address_diff_is_zero_chip: &IsZeroChip<F>,
        storage_key_diff_is_zero_chip: &IsZeroChip<F>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        if ops.len() > STORAGE_ROWS_MAX {
            panic!("too many storage operations");
        }
        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        let mut address_prev = F::zero();
        let mut storage_key_prev = F::zero();
        let mut offset = MEMORY_ROWS_MAX + STACK_ROWS_MAX;
        for (index, op) in ops.iter().enumerate() {
            let address = F::from_bytes(&op.address().to_bytes()).unwrap();
            let gc = usize::from(op.gc());
            let v_bytes = op.value().to_bytes();
            let val = F::from_bytes(&v_bytes).unwrap();
            let v_prev_bytes = op.value_prev().to_bytes();
            let val_prev = F::from_bytes(&v_prev_bytes).unwrap();

            let mut array = [0u8; 32];
            let bytes = op.storage_key().to_bytes_le();
            array[..bytes.len()].copy_from_slice(&bytes[0..bytes.len()]);
            let storage_key = F::from_bytes(&array).unwrap();

            let mut target = 1;
            if index > 0 {
                target = 4;
            }

            let bus_mapping = self.assign_op(
                region,
                offset,
                address,
                gc,
                val,
                op.rw().is_write(),
                target,
                storage_key,
                val_prev,
            )?;
            bus_mappings.push(bus_mapping);

            address_diff_is_zero_chip.assign(
                region,
                offset,
                Some(address - address_prev),
            )?;

            storage_key_diff_is_zero_chip.assign(
                region,
                offset,
                Some(storage_key - storage_key_prev),
            )?;

            address_prev = address;
            storage_key_prev = storage_key;
            offset += 1;
        }

        self.pad_rows(
            region,
            offset,
            MEMORY_ROWS_MAX + STACK_ROWS_MAX,
            STORAGE_ROWS_MAX,
            4,
        )?;

        Ok(bus_mappings)
    }

    fn pad_rows(
        &self,
        region: &mut Region<F>,
        offset: usize,
        start_offset: usize,
        max_rows: usize,
        target: usize,
    ) -> Result<(), Error> {
        // We pad all remaining rows to avoid the check at the first unused row.
        // Without padding, (address_cur - address_prev) would not be zero at
        // the first unused row and some checks would be triggered.

        for i in offset..start_offset + max_rows {
            if i == start_offset {
                region.assign_fixed(
                    || "target",
                    self.q_target,
                    i,
                    || Ok(F::one()),
                )?;
            } else {
                region.assign_fixed(
                    || "target",
                    self.q_target,
                    i,
                    || Ok(F::from_u64(target as u64)),
                )?;
            }
            region.assign_advice(
                || "padding",
                self.padding,
                i,
                || Ok(F::one()),
            )?;
            region.assign_advice(|| "memory", self.flag, i, || Ok(F::one()))?;
        }

        Ok(())
    }

    /// Assign cells.
    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        memory_ops: Vec<MemoryOp>,
        stack_ops: Vec<StackOp>,
        storage_ops: Vec<StorageOp>,
    ) -> Result<Vec<BusMapping<F>>, Error> {
        let mut bus_mappings: Vec<BusMapping<F>> = Vec::new();

        let address_diff_is_zero_chip =
            IsZeroChip::construct(self.address_diff_is_zero.clone());

        let memory_address_monotone_chip =
            MonotoneChip::<F, MEMORY_ADDRESS_MAX, true, false>::construct(
                self.address_monotone.clone(),
            );
        memory_address_monotone_chip.load(&mut layouter)?;

        let padding_monotone_chip =
            MonotoneChip::<F, 1, true, false>::construct(
                self.padding_monotone.clone(),
            );
        padding_monotone_chip.load(&mut layouter)?;

        let storage_key_diff_is_zero_chip =
            IsZeroChip::construct(self.storage_key_diff_is_zero.clone());

        layouter.assign_region(
            || "State operations",
            |mut region| {
                let memory_mappings = self.assign_memory_ops(
                    &mut region,
                    memory_ops.clone(),
                    &address_diff_is_zero_chip,
                );
                bus_mappings.extend(memory_mappings.unwrap());

                let stack_mappings = self.assign_stack_ops(
                    &mut region,
                    stack_ops.clone(),
                    &address_diff_is_zero_chip,
                );
                bus_mappings.extend(stack_mappings.unwrap());

                let storage_mappings = self.assign_storage_ops(
                    &mut region,
                    storage_ops.clone(),
                    &address_diff_is_zero_chip,
                    &storage_key_diff_is_zero_chip,
                );
                bus_mappings.extend(storage_mappings.unwrap());

                Ok(bus_mappings.clone())
            },
        )
    }

    /// Initialise first row for a new operation.
    fn init(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: F,
        target: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "init address",
            self.address,
            offset,
            || Ok(address),
        )?;

        region.assign_advice(
            || "init global counter",
            self.global_counter,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "init value",
            self.value,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "init memory",
            self.flag,
            offset,
            || Ok(F::one()),
        )?;

        region.assign_fixed(
            || "target",
            self.q_target,
            offset,
            || Ok(F::from_u64(target as u64)),
        )?;

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_op(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: F,
        global_counter: usize,
        value: F,
        flag: bool,
        target: usize,
        storage_key: F,
        value_prev: F,
    ) -> Result<BusMapping<F>, Error> {
        let address = {
            let cell = region.assign_advice(
                || "address",
                self.address,
                offset,
                || Ok(address),
            )?;
            Variable::<F, F> {
                cell,
                field_elem: Some(address),
                value: Some(address),
            }
        };

        let global_counter = {
            let field_elem = F::from_u64(global_counter as u64);

            let cell = region.assign_advice(
                || "global counter",
                self.global_counter,
                offset,
                || Ok(field_elem),
            )?;

            Variable::<usize, F> {
                cell,
                field_elem: Some(field_elem),
                value: Some(global_counter),
            }
        };

        let value = {
            let cell = region.assign_advice(
                || "value",
                self.value,
                offset,
                || Ok(value),
            )?;

            Variable::<F, F> {
                cell,
                field_elem: Some(value),
                value: Some(value),
            }
        };

        let storage_key = {
            let cell = region.assign_advice(
                || "storage key",
                self.storage_key,
                offset,
                || Ok(storage_key),
            )?;

            Variable::<F, F> {
                cell,
                field_elem: Some(storage_key),
                value: Some(storage_key),
            }
        };

        let value_prev = {
            let cell = region.assign_advice(
                || "value prev",
                self.value_prev,
                offset,
                || Ok(value_prev),
            )?;

            Variable::<F, F> {
                cell,
                field_elem: Some(value_prev),
                value: Some(value_prev),
            }
        };

        let flag = {
            let field_elem = F::from_u64(flag as u64);
            let cell = region.assign_advice(
                || "flag",
                self.flag,
                offset,
                || Ok(field_elem),
            )?;

            Variable::<bool, F> {
                cell,
                field_elem: Some(field_elem),
                value: Some(flag),
            }
        };

        let target = {
            let value = Some(target);
            let field_elem = Some(F::from_u64(target as u64));
            let cell = region.assign_fixed(
                || "target",
                self.q_target,
                offset,
                || Ok(F::from_u64(target as u64)),
            )?;
            Variable::<usize, F> {
                cell,
                field_elem,
                value,
            }
        };

        Ok(BusMapping {
            global_counter,
            target,
            flag,
            address,
            value,
            storage_key,
            value_prev,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::Config;
    use bus_mapping::evm::{GlobalCounter, MemoryAddress, StackAddress};
    use bus_mapping::{evm::EvmWord, BlockConstants, ExecutionTrace};

    use bus_mapping::operation::{MemoryOp, StackOp, StorageOp, RW};
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{
            MockProver, VerifyFailure::ConstraintNotSatisfied,
            VerifyFailure::Lookup,
        },
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use num::BigUint;

    use pasta_curves::{arithmetic::FieldExt, pallas};

    macro_rules! test_state_circuit {
        ($k:expr, $global_counter_max:expr, $memory_rows_max:expr, $memory_address_max:expr, $stack_rows_max:expr, $stack_address_max:expr, $storage_rows_max:expr, $memory_ops:expr, $stack_ops:expr, $storage_ops:expr, $result:expr) => {{
            #[derive(Default)]
            struct StateCircuit<
                const GLOBAL_COUNTER_MAX: usize,
                const MEMORY_ROWS_MAX: usize,
                const MEMORY_ADDRESS_MAX: usize,
                const STACK_ROWS_MAX: usize,
                const STACK_ADDRESS_MAX: usize,
                const STORAGE_ROWS_MAX: usize,
            > {
                memory_ops: Vec<MemoryOp>,
                stack_ops: Vec<StackOp>,
                storage_ops: Vec<StorageOp>,
            }

            impl<
                    F: FieldExt,
                    const GLOBAL_COUNTER_MAX: usize,
                    const MEMORY_ROWS_MAX: usize,
                    const MEMORY_ADDRESS_MAX: usize,
                    const STACK_ROWS_MAX: usize,
                    const STACK_ADDRESS_MAX: usize,
                    const STORAGE_ROWS_MAX: usize,
                > Circuit<F>
                for StateCircuit<
                    GLOBAL_COUNTER_MAX,
                    MEMORY_ROWS_MAX,
                    MEMORY_ADDRESS_MAX,
                    STACK_ROWS_MAX,
                    STACK_ADDRESS_MAX,
                    STORAGE_ROWS_MAX,
                >
            {
                type Config = Config<
                    F,
                    GLOBAL_COUNTER_MAX,
                    MEMORY_ROWS_MAX,
                    MEMORY_ADDRESS_MAX,
                    STACK_ROWS_MAX,
                    STACK_ADDRESS_MAX,
                    STORAGE_ROWS_MAX,
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
                    config.assign(
                        layouter,
                        self.memory_ops.clone(),
                        self.stack_ops.clone(),
                        self.storage_ops.clone(),
                    )?;

                    Ok(())
                }
            }

            let circuit = StateCircuit::<
                $global_counter_max,
                $memory_rows_max,
                $memory_address_max,
                $stack_rows_max,
                $stack_address_max,
                $storage_rows_max,
            > {
                memory_ops: $memory_ops,
                stack_ops: $stack_ops,
                storage_ops: $storage_ops,
            };

            let prover =
                MockProver::<pallas::Base>::run($k, &circuit, vec![]).unwrap();
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

    fn lookup_fail(
        row: usize,
        lookup_index: usize,
    ) -> halo2::dev::VerifyFailure {
        Lookup { lookup_index, row }
    }

    #[test]
    fn state_circuit() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_1 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(24),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let memory_op_2 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(17),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_3 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(87),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(17),
            StackAddress::from(1),
            EvmWord::from_str("32").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::READ,
            GlobalCounter::from(87),
            StackAddress::from(1),
            EvmWord::from_str("32").unwrap(),
        );

        let storage_op_0 = StorageOp::new(
            RW::WRITE,
            GlobalCounter::from(17),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_1 = StorageOp::new(
            RW::WRITE,
            GlobalCounter::from(18),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("32").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_2 = StorageOp::new(
            RW::WRITE,
            GlobalCounter::from(19),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("32").unwrap(),
            BigUint::from(0x40u8),
        );

        test_state_circuit!(
            14,
            2000,
            100,
            2,
            100,
            1023,
            1000,
            vec![memory_op_0, memory_op_1, memory_op_2, memory_op_3],
            vec![stack_op_0, stack_op_1],
            vec![storage_op_0, storage_op_1, storage_op_2],
            Ok(())
        );
    }

    #[test]
    fn no_stack_padding() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_1 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(24),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let memory_op_2 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(17),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_3 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(87),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(17),
            StackAddress::from(1),
            EvmWord::from_str("32").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::READ,
            GlobalCounter::from(87),
            StackAddress::from(1),
            EvmWord::from_str("32").unwrap(),
        );

        const STACK_ROWS_MAX: usize = 2;
        test_state_circuit!(
            14,
            2000,
            100,
            STACK_ROWS_MAX,
            100,
            1023,
            1000,
            vec![memory_op_0, memory_op_1, memory_op_2, memory_op_3],
            vec![stack_op_0, stack_op_1],
            vec![],
            Ok(())
        );
    }

    #[test]
    fn same_address_read() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("31").unwrap(),
        );
        let memory_op_1 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(24),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(), /* This should fail as it not
                                               * the same value as in
                                               * previous write op */
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(19),
            StackAddress::from(0),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::READ,
            GlobalCounter::from(28),
            StackAddress::from(0),
            EvmWord::from_str("13").unwrap(), /* This should fail as it not
                                               * the same value as in the
                                               * previous write op */
        );

        const MEMORY_ROWS_MAX: usize = 7;
        test_state_circuit!(
            14,
            2000,
            MEMORY_ROWS_MAX,
            1000,
            100,
            1023,
            1000,
            vec![memory_op_0, memory_op_1],
            vec![stack_op_0, stack_op_1],
            vec![],
            Err(vec![
                constraint_not_satisfied(2, 2, "Memory operation + padding", 4),
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + 1,
                    4,
                    "Stack operation",
                    2
                )
            ])
        );
    }

    #[test]
    fn first_write() {
        let stack_op_0 = StackOp::new(
            RW::READ, /* This fails because the first stack op when address
                       * changes should be write. */
            GlobalCounter::from(28),
            StackAddress::from(0),
            EvmWord::from_str("13").unwrap(),
        );

        let storage_op_0 = StorageOp::new(
            RW::READ, // Fails because the first storage op needs to be write.
            GlobalCounter::from(17),
            MemoryAddress::from_str("2").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_1 = StorageOp::new(
            RW::READ, /* Fails because when storage key changes, the op
                       * needs to be write. */
            GlobalCounter::from(18),
            MemoryAddress::from_str("2").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x41u8),
        );

        let storage_op_2 = StorageOp::new(
            RW::READ, /* Fails because when address changes, the op needs to
                       * be write. */
            GlobalCounter::from(19),
            MemoryAddress::from_str("3").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
            /* Intentionally different storage key as the last one in the previous ops to
            have two conditions met. */
        );

        const MEMORY_ROWS_MAX: usize = 2;
        const STORAGE_ROWS_MAX: usize = 2;
        test_state_circuit!(
            14,
            2000,
            MEMORY_ROWS_MAX,
            1000,
            STORAGE_ROWS_MAX,
            1023,
            1000,
            vec![],
            vec![stack_op_0],
            vec![storage_op_0, storage_op_1, storage_op_2],
            Err(vec![
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX,
                    3,
                    "First stack row operation",
                    0
                ),
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + STORAGE_ROWS_MAX,
                    6,
                    "First storage row operation",
                    0
                ),
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + STORAGE_ROWS_MAX + 1,
                    7,
                    "Storage operation",
                    1
                ),
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + STORAGE_ROWS_MAX + 2,
                    7,
                    "Storage operation",
                    0
                ),
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + STORAGE_ROWS_MAX + 2,
                    7,
                    "Storage operation",
                    1
                ),
            ])
        );
    }

    #[test]
    fn max_values() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            MemoryAddress::from_str(&format!("{:X}", MEMORY_ADDRESS_MAX))
                .unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_1 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(GLOBAL_COUNTER_MAX),
            MemoryAddress::from_str(&format!("{:X}", MEMORY_ADDRESS_MAX))
                .unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_2 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(GLOBAL_COUNTER_MAX + 1),
            MemoryAddress::from_str(&format!("{:X}", MEMORY_ADDRESS_MAX))
                .unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let memory_op_3 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            MemoryAddress::from_str(&format!("{:X}", MEMORY_ADDRESS_MAX + 1))
                .unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_4 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(24),
            MemoryAddress::from_str(&format!("{:X}", MEMORY_ADDRESS_MAX + 1))
                .unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            StackAddress::from(STACK_ADDRESS_MAX),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::READ,
            GlobalCounter::from(24),
            StackAddress::from(STACK_ADDRESS_MAX),
            EvmWord::from_str("12").unwrap(),
        );

        let stack_op_2 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(17),
            StackAddress::from(STACK_ADDRESS_MAX + 1),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_3 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(GLOBAL_COUNTER_MAX + 1),
            StackAddress::from(STACK_ADDRESS_MAX + 1),
            EvmWord::from_str("12").unwrap(),
        );

        // Small MEMORY_MAX_ROWS is set to avoid having padded rows (all padded
        // rows would fail because of the address they would have - the
        // address of the last unused row)
        const MEMORY_ROWS_MAX: usize = 7;
        const STACK_ROWS_MAX: usize = 7;
        const STORAGE_ROWS_MAX: usize = 7;
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
            STORAGE_ROWS_MAX,
            vec![
                memory_op_0,
                memory_op_1,
                memory_op_2,
                memory_op_3,
                memory_op_4
            ],
            vec![stack_op_0, stack_op_1, stack_op_2, stack_op_3],
            vec![],
            Err(vec![
                lookup_fail(4, 3),
                lookup_fail(5, 3),
                lookup_fail(6, 3),
                lookup_fail(9, 4),
                lookup_fail(10, 4),
                lookup_fail(3, 5),
                lookup_fail(10, 5)
            ])
        );
    }

    #[test]
    fn max_values_first_row() {
        // first row of a target needs to be checked for address to be in range
        // too
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            MemoryAddress::from_str(&format!("{:X}", MEMORY_ADDRESS_MAX + 1))
                .unwrap(), // this address is not in the allowed range
            EvmWord::from_str("32").unwrap(),
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(12),
            StackAddress::from(STACK_ADDRESS_MAX + 1),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::READ,
            GlobalCounter::from(24),
            StackAddress::from(STACK_ADDRESS_MAX + 1),
            EvmWord::from_str("12").unwrap(),
        );

        // Small MEMORY_MAX_ROWS is set to avoid having padded rows (all padded
        // rows would fail because of the address they would have - the
        // address of the last unused row)
        const MEMORY_ROWS_MAX: usize = 2;
        const STACK_ROWS_MAX: usize = 2;
        const STORAGE_ROWS_MAX: usize = 2;
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
            STORAGE_ROWS_MAX,
            vec![memory_op_0],
            vec![stack_op_0, stack_op_1],
            vec![],
            Err(vec![
                lookup_fail(0, 3),
                lookup_fail(1, 3),
                lookup_fail(2, 4),
                lookup_fail(3, 4),
            ])
        );
    }

    #[test]
    fn non_monotone_global_counter() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(1352),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_1 = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(1255),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let memory_op_2 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(1255), /* fails because it needs to be
                                        * strictly monotone */
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(228),
            StackAddress::from(1),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::READ,
            GlobalCounter::from(217),
            StackAddress::from(1),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_2 = StackOp::new(
            RW::READ,
            GlobalCounter::from(217),
            StackAddress::from(1),
            EvmWord::from_str("12").unwrap(),
        );

        let storage_op_0 = StorageOp::new(
            RW::WRITE,
            GlobalCounter::from(301),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_1 = StorageOp::new(
            RW::READ,
            GlobalCounter::from(302),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_2 = StorageOp::new(
            RW::READ,
            GlobalCounter::from(302), /*fails because the address and
                                       * storage key are the same as in
                                       * the previous row */
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_3 = StorageOp::new(
            RW::WRITE,
            // Global counter goes down, but it doesn't fail because
            // the storage key is not the same as in the previous row.
            GlobalCounter::from(297),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("32").unwrap(),
            BigUint::from(0x41u8),
        );

        let storage_op_4 = StorageOp::new(
            RW::WRITE,
            // Global counter goes down, but it doesn't fail because the
            // address is not the same as in the previous row (while the
            // storage key is).
            GlobalCounter::from(296),
            MemoryAddress::from_str("2").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x41u8),
        );

        const MEMORY_ROWS_MAX: usize = 100;
        const STACK_ROWS_MAX: usize = 100;
        test_state_circuit!(
            15,
            10000,
            MEMORY_ROWS_MAX,
            10000,
            STACK_ROWS_MAX,
            1023,
            1000,
            vec![memory_op_0, memory_op_1, memory_op_2],
            vec![stack_op_0, stack_op_1, stack_op_2],
            vec![
                storage_op_0,
                storage_op_1,
                storage_op_2,
                storage_op_3,
                storage_op_4
            ],
            Err(vec![
                lookup_fail(2, 2),
                lookup_fail(3, 2),
                lookup_fail(MEMORY_ROWS_MAX + 1, 2),
                lookup_fail(MEMORY_ROWS_MAX + 2, 2),
                lookup_fail(MEMORY_ROWS_MAX + STACK_ROWS_MAX + 2, 7),
            ])
        );
    }

    #[test]
    fn non_monotone_address() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(1352),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_1 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(1255),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
        );
        let memory_op_2 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(1255),
            MemoryAddress::from_str("0").unwrap(), /* fails because the
                                                    * address is not
                                                    * monotone */
            EvmWord::from_str("32").unwrap(),
        );

        let stack_op_0 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(228),
            StackAddress::from(0),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_1 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(229),
            StackAddress::from(1),
            EvmWord::from_str("12").unwrap(),
        );
        let stack_op_2 = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(230),
            StackAddress::from(0), /* this fails because the
                                    * address is not
                                    * monotone */
            EvmWord::from_str("12").unwrap(),
        );

        const MEMORY_ROWS_MAX: usize = 10;
        test_state_circuit!(
            14,
            10000,
            MEMORY_ROWS_MAX,
            10000,
            10,
            1023,
            1000,
            vec![memory_op_0, memory_op_1, memory_op_2],
            vec![stack_op_0, stack_op_1, stack_op_2],
            vec![],
            Err(vec![lookup_fail(4, 0), lookup_fail(MEMORY_ROWS_MAX + 2, 0)])
        );
    }

    #[test]
    fn memory_values() {
        let memory_op_0 = MemoryOp::new(
            RW::WRITE,
            GlobalCounter::from(1352),
            MemoryAddress::from_str("0").unwrap(),
            EvmWord::from_str(&format!("{:X}", 256)).unwrap(),
        );

        const MEMORY_ROWS_MAX: usize = 100;
        test_state_circuit!(
            15,
            10000,
            MEMORY_ROWS_MAX,
            10000,
            100,
            1023,
            1000,
            vec![memory_op_0],
            vec![],
            vec![],
            Err(vec![lookup_fail(1, 6),])
        );
    }

    #[test]
    fn storage() {
        let storage_op_0 = StorageOp::new(
            RW::WRITE,
            GlobalCounter::from(18),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_1 = StorageOp::new(
            RW::READ,
            GlobalCounter::from(19),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("33").unwrap(), /* Fails because it is READ op
                                               * and not the same
                                               * value as in the previous
                                               * row. */
            EvmWord::from_str("3").unwrap(),
            BigUint::from(0x40u8),
        );
        let storage_op_2 = StorageOp::new(
            RW::WRITE,
            GlobalCounter::from(20),
            MemoryAddress::from_str("1").unwrap(),
            EvmWord::from_str("32").unwrap(),
            EvmWord::from_str("0").unwrap(), /* Fails because not the same
                                              * as in the previous row. */
            BigUint::from(0x40u8),
        );

        const MEMORY_ROWS_MAX: usize = 2;
        const STORAGE_ROWS_MAX: usize = 2;
        test_state_circuit!(
            14,
            2000,
            MEMORY_ROWS_MAX,
            1000,
            STORAGE_ROWS_MAX,
            1023,
            1000,
            vec![],
            vec![],
            vec![storage_op_0, storage_op_1, storage_op_2],
            Err(vec![
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + STORAGE_ROWS_MAX + 1,
                    7,
                    "Storage operation",
                    3
                ),
                constraint_not_satisfied(
                    MEMORY_ROWS_MAX + STORAGE_ROWS_MAX + 2,
                    7,
                    "Storage operation",
                    4
                ),
            ])
        );
    }

    #[test]
    fn trace() {
        let input_trace = r#"
[
    {
        "memory": {
            "0": "0000000000000000000000000000000000000000000000000000000000000000",
            "20": "0000000000000000000000000000000000000000000000000000000000000000",
            "40": "0000000000000000000000000000000000000000000000000000000000000000"
        },
        "stack": [
            "40"
        ],
        "opcode": "PUSH1 40",
        "pc": 0
    },
    {
        "memory": {
            "00": "0000000000000000000000000000000000000000000000000000000000000000",
            "20": "0000000000000000000000000000000000000000000000000000000000000000",
            "40": "0000000000000000000000000000000000000000000000000000000000000000"
        },
        "stack": [
            "40",
            "80"
        ],
        "opcode": "PUSH1 80",
        "pc": 1
    }
]
"#;

        let block_ctants = BlockConstants::new(
            EvmWord::from(0u8),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
            pasta_curves::Fp::zero(),
        );

        let obtained_exec_trace = ExecutionTrace::from_trace_bytes(
            input_trace.as_bytes(),
            block_ctants,
        )
        .expect("Error on trace generation");

        let stack_ops = obtained_exec_trace.sorted_stack_ops();

        test_state_circuit!(
            14,
            2000,
            100,
            2,
            100,
            1023,
            1000,
            vec![],
            stack_ops,
            vec![],
            Ok(())
        );
    }
}

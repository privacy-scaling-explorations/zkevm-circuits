use super::super::{CaseAllocation, Word};
use super::constraint_builder::ConstraintBuilder;
use super::math_gadgets::{ConstantDivisionGadget, MaxGadget};
use super::{Address, MemorySize};
use crate::evm_circuit::param::MAX_MEMORY_SIZE_IN_BYTES;
use crate::util::Expr;
use bus_mapping::evm::GasCost;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

/// Decodes the usable part of an address stored in a Word
pub(crate) mod address_low {
    use super::super::super::Word;
    use super::super::Address;
    use crate::evm_circuit::{
        op_execution::utils::from_bytes, param::NUM_ADDRESS_BYTES_USED,
    };
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(address: &Word<F>) -> Expression<F> {
        from_bytes::expr(address.cells[0..NUM_ADDRESS_BYTES_USED].to_vec())
    }

    pub(crate) fn value<F: FieldExt>(address: [u8; 32]) -> Address {
        from_bytes::value::<F>(address[0..NUM_ADDRESS_BYTES_USED].to_vec())
            .get_lower_128() as Address
    }
}

/// The sum of bytes of the address that are unused for most calculations on the address
pub(crate) mod address_high {
    use super::super::super::Word;
    use crate::evm_circuit::{
        op_execution::utils::sum, param::NUM_ADDRESS_BYTES_USED,
    };
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(address: &Word<F>) -> Expression<F> {
        sum::expr(&address.cells[NUM_ADDRESS_BYTES_USED..32].to_vec())
    }

    pub(crate) fn value<F: FieldExt>(address: [u8; 32]) -> F {
        sum::value::<F>(&address[NUM_ADDRESS_BYTES_USED..32].to_vec())
    }
}

/// If any of the MSBs are non-zero we're always out of gas
pub(crate) fn require_address_in_range<F: FieldExt>(
    cb: &mut ConstraintBuilder<F>,
    address: &Word<F>,
) {
    cb.require_zero(address_high::expr(address));
}

/// Calculates the memory size required for a memory access at the specified address.
/// `memory_size = ceil(address/32) = floor((address + 31) / 32)`
#[derive(Clone, Debug)]
pub(crate) struct MemorySizeGadget<F> {
    memory_size: ConstantDivisionGadget<F, MAX_MEMORY_SIZE_IN_BYTES>,
}

impl<F: FieldExt> MemorySizeGadget<F> {
    pub const NUM_CELLS: usize =
        ConstantDivisionGadget::<F, MAX_MEMORY_SIZE_IN_BYTES>::NUM_CELLS;
    pub const NUM_WORDS: usize =
        ConstantDivisionGadget::<F, MAX_MEMORY_SIZE_IN_BYTES>::NUM_WORDS;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            memory_size: ConstantDivisionGadget::construct(alloc, 32),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        address: Expression<F>,
    ) -> Expression<F> {
        let (quotient, _remainder) =
            self.memory_size.constraints(cb, address + 31.expr());
        quotient
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: Address,
    ) -> Result<MemorySize, Error> {
        let (quotient, _) =
            self.memory_size
                .assign(region, offset, (address as u128) + 31)?;
        Ok(quotient as MemorySize)
    }
}

/// Returns (new memory size, memory gas cost) for a memory access.
/// If the memory needs to be expanded this will result in an extra gas cost.
/// This gas cost is the difference between the next and current memory costs:
/// `memory_cost = Gmem * memory_size + floor(memory_size * memory_size / 512)`
#[derive(Clone, Debug)]
pub(crate) struct MemoryExpansionGadget<F, const MAX_QUAD_COST_IN_BYTES: usize>
{
    address_memory_size: MemorySizeGadget<F>,
    next_memory_size: MaxGadget<F, MAX_MEMORY_SIZE_IN_BYTES>,
    curr_quad_memory_cost: ConstantDivisionGadget<F, MAX_QUAD_COST_IN_BYTES>,
    next_quad_memory_cost: ConstantDivisionGadget<F, MAX_QUAD_COST_IN_BYTES>,
}

impl<F: FieldExt, const MAX_QUAD_COST_IN_BYTES: usize>
    MemoryExpansionGadget<F, MAX_QUAD_COST_IN_BYTES>
{
    pub const NUM_CELLS: usize = MemorySizeGadget::<F>::NUM_CELLS
        + MaxGadget::<F, MAX_MEMORY_SIZE_IN_BYTES>::NUM_CELLS
        + ConstantDivisionGadget::<F, MAX_QUAD_COST_IN_BYTES>::NUM_CELLS * 2;
    pub const NUM_WORDS: usize = MemorySizeGadget::<F>::NUM_WORDS
        + MaxGadget::<F, MAX_MEMORY_SIZE_IN_BYTES>::NUM_WORDS
        + ConstantDivisionGadget::<F, MAX_QUAD_COST_IN_BYTES>::NUM_WORDS * 2;

    pub const GAS_MEM: GasCost = GasCost::MEMORY;
    pub const QUAD_COEFF_DIV: u64 = 512u64;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            address_memory_size: MemorySizeGadget::construct(alloc),
            next_memory_size: MaxGadget::construct(alloc),
            curr_quad_memory_cost: ConstantDivisionGadget::construct(
                alloc,
                Self::QUAD_COEFF_DIV,
            ),
            next_quad_memory_cost: ConstantDivisionGadget::construct(
                alloc,
                Self::QUAD_COEFF_DIV,
            ),
        }
    }

    /// Input requirements:
    /// - `curr_memory_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
    /// - `address < 32 * 256**MAX_MEMORY_SIZE_IN_BYTES`
    /// Output ranges:
    /// - `next_memory_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
    /// - `memory_gas_cost <= GAS_MEM*256**MAX_MEMORY_SIZE_IN_BYTES + 256**MAX_QUAD_COST_IN_BYTES`
    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        curr_memory_size: Expression<F>,
        address: Expression<F>,
    ) -> (Expression<F>, Expression<F>) {
        // Calculate the memory size of the memory access
        // `address_memory_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
        let address_memory_size =
            self.address_memory_size.constraints(cb, address);

        // The memory size needs to be updated if this memory access
        // requires expanding the memory.
        // `next_memory_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
        let next_memory_size = self.next_memory_size.constraints(
            cb,
            address_memory_size,
            curr_memory_size.clone(),
        );

        // Calculate the quad memory cost for the current and next memory size.
        // These quad costs will also be range limited to `< 256**MAX_QUAD_COST_IN_BYTES`.
        let (curr_quad_memory_cost, _) =
            self.curr_quad_memory_cost.constraints(
                cb,
                curr_memory_size.clone() * curr_memory_size.clone(),
            );
        let (next_quad_memory_cost, _) =
            self.next_quad_memory_cost.constraints(
                cb,
                next_memory_size.clone() * next_memory_size.clone(),
            );

        // Calculate the gas cost for the memory expansion.
        // This gas cost is the difference between the next and current memory costs.
        // `memory_gas_cost <= GAS_MEM*256**MAX_MEMORY_SIZE_IN_BYTES + 256**MAX_QUAD_COST_IN_BYTES`
        let memory_gas_cost = (next_memory_size.clone() - curr_memory_size)
            * Self::GAS_MEM.expr()
            + (next_quad_memory_cost - curr_quad_memory_cost);

        // Return the new memory size and the memory expansion gas cost
        (next_memory_size, memory_gas_cost)
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        curr_memory_size: MemorySize,
        address: Address,
    ) -> Result<(MemorySize, u128), Error> {
        // Calculate the active memory size
        let address_memory_size =
            self.address_memory_size.assign(region, offset, address)?;

        // Calculate the next memory size
        let next_memory_size = self
            .next_memory_size
            .assign(
                region,
                offset,
                F::from_u64(address_memory_size),
                F::from_u64(curr_memory_size),
            )?
            .get_lower_128() as MemorySize;

        // Calculate the quad gas cost for the memory size
        let (curr_quad_memory_cost, _) = self.curr_quad_memory_cost.assign(
            region,
            offset,
            (curr_memory_size as u128) * (curr_memory_size as u128),
        )?;
        let (next_quad_memory_cost, _) = self.next_quad_memory_cost.assign(
            region,
            offset,
            (next_memory_size as u128) * (next_memory_size as u128),
        )?;

        // Calculate the gas cost for the expansian
        let memory_cost = (next_memory_size - curr_memory_size) as u128
            * (Self::GAS_MEM.as_u64() as u128)
            + (next_quad_memory_cost - curr_quad_memory_cost);

        // Return the new memory size and the memory expansion gas cost
        Ok((next_memory_size, memory_cost))
    }
}

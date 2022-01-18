use crate::evm_circuit::{
    param::MAX_MEMORY_SIZE_IN_BYTES,
    util::{
        constraint_builder::ConstraintBuilder,
        math_gadget::{ConstantDivisionGadget, MaxGadget},
        Address, MemorySize,
    },
};
use crate::util::Expr;
use bus_mapping::evm::GasCost;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

/// Decodes the usable part of an address stored in a Word
pub(crate) mod address_low {
    use crate::evm_circuit::{
        param::NUM_ADDRESS_BYTES_USED,
        util::{from_bytes, Address, Word},
    };
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(address: &Word<F>) -> Expression<F> {
        from_bytes::expr(&address.cells[0..NUM_ADDRESS_BYTES_USED])
    }

    pub(crate) fn value<F: FieldExt>(address: [u8; 32]) -> Address {
        from_bytes::value::<F>(&address[0..NUM_ADDRESS_BYTES_USED])
            .get_lower_128() as Address
    }
}

/// The sum of bytes of the address that are unused for most calculations on the
/// address
pub(crate) mod address_high {
    use crate::evm_circuit::{
        param::NUM_ADDRESS_BYTES_USED,
        util::{sum, Word},
    };
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(address: &Word<F>) -> Expression<F> {
        sum::expr(&address.cells[NUM_ADDRESS_BYTES_USED..32])
    }

    pub(crate) fn value<F: FieldExt>(address: [u8; 32]) -> F {
        sum::value::<F>(&address[NUM_ADDRESS_BYTES_USED..32])
    }
}

/// Calculates the memory size in words required for a memory access at the
/// specified address.
/// `memory_word_size = ceil(address/32) = floor((address + 31) / 32)`
#[derive(Clone, Debug)]
pub(crate) struct MemoryWordSizeGadget<F> {
    memory_word_size: ConstantDivisionGadget<F, MAX_MEMORY_SIZE_IN_BYTES>,
}

impl<F: FieldExt> MemoryWordSizeGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        address: Expression<F>,
    ) -> Self {
        let memory_word_size =
            ConstantDivisionGadget::construct(cb, address + 31.expr(), 32);

        Self { memory_word_size }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        let (quotient, _) = self.memory_word_size.expr();
        quotient
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        address: Address,
    ) -> Result<MemorySize, Error> {
        let (quotient, _) = self.memory_word_size.assign(
            region,
            offset,
            (address as u128) + 31,
        )?;
        Ok(quotient as MemorySize)
    }
}

/// Returns (new memory size, memory gas cost) for a memory access.
/// If the memory needs to be expanded this will result in an extra gas cost.
/// This gas cost is the difference between the next and current memory costs:
/// `memory_cost = Gmem * memory_word_size + floor(memory_word_size *
/// memory_word_size / 512)`
#[derive(Clone, Debug)]
pub(crate) struct MemoryExpansionGadget<F, const MAX_QUAD_COST_IN_BYTES: usize>
{
    addr_memory_word_size: MemoryWordSizeGadget<F>,
    next_memory_word_size: MaxGadget<F, MAX_MEMORY_SIZE_IN_BYTES>,
    curr_quad_memory_cost: ConstantDivisionGadget<F, MAX_QUAD_COST_IN_BYTES>,
    next_quad_memory_cost: ConstantDivisionGadget<F, MAX_QUAD_COST_IN_BYTES>,
    gas_cost: Expression<F>,
}

impl<F: FieldExt, const MAX_QUAD_COST_IN_BYTES: usize>
    MemoryExpansionGadget<F, MAX_QUAD_COST_IN_BYTES>
{
    pub const GAS_MEM: GasCost = GasCost::MEMORY;
    pub const QUAD_COEFF_DIV: u64 = 512u64;

    /// Input requirements:
    /// - `curr_memory_word_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
    /// - `address < 32 * 256**MAX_MEMORY_SIZE_IN_BYTES`
    /// Output ranges:
    /// - `next_memory_word_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
    /// - `gas_cost <= GAS_MEM*256**MAX_MEMORY_SIZE_IN_BYTES +
    ///   256**MAX_QUAD_COST_IN_BYTES`
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        curr_memory_word_size: Expression<F>,
        address: Expression<F>,
    ) -> Self {
        // Calculate the memory size of the memory access
        // `addr_memory_word_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
        let addr_memory_word_size =
            MemoryWordSizeGadget::construct(cb, address);

        // The memory size needs to be updated if this memory access
        // requires expanding the memory.
        // `next_memory_word_size < 256**MAX_MEMORY_SIZE_IN_BYTES`
        let next_memory_word_size = MaxGadget::construct(
            cb,
            addr_memory_word_size.expr(),
            curr_memory_word_size.clone(),
        );

        // Calculate the quad memory cost for the current and next memory size.
        // These quad costs will also be range limited to `<
        // 256**MAX_QUAD_COST_IN_BYTES`.
        let curr_quad_memory_cost = ConstantDivisionGadget::construct(
            cb,
            curr_memory_word_size.clone() * curr_memory_word_size.clone(),
            Self::QUAD_COEFF_DIV,
        );
        let next_quad_memory_cost = ConstantDivisionGadget::construct(
            cb,
            next_memory_word_size.expr() * next_memory_word_size.expr(),
            Self::QUAD_COEFF_DIV,
        );

        // Calculate the gas cost for the memory expansion.
        // This gas cost is the difference between the next and current memory
        // costs. `gas_cost <=
        // GAS_MEM*256**MAX_MEMORY_SIZE_IN_BYTES + 256**MAX_QUAD_COST_IN_BYTES`
        let gas_cost = (next_memory_word_size.expr() - curr_memory_word_size)
            * Self::GAS_MEM.expr()
            + (next_quad_memory_cost.expr().0 - curr_quad_memory_cost.expr().0);

        Self {
            addr_memory_word_size,
            next_memory_word_size,
            curr_quad_memory_cost,
            next_quad_memory_cost,
            gas_cost,
        }
    }

    pub(crate) fn next_memory_word_size(&self) -> Expression<F> {
        // Return the new memory word size
        self.next_memory_word_size.expr()
    }

    pub(crate) fn gas_cost(&self) -> Expression<F> {
        // Return the gas cost
        self.gas_cost.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        curr_memory_word_size: MemorySize,
        address: Address,
    ) -> Result<(MemorySize, u128), Error> {
        // Calculate the active memory word size
        let addr_memory_word_size =
            self.addr_memory_word_size.assign(region, offset, address)?;

        // Calculate the next memory word size
        let next_memory_word_size = self
            .next_memory_word_size
            .assign(
                region,
                offset,
                F::from(addr_memory_word_size),
                F::from(curr_memory_word_size),
            )?
            .get_lower_128() as MemorySize;

        // Calculate the quad gas cost for the memory size
        let (curr_quad_memory_cost, _) = self.curr_quad_memory_cost.assign(
            region,
            offset,
            (curr_memory_word_size as u128) * (curr_memory_word_size as u128),
        )?;
        let (next_quad_memory_cost, _) = self.next_quad_memory_cost.assign(
            region,
            offset,
            (next_memory_word_size as u128) * (next_memory_word_size as u128),
        )?;

        // Calculate the gas cost for the expansian
        let memory_cost = (next_memory_word_size - curr_memory_word_size)
            as u128
            * (Self::GAS_MEM.as_u64() as u128)
            + (next_quad_memory_cost - curr_quad_memory_cost);

        // Return the new memory size and the memory expansion gas cost
        Ok((next_memory_word_size, memory_cost))
    }
}

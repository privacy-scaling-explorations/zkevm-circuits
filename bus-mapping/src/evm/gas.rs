/// Gas cost enum.
pub struct GasCost(pub u8);

impl GasCost {
    /// Constant cost for free step
    pub const ZERO: Self = Self(0);
    /// Constant cost for quick step
    pub const QUICK: Self = Self(2);
    /// Constant cost for fastest step
    pub const FASTEST: Self = Self(3);
    /// Constant cost for fast step
    pub const FAST: Self = Self(5);
    /// Constant cost for mid step
    pub const MID: Self = Self(8);
    /// Constant cost for slow step
    pub const SLOW: Self = Self(10);
    /// Constant cost for ext step
    pub const EXT: Self = Self(20);
    /// Constant cost for every additional word when expanding memory
    pub const MEMORY: Self = Self(3);
    /// Constant cost for a cold SLOAD
    pub const COLD_SLOAD_COST: Self = Self(2100);
    /// Constant cost for a cold account access
    pub const COLD_ACCOUNT_ACCESS_COST: Self = Self(2600);
    /// Constant cost for a warm storage read
    pub const WARM_STORAGE_READ_COST: Self = Self(100);
}

impl GasCost {
    /// Returns the `GasCost` as a `u8`.
    #[inline]
    pub const fn as_u8(&self) -> u8 {
        self.0
    }

    /// Returns the `GasCost` as a `usize`.
    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

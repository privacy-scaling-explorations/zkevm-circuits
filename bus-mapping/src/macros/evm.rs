//! Collection of utility macros used within this crate.

/// Helper to create GasInfos
/// The `gas` parameter will be modified inside this macro.
#[macro_export]
macro_rules! gas_info {
    ($gas:ident, $gas_cost: ident) => {{
        #[allow(unused_assignments)]
        GasInfo {
            gas: {
                let temp = $gas;
                $gas -= GasCost::$gas_cost.as_usize() as u64;
                temp
            },
            gas_cost: GasCost::$gas_cost,
        }
    }};
}

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

/// Helper to track pc
/// The `pc` parameter will be modified inside this macro.
#[macro_export]
macro_rules! advance_pc {
    ($pc:ident) => {{
        #[allow(unused_assignments)]
        {
            let temp = $pc;
            $pc = ProgramCounter::from($pc.0 + 1);
            temp
        }
    }};
}

/// Helper to track gc
/// The `gc` parameter will be modified inside this macro.
#[macro_export]
macro_rules! advance_gc {
    ($gc:ident) => {{
        #[allow(unused_assignments)]
        {
            let temp = $gc;
            $gc = GlobalCounter::from($gc.0 + 1);
            temp
        }
    }};
}

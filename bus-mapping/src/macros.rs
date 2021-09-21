//! Collection of utility macros used within this crate.

macro_rules! impl_from_big_uint_wrappers {
    ($implemented:ty = $alias:expr, ($($implementor:ty),*)) => {
        $(impl From<$implementor> for $implemented {
            fn from(item: $implementor) -> $implemented {
                $alias(BigUint::from(item))
            }
        })*
    };
}

macro_rules! impl_from_usize_wrappers {
    ($implemented:ty = $alias:expr, ($($implementor:ty),*)) => {
        $(impl From<$implementor> for $implemented {
            fn from(item: $implementor) -> $implemented {
                $alias(item as usize)
            }
        })*
    };
}

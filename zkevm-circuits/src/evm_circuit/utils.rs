use num::BigUint;

pub fn biguint_to_u8s(val: &BigUint) -> [u8; 32] {
    let mut ret = [0u8; 32];
    for (pos, v) in val.to_bytes_le().iter().enumerate() {
        ret[pos] = *v
    }
    ret
}

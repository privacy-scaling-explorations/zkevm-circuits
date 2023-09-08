use std::{
    ffi::{CStr, CString},
    os::raw::c_char,
};

mod witness {
    use super::*;
    extern "C" {
        pub fn GetWitness(str: *const c_char) -> *const c_char;
    }
}

pub fn get_witness(data: &str) -> String {
    let c_config = CString::new(data).expect("invalid config");
    let result = unsafe { witness::GetWitness(c_config.as_ptr()) };
    let c_str = unsafe { CStr::from_ptr(result) };
    let c_str_string = c_str.to_str().expect("Error translating from library");
    c_str_string.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let data = r#"
                {
                    "NodeUrl": "https://mainnet.infura.io/v3/9aa3d95b3bc440fa88ea12eaa4456161",
                    "BlockNum": 14359865,
                    "Addr": "0x4E5B2e1dc63F6b91cb6Cd759936495434C7e972F",
                    "Keys": ["0x12", "0x21"],
                    "Values": ["0x1123e2", "0xa21"]
                }"#;

        let result = get_witness(data);
        assert!(result.contains("disable_preimage_check"));
    }
}

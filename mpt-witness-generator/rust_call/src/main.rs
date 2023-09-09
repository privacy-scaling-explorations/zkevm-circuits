// use serde_json::{json, Value};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::fs::File;
use std::io::Write;

extern "C" {
    fn GetWitness(str: *const c_char) -> *const c_char;
}

fn main() {
    let data = r#"
        {
            "NodeUrl": "https://mainnet.infura.io/v3/9aa3d95b3bc440fa88ea12eaa4456161",
            "BlockNum": 14359865,
            "Addr": "0x4E5B2e1dc63F6b91cb6Cd759936495434C7e972F",
            "Keys": ["0x12", "0x21"],
            "Values": ["0x1123e2", "0xa21"]
        }"#;

    let c_config = CString::new(data).expect("invalid config");

    let result = unsafe { GetWitness(c_config.as_ptr()) };
    let c_str = unsafe { CStr::from_ptr(result) };
    let string = c_str.to_str().expect("Error translating from library");
    println!("{:?}", string);

    let mut f = File::create("proof.json").expect("Unable to create file");
    f.write_all(string.as_bytes()).expect("Unable to write data");
}

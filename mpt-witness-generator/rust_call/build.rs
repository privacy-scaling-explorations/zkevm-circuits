fn main() {
    let path = "./build";
    let lib = "mpt";

    println!("cargo:rustc-link-search=native={}", path);
    println!("cargo:rustc-link-lib=static={}", lib);
}


use std::env;

fn main() {
    let lib_name = "go-geth-utils";
    let out_dir = env::var("OUT_DIR").unwrap();

    // Build
    gobuild::Build::new()
        .file("./src/lib.go")
        .file("./src/trace.go")
        .compile(lib_name);

    // Link
    println!("cargo:rustc-link-search=native={}", out_dir);
    println!("cargo:rustc-link-lib=static={}", lib_name);
}

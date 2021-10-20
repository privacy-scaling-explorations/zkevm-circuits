use std::env;

fn main() {
    let lib_name = "go-geth-utils";
    let out_dir = env::var("OUT_DIR").unwrap();

    // Build
    gobuild::Build::new().file("./lib/lib.go").compile(lib_name);

    // Files the lib depends on that should recompile the lib
    let dep_files = vec!["./gethutil/trace.go"];
    for file in dep_files {
        println!("cargo:rerun-if-changed={}", file);
    }

    // Link
    println!("cargo:rustc-link-search=native={}", out_dir);
    println!("cargo:rustc-link-lib=static={}", lib_name);
}

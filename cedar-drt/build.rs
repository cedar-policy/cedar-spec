use std::env;
fn main() {
    let lean_dir = env::var("LEAN_LIB_DIR").unwrap();
    println!("cargo:rustc-link-search=native=../cedar-lean/build/lib");
    println!("cargo:rustc-link-search=native={lean_dir}");
    println!("cargo:rustc-link-search=native=../cedar-lean/lake-packages/std/build/lib");
    println!("cargo:rustc-link-search=native=../cedar-lean/lake-packages/mathlib/build/lib");
    println!("cargo:rustc-link-search=native=../cedar-lean/lake-packages/Qq/build/lib");
    println!("cargo:rustc-link-search=native=../cedar-lean/lake-packages/aesop/build/lib");
    println!("cargo:rustc-link-search=native=../cedar-lean/lake-packages/proofwidgets/build/lib");
}

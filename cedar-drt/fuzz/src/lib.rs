mod prt;
#[cfg(not(feature = "prt"))]
pub use libfuzzer_sys::fuzz_target;

pub mod schemas;
pub mod validation_drt;

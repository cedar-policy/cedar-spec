#![no_main]

use amzn_cedar_core::parser::parse_policyset;
use amzn_cedar_drt_inner::fuzz_target;

fuzz_target!(|input: String| {
    // Ensure the parser does not crash
    #[allow(clippy::single_match)]
    match parse_policyset(&input) {
        Ok(_) => (),
        Err(_) => (),
    };
});

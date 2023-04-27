#![no_main]

use cedar_policy_core::parser::parse_policyset;
use cedar_drt_inner::fuzz_target;

fuzz_target!(|input: String| {
    // Ensure the parser does not crash
    #[allow(clippy::single_match)]
    match parse_policyset(&input) {
        Ok(_) => (),
        Err(_) => (),
    };
});

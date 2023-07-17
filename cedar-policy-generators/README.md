# Cedar Policy Generators

This folder contains code for DRT input (i.e., schemas, entities, policies, requests, and etc.) generation using the [arbitrary](https://docs.rs/arbitrary/latest/arbitrary/index.html) crate.
Currently the only user of this crate is [cedar-drt](../cedar-drt).
An example is the target [`abac-type-directed`](../cedar-drt/fuzz/fuzz_targets/abac-type-directed.rs#L58-L72) that generates arbitrary typed ABAC policies.
We plan to extend the generators to take inputs as custom schemas.

## Build and Test
`cargo build` and `cargo test`

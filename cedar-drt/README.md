# Cedar DRT

This folder contains code for fuzzing, property-based testing, and differential testing of Cedar.
See the README in the toplevel directory `..` for instructions on how to run.

## Available fuzz targets

The table below lists all available fuzz targets, including which component of the code they test and whether they perform property-based testing of the Rust code (PBT) or differential testing of the Rust code against the Dafny spec (DRT).

| Name | Component(s) tested | Type | Description |
| ----------- | ----------- | ----------- | ----------- |
| [`abac-type-directed`](fuzz/fuzz_targets/abac-type-directed.rs) | Evaluator | DRT | Diff test evaluator on ABAC policies using (mostly) well-typed inputs |
| [`abac`](fuzz/fuzz_targets/abac.rs) | Evaluator | DRT | Diff test evaluator on ABAC policies |
| [`formatter`](fuzz/fuzz_targets/formatter.rs) | Policy formatter, Pretty printer, Parser | PBT | Test round trip property: parse ∘ format ∘ pretty-print == id for ASTs |
| [`partial-eval`](fuzz/fuzz_targets/partial-eval.rs) | Partial evaluator | PBT | Test that residual policies with unknowns substituted are equivalent to original policies with unknowns replaced |
| [`pp`](fuzz/fuzz_targets/pp.rs) | Pretty printer, Parser | PBT | Test round trip property: parse ∘ pretty-print == id for ASTs |
| [`rbac-authorizer`](fuzz/fuzz_targets/rbac-authorizer.rs) | Authorizer | PBT + DRT | Test for correct authorization responses over a set of simple policies |
| [`rbac`](fuzz/fuzz_targets/rbac.rs) | Authorizer | DRT | Diff test authorizer on sets of RBAC policies, including template instantiations |
| [`simple-parser`](fuzz/fuzz_targets/simple-parser.rs) |  Parser | PBT | Test that parsing doesn't crash with random input strings |
| [`strict-validation-drt-type-directed`](fuzz/fuzz_targets/strict-validation-drt-type-directed.rs) | Validator | DRT | Diff test strict validation using (mostly) well-typed inputs |
| [`validation-drt-type-directed`](fuzz/fuzz_targets/validation-drt-type-directed.rs) | Validator | DRT | Diff test permissive validation using (mostly) well-typed inputs |
| [`validation-drt`](fuzz/fuzz_targets/validation-drt.rs) | Validator | DRT | Diff test permissive validation |
| [`validation-pbt`](fuzz/fuzz_targets/validation-pbt.rs) | Validator | PBT | Test that validated policies do not result in type errors |
| [`wildcard-matching`](fuzz/fuzz_targets/wildcard-matching.rs) | String matching algorithm used for the `like` operator | DRT | Diff test wildcard matching using a regex-based implementation |


## Logging

If the fuzz targets are compiled with the `log` features, then they will log their entire corpus to the file pointed at in the `LOGFILE` environment variable.
The sampling rate can be controlled by the `RATE` environment variable, which defaults to 100% if not set.

## Generating corpus tests

When using the `abac` or `abac-type-directed` targets, you can set `DUMP_TEST_DIR` and `DUMP_TEST_NAME` to have the fuzzer write out inputs in the format used by our [integration tests](https://github.com/cedar-policy/cedar/tree/main/cedar-integration-tests).
The `create_corpus.sh` script will run the fuzzer for a set amount of time and then write the (minimized) corpus inputs into a folder using the integration test format.
You can adjust the script's behavior using the following environment variables:
* `FUZZ_TARGET`: `abac` or `abac-type-directed` (default = `abac`)
* `TIMEOUT`: how long to run (default = 15m)
* `JOBS`: number of jobs (default = 4)
* `DUMP_DIR`: where to write the results (default = `./corpus_tests`)

## Debugging build failures

If you run into weird build issues,
1. Make sure you have run `source set_env_vars.sh`, which sets all the environment variables needed to run the Dafny and Lean definitional code.
2. Try a `cargo clean` and rebuild.
3. If the steps above don't help, then file [an issue](https://github.com/cedar-policy/cedar-spec/issues).

If everything builds, but the integration tests are failing, then it may be helpful to set `RUST_BACKTRACE=1` and run `cargo test -- --nocapture` to print additional test information.
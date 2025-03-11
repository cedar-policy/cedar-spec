# Cedar DRT

This folder contains code for fuzzing, property-based testing, and differential testing of Cedar.
See the README in the toplevel directory `..` for instructions on how to run.

## Available fuzz targets

The table below lists all available fuzz targets, including which component of the code they test and whether they perform differential testing of the Rust code against the Lean spec (DRT) or property-based testing of the Rust code (PBT). The latter properties are subdivided in the table as _round trip_ properties and _general_ properties.

| Name | Component(s) tested | Type | Description |
| ----------- | ----------- | ----------- | ----------- |
| [`abac-type-directed`](fuzz/fuzz_targets/abac-type-directed.rs) | Authorizer | DRT | Diff test authorizer on ABAC policies using (mostly) well-typed inputs |
| [`abac`](fuzz/fuzz_targets/abac.rs) | Authorizer | DRT | Diff test authorizer on ABAC policies |
| [`eval-type-directed`](fuzz/fuzz_targets/eval-type-directed.rs) | Evaluator | DRT | Diff test evaluator on (mostly) well-typed expressions |
| [`rbac-authorizer`](fuzz/fuzz_targets/rbac-authorizer.rs) | Authorizer | DRT | Test for correct authorization responses over a set of simple policies |
| [`rbac`](fuzz/fuzz_targets/rbac.rs) | Authorizer | DRT | Diff test authorizer on sets of RBAC policies, including template instantiations |
| [`validation-drt-type-directed`](fuzz/fuzz_targets/validation-drt-type-directed.rs) | Validator | DRT | Diff test validation using (mostly) well-typed inputs |
| [`validation-drt`](fuzz/fuzz_targets/validation-drt.rs) | Validator | DRT | Diff test validation |
| [`entity-validation`](fuzz/fuzz_targets/entity-validation.rs) | Entity Validator | DRT | Diff test entity validation | 
| [`request-validation`](fuzz/fuzz_targets/request-validation.rs) | Request Validator | DRT | Diff test request validation |
|  |  |  |  |
| [`formatter`](fuzz/fuzz_targets/formatter.rs) | Policy formatter, Pretty printer, Parser | PBT | Test round trip property: parse ∘ format ∘ pretty-print == id for ASTs |
| [`formatter-bytes`](fuzz/fuzz_targets/formatter-bytes.rs) | Policy formatter, Parser | PBT | The same as `formatter`, but we start with an arbitrary string instead of pretty-printing a policy AST |
| [`json-schema-roundtrip`](fuzz/fuzz_targets/json-schema-roundtrip.rs) | Schema parser | PBT | Test round trip property: parse ∘ pretty-print ∘ parse-json ∘ print-json == id for schemas
| [`roundtrip`](fuzz/fuzz_targets/roundtrip.rs) | Pretty printer, Parser, Conversion to JSON | PBT | Test round trip property: parse ∘ pretty-print == deserialize ∘ serialize == id for ASTs |
| [`schema-roundtrip`](fuzz/fuzz_targets/schema-roundtrip.rs) | Schema parser | PBT | Test round trip property: parse ∘ pretty-print == id for schemas
| [`convert-schema-json-to-human`](fuzz/fuzz_targets/convert-schema-json-to-human.rs) | Schema parser | PBT | Test we can convert all human schemas to equivalent JSON. parse == parse-json ∘ print-json ∘ parse 
| [`convert-schema-human-to-json`](fuzz/fuzz_targets/convert-schema-human-to-json.rs) | Schema parser | PBT | Test we can convert all JSON schemas to an equivalent human format schema. parse-json == parse ∘ pretty-print ∘ parse-json
| [`convert-policy-cedar-to-json`](fuzz/fuzz_targets/convert-policy-cedar-to-json.rs) | Parser, Conversion to JSON | PBT | Test we can convert all policies to an equivalent EST.  parse-ast ∘ parse-cst == deserialize ∘ serialize ∘ parse-cst
| [`convert-policy-json-to-cedar`](fuzz/fuzz_targets/convert-policy-json-to-cedar.rs) | Parser, JSON Parser | PBT | Test we can convert all EST to an equivalent policy in the human-readable cedar syntax. deserialize == parse-ast ∘ pretty-print ∘ deserialize
| [`roundtrip-entities`](fuzz/fuzz_targets/roundtrip-entities.rs) | Entity parser | PBT | Test round trip property for entity data. parse-entity-json ∘ serialize-entity == id for entities |
| [`roundtrip-entities-bytes`](fuzz/fuzz_targets/roundtrip-entities.rs) | Entity parser | PBT | Test the same round trip property for entity data, starting from an arbitrary string instead of generating the entities data structure |
|  |  |  |  |
| [`simple-parser`](fuzz/fuzz_targets/simple-parser.rs) |  Parser | PBT | Test that parsing doesn't crash with random input strings |
| [`validation-pbt`](fuzz/fuzz_targets/validation-pbt.rs) | Validator | PBT | Test that validated policies do not result in type errors |
| [`validation-pbt-type-directed`](fuzz/fuzz_targets/validation-pbt-type-directed.rs) | Validator | PBT | Test that validated policies do not result in type errors using (mostly) well-typed inputs |
| [`entity-manifest-drt-type-directed`](fuzz/fuzz_targets/entity-slicing-pbt-type-directed.rs) | Entity Slicing | DRT | Test that entity slicing produces the same authorization response as without it. |
| [`wildcard-matching`](fuzz/fuzz_targets/wildcard-matching.rs) | String matching algorithm used for the `like` operator | PBT | Test algorithm against a regex-based implementation |

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
1. Make sure you have run `source set_env_vars.sh`, which sets all the environment variables needed to run the Lean definitional code.
2. Make sure you have built the Lean library with `( cd ../cedar-lean && ../cedar-drt/build_lean_lib.sh )`. See the [cedar-lean README](../cedar-lean/README.md) if this command doesn't work.
3. Try a `cargo clean` and rebuild.
4. If the steps above don't help, then file [an issue](https://github.com/cedar-policy/cedar-spec/issues).

If everything builds, but the integration tests are failing, then it may be helpful to set `RUST_BACKTRACE=1` and run `cargo test -- --nocapture` to print additional test information.

## Running integration tests

The integration tests are run by default in CI (e.g., as a part of each pull request), but you can also run them locally.
In order to do this, you need to have the [`cedar`](https://github.com/cedar-policy/cedar) and [`cedar-integration-tests`](https://github.com/cedar-policy/cedar-integration-tests) repositories cloned locally.
`cedar` should be in the toplevel directory (so `../cedar`) and `cedar-integration-tests` should be in the `cedar` directory (so `../cedar/cedar-integration-tests`).
Then, run `cargo test --features "integration-testing"`.

```bash
# starting in the top-level directory (..)
git clone --depth 1 https://github.com/cedar-policy/cedar
cd cedar
rm -rf cedar-integration-tests
git clone --depth 1 https://github.com/cedar-policy/cedar-integration-tests
cd cedar-integration-tests
tar xzf corpus-tests.tar.gz
cd ../../cedar-drt
cargo test --features "integration-testing"
```

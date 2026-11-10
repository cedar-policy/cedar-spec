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
| [`partial-schema-validation-drt`](fuzz/fuzz_targets/partial-schema-validation-drt.rs) | Entity and Request Validator (RFC 116) | DRT | Diff test entity and request validation against a schema that declares some entity types and actions `external` |
| [`partial-schema-link-drt`](fuzz/fuzz_targets/partial-schema-link-drt.rs) | Schema linker (RFC 116) | DRT | Diff test successful and rejected links between generated partial schemas |
| [`partial-schema-link-order-independence-pbt`](fuzz/fuzz_targets/partial-schema-link-order-independence-pbt.rs) | Schema linker (RFC 116) | PBT | Test that linking is independent of the order of its inputs, on schemas parsed from arbitrary JSON |
| [`tpe-is-authorized-drt`](fuzz/fuzz_targets/tpe-is-authorized-drt.rs) | TPE (partial authorization) | DRT | Diff test Rust and Lean TPE is_authorized API: decisions, policy categorizations, and residual expressions |
| [`tpe-residual-reauthorize-drt`](fuzz/fuzz_targets/tpe-residual-reauthorize-drt.rs) | TPE (reauthorization of arbitrary residuals) | DRT | Diff test concrete evaluation of a generated residual. The model walks the residual directly; Rust projects it to an `Expr` and evaluates that, so this compares the two routes `reauthorize` and `Residual.evaluate` take |
| [`partial-entity-validation-drt`](fuzz/fuzz_targets/partial-entity-validation-drt.rs) | TPE (partial entity validator) | DRT | Diff test whether partial entities are valid for a schema |
| [`partial-entity-consistency-drt`](fuzz/fuzz_targets/partial-entity-consistency-drt.rs) | TPE (partial entity validator) | DRT | Diff test whether partial entities are consistent with concrete entities |
| [`partial-request-validation-drt`](fuzz/fuzz_targets/partial-request-validation-drt.rs) | TPE (partial request validator) | DRT | Diff test whether a partial request is valid for a schema |
| [`partial-request-consistency-drt`](fuzz/fuzz_targets/partial-request-consistency-drt.rs) | TPE (partial request validator) | DRT | Diff test whether a partial request is consistent with a concrete request |
|  |  |  |  |
| [`formatter`](fuzz/fuzz_targets/formatter.rs) | Policy formatter, Pretty printer, Parser | PBT | Test round trip property: parse ∘ format ∘ pretty-print == id for ASTs |
| [`formatter-bytes`](fuzz/fuzz_targets/formatter-bytes.rs) | Policy formatter, Parser | PBT | The same as `formatter`, but we start with an arbitrary string instead of pretty-printing a policy AST |
| [`json-schema-roundtrip`](fuzz/fuzz_targets/json-schema-roundtrip.rs) | Schema parser | PBT | Test round trip property: parse ∘ pretty-print ∘ parse-json ∘ print-json == id for schemas
| [`roundtrip`](fuzz/fuzz_targets/roundtrip.rs) | Pretty printer, Parser, Conversion to JSON | PBT | Test round trip property: parse ∘ pretty-print == deserialize ∘ serialize == id for policy ASTs |
| [`policy-set-roundtrip`](fuzz/fuzz_targets/policy-setroundtrip.rs) | Pretty printer, Parser, Conversion to JSON | PBT | Test round trip property: parse ∘ pretty-print == deserialize ∘ serialize == id for a policy set ASTs
| [`schema-roundtrip`](fuzz/fuzz_targets/schema-roundtrip.rs) | Schema parser | PBT | Test round trip property: parse ∘ pretty-print == id for schemas
| [`convert-schema-json-to-human`](fuzz/fuzz_targets/convert-schema-json-to-human.rs) | Schema parser | PBT | Test we can convert all human schemas to equivalent JSON. parse == parse-json ∘ print-json ∘ parse
| [`convert-schema-human-to-json`](fuzz/fuzz_targets/convert-schema-human-to-json.rs) | Schema parser | PBT | Test we can convert all JSON schemas to an equivalent human format schema. parse-json == parse ∘ pretty-print ∘ parse-json
| [`convert-policy-cedar-to-json`](fuzz/fuzz_targets/convert-policy-cedar-to-json.rs) | Parser, Conversion to JSON | PBT | Test we can convert all policies to an equivalent EST.  parse-ast ∘ parse-cst == deserialize ∘ serialize ∘ parse-cst
| [`convert-policy-json-to-cedar`](fuzz/fuzz_targets/convert-policy-json-to-cedar.rs) | Parser, JSON Parser | PBT | Test we can convert all EST to an equivalent policy in the human-readable cedar syntax. deserialize == parse-ast ∘ pretty-print ∘ deserialize
| [`roundtrip-entities`](fuzz/fuzz_targets/roundtrip-entities.rs) | Entity parser | PBT | Test round trip property for entity data. parse-entity-json ∘ serialize-entity == id for entities |
| [`roundtrip-entities-bytes`](fuzz/fuzz_targets/roundtrip-entities.rs) | Entity parser | PBT | Test the same round trip property for entity data, starting from an arbitrary string instead of generating the entities data structure |
| [`pst-ast-roundtrip`](fuzz/fuzz_targets/pst-ast-roundtrip.rs) | PST ↔ AST conversion | PBT | Test idempotency: PST → AST → PST → AST → PST stabilizes after one normalization pass |
| [`pst-est-roundtrip`](fuzz/fuzz_targets/pst-est-roundtrip.rs) | PST ↔ EST conversion | PBT | Test round trip property: PST → EST → PST == id for templates |
| [`pst-policyset-text-roundtrip`](fuzz/fuzz_targets/pst-policyset-text-roundtrip.rs) | PST policy set conversion through API | PBT | Test round trip property: PST policy set -> PolicySet → cedar text → PolicySet -> PST == id with explicit policy id management, and through public API |
| [`pst-policyset-json-roundtrip`](fuzz/fuzz_targets/pst-policyset-json-roundtrip.rs) | PST policy set conversion through API | PBT | Test round trip property: PST policy set -> PolicySet → JSON → PolicySet -> PST == id with explicit policy id management, and through public API |
|  |  |  |  |
| [`simple-parser`](fuzz/fuzz_targets/simple-parser.rs) |  Parser | PBT | Test that parsing doesn't crash with random input strings |
| [`validation-pbt`](fuzz/fuzz_targets/validation-pbt.rs) | Validator | PBT | Test that validated policies do not result in type errors |
| [`validation-pbt-type-directed`](fuzz/fuzz_targets/validation-pbt-type-directed.rs) | Validator | PBT | Test that validated policies do not result in type errors using (mostly) well-typed inputs |
| [`entity-manifest-drt-type-directed`](fuzz/fuzz_targets/entity-slicing-pbt-type-directed.rs) | Entity Slicing | DRT | Test that entity slicing produces the same authorization response as without it. |
| [`wildcard-matching`](fuzz/fuzz_targets/wildcard-matching.rs) | String matching algorithm used for the `like` operator | PBT | Test algorithm against a regex-based implementation |
| [`tc-repair-equivalence`](fuzz/fuzz_targets/tc-repair-equivalence.rs) | Entity transitive closure (`repair_tc` vs `compute_tc`) | PBT | Test that incrementally repairing the transitive closure of an entity graph (`repair_tc` after adding edges) agrees with recomputing it from scratch (`compute_tc`), on both cycle detection and the resulting ancestor sets |
| [`entities-upsert-equivalence`](fuzz/fuzz_targets/entities-upsert-equivalence.rs) | Entity store incremental update (`Entities::upsert_entities`) | PBT | Test that applying a batch of entity upserts to a store agrees with rebuilding the store from scratch via `Entities::from_entities`, comparing ancestor sets and cycle detection. Catches the stale-ancestor bug fixed in [cedar#2628](https://github.com/cedar-policy/cedar/pull/2628) where a node repeated in one batch kept a dropped parent's ancestors |
|  |  |  |  |
| [`protobuf-roundtrip`](fuzz/fuzz_targets/protobuf-roundtrip.rs) | Protobuf encoding and decoding | PBT | Test round trip property: decode ∘ encode == id for generated policy sets, requests, entities, and schemas |
| [`protobuf-decode-bytes-entity`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-entity.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as an `Entity` does not crash, and that a decoded entity roundtrips through JSON |
| [`protobuf-decode-bytes-entities`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-entities.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as `Entities` does not crash, and that decoded entities roundtrip through JSON |
| [`protobuf-decode-bytes-expression`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-expression.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as an `Expression` does not crash, and that a decoded expression prints to Cedar and parses again |
| [`protobuf-decode-bytes-policyset`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-policyset.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as a `PolicySet` does not crash, and that a decoded policy set prints to Cedar and parses again, and serializes to JSON and deserializes again |
| [`protobuf-decode-bytes-request`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-request.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as a `Request` does not crash, and that the context values of a decoded request print to Cedar and parse again |
| [`protobuf-decode-bytes-schema`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-schema.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as a `Schema` does not crash, and that a decoded schema roundtrips through Cedar schema syntax and JSON |
| [`protobuf-decode-bytes-template`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-bytes-template.rs) | Protobuf decoder | PBT | Test that decoding arbitrary bytes as a `Template` does not crash, and that a decoded template prints to Cedar and parses again |
| [`protobuf-decode-gen-entity`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-entity.rs) | Protobuf decoder | PBT | Test that validation when decoding a generated protobuf entity is not stronger than when deserializing it from JSON |
| [`protobuf-decode-gen-entities`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-entities.rs) | Protobuf decoder | PBT | Test that validation when decoding generated protobuf entities is not stronger than when deserializing them from JSON |
| [`protobuf-decode-gen-expression`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-expression.rs) | Protobuf decoder | PBT | Test that validation when decoding a generated protobuf expression is not stronger than when parsing it from Cedar |
| [`protobuf-decode-gen-policyset`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-policyset.rs) | Protobuf decoder | PBT | Test that validation when decoding a generated protobuf policy set is not stronger than when parsing it from Cedar |
| [`protobuf-decode-gen-request`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-request.rs) | Protobuf decoder | PBT | Test that validation when decoding a generated protobuf request is not stronger than when parsing its context values from Cedar |
| [`protobuf-decode-gen-schema`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-schema.rs) | Protobuf decoder | PBT | Test that a schema decoded from a generated protobuf schema roundtrips through Cedar schema syntax and JSON |
| [`protobuf-decode-gen-template`](fuzz/fuzz_targets/protobuf-decode/protobuf-decode-gen-template.rs) | Protobuf decoder | PBT | Test that validation when decoding a generated protobuf template is not stronger than when parsing it from Cedar |
| [`protobuf-encode-bytes-entity`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-bytes-entity.rs) | Protobuf encoder, Entity parser | PBT | Test round trip property: decode ∘ encode == id for an `Entity` parsed from an arbitrary JSON string |
| [`protobuf-encode-bytes-entities`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-bytes-entities.rs) | Protobuf encoder, Entity parser | PBT | Test round trip property: decode ∘ encode == id for `Entities` parsed from an arbitrary JSON string |
| [`protobuf-encode-bytes-expression`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-bytes-expression.rs) | Protobuf encoder, Parser | PBT | Test that an `Expression` parsed (with a depth limit) from an arbitrary string encodes, decodes, prints to Cedar, and parses again |
| [`protobuf-encode-bytes-policyset`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-bytes-policyset.rs) | Protobuf encoder, Parser | PBT | Test round trip property: decode ∘ encode == id for a `PolicySet` parsed (with a depth limit) from an arbitrary string |
| [`protobuf-encode-bytes-schema`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-bytes-schema.rs) | Protobuf encoder, Schema parser | PBT | Test round trip property: decode ∘ encode == id for a `Schema` parsed from an arbitrary Cedar schema string |
| [`protobuf-encode-bytes-template`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-bytes-template.rs) | Protobuf encoder, Parser | PBT | Test round trip property: decode ∘ encode == id for a `Template` parsed (with a depth limit) from an arbitrary string |
| [`protobuf-encode-gen-entity`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-entity.rs) | Protobuf encoder | PBT | Test round trip property: decode ∘ encode == id for a generated `Entity` |
| [`protobuf-encode-gen-entities`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-entities.rs) | Protobuf encoder | PBT | Test round trip property: decode ∘ encode == id for generated `Entities` |
| [`protobuf-encode-gen-expression`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-expression.rs) | Protobuf encoder | PBT | Test that a generated expression encodes, decodes, prints to Cedar, and parses again |
| [`protobuf-encode-gen-policyset`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-policyset.rs) | Protobuf encoder | PBT | Test round trip property: decode ∘ encode == id for generated policy sets |
| [`protobuf-encode-gen-request`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-request.rs) | Protobuf encoder | PBT | Test round trip property: decode ∘ encode == id for generated requests |
| [`protobuf-encode-gen-schema`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-schema.rs) | Protobuf encoder | PBT | Test round trip property: decode ∘ encode == id (up to schema equivalence) for generated schemas |
| [`protobuf-encode-gen-template`](fuzz/fuzz_targets/protobuf-encode/protobuf-encode-gen-template.rs) | Protobuf encoder | PBT | Test round trip property: decode ∘ encode == id for generated templates |

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

# Cedar DRT

This folder contains code for input generation, fuzzing, property-based testing, and differential testing of Cedar.
See the README in the toplevel directory `..` for instructions on how to run.

## Available fuzz targets

The table below lists all available fuzz targets, including which component of the code they test and whether they perform property-based testing of the Rust code (PBT) or differential testing of the Rust code against the Dafny spec (DRT).

| Name | Component(s) tested | Type | Description |
| ----------- | ----------- | ----------- | ----------- |
| `abac-type-directed` | Evaluator | DRT | Diff test evaluator on ABAC policies using (mostly) well-typed inputs |
| `abac` | Evaluator | DRT | Diff test evaluator on ABAC policies |
| `formatter` | Policy formatter, Pretty printer, Parser | PBT | Test round trip property: parse ∘ format ∘ pretty-print == id for ASTs |
| `partial-eval` | Partial evaluator | PBT | Test that residual policies with unknowns substituted are equivalent to original policies with unknowns replaced |
| `pp` | Pretty printer, Parser | PBT | Test round trip property: parse ∘ pretty-print == id for ASTs |
| `rbac-authorizer` | Authorizer | PBT + DRT | Test for correct authorization responses over a set of simple policies |
| `rbac` | Authorizer | DRT | Diff test authorizer on sets of RBAC policies, including template instantiations |
| `simple-parser` |  Parser | DRT | Test that parsing doesn't crash with random input strings |
| `strict-validation-drt-type-directed` | Validator | DRT | Diff test strict validation using (mostly) well-typed inputs |
| `validation-drt-type-directed` | Validator | DRT | Diff test permissive validation using (mostly) well-typed inputs |
| `validation-drt` | Validator | DRT | Diff test permissive validation |
| `validation-pbt` | Validator | PBT | Test that validated policies do not result in type errors |
| `wildcard-matching` | String matching algorithm used for the `like` operator | DRT | Diff test wildcard matching using a regex-based implementation |

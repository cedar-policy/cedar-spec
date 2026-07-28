# Typed-expression DRT notes (issue #840)

Reproduction aids for the `typed-expression-drt` target.

- `run.sh` builds and tests the target. `./drt-840-notes/run.sh {build|test|lean|probe}`.
- `probe_full.lean` and `probe_like.lean` dump Lean's derived `ToJson` for every
  `TypedExpr` constructor and every `CedarType` shape. The Rust renderer in
  `cedar-drt/src/typed_expr.rs` was written against that output rather than against a
  guess at the encoding, and these are kept so the encoding can be re-checked when the
  Lean datatype changes.
- `probe_json.lean` is the smaller first probe, superseded by `probe_full.lean`.

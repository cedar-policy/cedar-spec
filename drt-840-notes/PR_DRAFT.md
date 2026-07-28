# PR draft. NOT PUSHED, NOT OPENED.

Branch: `drt-typed-expression-840`. Target: `cedar-policy/cedar-spec` `main`.

Title: **Add typechecker DRT target comparing the typed expression (#840)**

---

The existing validator DRT compares whether Rust and Lean agree that validation
passed. This adds a target that compares the `TypedExpr` each side produces, so a
disagreement about the annotated AST is visible even when both sides reach the same
verdict.

Rust side is `Typechecker::typecheck_by_single_request_env`. Lean side is a new
`typecheckPolicyTyped` export over `Validation.typecheckPolicy`. Results are aligned
by policy id and by a `(principal, action, resource)` environment key that both sides
produce independently.

## How the comparison works

Each side is rendered independently into a small neutral node type, with the type
annotation carried as a compared field. The Lean tree is not decoded into the Rust
AST, and neither side is projected through an untyped expression. The annotation is
the object under test here, so any representation without an annotation slot would
erase exactly what the target exists to compare, and a decoder would have to hardcode
the `Type` against `CedarType` correspondence that is under test. This is discussed
in the issue thread.

Declared normalisations, each with a test:

- Rust `Like` and `Is` are AST variants; Lean models both as `unaryApp`. The Rust side
  is folded to the Lean shape. A matching case agrees and a differing pattern is still
  caught.
- Record fields are compared as sorted key and value pairs, so ordering alone is never
  a divergence while a duplicated or missing key still is.
- `Slot` and `Unknown` have no Lean counterpart and are reported as unsupported rather
  than as a shape mismatch.
- A statically-true condition that Rust folds to `Lit(true)` and Lean keeps as a
  conjunction gets its own bucket. The folded side is a leaf, so the types the two
  sides assign to the whole condition are compared and reported instead. A folded pair
  whose types disagree stays a finding.

## Six phantom-divergence classes found while building this

Each of these made the harness report a difference that was an artifact of the two
encodings rather than anything about the validators. They are in their own commit.

1. `cedar-policy-core` enables serde_json's `preserve_order`, so object key order is
   insertion order. Lean emits entity types as `{"path": .., "id": ..}` and the natural
   Rust construction order is the reverse, so every entity-typed node mismatched.
2. Lean's derived `ToJson` does not emit constructor fields in declaration order
   (`and` comes back as `ty, b, a`), so positional child comparison mismatched on every
   binary node.
3. Round-tripping a policy set through `to_string` and `parse_policyset` is not
   id-preserving: the parser assigns fresh `policy0, policy1, ...` and every pair then
   failed to align.
4. `Display for PolicyID` escapes via `escape_debug` while Lean emits raw, so ids
   holding control characters never matched.
5. `Display for EntityUID` renders the eid through `Eid::escaped()`, giving the action
   component of the environment key the same problem.
6. Template-linked policies were skipped on the Rust side but still returned by Lean,
   leaving pairs that were never compared reported as unmatched environments.

The guard for the first was checked by removing the fix and confirming the test fails
with the predicted output, so it is not a test that passes for the wrong reason.

## What the target establishes, and what it does not

Controls are two-halved: each asserts that the clean pair produces zero divergences
and that the tampered pair produces exactly one classified divergence, in the same
run, so a control that catches its plant has also shown the correct case passing. 14
unit tests plus an end-to-end run against the real Lean backend.

**No claim is made that the two typecheckers agree.** The end-to-end test asserts only
that the harness ran and produced no harness problems. Asserting agreement would turn
a real disagreement into a broken test, and the point of the target is to report
disagreements rather than to encode an expected answer. Agreement is also bounded by
the shared Cedar specification: if the spec is wrong, both sides can agree and both be
wrong.

Over 40000 fuzz executions the target completes with zero harness problems, covering
71865 (policy, environment) pairs.

## One result worth a maintainer decision

`Validation.typecheckPolicy` substitutes the concrete action EUID before typechecking:

```lean
let expr := substituteAction env.reqty.action policy.toExpr
```

`typecheck_by_single_request_env` typechecks `t.condition()` directly and has no
equivalent, so it keeps `Var(Action)` where Lean has the literal. This is deliberate on
the Lean side. Both sides reach the same validation verdict, which is why a pass/fail
comparison never surfaced it. Whether the Rust typed expression should mirror the
substitution is your call, so the target reports it rather than normalising it away.

## Running it

```
cargo fuzz run typed-expression-drt
```

`CEDAR_TYPED_EXPR_SURVEY` counts and prints findings instead of asserting on them.
That downgrades the target to an observer and should stay unset in CI; it exists for
measuring how often a class appears before deciding what it is.

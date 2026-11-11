# Specimen-derived generators for Cedar

The schema, expression and policy generators that Specimen derives from the relational
specification of Cedar's typechecker (`Cedar/Validation/Relational`), against Basalt, and their
proofs.

- `Relational/SchemaGen*.lean`: the schema generator, from the generator-shaped `GenTypeEnvB` /
  `GenTypeEnvF`, and how they relate to the well-formed type environments.
- `Relational/ExprGen.lean`, `Relational/PolicyGen.lean`: the expression and policy generators,
  from `HasType` and the policy relations.
- `Relational/Sound`, `Relational/Depth`: theorems about the derived generators: what the schemas,
  requests and policies they produce are like (`Sound`), and a bound on the depth of the expressions
  (`Depth`).
- `Relational/Claims.lean`: the properties of the generated schemas and expressions, stated with
  the usual notation for probability. Start here.
- `../CedarGenProof`: the soundness and completeness of every derived expression generator,
  enumerator and checker. The large components' parts are proved in `ExprGen/Parts/Part0` to
  `Part23`, which Lake checks in parallel. Each file checks that the laws it proves depend only on
  `propext`, `Classical.choice` and `Quot.sound`, and fails otherwise.

Specimen (`strata-org/specimen`) is pinned in `../lakefile.lean`, and Basalt
(`hgoldstein95/basalt`) comes with it.

## Building

From `cedar-lean`:

```bash
lake exe cache get        # Mathlib's build, rather than compiling it
lake build Cedar
lake build CedarGen CedarGenProof
lake build $(find CedarGen/Relational/Sound CedarGen/Relational/Depth -name '*.lean' \
  | sed 's|\.lean$||; s|/|.|g')
lake build CedarGen.Relational.Claims
```

On a 32-core machine, from a fresh clone, these take about 100 s, 5 minutes and 1 minute. The
last lines of the `CedarGenProof` build report the laws checked (1284) and how many depend on a
nonstandard axiom (0).

Optionally, `./build_native_libs.sh` compiles Specimen's and Basalt's libraries (and their
dependencies'), which `lakefile.lean` then loads, so that the derivations and proofs run their
tactics compiled rather than interpreted: faster (about half the time for `ExprGen`), with the same
results. With them built, run the builds as `lake env lake -R build …`: `lake env` puts Lean's own
shared libraries on the library path, which the compiled ones need, and `-R` has `lakefile.lean`
look for them again.

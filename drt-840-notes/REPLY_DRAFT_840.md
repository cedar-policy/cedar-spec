# Draft reply to john-h-kastner-aws on cedar-spec #840 — NOT SENT

Thanks, that is the pattern I started from and I have adopted it where it carries
over: matching by policy id, the `assert_eq!` failure-reporting shape, and treating
"both sides errored" as agreement rather than as a finding. I diverged on the
expression comparison itself and would rather flag why than quietly do something
different. `Expr::try_from(Residual)` is total in the type dimension: every arm of
`convert_residual` binds `ty` with `..`, so a `CedarType` never reaches the
`pst::Expr`. For the TPE target that is the right call, since the question there is
whether both sides evaluated to the same residual and the typing was already agreed
upstream. For #840 the annotation is the whole object under test, so routing both
sides through `pst::Expr` would compare the erasure of the thing being compared.
Concretely: if Rust annotates the `1` in `context.amount < 1000` as `Long` and Lean
annotates it `Bool`, the two trees are structurally identical, both project to
`pst::Expr::Lit(Long(1))`, and the assertion passes. The same goes for Rust's
`Option<Type>` being `None` where Lean's `CedarType` is total, since `pst::Expr` has
no annotation slot at all and cannot express the difference. Decoding the Lean tree
into `Expr<Option<Type>>` instead would keep the types, because `educe` leaves `data`
in `PartialEq`, but it moves the problem rather than removing it: the decoder must
decide which Rust `Type` each Lean `CedarType` denotes, which is the correspondence
under test, and a disagreement then surfaces as a conversion `Err` behind
`.expect("...should succeed")`, filed as harness breakage rather than as a
divergence. So I render each side independently into a small neutral node type and
carry `ty` as a compared field. Happy to restructure if you would rather see it
another way.

---

## Notes for me, not for the comment

- Do not send until the PR exists; this reads better attached to code.
- The `Option<Type>` point is the strongest one and is not arguable: `pst::Expr`
  genuinely has no slot for an annotation.
- Do not claim either typechecker is wrong anywhere in this thread.
- Nothing here claims the two typecheckers agree or disagree in general.

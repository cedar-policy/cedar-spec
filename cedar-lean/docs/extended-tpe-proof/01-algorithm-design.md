# Extended TPE Algorithm: Design Analysis

## Overview

The Cedar Lean codebase implements an **extended Typed Partial Evaluation (TPE)** algorithm that goes beyond classical partial evaluation. This document analyzes the algorithm's design, its key components, and how it differs from a standard TPE.

## Architecture

The algorithm is organized into four layers:

```
┌─────────────────────────────────────────────────┐
│  TPE.Authorizer    (policy-level orchestration)  │
├─────────────────────────────────────────────────┤
│  TPE.BatchedEvaluator  (iterative entity loading)│
├─────────────────────────────────────────────────┤
│  TPE.Evaluator     (core partial evaluation)     │
├─────────────────────────────────────────────────┤
│  TPE.Residual / TPE.Input  (data representations)│
└─────────────────────────────────────────────────┘
```

## Core Data Representations

### Partial Inputs (`TPE.Input`)

The algorithm operates over *partial* versions of Cedar's request and entity store:

| Concrete Type | Partial Type | What Can Be Unknown |
|---|---|---|
| `Request` | `PartialRequest` | Principal ID, resource ID, context attributes |
| `EntityData` | `PartialEntityData` | Attrs, ancestors, tags (each independently `Option`) |
| `Value` | `PartialValue` | Individual record fields via `PartialAttribute` |
| `Entities` | `PartialEntities` | Per-entity data; missing entities are absent from the map |

The `PartialAttribute` type is the key abstraction:
```lean
inductive PartialAttribute (T : Type _) where
  | present (val : T)
  | unknown (ty : CedarType)
```

This allows *field-level* partiality within records and entity data — a single entity can have some attributes known and others unknown.

### Residuals (`TPE.Residual`)

The output of partial evaluation is a `Residual`, which is a mutually inductive type with `ResidualValue` and `ResidualAttribute`:

```
Residual  ≈  Expr + Value + Error + type annotations
```

Key design choices:
- **Every `Residual` node carries a `CedarType`** — this is what makes it "typed" partial evaluation. Types flow through the residual structure and are preserved by evaluation.
- **`ResidualValue` can contain `ResidualAttribute.unknown`** — a record value can have some fields resolved and others still pointing to a `Residual` expression that would compute them.
- **`Residual.error ty`** — a dedicated error node that collapses all error kinds into a single representation. This simplifies proofs at the cost of losing error specificity.

### The `ResidualAttribute.unknown` Target Pattern

When a `PartialValue.record` is converted to a `ResidualValue`, unknown fields store a *target* `Residual` expression:

```lean
| .unknown (expr : Residual) (ty : CedarType)
```

This target represents the expression that would need to be evaluated to resolve the unknown field. For entity attributes, the target is typically `.val (.prim (.entityUID uid)) (.entity uid.ty)` — pointing back to the entity. For nested records, the target chains: `.getAttr eveVal "address" outerRecTy`.

This design enables **incremental resolution**: when new entity data becomes available, `getAttr` on a record with unknown fields can delegate back to the entity-level expression.

## Core Evaluation (`TPE.evaluate`)

The evaluator (`TPE.Evaluator`) is a recursive function over `Residual` that attempts to reduce expressions given partial information:

```lean
def evaluate (x : Residual) (req : PartialRequest) (es : PartialEntities) : Residual
```

### Key Reduction Rules

1. **Values pass through**: `.val l ty` → `.val l ty`
2. **Variables resolve if known**: `.var .principal ty` → concrete value if `req.principal.id` is `some`
3. **Boolean short-circuiting**: `and`/`or` reduce when the first operand is a known boolean
4. **Error propagation**: Any sub-expression that is `.error` causes the parent to become `.error`
5. **Attribute access on known records**: `getAttr (.val (.record m) _) a _` looks up `a` in `m`
6. **Attribute access on known entities**: `getAttr (.val (.prim (.entityUID uid)) _) a _` looks up `uid` in `PartialEntities`
7. **Unknown attributes delegate**: When an attribute is `PartialAttribute.unknown`, `getAttr` returns a residual pointing to the target expression

### Smart Constructors

The evaluator uses smart constructors (`TPE.ite`, `TPE.and`, `TPE.or`, `TPE.apply₁`, `TPE.apply₂`, etc.) that perform reductions when possible:

- `TPE.and (.val true _) r _` → `r`
- `TPE.and (.val false _) _ _` → `false`
- `TPE.and l (.val false _) ty` → `false` only if `l.errorFree` (preserving error semantics)
- `TPE.and l r ty` → `.and l r ty` (residual)

The `errorFree` check is critical: it ensures that short-circuit optimizations don't swallow errors that would occur during full evaluation.

## Batched Evaluation (`TPE.BatchedEvaluator`)

The batched evaluator wraps the core evaluator in an iterative loop that incrementally loads entities:

```lean
def batchedEvalLoop (residual : Residual) (req : Request) (loader : EntityLoader)
    (store : PartialEntities) : Nat → Residual
```

### Algorithm

1. Start with an empty entity store and partially evaluate the expression
2. Scan the residual for literal `EntityUID`s not yet in the store (`allLiteralUIDs`)
3. Call the `EntityLoader` to fetch those entities
4. Merge new entities into the store (`newEntities ++ store`)
5. Re-evaluate the residual with the expanded store
6. If the result is a value, stop; otherwise repeat up to `n` iterations

### Entity Loader Contract

```lean
abbrev EntityLoader := Set EntityUID → Map EntityUID MaybeEntityData
```

Where `MaybeEntityData = Option EntityData` — `none` means the entity doesn't exist in the backing store.

The key insight: **a missing entity behaves identically to an entity with empty attrs/ancestors/tags** in Cedar's semantics. This is because Cedar has no way to test for entity existence directly.

## Authorization Layer (`TPE.Authorizer`)

The authorizer partially evaluates each policy and classifies the results:

```lean
structure Response where
  decision : Option Decision          -- None if undetermined
  satisfiedPermits / satisfiedForbids : Set PolicyID
  falsePermits / falseForbids : Set PolicyID
  errorPermits / errorForbids : Set PolicyID
  residualPermits / residualForbids : Set PolicyID
  residuals : List ResidualPolicy
```

### Decision Logic

The partial decision uses a conservative 4-way case analysis:

| Satisfied Forbid? | Satisfied Permit? | Residual Permit? | Residual Forbid? | Decision |
|---|---|---|---|---|
| Yes | * | * | * | `some deny` |
| * | No | No | * | `some deny` |
| No | * | * | Yes | `none` |
| No | No | Yes | No | `none` |
| No | Yes | * | No | `some allow` |

When the decision is `none`, re-authorization with concrete data is needed.

### Re-authorization

`Response.reauthorize` takes a partial response and fully evaluates all residuals against concrete request/entities, producing a standard `Spec.Response`. This is the bridge between partial and concrete authorization.

## Differences from Standard TPE

| Aspect | Standard TPE | Cedar Extended TPE |
|---|---|---|
| Partiality granularity | Whole values known/unknown | Field-level partiality in records |
| Entity handling | All-or-nothing | Per-attribute, per-ancestor, per-tag partiality |
| Iterative loading | Not applicable | Batched entity loading loop |
| Error representation | Propagate error types | Collapse to single `.error ty` node |
| Type annotations | Optional | Mandatory on every residual node |
| Unknown targets | Not applicable | `ResidualAttribute.unknown` stores target expression |
| Authorization | Single pass | Partial decision + re-authorization |
| Validation integration | Separate | `evaluatePolicy` type-checks before partial eval |

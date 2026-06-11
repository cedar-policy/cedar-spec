# Backward Compatibility for Entity Schema Extensions — Proof Plan

## Goal

Prove that adding new entity types to the entity schema never invalidates
existing policies:

```lean
theorem validate_preserved_of_ets_extension
    (schema₁ schema₂ : Schema)
    (policies : Policies)
    (hacts_eq : schema₁.acts = schema₂.acts)
    (hets_fwd : ∀ ety entry, schema₁.ets.find? ety = some entry →
                              schema₂.ets.find? ety = some entry)
    (hdisjoint : ∀ uid, schema₂.acts.contains uid = true →
                         schema₂.ets.isValidEntityUID uid = false)
    (hold : validate policies schema₁ = .ok ()) :
    validate policies schema₂ = .ok ()
```

## Architecture

The proof decomposes into three layers:

1. **Type invariant** (`typeOf_entity_type_in_ets`): entity types produced by
   `typeOf` are always in `env.ets` (or are action types)
2. **Expression-level congruence** (`typeOf_preserved_of_ets_extension`): `typeOf`
   gives the same result on both environments
3. **Policy-level** (`validate_preserved_of_ets_extension`): validate is preserved

Layer 3 depends on layer 2, which depends on layer 1. Layer 1 is the only
fundamentally new theorem — it's a type soundness property not currently in the
Cedar formalization.

## Layer 1: Type Invariant

### Statement

```lean
theorem typeOf_entity_type_in_ets (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities} {ety : EntityType}
    (hce : checkEntities ⟨env.ets, env.acts⟩ expr = .ok ())
    (hok : typeOf expr c env = .ok (tx, c'))
    (hty : tx.typeOf = .entity ety)
    (hdisjoint : ∀ uid, env.acts.contains uid = true →
                         env.ets.isValidEntityUID uid = false)
    (hreqty_principal : env.ets.contains env.reqty.principal)
    (hreqty_resource : env.ets.contains env.reqty.resource) :
    env.ets.contains ety
```

### Proof strategy

By structural induction on `expr`. For each case, show that the entity type in
the result is known to `env.ets`.

**Base cases:**

- `.lit (.entityUID uid)`: `typeOf` returns `.entity uid.ty`. From `checkEntities`,
  `ets.isValidEntityUID uid || acts.contains uid`. If validated by `ets`, then
  `ets.find? uid.ty = some _` so `ets.contains uid.ty`. If validated by `acts`,
  then by `hdisjoint`, `ets.isValidEntityUID uid = false`. But `typeOfLit` checks
  this condition and only returns `.entity uid.ty` if the uid is valid — in the
  acts case, we'd have `acts.contains uid.ty` as an action type. By examining
  `typeOfLit`: it returns `.entity uid.ty` unconditionally (just checks validity).
  In the `acts` case, `uid.ty` might NOT be in `ets`. But `hdisjoint` says action
  UIDs have types not in ets... Actually `ets.contains uid.ty` uses `ets.find?`,
  while `isValidEntityUID` also uses `ets.find?`. If `acts.contains uid` and
  `¬ ets.isValidEntityUID uid`, then `ets.find? uid.ty = none` so
  `¬ ets.contains uid.ty`. **This case produces an entity type NOT in ets.**

  **PROBLEM**: For action entity UIDs, `typeOf` produces `.entity uid.ty` where
  `uid.ty` is an action entity type NOT in `ets`. So the invariant as stated is
  FALSE.

### Revised statement

The invariant needs to be: entity types from `typeOf` are in `ets` OR are action
types:

```lean
theorem typeOf_entity_type_in_ets_or_actionType (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities} {ety : EntityType}
    (hce : checkEntities ⟨env.ets, env.acts⟩ expr = .ok ())
    (hok : typeOf expr c env = .ok (tx, c'))
    (hty : tx.typeOf = .entity ety)
    (hdisjoint : ∀ uid, env.acts.contains uid = true →
                         env.ets.isValidEntityUID uid = false)
    (hreqty_principal : env.ets.contains env.reqty.principal)
    (hreqty_resource : env.ets.contains env.reqty.resource) :
    env.ets.contains ety ∨ env.acts.actionType? ety
```

### Impact on Layer 2

In `typeOfHasAttr` with `.entity ety`:
```
match env.ets.attrs? ety with
| some rty => hasAttrInRecord ...
| none => if env.acts.actionType? ety then ok (.bool .ff) else err
```

If `ety` is in `env₁.ets`: by `ets_find_fwd`, same entry in `env₂.ets` → same
`attrs?` → same result.

If `ety` is an action type (not in ets): both `env₁.ets.attrs? ety = none` and
`env₂.ets.attrs? ety = none` (action types not in ets by disjointness of BOTH
schemas). Then both fall through to `acts.actionType?` which is the same (acts
equal). Same result.

If `env₂.ets.attrs? ety ≠ none` (new type has this ety): impossible because
`ety` is either in `env₁.ets` (then not new) or is an action type (then not in
any ets by disjointness).

**Wait** — disjointness says action UIDs have types not in ets. So action entity
types are not in ets. But a NEW entity type could coincidentally have the same
name as an action entity type! Then `env₂.ets.contains ety = true` AND
`env₂.acts.actionType? ety = true`. Is this possible with well-formed schemas?

By `hdisjoint`: `∀ uid, acts.contains uid → ¬ ets.isValidEntityUID uid`. This
means `ets.find? uid.ty = none` for action UIDs. So `ets.contains uid.ty = false`
for action entity types. In schema₂, if a new entity type matches an action
type: `schema₂.ets.contains ety = true` AND `schema₂.acts.actionType? ety = true`.
But disjointness on schema₂ would require `schema₂.ets.find? uid.ty = none` for
action UIDs. If `ety = uid.ty` for some action uid, then
`schema₂.ets.find? ety = none` — contradicting `schema₂.ets.contains ety = true`.

So disjointness on schema₂ prevents new entity types from having action entity
type names. **The case is impossible.** Good.

### Proof cases for the invariant

1. `.lit (.entityUID uid)`: returns `.entity uid.ty`.
   - If `ets.isValidEntityUID uid`: `ets.find? uid.ty ≠ none` → `ets.contains uid.ty`. Left disjunct.
   - If `acts.contains uid`: `acts.actionType? uid.ty = true` (uid has type uid.ty, and uid is in acts keys). Right disjunct.

2. `.var .principal`: returns `.entity env.reqty.principal`. By `hreqty_principal`. Left disjunct.

3. `.var .resource`: returns `.entity env.reqty.resource`. By `hreqty_resource`. Left disjunct.

4. `.var .action`: returns `.entity env.reqty.action.ty`. Since `env.reqty.action` is in `acts` (from environment construction), `acts.actionType? env.reqty.action.ty = true`. Right disjunct.

5. `.var .context`: returns `.record _`. Not `.entity`. Case doesn't apply.

6. `.unaryApp (.is ety) x₁`: returns `.bool _`. Not `.entity`. Case doesn't apply.

7. `.unaryApp _ x₁`: preserves type of subexpression OR returns non-entity. IH applies.

8. `.and`, `.or`: return `.bool _`. Case doesn't apply.

9. `.ite x₁ x₂ x₃`: returns `lub` of x₂ and x₃ types. If result is `.entity ety`, both x₂ and x₃ must produce compatible entity types. By IH on x₂ (or x₃), those types are in ets or action types. `lub` of two entity types... need to check.

10. `.binaryApp`: returns `.bool _` or `.entity _` depending on the op. Most ops return bool. `typeOfEq` returns bool. Check each op.

11. `.getAttr x₁ a`: returns the attribute type from the record/entity type of x₁. If x₁ has type `.entity ety`, looks up `ets.attrs? ety` or `acts.actionType?`. The returned type comes from the entity schema entry's attributes. If the attribute type is `.entity ety'`, then `ety'` appears in the schema entry for `ety` — which is in `env.ets`. Entity types referenced in entity schema entries should be in ets (by schema well-formedness).

    **This requires schema well-formedness!** Specifically: entity types referenced in attribute types are themselves in the entity schema.

12. `.hasAttr x₁ a`: returns `.bool _`. Case doesn't apply.

13. `.set xs`: returns `.set ty` where `ty` is the lub of element types. If elements produce `.entity ety`, IH applies.

14. `.record axs`: returns `.record _`. Case doesn't apply.

15. `.call xfn xs`: returns function-specific types. Need to check each extension function.

### Required preconditions

The invariant needs:
- `checkEntities` passing (for literal UIDs)
- `hdisjoint` (action types not in ets)
- `hreqty_principal`/`hreqty_resource` (reqty types in ets)
- **Schema well-formedness**: entity types referenced in attribute types are themselves declared in ets. This is needed for case 11 (`getAttr`).

The schema well-formedness property for attribute types is part of `EntitySchema.WellFormed` (each attribute's type references only valid entity types). This comes from `Schema.validateWellFormed`.

## Layer 2: Expression-Level Congruence

### Statement

```lean
theorem typeOf_preserved_of_ets_extension (expr : Expr) (c : Capabilities)
    {env₁ env₂ : TypeEnv}
    (hreqty : env₁.reqty = env₂.reqty)
    (hacts : env₁.acts = env₂.acts)
    (hets_fwd : ∀ ety entry, env₁.ets.find? ety = some entry →
                              env₂.ets.find? ety = some entry)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ expr = .ok ())
    (hdisjoint : ∀ uid, env₂.acts.contains uid = true →
                         env₂.ets.isValidEntityUID uid = false)
    (hreqty_principal : env₁.ets.contains env₁.reqty.principal)
    (hreqty_resource : env₁.ets.contains env₁.reqty.resource) :
    typeOf expr c env₁ = typeOf expr c env₂
```

### Proof strategy

By structural induction on `expr`, mirroring `typeOf_env_congr_weak`.

**Simple cases** (no ets query): `.var`, `.and`, `.or`, `.ite`, `.set`, `.record`,
`.call`, `.unaryApp` (non-`.is`) — same as `typeOf_env_congr_weak` but using
`hacts` for acts equality and `hreqty` for reqty equality.

**`.lit (.entityUID uid)`**: Both sides check `ets.isValidEntityUID uid || acts.contains uid`. Forward containment gives both true → same result.

**`.unaryApp (.is ety) x₁`**: `checkEntities` validates `ets.contains ety || acts.actionType? ety`. In both cases, the guard gives the same result (ets forward + acts equal). Then recurse on x₁.

**`.binaryApp op x₁ x₂`**: After IH, both sides have same subexpression results. `typeOfBinaryApp` uses:
- `actionUID? x env.acts` — same (acts equal + IH for checkEntities)
- `TypeEnv.descendentOf ety₁ ety₂` — uses `env.ets.find? ety` for ancestors.
  By layer 1, `ety` is in `env₁.ets` or is an action type. If in ets: same
  entry by `ets_find_fwd`. If action type: `ets.find? = none` on both (disjointness).
  Same result either way.
- `acts.descendentOf`, `acts.maybeDescendentOf` — same (acts equal).
- `typeOfHasTag`/`typeOfGetTag` — use `ets.tags?` which goes through `ets.find?`.
  Same argument as descendentOf.

**`.hasAttr x₁ a`**: After IH, same `tx₁`. `typeOfHasAttr` uses `env.ets.attrs? ety` where `ety = tx₁.typeOf` when it's `.entity`. By layer 1, `ety ∈ env₁.ets ∨ actionType`. If in ets: same `attrs?` by `ets_find_fwd`. If action type: `attrs? = none` on both → falls to `actionType?` → same (acts equal).

**`.getAttr x₁ a`**: Same argument as `.hasAttr`. `typeOfGetAttr` uses `env.ets.attrs?` at the same entity type.

### Estimated size

~150 lines, similar structure to `typeOf_env_congr_weak` (which is ~120 lines).

## Layer 3: Policy and Validate Level

### Strategy for `validate_preserved_of_ets_extension`

1. For each policy `p ∈ policies`, `typecheckPolicyWithEnvironments` passes on schema₁.
2. `checkEntities schema₁ p.toExpr = .ok ()`.
3. `checkEntities schema₂ p.toExpr = .ok ()` (by `checkEntities_monotone`: ets forward + acts same → entity validity forward-preserved).
4. `schema₂.environments` has the same reqtys as `schema₁.environments` (same acts → same flatMap → same reqty list, different ets).
5. For each `env₂ ∈ schema₂.environments`, there's `env₁ ∈ schema₁.environments` with same reqty.
6. `typecheckPolicy policy env₁ = typecheckPolicy policy env₂` (by layer 2, via `typecheckPolicy_preserved_of_ets_extension`).
7. So `mapM (typecheckPolicy p) schema₂.environments` gives the same result list as schema₁.
8. `allFalse` check gives the same answer → `typecheckPolicyWithEnvironments` gives same result.

### Preconditions needed for reqty types in ets

From `Schema.validateWellFormed schema₁ = .ok ()`, derive:
- `env₁.ets.contains env₁.reqty.principal` (from `ActionSchemaEntry.WellFormed` → appliesTo types are in ets)
- `env₁.ets.contains env₁.reqty.resource` (same)

This uses `RequestType.WellFormed` from `Cedar/Thm/Validation/Typechecker/WF.lean` which requires appliesTo types to be valid entity types.

## Implementation Status

The proof structure is fully implemented in `ValidationBackwardCompat.lean` (~550 lines).
Three sorry's remain:

1. **`typeOf_entity_type_in_ets`** (type invariant) — sorry
   - Structural induction on expr
   - Base cases: lit entityUID (from checkEntities), var principal/resource (from precondition), var action (from acts membership)
   - Recursive cases: ite (from lub? preservation), getAttr (from schema WF), binaryApp/getTag (from schema WF for tag types)
   - `getAttr` case needs schema WF for attribute types (have `EntitySchema.WellFormed` precondition)

2. **`typeOf_preserved_of_ets_extension` — binaryApp case** — sorry
   - After IH on subexpressions, need `TypeEnv.descendentOf`, `typeOfHasTag`, `typeOfGetTag` to agree
   - These query `env.ets.find?` / `env.ets.tags?` at entity types from subexpression results
   - Agreement follows from type invariant + `descendentOf_agree` / `ets_tags_agree` (already proved)
   - Just needs wiring up with cases on op/type patterns

3. **`validate_preserved_of_ets_extension`** — sorry
   - Iterate over policies via `List.all_ok_implies_forM_ok`
   - For each policy: derive `checkEntities` monotonicity, environments correspondence, apply `typecheckPolicy_preserved_of_ets_extension`
   - Needs `Schema.validateWellFormed` → per-env well-formedness derivation
   - Structurally straightforward but requires connecting WF preconditions

### Fully proved:
- All helper lemmas (actionType_implies_contains, ets_attrs_agree, ets_tags_agree, descendentOf_agree, etc.)
- `typeOf_preserved_of_ets_extension` for all cases EXCEPT binaryApp
- `typecheckPolicy_preserved_of_ets_extension` (uses typeOf_preserved)
- hasAttr/getAttr cases (modulo type invariant being sorry)

## Open questions

1. **Schema well-formedness for `getAttr`**: Does `env.ets.attrs? ety = some rty` guarantee that entity types in `rty` are also in `env.ets`? This is needed for the `getAttr` case of the type invariant. If not, the invariant needs to be weakened or an additional precondition added.

2. **Extension functions**: Do any extension functions (`ip`, `decimal`, etc.) produce entity types? If not, the `.call` case is trivial.

3. **`lub` for entity types**: What does `lub (.entity ety₁) (.entity ety₂)` produce? If it can produce a new entity type not from either input, the `.ite` case needs more care.

## Dependencies

- `Cedar.Thm.Validation.ValidationPolicySlice.CheckEntities` (for `checkEntities_monotone`, `checkEntities_substituteAction`)
- `Cedar.Thm.Validation.ValidationPolicySlice.TypeOfCongr` (for `WeakTypeEnvAgreement` structure reference)
- `Cedar.Thm.Validation.EnvironmentValidation` (for deriving reqty types from schema WF)
- `Cedar.Thm.Data` (standard list/map lemmas)

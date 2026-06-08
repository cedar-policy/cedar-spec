# Validation Policy Slicing: Algorithm and Proof Sketch

## Algorithm Description

### Problem Statement

Given:
- An old schema `schema₁` and a new schema `schema₂`
- A set of policies that validated successfully under `schema₁`

Determine which policies need to be revalidated against `schema₂`, such that if
only those policies are revalidated (and pass), then ALL policies validate under
`schema₂`.

### Preconditions for Incremental Revalidation

A full revalidation of all policies is required unless:
1. The entity schema is unchanged (`schema₁.ets = schema₂.ets`)
2. The same set of action UIDs exists in both schemas
3. The action hierarchy (ancestors) is identical for all actions
4. The `actionType?` query gives the same results (same entity types for actions)

When these hold, only the context type and appliesTo lists of individual actions
may differ.

### The Slicing Algorithm

```
function validationSlice(acts, changes, policies):
  return policies.filter(p => actionScopeMatchesAnyChangedAction(acts, changes, p.actionScope))

function computeActionChanges(oldSchema, newSchema):
  for each action in newSchema.acts:
    if action not in oldSchema.acts:
      emit contextChanged(action)
    else:
      oldEntry = oldSchema.acts[action]
      newEntry = newSchema.acts[action]
      if oldEntry.context ≠ newEntry.context:
        emit contextChanged(action)
      else if newEntry.appliesToPrincipal ⊄ oldEntry.appliesToPrincipal
           or newEntry.appliesToResource ⊄ oldEntry.appliesToResource:
        emit appliesToExtended(action)
      // If appliesTo only shrunk: no change needed (monotonicity)

function actionScopeMatchesAction(acts, changedAction, scope):
  match scope:
    .any           => true   // unconstrained scopes always match
    .eq uid        => uid == changedAction || acts.descendentOf(changedAction, uid)
    .mem uid       => acts.descendentOf(changedAction, uid)
    .is ety        => changedAction.ty == ety
    .isMem ety uid => changedAction.ty == ety && acts.descendentOf(changedAction, uid)
    .actionInAny ls => ls.any(l => acts.descendentOf(changedAction, l))
```

### Key Insight

The Cedar validator checks each policy against ALL environments derived from the
schema. An environment is a (principal_type, action_uid, resource_type, context_type)
tuple. The validator:

1. Calls `checkEntities` to verify all entity literals in the policy are valid
2. For each environment, substitutes the action UID into the policy expression
   and typechecks the result
3. Rejects the policy if ALL environments produce type `bool.ff` (impossible policy)

After `substituteAction`, if the environment's action doesn't match the policy's
action scope, the action scope expression typechecks to `bool.ff`. Since the
policy expression is `and(principalScope, and(actionScope, and(resourceScope,
conditions)))`, a `ff` in the action scope propagates through the `and` chain,
making the entire policy typecheck to `ff` for that environment.

Therefore, the validation result for a policy depends ONLY on environments whose
action matches the policy's scope. If those actions haven't changed between
schemas, the validation result is preserved.

---

## Proof Sketch

### Theorem: `validation_slice_is_sufficient`

**Statement:** If `validate(policies, schema₁) = ok` and
`validate(slice, schema₂) = ok` (where `slice = validationSlice(changes, policies)`),
then `validate(policies, schema₂) = ok`.

**Proof:** `validate` is `policies.forM(typecheckPolicyWithEnvironments ...)`.
For each policy `p`:
- If `p ∈ slice`: it passed validation under `schema₂` (from `hslice`). ✓
- If `p ∉ slice`: its action scope doesn't match any changed action. By
  `single_policy_single_change_preserved`, it still validates under `schema₂`. ✓

**Status: PROVEN** (with `hpreserved` as parameter for the per-policy fact)

---

### Theorem: `single_policy_single_change_preserved`

**Statement:** If a policy validated under `schema₁` and its action scope doesn't
match the changed action, then it validates under `schema₂`.

**Proof outline:**

`typecheckPolicyWithEnvironments` does three things:
1. `checkEntities schema₂ policy.toExpr = ok`
2. `schema₂.environments.mapM (typecheckPolicy policy) = ok txs`
3. `¬ allFalse txs`

For (1): `checkEntities` only uses `schema.ets` and `schema.acts.contains/actionType?`.
Since `IncrementallyRevalidatable` guarantees these agree, the result is preserved.

For (2): For each env in `schema₂.environments`:
- If `env.reqty.action = changedAction`: By `typecheckPolicy_nonmatching_action_produces_ff`,
  the policy typechecks to `ok tx` with `tx.typeOf = .bool .ff`. (It succeeds, just gives ff.)
- If `env.reqty.action ≠ changedAction`: The action's entry is identical in both schemas
  (`other_actions_unchanged`). The environment has the same `reqty`. The typechecker uses
  `env.acts` only for `descendentOf`, `contains`, and `actionType?`, which all agree by
  `IncrementallyRevalidatable`. So `typecheckPolicy` produces the same result as on `schema₁`.

For (3): Since validation passed on `schema₁`, not all environments gave `ff` there. The
non-ff results came from environments for unchanged actions. Those same environments exist
in `schema₂` (same entry → same requestTypes) and produce the same result. So not all are
ff in `schema₂` either.

**Status: SORRY'd** — The missing piece is a "typeOf congruence" lemma showing that
`typecheckPolicy` gives the same result when `env.acts` differs but agrees on all
queries the typechecker makes (descendentOf, contains, actionType?).

---

### Theorem: `typecheckPolicy_nonmatching_action_produces_ff`

**Statement:** If a policy's action scope doesn't match the environment's action,
and checkEntities passed, and the principal scope typechecks to a bool, then
`typecheckPolicy` returns `ok tx` with `tx.typeOf = .bool .ff`.

**Proof:**

1. `substituteAction` distributes over `and`:
   `sub(policy.toExpr) = and(sub(P), and(sub(A), and(sub(R), sub(C))))`

2. `typeOf(sub(A), caps, env)` gives `(tx_a, c_a)` with `tx_a.typeOf = .bool .ff`
   (by `action_scope_typechecks_to_ff`)

3. The inner `and(sub(A), rest)`: since left side types to `ff`, `typeOfAnd`
   short-circuits and returns `ff` without evaluating `rest`.

4. The outer `and(sub(P), inner)`: `sub(P)` types to some bool (by `hprincipal`).
   Since the right side (inner) gives `ff`, `typeOfAnd` returns `ff` via the
   `| .bool .ff => ok (.bool .ff)` branch.

5. `typecheckPolicy` sees `typeOf = .ok (tx, _)` with `tx.typeOf = .bool .ff ⊑ .bool .anyBool`,
   so returns `.ok tx`.

**Status: PROVEN** (with `hprincipal` as hypothesis that principal scope types to a bool)

---

### Theorem: `action_scope_typechecks_to_ff`

**Statement:** If `actionScopeMatchesAction(acts, action, scope) = false` and
`acts.contains(action)` and `checkEntities` passed, then
`typeOf(substituteAction(action, scope.toExpr), caps, env)` gives `(tx, c)` with
`tx.typeOf = .bool .ff`.

**Proof:** Case split on the action scope variant. After `substituteAction`,
the scope expression becomes:

| Scope | Substituted expression | Why it types to ff |
|-------|----------------------|-------------------|
| `.any` | `true` | Contradiction (always matches) |
| `.eq uid` | `(.lit action) == (.lit uid)` | `typeOfEq` with two different literal UIDs → ff |
| `.mem uid` | `(.lit action) in (.lit uid)` | `typeOfInₑ` with non-descendant → ff |
| `.is ety` | `(.lit action) is ety` | `typeOfUnaryApp(.is)` with wrong type → ff |
| `.isMem ety uid` | `(is ety) && (in uid)` | Either `is` gives ff (short-circuit) or `in` gives ff |
| `.actionInAny ls` | `(.lit action) in (.set ls)` | `typeOfInₛ` with no descendant match → ff |

Each case requires showing:
- The entity UID literals are valid (from `checkEntities`)
- The specific typechecker function produces `.ff` given the non-match condition

**Status:** 5/6 cases PROVEN in dispatch. The `actionInAny` dispatch case is sorry'd
because it needs `hset_ok` and `hset_ty` which require knowing the set expression
typechecks — this is only guaranteed when the policy previously validated, but the
current theorem statement doesn't carry that information.

---

### Theorem: `checkEntities_preserved`

**Statement:** If `checkEntities(schema₁, expr) = ok` and schemas are
`IncrementallyRevalidatable`, then `checkEntities(schema₂, expr) = ok`.

**Proof:** `checkEntities` only uses the schema for:
- `schema.ets.isValidEntityUID uid || schema.acts.contains uid` (for entity UID literals)
- `schema.ets.contains ety || schema.acts.actionType? ety` (for `is` type checks)

Both agree between schemas (by `ets_eq`, `same_actions`, `same_action_types`). So
`checkEntities schema₁ expr = checkEntities schema₂ expr` for all expressions.

**Status: PROVEN** (via `checkEntities_eq` which handles all Expr constructors
including set/record/call via well-founded recursion)

---

### Per-case lemmas for action scope typing

| Lemma | Status |
|-------|--------|
| `action_scope_eq_typechecks_to_ff` | PROVEN |
| `action_scope_mem_typechecks_to_ff` | PROVEN |
| `action_scope_is_typechecks_to_ff` | PROVEN |
| `action_scope_isMem_typechecks_to_ff` | PROVEN |
| `action_scope_actionInAny_typechecks_to_ff` | PROVEN |
| `typeOfInₛ_not_in_list` | PROVEN |
| `entityUIDs_map_lit` | PROVEN |
| `actionUID_lit` | PROVEN |
| `entityUIDs_set_map_lit` | PROVEN |

---

### Helper lemmas for `and` propagation

| Lemma | Status |
|-------|--------|
| `typeOfAnd_ff_left` | PROVEN |
| `and_right_ff` | PROVEN |

---

### Helper lemmas for checkEntities

| Lemma | Status |
|-------|--------|
| `checkEntities_and` | PROVEN |
| `checkEntities_binaryApp` | PROVEN |
| `checkEntities_policy_implies_actionScope` | PROVEN |
| `checkEntities_eq` (all Expr constructors) | PROVEN |

---

## Summary of Remaining Work

### Sorry 1: `action_scope_typechecks_to_ff` dispatch for `actionInAny`

The standalone lemma `action_scope_actionInAny_typechecks_to_ff` IS proven, but
requires two extra hypotheses:
- `hset_ok`: the set expression typechecks
- `hset_ty`: the set's type is `.set (.entity ety)` for some `ety`

In the dispatch, we only have `checkEntities` which guarantees entity literals are
valid but doesn't guarantee the set typechecks (set typing requires all elements to
have a compatible lub type). To discharge this, we either need:
- A precondition that the policy previously validated (then the set DID typecheck), OR
- A proof that `checkEntities` + action literals all being valid implies the set types
  correctly (which requires all UIDs to have the same entity type)

**Fix:** Add `hpreviously_validated` as a precondition to `action_scope_typechecks_to_ff`,
or restructure to carry the set typing fact through from the validation of schema₁.

### Sorry 2: `single_policy_single_change_preserved`

This is the main composition theorem. The proof requires:
1. Showing `checkEntities` preserved (DONE)
2. For changed-action environments: `typecheckPolicy_nonmatching_action_produces_ff` (DONE)
3. For unchanged-action environments: a "typeOf congruence" lemma showing that
   `typecheckPolicy` gives the same result when only `env.acts` changes but all
   queries on it agree.
4. The `allFalse` check still passes (non-ff results preserved from unchanged actions)

The main missing piece is (3): proving that the typechecker is parametric in the
action schema as long as `descendentOf`, `contains`, and `actionType?` agree. This
would require structural recursion on `typeOf` (similar to `checkEntities_eq` but
for the full typechecker).

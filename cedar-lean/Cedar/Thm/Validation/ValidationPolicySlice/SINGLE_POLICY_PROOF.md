# Detailed Paper Proof: `single_policy_single_change_preserved`

## Statement

Given:
- `schema₁, schema₂ : Schema` with `hchange : SingleActionChange schema₁ schema₂ changedAction`
- `policy : Policy` with `hnotmatch : actionScopeMatchesAction schema₁.acts changedAction policy.actionScope = false`
- `hvalid : typecheckPolicyWithEnvironments typecheckPolicy policy schema₁ = .ok ()`

Prove: `typecheckPolicyWithEnvironments typecheckPolicy policy schema₂ = .ok ()`

## Definitions Involved

```
typecheckPolicyWithEnvironments tc policy schema := do
  (checkEntities schema policy.toExpr).mapError (.typeError policy.id)  -- (A)
  let policyTypes ← schema.environments.mapM (tc policy)               -- (B)
  if allFalse policyTypes then .error (.impossiblePolicy policy.id)     -- (C)
  else .ok ()

Schema.environments schema :=
  schema.acts.toList.flatMap (fun (action, entry) => entry.requestTypes action)
  |>.map (fun reqty => { ets := schema.ets, acts := schema.acts, reqty })
```

## Proof Structure

We must show that all three steps (A), (B), (C) succeed for `schema₂`.

---

### Part A: `checkEntities schema₂ policy.toExpr = .ok ()`

**From `hvalid`:** Since `typecheckPolicyWithEnvironments` succeeded on schema₁,
its first step succeeded: `checkEntities schema₁ policy.toExpr = .ok ()`.

**By `checkEntities_preserved`:** Since `IncrementallyRevalidatable schema₁ schema₂`
(from `hchange.incr`), we have `checkEntities schema₂ policy.toExpr = .ok ()`. ∎

This is **already proven** as `checkEntities_preserved`.

---

### Part B: `schema₂.environments.mapM (typecheckPolicy policy) = .ok policyTypes₂`

We need: for every `env₂ ∈ schema₂.environments`, `typecheckPolicy policy env₂` succeeds.

**Structure of `schema₂.environments`:**
Each environment has `env₂ = { ets := schema₂.ets, acts := schema₂.acts, reqty := rt }`
where `rt` comes from some action `a` in `schema₂.acts` via `entry.requestTypes a`.

**Case split on `env₂.reqty.action`:**

#### Case B1: `env₂.reqty.action = changedAction`

Since the policy's action scope doesn't match `changedAction` (by `hnotmatch`),
and `schema₁.acts` and `schema₂.acts` agree on `descendentOf` (by `hchange.incr.same_ancestors`),
and `actionScopeMatchesAction` only uses `descendentOf` and `contains`:

`actionScopeMatchesAction schema₂.acts changedAction policy.actionScope = false`

(This requires a **helper lemma**: `actionScopeMatchesAction` gives the same result
when `acts` agrees on `contains` and `descendentOf`. Since `IncrementallyRevalidatable`
gives us `same_actions` and `same_ancestors`, and `descendentOf` only uses `find?` and
`ancestors`, and `contains` is preserved, the result is the same.)

Then by `typecheckPolicy_nonmatching_action_produces_ff`:
- `hnotmatch'`: `actionScopeMatchesAction env₂.acts env₂.reqty.action policy.actionScope = false`
  (since `env₂.acts = schema₂.acts` and `env₂.reqty.action = changedAction`)
- `hcontains`: `env₂.acts.contains env₂.reqty.action = true`
  (since `hchange.action_exists₂`)
- `hentities`: `checkEntities ⟨env₂.ets, env₂.acts⟩ policy.toExpr = .ok ()`
  (same as Part A since `env₂.ets = schema₂.ets` and `env₂.acts = schema₂.acts`)
- `hprincipal`: the principal scope typechecks to a bool (see Lemma P below)
- `hscope_types`: for actionInAny, the set typechecks (see Lemma S below)

Result: `typecheckPolicy policy env₂ = .ok tx₂` with `tx₂.typeOf = .bool .ff`. ✓

#### Case B2: `env₂.reqty.action ≠ changedAction`

Let `a = env₂.reqty.action`. Since `a ≠ changedAction`, by `hchange.other_actions_unchanged`:
`schema₁.acts.find? a = schema₂.acts.find? a`

So the action entry for `a` is the same in both schemas. This means `requestTypes a`
generates the same list of `RequestType`s. In particular, `env₂.reqty` also appears
as a `reqty` in some environment in `schema₁.environments`.

Construct `env₁ := { ets := schema₁.ets, acts := schema₁.acts, reqty := env₂.reqty }`.
Then `env₁ ∈ schema₁.environments` (because `a`'s entry is the same, so the same
requestTypes are generated).

**Claim:** `TypeEnvAgreement env₁ env₂`.

Proof of claim:
- `env₁.ets = schema₁.ets = schema₂.ets = env₂.ets` (by `hchange.incr.ets_eq`)
- `env₁.reqty = env₂.reqty` (by construction)
- `env₁.acts.contains = schema₁.acts.contains = schema₂.acts.contains = env₂.acts.contains`
  (by `hchange.incr.same_actions`)
- `env₁.acts.actionType? = schema₂.acts.actionType?` (by `hchange.incr.same_action_types`)
- `env₁.acts.descendentOf`: For any uid₁ uid₂, `schema₁.acts.descendentOf uid₁ uid₂ = schema₂.acts.descendentOf uid₁ uid₂`
  (proved by: `descendentOf` checks if `uid₁ == uid₂` or looks up `uid₁`'s entry and checks ancestors.
  Since `same_actions` gives same `contains`, and for any action that exists, `same_ancestors` gives same ancestors,
  the result is the same.)
- `env₁.acts.maybeDescendentOf`: iterates over `toList` checking `act.ty` and `entry.ancestors`.
  Since same actions exist with same ancestors, this agrees. ∎

**By `typecheckPolicy_env_congr`:** `typecheckPolicy policy env₁ = typecheckPolicy policy env₂`.

**From `hvalid`:** `schema₁.environments.mapM (typecheckPolicy policy) = .ok policyTypes₁`,
which means `typecheckPolicy policy env₁ = .ok tx₁` for some `tx₁`.

Therefore `typecheckPolicy policy env₂ = .ok tx₁`. ✓

---

### Part C: `¬ allFalse policyTypes₂`

We need: not all elements of `policyTypes₂` have `typeOf = .bool .ff`.

**From `hvalid`:** `¬ allFalse policyTypes₁`. So there exists some `env₁ ∈ schema₁.environments`
where `typecheckPolicy policy env₁ = .ok tx₁` with `tx₁.typeOf ≠ .bool .ff`.

**Claim:** `env₁.reqty.action ≠ changedAction`.

Proof: If `env₁.reqty.action = changedAction`, then by the same argument as Case B1
(but for schema₁), `typecheckPolicy policy env₁` would produce `tx₁.typeOf = .bool .ff`.
Contradiction with `tx₁.typeOf ≠ .bool .ff`. ∎

So `env₁.reqty.action ≠ changedAction`, meaning the action entry is unchanged.
The same `reqty` exists in `schema₂.environments` (same action entry → same requestTypes).
Let `env₂` be the corresponding environment in schema₂. By Case B2 above,
`typecheckPolicy policy env₂ = typecheckPolicy policy env₁ = .ok tx₁`.

So `tx₁ ∈ policyTypes₂` with `tx₁.typeOf ≠ .bool .ff`. Therefore `¬ allFalse policyTypes₂`. ✓

---

## Required Helper Lemmas

### Lemma D: `descendentOf` agreement

```
theorem acts_descendentOf_agree (hincr : IncrementallyRevalidatable schema₁ schema₂) :
    ∀ uid₁ uid₂, schema₁.acts.descendentOf uid₁ uid₂ = schema₂.acts.descendentOf uid₁ uid₂
```

**Proof:** `ActionSchema.descendentOf uid₁ uid₂` is:
- If `uid₁ == uid₂`: `true` (both sides agree)
- Else: look up `find? uid₁`, check if `uid₂ ∈ entry.ancestors`

For the lookup: if `find?` gives `none` on one schema, then `contains uid₁ = false`.
By `same_actions`, contains agrees, so `find?` gives `none` on the other too. Both return `false`.

If `find?` gives `some entry₁` on schema₁ and `some entry₂` on schema₂ (both exist by `same_actions`),
then `entry₁.ancestors = entry₂.ancestors` by `same_ancestors`. So the check gives the same result. ∎

**Status:** This is essentially `incrementally_revalidatable_descendentOf` which was proven
earlier but removed. It follows directly from the `IncrementallyRevalidatable` fields.

### Lemma M: `maybeDescendentOf` agreement

```
theorem acts_maybeDescendentOf_agree (hincr : IncrementallyRevalidatable schema₁ schema₂) :
    ∀ ety₁ ety₂, schema₁.acts.maybeDescendentOf ety₁ ety₂ = schema₂.acts.maybeDescendentOf ety₁ ety₂
```

**Proof:** `maybeDescendentOf` iterates `acts.toList.any (fun (act, entry) => act.ty = ety₁ && entry.ancestors.any ...)`.

This requires showing that `schema₁.acts.toList` and `schema₂.acts.toList` have the same
elements (same UIDs with same ancestors). This follows from:
- Same UIDs: `same_actions` implies the same keys are present
- Same ancestors: `same_ancestors` gives the same ancestors for each key

Formally: For any `(uid, entry₁) ∈ schema₁.acts.toList`, there exists `entry₂` with
`(uid, entry₂) ∈ schema₂.acts.toList` and `entry₁.ancestors = entry₂.ancestors`.
So the `any` predicate `(uid.ty = ety₁ && entry.ancestors.any ...)` evaluates the same. ∎

**Difficulty:** This requires a lemma relating `Map.toList` membership to `Map.find?`,
which should exist in the Cedar data library.

### Lemma P: Principal scope typechecks to a bool

```
theorem principal_scope_typechecks_to_bool {policy : Policy} {env : TypeEnv}
    (hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ()) :
    ∃ tx c, typeOf (substituteAction env.reqty.action policy.principalScope.toExpr) ∅ env = .ok (tx, c) ∧
            ∃ bty, tx.typeOf = .bool bty
```

**Proof:** The principal scope expression is one of:
- `.lit (.bool true)` for `.any` → types to `(.bool .tt)` ✓
- `.binaryApp .eq (.var .principal) (.lit (.entityUID uid))` → `.var .principal` types to
  `.entity env.reqty.principal`, the literal types (since `checkEntities` passed), and
  `typeOfEq` with entity types gives `.bool something` ✓
- `.binaryApp .mem (.var .principal) (.lit (.entityUID uid))` → same pattern ✓
- `.unaryApp (.is ety) (.var .principal)` → types to `.bool .tt` or `.bool .ff` ✓
- `.and (is) (mem)` → both sub-parts type to bools, and types to bool ✓

Each case is straightforward. `substituteAction` doesn't affect the principal scope
(no `.var .action` in it), so it's just `typeOf principalScope.toExpr ∅ env`.

**Difficulty:** Medium. Requires case split on `PrincipalScope`/`Scope` and showing each
variant typechecks to a bool. Similar in structure to `action_scope_typechecks_to_ff`.

### Lemma S: actionInAny set typechecks (for previously validated policy)

```
theorem actionInAny_set_typechecks {ls : List EntityUID} {env : TypeEnv} {caps : Capabilities}
    (policy_validated : typecheckPolicy policy env' = .ok tx for some env' with same ets/acts) :
    ∃ tx_set c_set ety, typeOf (.set (ls.map ...)) caps env = .ok (tx_set, c_set) ∧
                         tx_set.typeOf = .set (.entity ety)
```

**Proof sketch:** If the policy validated on schema₁ (for ANY environment), the `typeOf`
call inside `typecheckPolicy` succeeded on the full policy expression. This means the
action scope sub-expression typechecked. For `actionInAny`, this means the set of entity
UID literals typechecked to some `.set (.entity ety)`. Since set typing only depends on
the UIDs (not the schema — entity literals type to `.entity uid.ty` which is schema-independent
once `checkEntities` passes), the same set typechecks the same way in any env with the same
validity checks.

**Difficulty:** Hard. Requires connecting "policy validated" to "sub-expression typechecked"
which means unwinding the `typeOf` recursion on the policy expression structure.

### Lemma E: Environments for unchanged actions exist in both schemas

```
theorem unchanged_action_env_in_both {a : EntityUID} {schema₁ schema₂ : Schema}
    (hchange : SingleActionChange schema₁ schema₂ changedAction)
    (hne : a ≠ changedAction) :
    -- For any reqty generated by action a in schema₁, the same reqty is generated in schema₂
    ∀ rt ∈ (schema₁.acts.find? a).get!.requestTypes a,
      ∃ env₂ ∈ schema₂.environments, env₂.reqty = rt
```

**Proof:** Since `schema₁.acts.find? a = schema₂.acts.find? a` (by `other_actions_unchanged`),
the action entry is identical. So `entry.requestTypes a` generates the same list of
`RequestType`s. Each is then wrapped with `{ ets := schema₂.ets, acts := schema₂.acts, reqty := rt }`,
producing an environment in `schema₂.environments`. ∎

**Difficulty:** Medium. Requires relating `flatMap` and `map` to membership in the
resulting list. Should be provable with list membership lemmas.

---

## Proof Execution Plan

The proof decomposes into proving these lemmas (D, M, P, S, E) and then combining them
in the structure of Parts A, B, C above. The most impactful approach:

1. **Lemma D** (descendentOf): Small, directly from IncrementallyRevalidatable fields.
2. **Lemma M** (maybeDescendentOf): Medium, requires toList/find? relationship.
3. **Construct TypeEnvAgreement** from SingleActionChange + Lemmas D, M.
4. **Part A**: Direct from `checkEntities_preserved` (already proven).
5. **Part B, Case B2**: Direct from `typecheckPolicy_env_congr` + TypeEnvAgreement.
6. **Part B, Case B1**: From `typecheckPolicy_nonmatching_action_produces_ff` + Lemmas P, S.
7. **Part C**: Existential argument using Case B2 and the fact that schema₁ had a non-ff env.
8. **Compose** Parts A, B, C to close the theorem.

Steps 1-5 are feasible. Steps 6-7 are where the remaining difficulty lies (Lemmas P, S
and the existential reasoning about environments).

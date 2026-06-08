# typeOf Congruence: Detailed Proof Sketch

## Goal

We want to show that `typecheckPolicy policy env₁ = typecheckPolicy policy env₂` when
`env₁` and `env₂` agree on everything the typechecker queries.

## What typecheckPolicy does

```
typecheckPolicy policy env :=
  let expr := substituteAction env.reqty.action policy.toExpr
  match typeOf expr ∅ env with
  | .ok (tx, _) => if tx.typeOf ⊑ .bool .anyBool then .ok tx else .error ...
  | .error e => .error ...
```

Since `env₁.reqty = env₂.reqty` (same action entry → same reqty), the substituted
expression is the same. So we need: `typeOf expr ∅ env₁ = typeOf expr ∅ env₂`.

## What typeOf uses from env

Looking at every place `env` is accessed in the typechecker:

1. **`typeOfLit (.entityUID uid)`**: uses `env.ets.isValidEntityUID uid || env.acts.contains uid`
2. **`typeOfVar .principal`**: uses `env.reqty.principal`
3. **`typeOfVar .action`**: uses `env.reqty.action.ty`
4. **`typeOfVar .resource`**: uses `env.reqty.resource`
5. **`typeOfVar .context`**: uses `env.reqty.context`
6. **`typeOfUnaryApp (.is ety)`**: no env access (just compares types)
7. **`typeOfEq`**: no env access (compares literal values or types)
8. **`typeOfInₑ ety₁ ety₂ x₁ x₂ env`**: uses `env.acts` (actionUID?, descendentOf) and `env.descendentOf` (uses `env.ets` and `env.acts`)
9. **`typeOfInₛ ety₁ ety₂ x₁ x₂ env`**: uses `env.acts` (actionUID?, descendentOf)
10. **`typeOfHasAttr ty x a c env`**: uses `env.ets.attrs?` and `env.acts.actionType?`
11. **`typeOfGetAttr ty x a c env`**: uses `env.ets.attrs?`
12. **`typeOfHasTag ety x t c env`**: uses `env.ets.tags?` and `env.acts.actionType?`
13. **`typeOfGetTag ety x t c env`**: uses `env.ets.tags?`
14. **`TypeEnv.descendentOf env ety₁ ety₂`**: uses `env.ets.find?` and `env.acts.maybeDescendentOf`

## What we need env₁ and env₂ to agree on

Given `IncrementallyRevalidatable schema₁ schema₂` and `env₁.ets = env₂.ets` (from
`schema₁.ets = schema₂.ets`), and `env₁.reqty = env₂.reqty` (same action entry):

| Query | Why it agrees |
|-------|---------------|
| `env.ets.isValidEntityUID uid` | `env₁.ets = env₂.ets` |
| `env.acts.contains uid` | `same_actions` |
| `env.reqty.*` | `env₁.reqty = env₂.reqty` |
| `env.acts.descendentOf uid₁ uid₂` | same ancestors + same contains |
| `env.descendentOf ety₁ ety₂` | same ets + same acts.maybeDescendentOf |
| `env.ets.attrs? ety` | `env₁.ets = env₂.ets` |
| `env.ets.tags? ety` | `env₁.ets = env₂.ets` |
| `env.acts.actionType? ety` | `same_action_types` |
| `env.acts.maybeDescendentOf ety₁ ety₂` | needs proof |

## The tricky one: `acts.maybeDescendentOf`

```
def ActionSchema.maybeDescendentOf (as : ActionSchema) (ety₁ ety₂ : EntityType) : Bool :=
  as.toList.any λ (act, entry) => act.ty = ety₁ && entry.ancestors.any (EntityUID.ty · == ety₂)
```

This iterates over ALL action entries and checks their ancestors. Two schemas with
the same actions and same ancestors for each action will give the same result:

- Same set of `(act, entry)` pairs where `act.ty = ety₁` (same action UIDs → same types)
- For each such pair, `entry.ancestors` is the same (by `same_ancestors`)

So `maybeDescendentOf` agrees. ✓

## Proof Structure

The congruence theorem would be:

```lean
theorem typeOf_env_congr (expr : Expr) (c : Capabilities) (env₁ env₂ : TypeEnv)
    (hets : env₁.ets = env₂.ets)
    (hreqty : env₁.reqty = env₂.reqty)
    (hcontains : ∀ uid, env₁.acts.contains uid = env₂.acts.contains uid)
    (htype : ∀ ety, env₁.acts.actionType? ety = env₂.acts.actionType? ety)
    (hdesc : ∀ uid₁ uid₂, env₁.acts.descendentOf uid₁ uid₂ = env₂.acts.descendentOf uid₁ uid₂)
    (hmaybe : ∀ ety₁ ety₂, env₁.acts.maybeDescendentOf ety₁ ety₂ = env₂.acts.maybeDescendentOf ety₁ ety₂) :
    typeOf expr c env₁ = typeOf expr c env₂
```

The proof is by well-founded recursion on `expr` (same pattern as `checkEntities_eq`),
showing that each `typeOf` case produces the same result because all env queries agree.

### Case analysis (following typeOf definition):

1. **`.lit p`**: `typeOfLit` uses `env.ets.isValidEntityUID` (same by `hets`) and
   `env.acts.contains` (same by `hcontains`). ✓

2. **`.var v`**: `typeOfVar` uses `env.reqty` (same by `hreqty`). ✓

3. **`.ite x₁ x₂ x₃`**: By IH on x₁, x₂, x₃, the sub-results are the same.
   `typeOfIf` only uses the typed results, not env directly. ✓

4. **`.and x₁ x₂`**: By IH on x₁. Then `typeOfAnd` uses the result to decide
   whether to evaluate x₂. If it does, IH on x₂ (with updated caps from x₁,
   which is the same since x₁'s result is the same). ✓

5. **`.or x₁ x₂`**: Same as `.and`. ✓

6. **`.unaryApp op x₁`**: By IH on x₁. `typeOfUnaryApp` doesn't use env. ✓

7. **`.binaryApp op x₁ x₂`**: By IH on x₁ and x₂. Then `typeOfBinaryApp` uses:
   - `typeOfEq`: no env access. ✓
   - `typeOfInₑ`: uses `actionUID?` (needs `env.acts.contains`) and
     `env.acts.descendentOf` and `env.descendentOf` (needs hets + hmaybe). Same by assumptions. ✓
   - `typeOfInₛ`: uses `actionUID?` and `entityUIDs?` (no env) and `env.acts.descendentOf`. ✓
   - `typeOfHasTag`: uses `env.ets.tags?` (same by hets) and `env.acts.actionType?` (same by htype). ✓
   - `typeOfGetTag`: uses `env.ets.tags?`. ✓
   - Other ops: no env access. ✓

8. **`.hasAttr x₁ a`**: By IH on x₁. `typeOfHasAttr` uses `env.ets.attrs?` (same by hets)
   and `env.acts.actionType?` (same by htype). ✓

9. **`.getAttr x₁ a`**: By IH on x₁. `typeOfGetAttr` uses `env.ets.attrs?` (same by hets). ✓

10. **`.set xs`**: By IH on each element. `typeOfSet` doesn't use env. ✓

11. **`.record axs`**: By IH on each value. Record typing doesn't use env. ✓

12. **`.call xfn xs`**: By IH on each argument. `typeOfCall` doesn't use env. ✓

### Subtlety: Capabilities threading

The capabilities `c` are threaded through: `typeOf x₂ (c ∪ c₁) env` where `c₁`
comes from typing x₁. Since typing x₁ gives the same result on both envs (by IH),
`c₁` is the same, so the caps argument to x₂'s typeOf is the same. This means
the IH applies cleanly.

### Proof technique

Same as `checkEntities_eq`: well-founded recursion on `sizeOf expr`, match on
each `Expr` constructor, apply IH to sub-expressions. The key difference from
`checkEntities_eq` is:

1. More cases to handle (typeOfBinaryApp has many sub-cases)
2. Need to handle capabilities threading (show c₁ is same → c ∪ c₁ is same)
3. Need to handle the monadic `do` notation (if first sub-expr errors, both error the same way)

### Effort estimate

This proof is ~150-200 lines following the `checkEntities_eq` pattern. Each case is
straightforward but there are ~12 top-level cases with `binaryApp` having ~10 sub-cases.
The main challenge is that `typeOf` is not structurally recursive (it uses `sizeOf`)
and has nested match expressions that need careful handling.

## Alternative approach: avoid typeOf congruence entirely

Instead of proving typeOf congruence, we could restructure `single_policy_single_change_preserved`
to avoid needing it:

**Key observation:** We don't need `typecheckPolicy policy env₁ = typecheckPolicy policy env₂`.
We only need: if `typecheckPolicy policy env₁ = .ok tx₁`, then there exists `tx₂` such
that `typecheckPolicy policy env₂ = .ok tx₂` (not necessarily the same typed expr).
And specifically, if `tx₁.typeOf ≠ .bool .ff`, then `tx₂.typeOf ≠ .bool .ff`.

But actually we DO need exact equality of the typeOf result, because:
- `typecheckPolicyWithEnvironments` calls `mapM` which requires ALL envs to typecheck
- It then checks `allFalse` on the results

For `mapM` to succeed on schema₂, we need each env's typecheck to succeed. For unchanged
actions, we need `typecheckPolicy policy env₂ = .ok tx₂` (success, any tx₂). This is
exactly what typeOf congruence gives us (if it succeeded on env₁, it succeeds on env₂
with the same result).

## Conclusion

The typeOf congruence proof is the remaining piece. It's:
- Conceptually straightforward (every env query agrees → result agrees)
- Mechanically tedious (many cases)
- Follows the exact same pattern as the proven `checkEntities_eq`

The proof would be ~150-200 lines of case analysis.

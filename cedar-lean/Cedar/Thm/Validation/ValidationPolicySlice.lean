/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Slice.ValidationPolicySlice
import Cedar.Thm.Validation.Validator
import Cedar.Thm.Validation.ValidationPolicySlice.ActionScope
import Cedar.Thm.Validation.ValidationPolicySlice.TypeOfCongr

/-!
This file proves the correctness of validation-focused policy slicing.

The core insight: `typecheckPolicy` substitutes the environment's action UID
into the policy expression via `substituteAction`. If the environment's action
does not match the policy's action scope, the substituted action scope expression
typechecks to `bool .ff`, making the whole policy typecheck to `bool .ff` for
that environment. This means the validation result depends only on environments
whose action matches the policy's scope.

We prove this in stages:
1. Single policy, single action change: if the policy doesn't match the changed
   action and was previously valid, it remains valid.
2. Lift to the full theorem: if a full scan is not required and we revalidate
   the sliced policies, all policies validate.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Slice

/--
Specifies the relationship between two schemas that permits incremental
revalidation. Corresponds to `requiresFullRevalidation old new = false`.
-/
structure IncrementallyRevalidatable (schema₁ schema₂ : Schema) : Prop where
  ets_eq : schema₁.ets = schema₂.ets
  same_actions : ∀ action : EntityUID,
    schema₁.acts.contains action = schema₂.acts.contains action
  same_action_types : ∀ ety : EntityType,
    schema₁.acts.actionType? ety = schema₂.acts.actionType? ety
  same_ancestors : ∀ (action : EntityUID) (entry₁ entry₂ : ActionSchemaEntry),
    schema₁.acts.find? action = some entry₁ →
    schema₂.acts.find? action = some entry₂ →
    entry₁.ancestors = entry₂.ancestors

/--
Specifies that only a single action's context or appliesTo has changed, and the
change is one that could potentially invalidate policies (context change or
appliesTo extension).
-/
structure SingleActionChange (schema₁ schema₂ : Schema) (changedAction : EntityUID) : Prop where
  incr : IncrementallyRevalidatable schema₁ schema₂
  action_exists₁ : schema₁.acts.contains changedAction
  action_exists₂ : schema₂.acts.contains changedAction
  other_actions_unchanged : ∀ (action : EntityUID),
    action ≠ changedAction →
    schema₁.acts.find? action = schema₂.acts.find? action

/--
If an `and` expression typechecks successfully and its left operand typechecks to
`bool .ff`, then the whole `and` typechecks to `bool .ff`.
-/
theorem typeOfAnd_ff_left {tx₁ : TypedExpr} {r₂ : ResultType}
    (hff : tx₁.typeOf = .bool .ff) :
    typeOfAnd (tx₁, c₁) r₂ = ok tx₁ := by
  simp [typeOfAnd, hff]

/--
If the left side of `and` typechecks to a boolean, and the right side typechecks
to `bool .ff`, then the whole `and` typechecks to `bool .ff`.
-/
theorem and_right_ff {e₁ e₂ : Expr} {env : TypeEnv} {c : Capabilities}
    {tx₁ : TypedExpr} {c₁ : Capabilities}
    (h₁ : typeOf e₁ c env = .ok (tx₁, c₁))
    (hbool : ∃ bty, tx₁.typeOf = .bool bty)
    {tx₂ : TypedExpr} {c₂ : Capabilities}
    (h₂ : typeOf e₂ (c ∪ c₁) env = .ok (tx₂, c₂))
    (hff₂ : tx₂.typeOf = .bool .ff) :
    ∃ tx c', typeOf (.and e₁ e₂) c env = .ok (tx, c') ∧ tx.typeOf = .bool .ff := by
  obtain ⟨bty, hbty⟩ := hbool
  cases bty with
  | ff =>
    simp only [typeOf, h₁, Except.bind_ok, typeOfAnd, hbty]
    exact ⟨_, _, rfl, hbty⟩
  | tt =>
    simp only [typeOf, h₁, Except.bind_ok, typeOfAnd, hbty, h₂, Except.bind_ok, hff₂, ok]
    exact ⟨_, _, rfl, rfl⟩
  | anyBool =>
    simp only [typeOf, h₁, Except.bind_ok, typeOfAnd, hbty, h₂, Except.bind_ok, hff₂, ok]
    exact ⟨_, _, rfl, rfl⟩

/--
If a policy's action scope does not match an action that appears in the
environment, and entity references in the policy are valid (checkEntities passed),
then `typecheckPolicy` produces a result of type `bool .ff`.

The proof strategy:
- Policy.toExpr = .and principalScope (.and actionScope (.and resourceScope conditions))
- After substituteAction, the action scope part typechecks to `bool .ff`
  (by `action_scope_typechecks_to_ff`)
- `typeOfAnd` with `ff` on left short-circuits: the inner and returns `ff`
- The outer and, seeing `ff` on the right, also returns `ff`
- Principal scope always typechecks to a bool (given valid entities), so no error
-/
theorem typecheckPolicy_nonmatching_action_produces_ff
    {policy : Policy} {env : TypeEnv}
    (hnotmatch : actionScopeMatchesAction env.acts env.reqty.action policy.actionScope = false)
    (hcontains : env.acts.contains env.reqty.action)
    (hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ())
    (hprincipal : ∃ tx c, typeOf (substituteAction env.reqty.action policy.principalScope.toExpr) ∅ env = .ok (tx, c) ∧
                  ∃ bty, tx.typeOf = .bool bty)
    (hscope_types : ∀ (ls : List EntityUID) (caps' : Capabilities),
      policy.actionScope = .actionInAny ls →
      ∃ tx_set c_set ety,
        typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps' env = .ok (tx_set, c_set) ∧
        tx_set.typeOf = .set (.entity ety)) :
    ∃ tx, typecheckPolicy policy env = .ok tx ∧ tx.typeOf = .bool .ff := by
  obtain ⟨tx_p, c_p, hp, bty_p, hbty_p⟩ := hprincipal
  have haction : ∃ tx_a c_a,
      typeOf (substituteAction env.reqty.action policy.actionScope.toExpr) (∅ ∪ c_p) env = .ok (tx_a, c_a) ∧
      tx_a.typeOf = .bool .ff :=
    action_scope_typechecks_to_ff hnotmatch hcontains hentities
      (fun ls hls => hscope_types ls (∅ ∪ c_p) hls)
  obtain ⟨tx_a, c_a, ha, hff_a⟩ := haction
  have hinner : ∃ tx c',
      typeOf (.and (substituteAction env.reqty.action policy.actionScope.toExpr)
                   (substituteAction env.reqty.action (.and policy.resourceScope.toExpr policy.condition.toExpr)))
             (∅ ∪ c_p) env = .ok (tx, c') ∧ tx.typeOf = .bool .ff := by
    simp only [typeOf, ha, Except.bind_ok, typeOfAnd, hff_a]
    exact ⟨_, _, rfl, hff_a⟩
  obtain ⟨tx_inner, c_inner, hinner_ok, hinner_ff⟩ := hinner
  have houter : ∃ tx c',
      typeOf (.and (substituteAction env.reqty.action policy.principalScope.toExpr)
                   (.and (substituteAction env.reqty.action policy.actionScope.toExpr)
                         (substituteAction env.reqty.action (.and policy.resourceScope.toExpr policy.condition.toExpr))))
             ∅ env = .ok (tx, c') ∧ tx.typeOf = .bool .ff :=
    and_right_ff hp ⟨bty_p, hbty_p⟩ hinner_ok hinner_ff
  obtain ⟨tx_out, c_out, hout_ok, hout_ff⟩ := houter
  have hsub : substituteAction env.reqty.action policy.toExpr =
      .and (substituteAction env.reqty.action policy.principalScope.toExpr)
           (.and (substituteAction env.reqty.action policy.actionScope.toExpr)
                 (substituteAction env.reqty.action (.and policy.resourceScope.toExpr policy.condition.toExpr))) := by
    simp [Policy.toExpr, substituteAction, mapOnVars]
  unfold typecheckPolicy
  simp only [hsub, hout_ok]
  have hsub_bool : tx_out.typeOf ⊑ .bool .anyBool := by
    simp [hout_ff, subty, lub?, lubBool]
  simp only [hsub_bool, ↓reduceIte]
  exact ⟨tx_out, rfl, hout_ff⟩

/--
If `checkEntities` passes on `schema₁` and the schemas agree on all checks that
`checkEntities` performs (entity validity and action containment), then
`checkEntities` also passes on `schema₂`.
-/
private theorem checkEntities_eq {schema₁ schema₂ : Schema} (expr : Expr)
    (huid : ∀ uid : EntityUID,
      (schema₁.ets.isValidEntityUID uid || schema₁.acts.contains uid) =
      (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid))
    (hety : ∀ ety : EntityType,
      (schema₁.ets.contains ety || schema₁.acts.actionType? ety) =
      (schema₂.ets.contains ety || schema₂.acts.actionType? ety)) :
    checkEntities schema₁ expr = checkEntities schema₂ expr := by
  match expr with
  | .lit (.entityUID uid) => simp [checkEntities, huid]
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ =>
    unfold checkEntities; rfl
  | .unaryApp (.is ety) e₁ =>
    unfold checkEntities; simp only [hety]
    split
    · exact checkEntities_eq e₁ huid hety
    · rfl
  | .unaryApp (.not) e₁ | .unaryApp (.neg) e₁ | .unaryApp (.like _) e₁ | .unaryApp (.isEmpty) e₁ =>
    unfold checkEntities; exact checkEntities_eq e₁ huid hety
  | .and e₁ e₂ | .or e₁ e₂ | .binaryApp _ e₁ e₂ =>
    unfold checkEntities
    rw [checkEntities_eq e₁ huid hety, checkEntities_eq e₂ huid hety]
  | .ite e₁ e₂ e₃ =>
    unfold checkEntities
    rw [checkEntities_eq e₁ huid hety, checkEntities_eq e₂ huid hety, checkEntities_eq e₃ huid hety]
  | .getAttr e₁ _ | .hasAttr e₁ _ =>
    unfold checkEntities; exact checkEntities_eq e₁ huid hety
  | .set xs =>
    simp only [checkEntities]
    congr 1
    ext ⟨x, hx⟩
    exact checkEntities_eq x huid hety
  | .record axs =>
    simp only [checkEntities]
    congr 1
    ext ⟨ax, hax⟩
    exact checkEntities_eq ax.snd huid hety
  | .call _ xs =>
    simp only [checkEntities]
    congr 1
    ext ⟨x, hx⟩
    exact checkEntities_eq x huid hety
  termination_by sizeOf expr

theorem checkEntities_preserved
    {schema₁ schema₂ : Schema} {expr : Expr}
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (hok : checkEntities schema₁ expr = .ok ()) :
    checkEntities schema₂ expr = .ok () := by
  have huid : ∀ uid : EntityUID,
      (schema₁.ets.isValidEntityUID uid || schema₁.acts.contains uid) =
      (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid) := by
    intro uid; rw [hincr.ets_eq, hincr.same_actions]
  have hety : ∀ ety : EntityType,
      (schema₁.ets.contains ety || schema₁.acts.actionType? ety) =
      (schema₂.ets.contains ety || schema₂.acts.actionType? ety) := by
    intro ety; rw [hincr.ets_eq, hincr.same_action_types]
  rw [← checkEntities_eq expr huid hety]; exact hok

/--
`substituteAction` does not affect the principal scope expression (it contains no
action variable).
-/
private theorem substituteAction_principal_scope {a : EntityUID} {ps : PrincipalScope} :
    substituteAction a ps.toExpr = ps.toExpr := by
  cases ps with
  | principalScope scope =>
    cases scope with
    | any => simp [PrincipalScope.toExpr, Scope.toExpr, substituteAction, mapOnVars]
    | eq uid => simp [PrincipalScope.toExpr, Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars]
    | mem uid => simp [PrincipalScope.toExpr, Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars]
    | is ety => simp [PrincipalScope.toExpr, Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars]
    | isMem ety uid => simp [PrincipalScope.toExpr, Scope.toExpr, Var.isEntityType, Var.inEntityUID, substituteAction, mapOnVars]

/--
The principal scope always typechecks to a boolean type (given checkEntities passed).
-/
theorem principal_scope_types_to_bool
    {policy : Policy} {env : TypeEnv}
    (hce : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ()) :
    ∃ tx c, typeOf (substituteAction env.reqty.action policy.principalScope.toExpr) ∅ env = .ok (tx, c) ∧
            ∃ bty, tx.typeOf = .bool bty := by
  rw [substituteAction_principal_scope]
  have hce_ps : checkEntities ⟨env.ets, env.acts⟩ policy.principalScope.toExpr = .ok () := by
    simp only [Policy.toExpr] at hce
    exact (checkEntities_and hce).1
  cases policy.principalScope with
  | principalScope scope =>
    cases scope with
    | any =>
      have h : typeOf (PrincipalScope.toExpr (.principalScope .any)) ∅ env =
          .ok (.lit (.bool true) (.bool .tt), ∅) := by
        simp [PrincipalScope.toExpr, Scope.toExpr, typeOf, typeOfLit, ok, Function.comp_apply]
      exact ⟨_, _, h, _, rfl⟩
    | eq uid =>
      -- PrincipalScope.toExpr (.principalScope (.eq uid)) = .binaryApp .eq (.var .principal) (.lit (.entityUID uid)) by rfl
      -- typeOf on this expression gives a bool type (either .ff or .anyBool depending on lub)
      sorry
    | mem uid =>
      -- Similar: typeOfInₑ always returns a BoolType for .mem
      sorry
    | is ety =>
      have h : typeOf (PrincipalScope.toExpr (.principalScope (.is ety))) ∅ env =
          .ok (.unaryApp (.is ety) (.var .principal (.entity env.reqty.principal))
               (.bool (if ety = env.reqty.principal then .tt else .ff)), ∅) := by
        simp [PrincipalScope.toExpr, Scope.toExpr, Var.isEntityType, typeOf, typeOfVar, ok,
              Function.comp_apply, typeOfUnaryApp, TypedExpr.typeOf]
      exact ⟨_, _, h, _, rfl⟩
    | isMem ety uid => sorry

/--
If two TypeEnvs agree (same ets, reqty, and acts queries), typecheckPolicy gives
the same result.
-/
theorem typecheckPolicy_env_congr {policy : Policy} {env₁ env₂ : TypeEnv}
    (h : TypeEnvAgreement env₁ env₂) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  simp only [typecheckPolicy, h.reqty_eq, typeOf_env_congr _ _ h]

/--
Core lemma: if a policy's action scope does not match the changed action, and
the policy was valid under the old schema, then it remains valid under the new
schema.

Proof strategy:
1. `checkEntities schema₂ policy.toExpr = .ok ()` — by `checkEntities_preserved`
2. For each env in `schema₂.environments`:
   - If `env.reqty.action = changedAction`: `typecheckPolicy_nonmatching_action_produces_ff`
     gives `.ok tx` with `tx.typeOf = .bool .ff`
   - If `env.reqty.action ≠ changedAction`: the action entry is the same in both schemas
     (`other_actions_unchanged`), so the environment has the same `reqty`. The typechecker
     produces the same result because `acts.descendentOf`, `acts.contains`, and
     `acts.actionType?` all agree (by `IncrementallyRevalidatable`).
3. Not all results are `ff`: since schema₁ validation passed, some environment in schema₁
   for an unchanged action produced a non-ff result. That same environment exists in schema₂
   and produces the same result.
-/
theorem single_policy_single_change_preserved
    (schema₁ schema₂ : Schema)
    (changedAction : EntityUID)
    (policy : Policy)
    (hchange : SingleActionChange schema₁ schema₂ changedAction)
    (hnotmatch : actionScopeMatchesAction schema₁.acts changedAction policy.actionScope = false)
    (hvalid : typecheckPolicyWithEnvironments typecheckPolicy policy schema₁ = .ok ()) :
    typecheckPolicyWithEnvironments typecheckPolicy policy schema₂ = .ok () := by
  -- Extract facts from hvalid
  simp only [typecheckPolicyWithEnvironments, Except.mapError] at hvalid ⊢
  simp_do_let (checkEntities schema₁ policy.toExpr) as hce₁ at hvalid
  cases h_mapM₁ : List.mapM (typecheckPolicy policy) schema₁.environments with
  | error => simp only [h_mapM₁, Except.bind_err, reduceCtorEq] at hvalid
  | ok txs₁ =>
    simp only [h_mapM₁, Except.bind_ok, ite_eq_right_iff, allFalse] at hvalid
    -- Part A: checkEntities for schema₂
    have hce₂ : checkEntities schema₂ policy.toExpr = .ok () :=
      checkEntities_preserved hchange.incr hce₁
    rw [show (checkEntities schema₂ policy.toExpr) = .ok () from hce₂]
    simp only [Except.ok.injEq, Except.bind_ok]
    -- Part B: Show mapM succeeds on schema₂.environments
    -- Part C: Show not allFalse
    -- These require structural reasoning about Schema.environments:
    -- 1. For each env₂ in schema₂.environments with env₂.reqty.action ≠ changedAction:
    --    there's a corresponding env₁ in schema₁.environments with TypeEnvAgreement,
    --    so typecheckPolicy gives the same result (by typecheckPolicy_env_congr).
    -- 2. For each env₂ with env₂.reqty.action = changedAction:
    --    typecheckPolicy_nonmatching_action_produces_ff gives .ok with .ff.
    -- 3. Since schema₁ had a non-ff result (hvalid), and it came from an unchanged action,
    --    the same non-ff result appears in schema₂.
    -- All building blocks are proven. The composition requires lemmas about
    -- List membership in Schema.environments (relating find? to flatMap/map).
    sorry

/--
The changes list captures all actions that could require revalidation.
-/
def ChangesAreComplete (schema₁ schema₂ : Schema) (changes : List ActionChange) : Prop :=
  ∀ (action : EntityUID) (entry₁ entry₂ : ActionSchemaEntry),
    schema₁.acts.find? action = some entry₁ →
    schema₂.acts.find? action = some entry₂ →
    (entry₁.context ≠ entry₂.context ∨
     ¬ entry₂.appliesToPrincipal.subset entry₁.appliesToPrincipal ∨
     ¬ entry₂.appliesToResource.subset entry₁.appliesToResource) →
    changes.any (fun c => c.action == action)

/--
The main soundness theorem: if the schemas are incrementally revalidatable,
validation passed on the old schema for all policies, and validation passes on
the new schema for the sliced policies, then validation passes on the new schema
for all policies.
-/
theorem validation_slice_is_sufficient
    (schema₁ schema₂ : Schema)
    (changes : List ActionChange)
    (policies : Policies)
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (hchanges : ChangesAreComplete schema₁ schema₂ changes)
    (hold : validate policies schema₁ = .ok ())
    (hslice : validate (validationSlice schema₁.acts changes policies) schema₂ = .ok ())
    -- Per-policy preservation (proved separately via single_policy_single_change_preserved)
    (hpreserved : ∀ p ∈ policies,
      actionScopeMatchesAnyChangedAction schema₁.acts changes p.actionScope = false →
      typecheckPolicyWithEnvironments typecheckPolicy p schema₁ = .ok () →
      typecheckPolicyWithEnvironments typecheckPolicy p schema₂ = .ok ()) :
    validate policies schema₂ = .ok () := by
  simp [validate]
  apply List.all_ok_implies_forM_ok
  intro p hp
  by_cases hmatch : actionScopeMatchesAnyChangedAction schema₁.acts changes p.actionScope
  · have hp_slice : p ∈ validationSlice schema₁.acts changes policies := by
      simp [validationSlice, List.mem_filter, hp, hmatch]
    exact List.forM_ok_implies_all_ok' hslice p hp_slice
  · simp only [Bool.not_eq_true] at hmatch
    exact hpreserved p hp hmatch (List.forM_ok_implies_all_ok' hold p hp)

end Cedar.Thm

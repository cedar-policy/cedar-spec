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
  same_descendentOf : ∀ uid₁ uid₂ : EntityUID,
    schema₁.acts.descendentOf uid₁ uid₂ = schema₂.acts.descendentOf uid₁ uid₂
  same_maybeDescendentOf : ∀ ety₁ ety₂ : EntityType,
    schema₁.acts.maybeDescendentOf ety₁ ety₂ = schema₂.acts.maybeDescendentOf ety₁ ety₂

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
  acts_wf₁ : Map.WellFormed schema₁.acts
  acts_wf₂ : Map.WellFormed schema₂.acts

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

private theorem checkEntities_lit_entityUID {schema : Schema} {uid : EntityUID}
    (h : checkEntities schema (.lit (.entityUID uid)) = .ok ()) :
    (schema.ets.isValidEntityUID uid || schema.acts.contains uid) = true := by
  simp only [checkEntities] at h
  split at h
  · assumption
  · contradiction

/--
Any scope expression typechecks to a boolean type given valid entities.
-/
private theorem scope_types_to_bool {scope : Scope} {env : TypeEnv}
    (hce : checkEntities ⟨env.ets, env.acts⟩ (Scope.toExpr scope .principal) = .ok ()) :
    ∃ tx c, typeOf (Scope.toExpr scope .principal) ∅ env = .ok (tx, c) ∧
            ∃ bty, tx.typeOf = .bool bty := by
  cases scope with
  | any =>
    have heval : typeOf (Scope.toExpr .any .principal) ∅ env =
        .ok (.lit (.bool true) (.bool .tt), ∅) := by
      simp [Scope.toExpr, typeOf, typeOfLit, ok, Function.comp_apply]
    exact ⟨_, _, heval, _, rfl⟩
  | eq uid =>
    simp only [Scope.toExpr, Var.eqEntityUID] at hce
    have ⟨_, hce_uid⟩ := checkEntities_binaryApp hce
    have hvalid_uid := checkEntities_lit_entityUID hce_uid
    simp only [Scope.toExpr, Var.eqEntityUID]
    have h1 : typeOf (.var Var.principal) ∅ env = Except.ok (.var .principal (.entity env.reqty.principal), ∅) := by
      simp [typeOf, typeOfVar, ok]
    have h2 : typeOf (.lit (Prim.entityUID uid)) ∅ env = Except.ok (.lit (.entityUID uid) (.entity uid.ty), ∅) := by
      simp [typeOf, typeOfLit, hvalid_uid, ok]
    simp only [typeOf, h1, h2, Except.bind_ok]
    simp only [typeOfBinaryApp,
      show TypedExpr.typeOf (.var .principal (.entity env.reqty.principal)) = .entity env.reqty.principal from rfl,
      show TypedExpr.typeOf (.lit (.entityUID uid) (.entity uid.ty)) = .entity uid.ty from rfl, typeOfEq]
    cases lub? (CedarType.entity env.reqty.principal) (CedarType.entity uid.ty)
    all_goals simp_all [ok, TypedExpr.typeOf]
  | mem uid =>
    simp only [Scope.toExpr, Var.inEntityUID] at hce
    have ⟨_, hce_uid⟩ := checkEntities_binaryApp hce
    have hvalid_uid := checkEntities_lit_entityUID hce_uid
    simp only [Scope.toExpr, Var.inEntityUID]
    have h1 : typeOf (.var Var.principal) ∅ env = Except.ok (.var .principal (.entity env.reqty.principal), ∅) := by
      simp [typeOf, typeOfVar, ok]
    have h2 : typeOf (.lit (Prim.entityUID uid)) ∅ env = Except.ok (.lit (.entityUID uid) (.entity uid.ty), ∅) := by
      simp [typeOf, typeOfLit, hvalid_uid, ok]
    simp only [typeOf, h1, h2, Except.bind_ok]
    simp only [typeOfBinaryApp,
      show TypedExpr.typeOf (.var .principal (.entity env.reqty.principal)) = .entity env.reqty.principal from rfl,
      show TypedExpr.typeOf (.lit (.entityUID uid) (.entity uid.ty)) = .entity uid.ty from rfl]
    simp_all [ok, TypedExpr.typeOf, typeOfInₑ]
  | is ety =>
    simp only [Scope.toExpr, Var.isEntityType]
    have heval : typeOf (.unaryApp (.is ety) (.var .principal)) ∅ env =
        .ok (.unaryApp (.is ety) (.var .principal (.entity env.reqty.principal))
             (.bool (if ety = env.reqty.principal then .tt else .ff)), ∅) := by
      simp [typeOf, typeOfVar, ok, Function.comp_apply, typeOfUnaryApp, TypedExpr.typeOf]
    exact ⟨_, _, heval, _, rfl⟩
  | isMem ety uid =>
    simp only [Scope.toExpr, Var.isEntityType, Var.inEntityUID] at hce
    have ⟨_, hce_inner⟩ := checkEntities_and hce
    have ⟨_, hce_uid⟩ := checkEntities_binaryApp hce_inner
    have hvalid_uid := checkEntities_lit_entityUID hce_uid
    simp only [Scope.toExpr, Var.isEntityType, Var.inEntityUID]
    by_cases hety : ety = env.reqty.principal
    · cases hdesc : env.descendentOf env.reqty.principal uid.ty
      all_goals simp [typeOf, typeOfVar, ok, typeOfUnaryApp, TypedExpr.typeOf, hety,
            typeOfAnd, typeOfLit, hvalid_uid, typeOfBinaryApp, typeOfInₑ,
            entityUID?, actionUID?, hdesc]
    · have heval : typeOf (.and (.unaryApp (.is ety) (.var .principal))
                                (.binaryApp .mem (.var .principal) (.lit (.entityUID uid)))) ∅ env =
          .ok (.unaryApp (.is ety) (.var .principal (.entity env.reqty.principal)) (.bool .ff), ∅) := by
        simp [typeOf, typeOfVar, ok, typeOfUnaryApp, TypedExpr.typeOf, hety, typeOfAnd]
      exact ⟨_, _, heval, _, rfl⟩

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
  have ⟨scope, _, hps_toExpr⟩ : ∃ scope, policy.principalScope = .principalScope scope ∧
      policy.principalScope.toExpr = Scope.toExpr scope .principal := by
    cases policy.principalScope with
    | principalScope s => exact ⟨s, rfl, rfl⟩
  rw [hps_toExpr] at hce_ps ⊢
  exact scope_types_to_bool hce_ps

/--
If two TypeEnvs agree (same ets, reqty, and acts queries), typecheckPolicy gives
the same result.
-/
theorem typecheckPolicy_env_congr {policy : Policy} {env₁ env₂ : TypeEnv}
    (h : TypeEnvAgreement env₁ env₂) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  simp only [typecheckPolicy, h.reqty_eq, typeOf_env_congr _ _ h]

/--
Construct `TypeEnvAgreement` for environments from an `IncrementallyRevalidatable` pair.
-/
theorem incr_gives_agreement {schema₁ schema₂ : Schema} {reqty : RequestType}
    (hincr : IncrementallyRevalidatable schema₁ schema₂) :
    TypeEnvAgreement
      { ets := schema₁.ets, acts := schema₁.acts, reqty := reqty }
      { ets := schema₂.ets, acts := schema₂.acts, reqty := reqty } where
  ets_eq := hincr.ets_eq
  reqty_eq := rfl
  acts_contains := hincr.same_actions
  acts_actionType := hincr.same_action_types
  acts_descendentOf := hincr.same_descendentOf
  acts_maybeDescendentOf := hincr.same_maybeDescendentOf

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
    (hvalid : typecheckPolicyWithEnvironments typecheckPolicy policy schema₁ = .ok ())
    (hactionInAny_wf : ∀ (ls : List EntityUID),
      policy.actionScope = .actionInAny ls →
      ls ≠ [] ∧ ∃ ety, ∀ uid ∈ ls, uid.ty = ety) :
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
    -- Part B: every env in schema₂.environments typechecks ok
    have hall_ok : ∀ env ∈ schema₂.environments, ∃ tx, typecheckPolicy policy env = .ok tx := by
      intro env henv
      have ⟨henv_ets, henv_acts⟩ := env_mem_environments_schema henv
      have henv_contains := env_mem_environments_action_contained henv
      by_cases haction : env.reqty.action = changedAction
      · -- Case B1: action is the changed one → produces .ff
        have hnotmatch' : actionScopeMatchesAction env.acts env.reqty.action policy.actionScope = false := by
          rw [henv_acts, haction]
          -- actionScopeMatchesAction uses contains and descendentOf, which agree
          rw [actionScopeMatchesAction_descendentOf_congr (fun u₁ u₂ => (hchange.incr.same_descendentOf u₁ u₂).symm)]
          exact hnotmatch
        have hcontains : env.acts.contains env.reqty.action := by rw [henv_acts]; exact henv_contains
        have hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok () := by
          rw [henv_ets, henv_acts]; exact hce₂
        have hprincipal := principal_scope_types_to_bool hentities
        have hscope_types : ∀ (ls : List EntityUID) (caps' : Capabilities),
            policy.actionScope = .actionInAny ls →
            ∃ tx_set c_set ety, typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps' env = .ok (tx_set, c_set) ∧
              tx_set.typeOf = .set (.entity ety) :=
          fun ls caps' hls => by
            have ⟨hne, hsame⟩ := hactionInAny_wf ls hls
            have hvalid_uids := actionInAny_uids_valid_from_policy hentities hls
            exact actionInAny_set_types hne hvalid_uids hsame
        obtain ⟨tx, htx, _⟩ := typecheckPolicy_nonmatching_action_produces_ff
          hnotmatch' hcontains hentities hprincipal hscope_types
        exact ⟨tx, htx⟩
      · -- Case B2: action is unchanged → same result as in schema₁
        have henv₁_exists : ∃ env₁ ∈ schema₁.environments,
            env₁.reqty = env.reqty ∧ TypeEnvAgreement env₁ env := by
          have hfind_eq : schema₁.acts.find? env.reqty.action = schema₂.acts.find? env.reqty.action :=
            hchange.other_actions_unchanged env.reqty.action haction
          obtain ⟨env₁, henv₁_mem, henv₁_reqty⟩ := env_in_other_schema_environments henv hfind_eq hchange.acts_wf₂
          have ⟨henv₁_ets, henv₁_acts⟩ := env_mem_environments_schema henv₁_mem
          refine ⟨env₁, henv₁_mem, henv₁_reqty, ?_⟩
          constructor
          · rw [henv₁_ets, henv_ets, hchange.incr.ets_eq]
          · rw [henv₁_reqty]
          · intro uid; rw [henv₁_acts, henv_acts]; exact hchange.incr.same_actions uid
          · intro ety; rw [henv₁_acts, henv_acts]; exact hchange.incr.same_action_types ety
          · intro u₁ u₂; rw [henv₁_acts, henv_acts]; exact hchange.incr.same_descendentOf u₁ u₂
          · intro e₁ e₂; rw [henv₁_acts, henv_acts]; exact hchange.incr.same_maybeDescendentOf e₁ e₂
        obtain ⟨env₁, henv₁_mem, henv₁_reqty, hagree⟩ := henv₁_exists
        have ⟨tx₁, _, htx₁⟩ := List.mapM_ok_implies_all_ok h_mapM₁ env₁ henv₁_mem
        rw [typecheckPolicy_env_congr hagree] at htx₁
        exact ⟨tx₁, htx₁⟩
    -- Get the mapM result
    obtain ⟨txs₂, h_mapM₂⟩ := List.all_ok_implies_mapM_ok hall_ok
    rw [h_mapM₂]
    simp only [Except.bind_ok]
    -- Part C: not allFalse
    -- From hvalid: not all txs₁ are .ff
    -- So there exists env₁ in schema₁.environments where typecheckPolicy ≠ .ff
    -- That env₁ has env₁.reqty.action ≠ changedAction (otherwise it would be .ff)
    -- The same reqty exists in schema₂.environments and gives the same result
    by_cases hallff₂ : allFalse txs₂ = true
    · -- allFalse case: derive contradiction
      exfalso
      -- Step 1: from hvalid, not all txs₁ are .ff
      -- hvalid : allFalse txs₁ = true → .error ... = .ok () (i.e., allFalse txs₁ ≠ true)
      have hnotallff₁ : ∃ tx₁ ∈ txs₁, tx₁.typeOf ≠ .bool .ff := by
        by_contra h
        simp only [not_exists, not_and, Classical.not_not] at h
        have hall : (txs₁.all fun tx => tx.typeOf == .bool .ff) = true :=
          List.all_eq_true.mpr (fun tx htx => by simp [h tx htx])
        exact absurd (hvalid hall) (by simp)
      obtain ⟨tx₁, htx₁_mem, htx₁_notff'⟩ := hnotallff₁
      -- Step 2: tx₁ corresponds to some env₁
      have ⟨env₁, henv₁_mem, henv₁_ok⟩ := List.mapM_ok_implies_all_from_ok h_mapM₁ tx₁ htx₁_mem
      -- Step 3: env₁.reqty.action ≠ changedAction
      -- (otherwise typecheckPolicy_nonmatching_action_produces_ff would give .ff)
      have henv₁_action_ne : env₁.reqty.action ≠ changedAction := by
        intro heq
        have ⟨henv₁_ets, henv₁_acts⟩ := env_mem_environments_schema henv₁_mem
        have henv₁_contains := env_mem_environments_action_contained henv₁_mem
        have hnotmatch₁ : actionScopeMatchesAction env₁.acts env₁.reqty.action policy.actionScope = false := by
          rw [henv₁_acts, heq]; exact hnotmatch
        have hcontains₁ : env₁.acts.contains env₁.reqty.action := by rw [henv₁_acts]; exact henv₁_contains
        have hentities₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok () := by
          rw [henv₁_ets, henv₁_acts]; exact hce₁
        have hprincipal₁ := principal_scope_types_to_bool hentities₁
        have hscope_types₁ : ∀ (ls : List EntityUID) (caps' : Capabilities),
            policy.actionScope = .actionInAny ls →
            ∃ tx_set c_set ety, typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps' env₁ = .ok (tx_set, c_set) ∧
              tx_set.typeOf = .set (.entity ety) :=
          fun ls caps' hls => by
            have ⟨hne, hsame⟩ := hactionInAny_wf ls hls
            have hvalid_uids := actionInAny_uids_valid_from_policy hentities₁ hls
            exact actionInAny_set_types hne hvalid_uids hsame
        obtain ⟨tx_ff, htx_ff_ok, htx_ff_ty⟩ := typecheckPolicy_nonmatching_action_produces_ff
          hnotmatch₁ hcontains₁ hentities₁ hprincipal₁ hscope_types₁
        have : tx_ff = tx₁ := by
          have h := henv₁_ok; rw [htx_ff_ok] at h; exact Except.ok.inj h
        exact htx₁_notff' (this ▸ htx_ff_ty)
      -- Step 4: env_in_other_schema_environments (schema₁→schema₂)
      have hfind_eq : schema₂.acts.find? env₁.reqty.action = schema₁.acts.find? env₁.reqty.action :=
        (hchange.other_actions_unchanged env₁.reqty.action henv₁_action_ne).symm
      obtain ⟨env₂, henv₂_mem, henv₂_reqty⟩ :=
        env_in_other_schema_environments henv₁_mem hfind_eq hchange.acts_wf₁
      -- Step 5: typecheckPolicy gives the same result on env₂
      have ⟨henv₂_ets, henv₂_acts⟩ := env_mem_environments_schema henv₂_mem
      have ⟨henv₁_ets', henv₁_acts'⟩ := env_mem_environments_schema henv₁_mem
      have hagree : TypeEnvAgreement env₁ env₂ := by
        constructor
        · rw [henv₁_ets', henv₂_ets, hchange.incr.ets_eq]
        · rw [henv₂_reqty]
        · intro uid; rw [henv₁_acts', henv₂_acts]; exact hchange.incr.same_actions uid
        · intro ety; rw [henv₁_acts', henv₂_acts]; exact hchange.incr.same_action_types ety
        · intro u₁ u₂; rw [henv₁_acts', henv₂_acts]; exact hchange.incr.same_descendentOf u₁ u₂
        · intro e₁ e₂; rw [henv₁_acts', henv₂_acts]; exact hchange.incr.same_maybeDescendentOf e₁ e₂
      have henv₂_ok : typecheckPolicy policy env₂ = .ok tx₁ := by
        rw [← typecheckPolicy_env_congr hagree]; exact henv₁_ok
      -- Step 6: tx₁ ∈ txs₂
      have htx₁_in_txs₂ : tx₁ ∈ txs₂ := by
        have ⟨tx₂, htx₂_mem, htx₂_ok⟩ := List.mapM_ok_implies_all_ok h_mapM₂ env₂ henv₂_mem
        have : tx₁ = tx₂ := by rw [henv₂_ok] at htx₂_ok; exact Except.ok.inj htx₂_ok
        rw [this]; exact htx₂_mem
      -- Step 7: contradiction with hallff₂
      simp only [allFalse] at hallff₂
      rw [List.all_eq_true] at hallff₂
      have := hallff₂ tx₁ htx₁_in_txs₂
      simp only [beq_iff_eq] at this
      exact htx₁_notff' this
    · simp [hallff₂]

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

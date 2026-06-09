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
import Cedar.Thm.Validation.ValidationPolicySlice.Environments

/-!
# Validation Policy Slicing: Correctness Proof

## Main result

`validation_slice_iff`: when a schema change does not require full revalidation,
no type errors across all policies iff no type errors in the slice:

    validateOrImpossible policies newSchema = true ↔
    validateOrImpossible (validationSlice oldSchema newSchema policies) newSchema = true

This handles appliesTo truncation: removing principal/resource types from an
action's appliesTo can make policies "impossible" (all environments yield `.ff`)
but cannot introduce type errors.

## Key insight

`typecheckPolicy` substitutes the environment's action UID into the policy
expression. If the environment's action does not match the policy's action scope,
the substituted expression typechecks to `bool .ff`. This means the validation
result depends only on environments whose action matches the policy's scope —
so policies whose scope doesn't match any changed action are unaffected.

## Proof structure

1. **Infrastructure**: `checkEntities` preservation, principal scope typing,
   `typeOf`/`typecheckPolicy` congruence across environments
2. **Per-policy** (`policy_preserved`): if a policy's action scope does not match
   any changed action, and was previously valid, it remains valid
3. **Core lemma** (`nonslice_policy_noTypeErrors`): non-slice policies have no
   type errors on the new schema (handles appliesTo subset via congruence)
4. **Completeness** (`validation_slice_complete`): all validate → slice validates
5. **Soundness** (`validation_slice_soundness`): slice validates → no type errors
6. **Equivalence** (`validation_slice_iff`): combines into biconditional
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Slice

/-! ## Infrastructure: typeOf helpers for and-expressions -/

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

/-! ## Infrastructure: checkEntities preservation -/

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

private theorem checkEntities_monotone {schema₁ schema₂ : Schema} (expr : Expr)
    (huid : ∀ uid : EntityUID,
      (schema₁.ets.isValidEntityUID uid || schema₁.acts.contains uid) = true →
      (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid) = true)
    (hety : ∀ ety : EntityType,
      (schema₁.ets.contains ety || schema₁.acts.actionType? ety) = true →
      (schema₂.ets.contains ety || schema₂.acts.actionType? ety) = true)
    (hok : checkEntities schema₁ expr = .ok ()) :
    checkEntities schema₂ expr = .ok () := by
  match expr with
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at hok ⊢
    split at hok
    · rename_i hv; rw [show (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid) = true from huid uid hv]; rfl
    · contradiction
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ =>
    unfold checkEntities; rfl
  | .unaryApp (.is ety) e₁ =>
    simp only [checkEntities] at hok ⊢
    split at hok
    · rename_i hv
      rw [show (schema₂.ets.contains ety || schema₂.acts.actionType? ety) = true from hety ety hv]
      exact checkEntities_monotone e₁ huid hety hok
    · contradiction
  | .unaryApp (.not) e₁ | .unaryApp (.neg) e₁ | .unaryApp (.like _) e₁ | .unaryApp (.isEmpty) e₁ =>
    unfold checkEntities at hok ⊢; exact checkEntities_monotone e₁ huid hety hok
  | .and e₁ e₂ | .or e₁ e₂ | .binaryApp _ e₁ e₂ =>
    unfold checkEntities at hok ⊢
    cases h₁ : checkEntities schema₁ e₁ with
    | error => simp [h₁] at hok
    | ok _ =>
      simp [h₁] at hok
      have h₁' := checkEntities_monotone e₁ huid hety (by exact h₁ ▸ rfl)
      simp [h₁']
      exact checkEntities_monotone e₂ huid hety hok
  | .ite e₁ e₂ e₃ =>
    unfold checkEntities at hok ⊢
    cases h₁ : checkEntities schema₁ e₁ with
    | error => simp [h₁] at hok
    | ok _ =>
      cases h₂ : checkEntities schema₁ e₂ with
      | error => simp [h₁, h₂] at hok
      | ok _ =>
        simp [h₁, h₂] at hok
        have h₁' := checkEntities_monotone e₁ huid hety (by exact h₁ ▸ rfl)
        have h₂' := checkEntities_monotone e₂ huid hety (by exact h₂ ▸ rfl)
        simp [h₁', h₂']
        exact checkEntities_monotone e₃ huid hety hok
  | .hasAttr e₁ _ | .getAttr e₁ _ =>
    unfold checkEntities at hok ⊢; exact checkEntities_monotone e₁ huid hety hok
  | .set xs =>
    simp only [checkEntities] at hok ⊢
    apply List.all_ok_implies_forM_ok
    intro ⟨x, hx⟩ hmem
    have hok_x := List.forM_ok_implies_all_ok' hok ⟨x, hx⟩ hmem
    exact checkEntities_monotone x huid hety hok_x
  | .record axs =>
    simp only [checkEntities] at hok ⊢
    apply List.all_ok_implies_forM_ok
    intro ⟨ax, hax⟩ hmem
    have hok_ax := List.forM_ok_implies_all_ok' hok ⟨ax, hax⟩ hmem
    exact checkEntities_monotone ax.snd huid hety hok_ax
  | .call _ xs =>
    simp only [checkEntities] at hok ⊢
    apply List.all_ok_implies_forM_ok
    intro ⟨x, hx⟩ hmem
    have hok_x := List.forM_ok_implies_all_ok' hok ⟨x, hx⟩ hmem
    exact checkEntities_monotone x huid hety hok_x
  termination_by sizeOf expr

theorem checkEntities_preserved
    {schema₁ schema₂ : Schema} {expr : Expr}
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (hok : checkEntities schema₁ expr = .ok ()) :
    checkEntities schema₂ expr = .ok () := by
  have huid_fwd : ∀ uid : EntityUID,
      (schema₁.ets.isValidEntityUID uid || schema₁.acts.contains uid) = true →
      (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid) = true := by
    intro uid hv
    cases hv₁ : schema₁.ets.isValidEntityUID uid
    · simp only [hv₁] at hv
      have := hincr.acts_contains_fwd uid hv
      simp [this]
    · have : schema₂.ets.isValidEntityUID uid = true := hincr.ets_eq ▸ hv₁
      simp [this]
  have hety_fwd : ∀ ety : EntityType,
      (schema₁.ets.contains ety || schema₁.acts.actionType? ety) = true →
      (schema₂.ets.contains ety || schema₂.acts.actionType? ety) = true := by
    intro ety hv; rw [← hincr.ets_eq, ← hincr.same_action_types]; exact hv
  exact checkEntities_monotone expr huid_fwd hety_fwd hok

/-! ## Infrastructure: principal scope typing -/

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

/-! ## Infrastructure: typecheckPolicy congruence -/

/--
If two TypeEnvs agree (same ets, reqty, and acts queries), typecheckPolicy gives
the same result.
-/
theorem typecheckPolicy_env_congr {policy : Policy} {env₁ env₂ : TypeEnv}
    (h : TypeEnvAgreement env₁ env₂) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  simp only [typecheckPolicy, h.reqty_eq, typeOf_env_congr _ _ h]

/--
Weak congruence: if `checkEntities` passes on env₁ and the environments have
`WeakTypeEnvAgreement`, then `typecheckPolicy` gives the same result.
-/
private theorem checkEntities_mapOnVars {schema : Schema} {f : Var → Expr} (expr : Expr)
    (hf : ∀ v, checkEntities schema (f v) = .ok ())
    (hce : checkEntities schema expr = .ok ()) :
    checkEntities schema (mapOnVars f expr) = .ok () := by
  match expr with
  | .lit _ => simp [mapOnVars, hce]
  | .var v => simp [mapOnVars, hf]
  | .unaryApp (.is ety) e₁ =>
    simp only [checkEntities] at hce
    split at hce
    · rename_i hv; simp only [mapOnVars, checkEntities, hv]; exact checkEntities_mapOnVars e₁ hf hce
    · contradiction
  | .unaryApp (.not) e₁ | .unaryApp (.neg) e₁ | .unaryApp (.like _) e₁ | .unaryApp (.isEmpty) e₁ =>
    unfold checkEntities at hce; simp only [mapOnVars]; unfold checkEntities
    exact checkEntities_mapOnVars e₁ hf hce
  | .and e₁ e₂ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf hce]
  | .or e₁ e₂ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf hce]
  | .binaryApp _ e₁ e₂ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf hce]
  | .ite e₁ e₂ e₃ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    cases h₂ : checkEntities schema e₂ <;> simp [h₂] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf (by rw [h₂]),
          checkEntities_mapOnVars e₃ hf hce]
  | .hasAttr e₁ _ =>
    unfold checkEntities at hce; simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf hce]
  | .getAttr e₁ _ =>
    unfold checkEntities at hce; simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf hce]
  | .set xs =>
    simp only [checkEntities] at hce
    simp only [mapOnVars, List.map₁, checkEntities]
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    have hy_in_map : y ∈ xs.attach.map (fun ⟨x, _⟩ => mapOnVars f x) := hy
    rw [List.mem_map] at hy_in_map
    obtain ⟨⟨x, hx⟩, hmem_att, heq⟩ := hy_in_map
    have : checkEntities schema y = .ok () := by
      rw [← heq]
      exact checkEntities_mapOnVars x hf (List.forM_ok_implies_all_ok' hce ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩))
    exact this
  | .record axs =>
    simp only [checkEntities] at hce
    simp only [mapOnVars, List.map₂, checkEntities]
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    -- y ∈ the mapped list. Get membership from hmem via attach₂ → mem_attach₂
    have hy_mem : y ∈ axs.attach₂.map (fun ⟨⟨a, x⟩, _⟩ => (a, mapOnVars f x)) :=
      List.mem_attach₂ hmem
    simp only [List.mem_map] at hy_mem
    obtain ⟨⟨ax, hax⟩, hmem_att, heq⟩ := hy_mem
    have heq_snd : y.snd = mapOnVars f ax.snd := by
      have := congrArg Prod.snd heq; simp at this; exact this.symm
    rw [heq_snd]
    exact checkEntities_mapOnVars ax.snd hf (List.forM_ok_implies_all_ok' hce ⟨ax, hax⟩ hmem_att)
  | .call _ xs =>
    simp only [checkEntities] at hce
    simp only [mapOnVars, List.map₁, checkEntities]
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    have hy_in_map : y ∈ xs.attach.map (fun ⟨x, _⟩ => mapOnVars f x) := hy
    rw [List.mem_map] at hy_in_map
    obtain ⟨⟨x, hx⟩, hmem_att, heq⟩ := hy_in_map
    have : checkEntities schema y = .ok () := by
      rw [← heq]
      exact checkEntities_mapOnVars x hf (List.forM_ok_implies_all_ok' hce ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩))
    exact this
  termination_by sizeOf expr

private theorem checkEntities_substituteAction {schema : Schema} {uid : EntityUID} {expr : Expr}
    (hce : checkEntities schema expr = .ok ())
    (hvalid : (schema.ets.isValidEntityUID uid || schema.acts.contains uid) = true) :
    checkEntities schema (substituteAction uid expr) = .ok () := by
  simp only [substituteAction]
  exact checkEntities_mapOnVars expr (fun v => by cases v <;> simp [checkEntities, hvalid]) hce

theorem typecheckPolicy_env_congr_weak {policy : Policy} {env₁ env₂ : TypeEnv}
    (h : WeakTypeEnvAgreement env₁ env₂)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok ())
    (haction_valid : (env₁.ets.isValidEntityUID env₁.reqty.action ||
                      env₁.acts.contains env₁.reqty.action) = true) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  simp only [typecheckPolicy]
  have hce_sub : checkEntities ⟨env₁.ets, env₁.acts⟩
      (substituteAction env₁.reqty.action policy.toExpr) = .ok () :=
    checkEntities_substituteAction hce haction_valid
  have heq := typeOf_env_congr_weak (substituteAction env₁.reqty.action policy.toExpr) ∅ h hce_sub
  simp only [h.reqty_eq] at heq ⊢
  rw [heq]

/-! ## Per-policy non-matching action produces ff -/

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

/-! ## Per-policy preservation theorem -/

/--
Helper: if action scope doesn't match a given action, checkEntities passes,
and actionInAny is well-formed, then typecheckPolicy produces `.ff`.
This factors out the repeated setup for `typecheckPolicy_nonmatching_action_produces_ff`.
-/
private theorem typecheckPolicy_produces_ff_for_nonmatching_env
    {policy : Policy} {env : TypeEnv}
    (hnotmatch : actionScopeMatchesAction env.acts env.reqty.action policy.actionScope = false)
    (hcontains : env.acts.contains env.reqty.action)
    (hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ())
    (hactionInAny_wf : ∀ (ls : List EntityUID),
      policy.actionScope = .actionInAny ls → ls ≠ [] ∧ ∃ ety, ∀ uid ∈ ls, uid.ty = ety) :
    ∃ tx, typecheckPolicy policy env = .ok tx ∧ tx.typeOf = .bool .ff := by
  have hprincipal := principal_scope_types_to_bool hentities
  have hscope_types : ∀ (ls : List EntityUID) (caps' : Capabilities),
      policy.actionScope = .actionInAny ls →
      ∃ tx_set c_set ety, typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps' env = .ok (tx_set, c_set) ∧
        tx_set.typeOf = .set (.entity ety) :=
    fun ls caps' hls => by
      have ⟨hne, hsame⟩ := hactionInAny_wf ls hls
      exact actionInAny_set_types hne (actionInAny_uids_valid_from_policy hentities hls) hsame
  exact typecheckPolicy_nonmatching_action_produces_ff hnotmatch hcontains hentities hprincipal hscope_types

/--
If a policy's action scope doesn't match any action in a changes list, then for
any specific action in that list, the scope doesn't match that action either.
-/
private theorem actionScopeNotMatchesIndividual
    {acts : ActionSchema} {changes : List ActionChange} {scope : ActionScope}
    (hnotmatch : actionScopeMatchesAnyChangedAction acts changes scope = false)
    {action : EntityUID}
    (haction : changes.any (fun c => c.action == action)) :
    actionScopeMatchesAction acts action scope = false := by
  simp only [actionScopeMatchesAnyChangedAction, List.any_eq_false] at hnotmatch
  simp only [List.any_eq_true, beq_iff_eq] at haction
  obtain ⟨c, hc_mem, hc_eq⟩ := haction
  exact Bool.eq_false_iff.mpr (hc_eq ▸ hnotmatch c hc_mem)

/--
Multi-change version: if a policy's scope doesn't match ANY action whose entry
differs between schemas, and the policy validated on schema₁, it validates on schema₂.
This directly connects to the slicing algorithm.
-/
theorem policy_preserved
    (schema₁ schema₂ : Schema)
    (changes : List ActionChange)
    (policy : Policy)
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (hnotmatch : actionScopeMatchesAnyChangedAction schema₁.acts changes policy.actionScope = false)
    (hvalid : typecheckPolicyWithEnvironments typecheckPolicy policy schema₁ = .ok ())
    (hunchanged : ∀ (action : EntityUID),
      ¬ changes.any (fun c => c.action == action) →
      schema₁.acts.find? action = schema₂.acts.find? action)
    (hacts_wf₁ : Map.WellFormed schema₁.acts)
    (hacts_wf₂ : Map.WellFormed schema₂.acts) :
    typecheckPolicyWithEnvironments typecheckPolicy policy schema₂ = .ok () := by
  -- Extract validation components
  simp only [typecheckPolicyWithEnvironments, Except.mapError] at hvalid ⊢
  simp_do_let (checkEntities schema₁ policy.toExpr) as hce₁ at hvalid
  cases h_mapM₁ : List.mapM (typecheckPolicy policy) schema₁.environments with
  | error => simp only [h_mapM₁, Except.bind_err, reduceCtorEq] at hvalid
  | ok txs₁ =>
    simp only [h_mapM₁, Except.bind_ok, ite_eq_right_iff, allFalse] at hvalid
    have hce₂ : checkEntities schema₂ policy.toExpr = .ok () :=
      checkEntities_preserved hincr hce₁
    rw [show (checkEntities schema₂ policy.toExpr) = .ok () from hce₂]
    simp only [Except.bind_ok]
    have hactionInAny_wf : ∀ (ls : List EntityUID),
        policy.actionScope = .actionInAny ls →
        ls ≠ [] ∧ ∃ ety, ∀ uid ∈ ls, uid.ty = ety := by
      intro ls hls
      have hvalid_full : typecheckPolicyWithEnvironments typecheckPolicy policy schema₁ = .ok () := by
        simp only [typecheckPolicyWithEnvironments, Except.mapError, hce₁, Except.bind_ok,
                   h_mapM₁, Except.bind_ok, ite_eq_right_iff, allFalse]
        exact hvalid
      exact actionInAny_wf_of_valid hls hvalid_full
    -- Part B: every env in schema₂.environments typechecks ok
    have hall_ok : ∀ env ∈ schema₂.environments, ∃ tx, typecheckPolicy policy env = .ok tx := by
      intro env henv
      have ⟨henv_ets, henv_acts⟩ := env_mem_environments_schema henv
      have henv_contains := env_mem_environments_action_contained henv
      by_cases haction : changes.any (fun c => c.action == env.reqty.action)
      · -- Case B1: action is in changes → scope doesn't match → .ff
        have hnotmatch' : actionScopeMatchesAction env.acts env.reqty.action policy.actionScope = false := by
          rw [henv_acts]
          rw [actionScopeMatchesAction_descendentOf_congr (fun u₁ u₂ => (hincr.same_descendentOf u₁ u₂).symm)]
          exact actionScopeNotMatchesIndividual hnotmatch haction
        have hcontains : env.acts.contains env.reqty.action := by rw [henv_acts]; exact henv_contains
        have hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok () := by
          rw [henv_ets, henv_acts]; exact hce₂
        obtain ⟨tx, htx, _⟩ := typecheckPolicy_produces_ff_for_nonmatching_env
          hnotmatch' hcontains hentities hactionInAny_wf
        exact ⟨tx, htx⟩
      · -- Case B2: action not in changes → same entry → same result
        have hfind_eq : schema₁.acts.find? env.reqty.action = schema₂.acts.find? env.reqty.action :=
          hunchanged env.reqty.action haction
        obtain ⟨env₁, henv₁_mem, henv₁_reqty⟩ := env_in_other_schema_environments henv hfind_eq hacts_wf₂
        have ⟨henv₁_ets, henv₁_acts⟩ := env_mem_environments_schema henv₁_mem
        have hagree := mk_weakTypeEnvAgreement_from_schemas hincr henv₁_ets henv₁_acts henv_ets henv_acts henv₁_reqty
        have hce_env₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok () := by
          rw [henv₁_ets, henv₁_acts]; exact hce₁
        have ⟨tx₁, _, htx₁⟩ := List.mapM_ok_implies_all_ok h_mapM₁ env₁ henv₁_mem
        rw [typecheckPolicy_env_congr_weak hagree hce_env₁ (by simp [henv₁_acts, env_mem_environments_action_contained henv₁_mem])] at htx₁
        exact ⟨tx₁, htx₁⟩
    obtain ⟨txs₂, h_mapM₂⟩ := List.all_ok_implies_mapM_ok hall_ok
    rw [h_mapM₂]
    simp only [Except.bind_ok]
    -- Part C: not allFalse (same as single_policy_single_change_preserved)
    by_cases hallff₂ : allFalse txs₂ = true
    · exfalso
      have ⟨tx₁, htx₁_mem, htx₁_notff'⟩ : ∃ tx₁ ∈ txs₁, tx₁.typeOf ≠ .bool .ff := by
        by_contra h
        simp only [not_exists, not_and, Classical.not_not] at h
        exact absurd (hvalid (List.all_eq_true.mpr (fun tx htx => by simp [h tx htx]))) (by simp)
      obtain ⟨env₁, henv₁_mem, henv₁_ok⟩ := List.mapM_ok_implies_all_from_ok h_mapM₁ tx₁ htx₁_mem
      have henv₁_action_ne : ¬ changes.any (fun c => c.action == env₁.reqty.action) := by
        intro hany
        have ⟨henv₁_ets, henv₁_acts⟩ := env_mem_environments_schema henv₁_mem
        have henv₁_contains := env_mem_environments_action_contained henv₁_mem
        have hnotmatch₁ : actionScopeMatchesAction env₁.acts env₁.reqty.action policy.actionScope = false := by
          rw [henv₁_acts]; exact actionScopeNotMatchesIndividual hnotmatch hany
        have hcontains₁ : env₁.acts.contains env₁.reqty.action := by rw [henv₁_acts]; exact henv₁_contains
        have hentities₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok () := by
          rw [henv₁_ets, henv₁_acts]; exact hce₁
        obtain ⟨tx_ff, htx_ff_ok, htx_ff_ty⟩ := typecheckPolicy_produces_ff_for_nonmatching_env
          hnotmatch₁ hcontains₁ hentities₁ hactionInAny_wf
        have : tx_ff = tx₁ := by
          have h := henv₁_ok; rw [htx_ff_ok] at h; exact Except.ok.inj h
        exact htx₁_notff' (this ▸ htx_ff_ty)
      have hfind_eq : schema₂.acts.find? env₁.reqty.action = schema₁.acts.find? env₁.reqty.action :=
        (hunchanged env₁.reqty.action henv₁_action_ne).symm
      obtain ⟨env₂, henv₂_mem, henv₂_reqty⟩ :=
        env_in_other_schema_environments henv₁_mem hfind_eq hacts_wf₁
      have ⟨henv₂_ets, henv₂_acts⟩ := env_mem_environments_schema henv₂_mem
      have ⟨henv₁_ets', henv₁_acts'⟩ := env_mem_environments_schema henv₁_mem
      have hagree := mk_weakTypeEnvAgreement_from_schemas hincr henv₁_ets' henv₁_acts' henv₂_ets henv₂_acts henv₂_reqty.symm
      have hce_env₁' : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok () := by
        rw [henv₁_ets', henv₁_acts']; exact hce₁
      have henv₂_ok : typecheckPolicy policy env₂ = .ok tx₁ := by
        rw [← typecheckPolicy_env_congr_weak hagree hce_env₁' (by simp [henv₁_acts', env_mem_environments_action_contained henv₁_mem])]; exact henv₁_ok
      have htx₁_in_txs₂ : tx₁ ∈ txs₂ := by
        have ⟨tx₂, htx₂_mem, htx₂_ok⟩ := List.mapM_ok_implies_all_ok h_mapM₂ env₂ henv₂_mem
        have : tx₁ = tx₂ := by rw [henv₂_ok] at htx₂_ok; exact Except.ok.inj htx₂_ok
        rw [this]; exact htx₂_mem
      simp only [allFalse] at hallff₂
      rw [List.all_eq_true] at hallff₂
      have := hallff₂ tx₁ htx₁_in_txs₂
      simp only [beq_iff_eq] at this
      exact htx₁_notff' this
    · simp [hallff₂]

/-! ## Top-level theorems

The main result is `validation_slice_iff` at the bottom of this file:
no type errors across all policies ↔ no type errors in the slice.
-/

/-! ### Connecting executable checks to propositional specs -/

private theorem rfr_false_ets_eq {old new : Schema}
    (h : requiresFullRevalidation old new = false) :
    old.ets = new.ets := by
  unfold requiresFullRevalidation at h
  simp only [Bool.or_eq_false_iff] at h; simp [bne] at h; exact h.1.1

private theorem rfr_false_old_in_new {old new : Schema}
    (h : requiresFullRevalidation old new = false)
    {action : EntityUID} {oldEntry : ActionSchemaEntry}
    (hfind : old.acts.find? action = some oldEntry) :
    ∃ newEntry, new.acts.find? action = some newEntry ∧
      oldEntry.ancestors = newEntry.ancestors := by
  unfold requiresFullRevalidation at h
  simp only [Bool.or_eq_false_iff, List.any_eq_false] at h
  have h_entry := h.1.2 ⟨action, oldEntry⟩ (Map.find?_mem_toList hfind)
  cases hfn : new.acts.find? action with
  | none => simp [hfn] at h_entry
  | some ne => simp [hfn, bne] at h_entry; exact ⟨ne, rfl, h_entry⟩

private theorem rfr_false_same_ancestors {old new : Schema}
    (h : requiresFullRevalidation old new = false)
    {action : EntityUID} {e₁ e₂ : ActionSchemaEntry}
    (hf₁ : old.acts.find? action = some e₁) (hf₂ : new.acts.find? action = some e₂) :
    e₁.ancestors = e₂.ancestors := by
  have ⟨_, hf₂', heq⟩ := rfr_false_old_in_new h hf₁
  exact (Option.some.inj (hf₂' ▸ hf₂)) ▸ heq

/--
`requiresFullRevalidation = false` implies `IncrementallyRevalidatable`.
This bridges the executable check to the propositional spec.
-/
theorem rfr_false_implies_incr {oldSchema newSchema : Schema}
    (hno_full : requiresFullRevalidation oldSchema newSchema = false)
    (hacts_wf₁ : Map.WellFormed oldSchema.acts)
    (hacts_wf₂ : Map.WellFormed newSchema.acts)
    (hdisjoint : ∀ uid, newSchema.acts.contains uid = true → newSchema.ets.isValidEntityUID uid = false) :
    IncrementallyRevalidatable oldSchema newSchema := by
  have hets := rfr_false_ets_eq hno_full
  have hcontains_fwd : ∀ uid, oldSchema.acts.contains uid = true → newSchema.acts.contains uid = true := by
    intro uid hc
    simp only [ActionSchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨oe, hfo⟩ := hc
    have ⟨_, hfn, _⟩ := rfr_false_old_in_new hno_full hfo
    simp [ActionSchema.contains, hfn]
  have hsame_anc : ∀ (a : EntityUID) (e₁ e₂ : ActionSchemaEntry),
      oldSchema.acts.find? a = some e₁ → newSchema.acts.find? a = some e₂ →
      e₁.ancestors = e₂.ancestors := fun a e₁ e₂ h₁ h₂ => rfr_false_same_ancestors hno_full h₁ h₂
  have hnew_leaf : ∀ (action : EntityUID) (newEntry : ActionSchemaEntry),
      (action, newEntry) ∈ newSchema.acts.toList →
      oldSchema.acts.contains action = false →
      newEntry.ancestors.isEmpty ∧ oldSchema.acts.actionType? action.ty := by
    intro action newEntry hmem hnot_old
    unfold requiresFullRevalidation at hno_full
    simp only [Bool.or_eq_false_iff, List.any_eq_false] at hno_full
    have h_entry := hno_full.2 ⟨action, newEntry⟩ hmem
    simp [hnot_old] at h_entry
    exact h_entry
  exact {
    ets_eq := hets
    acts_contains_fwd := hcontains_fwd
    acts_disjoint := hdisjoint
    same_action_types := by
      intro ety; simp only [ActionSchema.actionType?, Set.any]
      cases h : oldSchema.acts.keys.elts.any (EntityUID.ty · == ety)
      · symm; rw [List.any_eq_false]; intro uid hmem
        rw [List.any_eq_false] at h
        have hc : newSchema.acts.contains uid = true := Map.in_keys_iff_contains.mp hmem
        cases hold : oldSchema.acts.contains uid with
        | true => exact h uid (Map.in_keys_iff_contains.mpr hold)
        | false =>
          have hfind_new := Option.isSome_iff_exists.mp (by simp [ActionSchema.contains] at hc; exact hc)
          obtain ⟨entry, hfind⟩ := hfind_new
          have ⟨_, hat⟩ := hnew_leaf uid entry (Map.find?_mem_toList hfind) (by simp [hold])
          simp only [ActionSchema.actionType?, Set.any, List.any_eq_true] at hat
          obtain ⟨uid', hmem', hty'⟩ := hat
          by_contra heq; simp only [beq_iff_eq] at heq
          rw [heq] at hty'; exact absurd hty' (h uid' hmem')
      · symm; rw [List.any_eq_true] at h ⊢; obtain ⟨uid, hmem, hty⟩ := h
        have hc : oldSchema.acts.contains uid = true := Map.in_keys_iff_contains.mp hmem
        have hc' : newSchema.acts.contains uid = true := hcontains_fwd uid hc
        exact ⟨uid, Map.in_keys_iff_contains.mpr hc', hty⟩
    same_ancestors := hsame_anc
    same_descendentOf := by
      intro uid₁ uid₂
      simp only [ActionSchema.descendentOf]
      split
      · rfl
      · cases hf₁ : oldSchema.acts.find? uid₁ with
        | none =>
          -- uid₁ not in old. Is it in new?
          cases hf₂ : newSchema.acts.find? uid₁ with
          | none => rfl
          | some entry₂ =>
            -- uid₁ is new. By hnew_leaf, entry₂.ancestors.isEmpty
            have hnotold : oldSchema.acts.contains uid₁ = false := by
              simp [ActionSchema.contains, hf₁]
            have ⟨hempty, _⟩ := hnew_leaf uid₁ entry₂ (Map.find?_mem_toList hf₂) hnotold
            simp only [Set.isEmpty, beq_iff_eq] at hempty
            simp only [Set.contains]
            have : entry₂.ancestors.elts = [] := by
              have := congrArg Set.elts hempty; simp [Set.empty] at this; exact this
            simp [this]
        | some entry₁ =>
          have ⟨entry₂, hf₂, hanc⟩ := rfr_false_old_in_new hno_full hf₁
          simp [hf₂, hanc]
    same_maybeDescendentOf := by
      intro ety₁ ety₂; simp only [ActionSchema.maybeDescendentOf]
      cases h : oldSchema.acts.toList.any (fun x => x.1.ty = ety₁ && x.2.ancestors.any (EntityUID.ty · == ety₂))
      · -- No old action has the property. Show no new action does either.
        symm; rw [List.any_eq_false] at h ⊢
        intro ⟨act, entry₂⟩ hmem₂
        have hfind₂ := (Map.in_list_iff_find?_some hacts_wf₂).mp hmem₂
        cases hold : oldSchema.acts.contains act
        · -- act is new: ancestors is empty, so ancestors.any is false
          have ⟨hempty, _⟩ := hnew_leaf act entry₂ hmem₂ hold
          simp only [Set.isEmpty, beq_iff_eq] at hempty
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          intro _
          have helts : entry₂.ancestors.elts = [] := by
            have := congrArg Set.elts hempty; simp [Set.empty] at this; exact this
          simp_all [Set.any]
        · -- act is in old: use h
          obtain ⟨entry₁, hfind₁⟩ := Option.isSome_iff_exists.mp hold
          have := h ⟨act, entry₁⟩ (Map.find?_mem_toList hfind₁)
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this ⊢
          rw [← hsame_anc act entry₁ entry₂ hfind₁ hfind₂]; exact this
      · -- Some old action has the property. Transfer to new.
        symm; rw [List.any_eq_true] at h ⊢
        obtain ⟨⟨act, entry₁⟩, hmem₁, hpred⟩ := h
        have hfind₁ := (Map.in_list_iff_find?_some hacts_wf₁).mp hmem₁
        have hc₂ : newSchema.acts.contains act = true := hcontains_fwd act (by simp [ActionSchema.contains, hfind₁])
        obtain ⟨entry₂, hfind₂⟩ := Option.isSome_iff_exists.mp hc₂
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred ⊢
        exact ⟨⟨act, entry₂⟩, Map.find?_mem_toList hfind₂,
          by rw [← hsame_anc act entry₁ entry₂ hfind₁ hfind₂]; exact hpred⟩
  }

/-! ### Completeness -/

/--
Completeness for `validateOrImpossible`: the slice is a subset of all policies,
so if all pass then the slice passes.
-/
theorem validation_slice_complete
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hall : validateOrImpossible policies newSchema = true) :
    validateOrImpossible (validationSlice oldSchema newSchema policies) newSchema = true := by
  simp only [validateOrImpossible, List.all_eq_true] at hall ⊢
  intro p hp
  exact hall p ((List.mem_filter.mp hp).1)

/-! ### Soundness: non-slice policies have no type errors -/

/--
A policy whose action scope doesn't match any changed action has no type errors
on the new schema. This is the core lemma for both soundness theorems.
-/
private theorem nonslice_policy_noTypeErrors
    {oldSchema newSchema : Schema} {p : Policy}
    (hno_full : requiresFullRevalidation oldSchema newSchema = false)
    (hvalid_p : typecheckPolicyWithEnvironments typecheckPolicy p oldSchema = .ok ())
    (hmatch : actionScopeMatchesAnyChangedAction oldSchema.acts
      (computeActionChanges oldSchema newSchema) p.actionScope = false)
    (hacts_wf₁ : oldSchema.acts.wellFormed)
    (hacts_wf₂ : newSchema.acts.wellFormed)
    (hdisjoint : ∀ uid, newSchema.acts.contains uid = true → newSchema.ets.isValidEntityUID uid = false) :
    (match typecheckPolicyWithEnvironments typecheckPolicy p newSchema with
    | .ok () => true
    | .error (.impossiblePolicy _) => true
    | _ => false) = true := by
  have hacts_wf₁' : Map.WellFormed oldSchema.acts :=
    Map.wf_iff_sorted.mpr (List.isSortedBy_correct.mpr hacts_wf₁)
  have hacts_wf₂' : Map.WellFormed newSchema.acts :=
    Map.wf_iff_sorted.mpr (List.isSortedBy_correct.mpr hacts_wf₂)
  have hincr := rfr_false_implies_incr hno_full hacts_wf₁' hacts_wf₂' hdisjoint
  have hvalid_p_orig := hvalid_p
  simp only [typecheckPolicyWithEnvironments, Except.mapError] at hvalid_p ⊢
  simp_do_let (checkEntities oldSchema p.toExpr) as hce₁ at hvalid_p
  have hce₂ : checkEntities newSchema p.toExpr = .ok () :=
    checkEntities_preserved hincr hce₁
  rw [show (checkEntities newSchema p.toExpr) = .ok () from hce₂]
  simp only [Except.bind_ok]
  have hactionInAny_wf : ∀ (ls : List EntityUID),
      p.actionScope = .actionInAny ls →
      ls ≠ [] ∧ ∃ ety, ∀ uid ∈ ls, uid.ty = ety :=
    fun ls hls => actionInAny_wf_of_valid hls hvalid_p_orig
  cases h_mapM₁ : List.mapM (typecheckPolicy p) oldSchema.environments with
  | error => simp only [h_mapM₁, Except.bind_err, reduceCtorEq] at hvalid_p
  | ok txs₁ =>
  have hall_ok : ∀ env ∈ newSchema.environments, ∃ tx, typecheckPolicy p env = .ok tx := by
    intro env henv
    have ⟨henv_ets, henv_acts⟩ := env_mem_environments_schema henv
    have henv_contains := env_mem_environments_action_contained henv
    by_cases haction : (computeActionChanges oldSchema newSchema).any (fun c => c.action == env.reqty.action)
    · have hnotmatch' : actionScopeMatchesAction env.acts env.reqty.action p.actionScope = false := by
        rw [henv_acts]
        rw [actionScopeMatchesAction_descendentOf_congr (fun u₁ u₂ => (hincr.same_descendentOf u₁ u₂).symm)]
        exact actionScopeNotMatchesIndividual hmatch haction
      have hcontains : env.acts.contains env.reqty.action := by rw [henv_acts]; exact henv_contains
      have hentities : checkEntities ⟨env.ets, env.acts⟩ p.toExpr = .ok () := by
        rw [henv_ets, henv_acts]; exact hce₂
      obtain ⟨tx, htx, _⟩ := typecheckPolicy_produces_ff_for_nonmatching_env
        hnotmatch' hcontains hentities hactionInAny_wf
      exact ⟨tx, htx⟩
    · have henv_action_in_new : newSchema.acts.contains env.reqty.action := henv_contains
      obtain ⟨newEntry, hfind_new⟩ := Option.isSome_iff_exists.mp henv_action_in_new
      have henv_action_in_old : oldSchema.acts.contains env.reqty.action := by
        -- If the action were NOT in old, computeActionChanges would include it
        by_contra h; simp [ActionSchema.contains] at h
        have hmem_out : ActionChange.contextChanged env.reqty.action ∈
            computeActionChanges oldSchema newSchema := by
          simp only [computeActionChanges, List.mem_filterMap]
          exact ⟨(env.reqty.action, newEntry), Map.find?_mem_toList hfind_new, by simp [h]⟩
        exact absurd (List.any_eq_true.mpr ⟨_, hmem_out, by simp [ActionChange.action]⟩) haction
      obtain ⟨oldEntry, hfind_old⟩ := Option.isSome_iff_exists.mp henv_action_in_old
      have ⟨hctx, hprincipal, hresource⟩ := computeActionChanges_not_in_gives_subset
        haction hfind_old hfind_new
      obtain ⟨env₁, henv₁_mem, henv₁_reqty⟩ := env_in_other_schema_environments_subset
        henv hfind_old hfind_new hctx hprincipal hresource hacts_wf₂'
      have ⟨henv₁_ets, henv₁_acts⟩ := env_mem_environments_schema henv₁_mem
      have hagree := mk_weakTypeEnvAgreement_from_schemas hincr henv₁_ets henv₁_acts henv_ets henv_acts henv₁_reqty
      have hce_env₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ p.toExpr = .ok () := by
        rw [henv₁_ets, henv₁_acts]; exact hce₁
      have ⟨tx₁, _, htx₁⟩ := List.mapM_ok_implies_all_ok h_mapM₁ env₁ henv₁_mem
      rw [typecheckPolicy_env_congr_weak hagree hce_env₁ (by simp [henv₁_acts, env_mem_environments_action_contained henv₁_mem])] at htx₁
      exact ⟨tx₁, htx₁⟩
  obtain ⟨txs₂, h_mapM₂⟩ := List.all_ok_implies_mapM_ok hall_ok
  simp only [Except.bind_ok, h_mapM₂]
  cases hallff : allFalse txs₂ <;> simp

/-! ### Equivalence -/

/--
**Soundness**: if the slice has no type errors, then all policies have no type
errors. Non-slice policies are unaffected by the schema change (their environments
either don't match the changed actions, or transfer via appliesTo subset).
-/
theorem validation_slice_soundness
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hno_full : requiresFullRevalidation oldSchema newSchema = false)
    (hold : validate policies oldSchema = .ok ())
    (hslice : validateOrImpossible (validationSlice oldSchema newSchema policies) newSchema = true)
    (hacts_wf₁ : oldSchema.acts.wellFormed)
    (hacts_wf₂ : newSchema.acts.wellFormed)
    (hdisjoint : ∀ uid, newSchema.acts.contains uid = true → newSchema.ets.isValidEntityUID uid = false) :
    validateOrImpossible policies newSchema = true := by
  simp only [validateOrImpossible, List.all_eq_true] at hslice ⊢
  intro p hp
  by_cases hmatch : actionScopeMatchesAnyChangedAction oldSchema.acts
      (computeActionChanges oldSchema newSchema) p.actionScope
  · exact hslice p (List.mem_filter.mpr ⟨hp, hmatch⟩)
  · simp only [Bool.not_eq_true] at hmatch
    have hvalid_p := List.forM_ok_implies_all_ok' (by simp [validate] at hold; exact hold) p hp
    exact nonslice_policy_noTypeErrors hno_full hvalid_p hmatch hacts_wf₁ hacts_wf₂ hdisjoint

/--
**Main theorem**: no type errors across all policies iff no type errors in the
slice.

This handles the general case including appliesTo truncation. Truncated actions
can make non-slice policies "impossible" but cannot introduce type errors. The
slice captures exactly the policies whose type-error status could change.
-/
theorem validation_slice_iff
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hno_full : requiresFullRevalidation oldSchema newSchema = false)
    (hold : validate policies oldSchema = .ok ())
    (hacts_wf₁ : oldSchema.acts.wellFormed)
    (hacts_wf₂ : newSchema.acts.wellFormed)
    (hdisjoint : ∀ uid, newSchema.acts.contains uid = true → newSchema.ets.isValidEntityUID uid = false) :
    validateOrImpossible policies newSchema = true ↔
    validateOrImpossible (validationSlice oldSchema newSchema policies) newSchema = true :=
  ⟨validation_slice_complete oldSchema newSchema policies,
   fun h => validation_slice_soundness oldSchema newSchema policies hno_full hold h hacts_wf₁ hacts_wf₂ hdisjoint⟩

end Cedar.Thm

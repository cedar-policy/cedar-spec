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

/-!
This file proves that action scope expressions typecheck to `bool .ff` when the
environment's action does not match the policy's action scope.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Slice

set_option maxHeartbeats 1600000

/-! ### checkEntities helpers -/

theorem checkEntities_and {schema : Schema} {e₁ e₂ : Expr}
    (h : checkEntities schema (.and e₁ e₂) = .ok ()) :
    checkEntities schema e₁ = .ok () ∧ checkEntities schema e₂ = .ok () := by
  simp only [checkEntities] at h
  cases h₁ : checkEntities schema e₁ with
  | error e => simp [h₁] at h
  | ok _ => simp [h₁] at h; exact ⟨rfl, h⟩

theorem checkEntities_binaryApp {schema : Schema} {op : BinaryOp} {e₁ e₂ : Expr}
    (h : checkEntities schema (.binaryApp op e₁ e₂) = .ok ()) :
    checkEntities schema e₁ = .ok () ∧ checkEntities schema e₂ = .ok () := by
  simp only [checkEntities] at h
  cases h₁ : checkEntities schema e₁ with
  | error e => simp [h₁] at h
  | ok _ => simp [h₁] at h; exact ⟨rfl, h⟩

theorem checkEntities_policy_implies_actionScope {schema : Schema} {policy : Policy}
    (h : checkEntities schema policy.toExpr = .ok ()) :
    checkEntities schema policy.actionScope.toExpr = .ok () := by
  simp only [Policy.toExpr] at h
  have ⟨_, h₂⟩ := checkEntities_and h
  have ⟨h₃, _⟩ := checkEntities_and h₂
  exact h₃

/-! ### Per-case action scope lemmas

Each lemma proves that a specific action scope variant typechecks to `bool .ff`
when the match condition fails. These are standalone and don't require case
splitting on an abstract `ActionScope`.
-/

theorem action_scope_eq_typechecks_to_ff
    {uid : EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hneq : ¬ (uid = env.reqty.action))
    (hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true)
    (hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    ∃ tx c,
      typeOf (.binaryApp .eq (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  have hne_prim : (Prim.entityUID env.reqty.action == Prim.entityUID uid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Prim.entityUID.injEq]; exact fun h => hneq h.symm
  have heval : typeOf (.binaryApp .eq (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) caps env =
      .ok (TypedExpr.binaryApp .eq
        (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty))
        (.lit (.entityUID uid) (.entity uid.ty))
        (.bool .ff), ∅) := by
    simp [typeOf, typeOfLit, hvalid_action, hvalid_uid, ok, Function.comp_apply,
      typeOfBinaryApp, TypedExpr.typeOf, typeOfEq, hne_prim]
  exact ⟨_, _, heval, rfl⟩

theorem action_scope_mem_typechecks_to_ff
    {uid : EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hnotdesc : env.acts.descendentOf env.reqty.action uid = false)
    (hcontains : env.acts.contains env.reqty.action)
    (hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true)
    (hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    ∃ tx c,
      typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  have heval : typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) caps env =
      .ok (TypedExpr.binaryApp .mem
        (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty))
        (.lit (.entityUID uid) (.entity uid.ty))
        (.bool .ff), ∅) := by
    simp [typeOf, typeOfLit, hvalid_action, hvalid_uid, ok, Function.comp_apply,
      typeOfBinaryApp, TypedExpr.typeOf, typeOfInₑ, actionUID?, entityUID?,
      hcontains, hnotdesc]
  exact ⟨_, _, heval, rfl⟩

theorem action_scope_is_typechecks_to_ff
    {ety : EntityType} {env : TypeEnv} {caps : Capabilities}
    (hne : ¬ (ety = env.reqty.action.ty))
    (hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true) :
    ∃ tx c,
      typeOf (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  have heval : typeOf (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action))) caps env =
      .ok (TypedExpr.unaryApp (.is ety)
        (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty))
        (.bool .ff), ∅) := by
    simp [typeOf, typeOfLit, hvalid_action, ok, Function.comp_apply,
      typeOfUnaryApp, TypedExpr.typeOf, hne]
  exact ⟨_, _, heval, rfl⟩

theorem action_scope_isMem_typechecks_to_ff
    {ety : EntityType} {uid : EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hnotmatch : (env.reqty.action.ty == ety && env.acts.descendentOf env.reqty.action uid) = false)
    (hcontains : env.acts.contains env.reqty.action)
    (hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true)
    (hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    ∃ tx c,
      typeOf (.and (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action)))
                   (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid)))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  by_cases hety : ety = env.reqty.action.ty
  case pos =>
    have hnotdesc : env.acts.descendentOf env.reqty.action uid = false := by
      cases h : env.acts.descendentOf env.reqty.action uid
      · rfl
      · simp [hety, h] at hnotmatch
    have heval : typeOf (.and (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action)))
                   (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid)))) caps env =
        .ok (TypedExpr.and
          (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty)) (.bool .tt))
          (.binaryApp .mem (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty))
                           (.lit (.entityUID uid) (.entity uid.ty)) (.bool .ff))
          (.bool .ff), ∅) := by
      simp [typeOf, typeOfLit, hvalid_action, hvalid_uid, ok, Function.comp_apply,
            typeOfUnaryApp, TypedExpr.typeOf, hety, typeOfAnd,
            typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, hcontains, hnotdesc]
    exact ⟨_, _, heval, rfl⟩
  case neg =>
    have heval : typeOf (.and (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action)))
                   (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid)))) caps env =
        .ok (TypedExpr.unaryApp (.is ety) (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty)) (.bool .ff), ∅) := by
      simp [typeOf, typeOfLit, hvalid_action, ok, Function.comp_apply,
            typeOfUnaryApp, TypedExpr.typeOf, hety, typeOfAnd]
    exact ⟨_, _, heval, rfl⟩

private theorem entityUIDs_map_lit (ls : List EntityUID) :
    (ls.map (fun e => Expr.lit (.entityUID e))).mapM entityUID? = .some ls := by
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mapM_cons, entityUID?, Option.bind_some_fun, ih, Option.pure_def]

private theorem actionUID_lit {action : EntityUID} {acts : ActionSchema} (h : acts.contains action) :
    actionUID? (.lit (.entityUID action)) acts = .some action := by
  simp [actionUID?, entityUID?, h]

private theorem entityUIDs_set_map_lit {ls : List EntityUID} :
    entityUIDs? (.set (ls.map (fun e => Expr.lit (.entityUID e)))) = .some ls := by
  unfold entityUIDs?
  exact entityUIDs_map_lit ls

private theorem typeOfInₛ_not_in_list
    {action : EntityUID} {ls : List EntityUID} {ety₁ ety₂ : EntityType} {env : TypeEnv}
    (hcontains : env.acts.contains action)
    (hnotmatch : (ls.any fun l => env.acts.descendentOf action l) = false) :
    typeOfInₛ ety₁ ety₂ (.lit (.entityUID action)) (.set (ls.map (fun e => Expr.lit (.entityUID e)))) env = .ff := by
  unfold typeOfInₛ
  rw [actionUID_lit hcontains, entityUIDs_set_map_lit]
  simp [hnotmatch]

/--
For `actionInAny ls`, the set typing may fail if the UIDs in `ls` have
incompatible entity types. We add the assumption that the set expression
successfully typechecks (which is guaranteed when the policy has previously
validated).
-/
theorem action_scope_actionInAny_typechecks_to_ff
    {ls : List EntityUID} {env : TypeEnv} {caps : Capabilities}
    {tx_set : TypedExpr} {c_set : Capabilities}
    (hnotmatch : (ls.any fun listedAction => env.acts.descendentOf env.reqty.action listedAction) = false)
    (hcontains : env.acts.contains env.reqty.action)
    (hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true)
    (hset_ok : typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps env = .ok (tx_set, c_set))
    (hset_ty : ∃ ety, tx_set.typeOf = .set (.entity ety)) :
    ∃ tx c,
      typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.set (ls.map (fun e => Expr.lit (.entityUID e))))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  obtain ⟨ety, hety⟩ := hset_ty
  have haction_ty : typeOf (.lit (.entityUID env.reqty.action)) caps env =
      .ok (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty), ∅) := by
    simp [typeOf, typeOfLit, hvalid_action, ok, Function.comp_apply]
  -- Build the proof that typeOf gives ff
  suffices h : ∃ tx c,
      typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.set (ls.map (fun e => Expr.lit (.entityUID e))))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff from h
  have hinₛ := @typeOfInₛ_not_in_list _ ls env.reqty.action.ty ety env hcontains hnotmatch
  simp only [typeOf, haction_ty, hset_ok, Except.bind_ok]
  have hety' : TypedExpr.typeOf tx_set = CedarType.set (CedarType.entity ety) := hety
  simp only [typeOfBinaryApp, TypedExpr.typeOf] at *
  simp only [hety', hinₛ, ok]
  exact ⟨_, _, rfl, rfl⟩

/-! ### Main theorem (dispatches to per-case lemmas) -/

/--
If the action scope doesn't match an action, then after substituting that action
UID, the action scope expression typechecks to `bool .ff`.
-/
theorem action_scope_typechecks_to_ff
    {policy : Policy} {env : TypeEnv} {caps : Capabilities}
    (hnotmatch : actionScopeMatchesAction env.acts env.reqty.action policy.actionScope = false)
    (hcontains : env.acts.contains env.reqty.action)
    (hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ()) :
    ∃ tx c,
      typeOf (substituteAction env.reqty.action policy.actionScope.toExpr) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  have hce_scope := checkEntities_policy_implies_actionScope hentities
  have hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true := by
    simp [hcontains]
  simp only [ActionScope.toExpr, Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType,
             substituteAction] at hce_scope ⊢
  unfold actionScopeMatchesAction at hnotmatch
  split at hnotmatch
  next => simp at hnotmatch
  next uid heq =>
    rw [heq] at hce_scope ⊢
    simp only [ActionScope.toExpr, Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars] at hce_scope ⊢
    have hne : ¬ (uid = env.reqty.action) := by
      cases huid : (uid == env.reqty.action) <;> simp_all [Bool.or_eq_false_iff]
    have ⟨_, hce_uid⟩ := checkEntities_binaryApp hce_scope
    have hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true := by
      simp only [checkEntities] at hce_uid; split at hce_uid <;> [assumption; contradiction]
    exact action_scope_eq_typechecks_to_ff hne hvalid_action hvalid_uid
  next uid heq =>
    rw [heq] at hce_scope ⊢
    simp only [ActionScope.toExpr, Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars] at hce_scope ⊢
    have ⟨_, hce_uid⟩ := checkEntities_binaryApp hce_scope
    have hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true := by
      simp only [checkEntities] at hce_uid; split at hce_uid <;> [assumption; contradiction]
    exact action_scope_mem_typechecks_to_ff hnotmatch hcontains hvalid_action hvalid_uid
  next ety heq =>
    rw [heq] at hce_scope ⊢
    simp only [ActionScope.toExpr, Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars] at hce_scope ⊢
    have hne : ¬ (ety = env.reqty.action.ty) := by
      exact fun h => by simp [h] at hnotmatch
    exact action_scope_is_typechecks_to_ff hne hvalid_action
  next ety uid heq =>
    rw [heq] at hce_scope ⊢
    simp only [ActionScope.toExpr, Scope.toExpr, Var.isEntityType, Var.inEntityUID,
               substituteAction, mapOnVars] at hce_scope ⊢
    have ⟨_, hce_inner⟩ := checkEntities_and hce_scope
    have ⟨_, hce_uid⟩ := checkEntities_binaryApp hce_inner
    have hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true := by
      simp only [checkEntities] at hce_uid; split at hce_uid <;> [assumption; contradiction]
    exact action_scope_isMem_typechecks_to_ff hnotmatch hcontains hvalid_action hvalid_uid
  next ls heq =>
    rw [heq] at hce_scope ⊢
    simp only [ActionScope.toExpr, substituteAction, mapOnVars] at hce_scope ⊢
    -- Need hset_ok and hset_ty from the precondition that the policy validated previously.
    -- These require knowing the set typechecks, which we take as sorry for now.
    sorry

end Cedar.Thm

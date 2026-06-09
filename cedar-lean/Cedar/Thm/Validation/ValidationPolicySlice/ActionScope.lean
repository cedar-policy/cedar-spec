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
      typeOfBinaryApp, typeOfEq, hne_prim]
  exact ⟨_, _, heval, rfl⟩

theorem action_scope_mem_typechecks_to_ff
    {uid : EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hnotdesc : env.acts.descendentOf env.reqty.action uid = false)
    (hcontains : env.acts.contains env.reqty.action)
    (_hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true)
    (hvalid_uid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    ∃ tx c,
      typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  have heval : typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) caps env =
      .ok (TypedExpr.binaryApp .mem
        (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty))
        (.lit (.entityUID uid) (.entity uid.ty))
        (.bool .ff), ∅) := by
    simp [typeOf, typeOfLit, hvalid_uid, ok, Function.comp_apply,
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
      simp [typeOf, typeOfLit, hvalid_uid, ok, Function.comp_apply,
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
    (hentities : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ())
    (hscope_types : ∀ (ls : List EntityUID),
      policy.actionScope = .actionInAny ls →
      ∃ tx_set c_set ety,
        typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps env = .ok (tx_set, c_set) ∧
        tx_set.typeOf = .set (.entity ety)) :
    ∃ tx c,
      typeOf (substituteAction env.reqty.action policy.actionScope.toExpr) caps env = .ok (tx, c) ∧
      tx.typeOf = .bool .ff := by
  have hce_scope := checkEntities_policy_implies_actionScope hentities
  have hvalid_action : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true := by
    simp [hcontains]
  simp only [ActionScope.toExpr, Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType] at hce_scope
  unfold actionScopeMatchesAction at hnotmatch
  split at hnotmatch
  next => simp at hnotmatch
  next uid heq =>
    rw [heq] at hce_scope ⊢
    simp only [ActionScope.toExpr, Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars] at hce_scope ⊢
    have hne : ¬ (uid = env.reqty.action) := by
      cases huid : (uid == env.reqty.action) <;> simp_all
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
    have ⟨tx_set, c_set, ety, hset_ok, hset_ty⟩ := hscope_types ls heq
    have hsub : substituteAction env.reqty.action (ActionScope.toExpr (.actionInAny ls)) =
        .binaryApp .mem (.lit (.entityUID env.reqty.action)) (.set (ls.map (fun e => .lit (.entityUID e)))) := by
      simp [ActionScope.toExpr, substituteAction, mapOnVars, List.map₁_eq_map, List.map_map,
            Function.comp]
    rw [heq, hsub]
    exact action_scope_actionInAny_typechecks_to_ff hnotmatch hcontains hvalid_action hset_ok ⟨ety, hset_ty⟩

/--
`actionScopeMatchesAction` only depends on `descendentOf`, so if two action schemas
agree on `descendentOf`, they give the same result.
-/
theorem actionScopeMatchesAction_descendentOf_congr
    {acts₁ acts₂ : ActionSchema} {action : EntityUID} {scope : ActionScope}
    (hdesc : ∀ uid₁ uid₂, acts₁.descendentOf uid₁ uid₂ = acts₂.descendentOf uid₁ uid₂) :
    actionScopeMatchesAction acts₁ action scope = actionScopeMatchesAction acts₂ action scope := by
  unfold actionScopeMatchesAction
  cases scope with
  | actionScope s =>
    cases s with
    | any => rfl
    | eq uid => simp [hdesc]
    | mem uid => exact hdesc action uid
    | is ety => rfl
    | isMem ety uid => simp [hdesc]
  | actionInAny ls =>
    simp only
    induction ls with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.any_cons, hdesc action hd, ih]

/--
`checkEntities` on a set succeeds implies `checkEntities` on each element succeeds.
-/
theorem checkEntities_set_elem {schema : Schema} {xs : List Expr} {x : Expr}
    (hce : checkEntities schema (.set xs) = .ok ())
    (hmem : x ∈ xs) :
    checkEntities schema x = .ok () := by
  simp only [checkEntities] at hce
  exact List.forM_ok_implies_all_ok' hce ⟨x, hmem⟩ (List.mem_attach xs ⟨x, hmem⟩)

/--
From `checkEntities` on a policy with `actionInAny` scope, all UIDs in the list are valid.
-/
theorem actionInAny_uids_valid_from_policy
    {policy : Policy} {env : TypeEnv} {ls : List EntityUID}
    (hce : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok ())
    (hscope : policy.actionScope = .actionInAny ls) :
    ∀ uid ∈ ls, (env.ets.isValidEntityUID uid || env.acts.contains uid) = true := by
  have hce_scope := checkEntities_policy_implies_actionScope hce
  rw [hscope] at hce_scope
  simp only [ActionScope.toExpr] at hce_scope
  have ⟨_, hce_set⟩ := checkEntities_binaryApp hce_scope
  intro uid huid
  have hmem : Expr.lit (.entityUID uid) ∈ ls.map (fun e => Expr.lit (.entityUID e)) :=
    List.mem_map.mpr ⟨uid, huid, rfl⟩
  have helem := checkEntities_set_elem hce_set hmem
  simp only [checkEntities] at helem
  split at helem
  · assumption
  · contradiction

private theorem justType_typeOf_entityUID_lit
    {uid : EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hvalid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    justType (typeOf (.lit (.entityUID uid)) caps env) =
    .ok (.lit (.entityUID uid) (.entity uid.ty)) := by
  simp [typeOf, typeOfLit, hvalid, ok, justType, Except.map]

theorem mapM_justType_entityUID_lits
    {ls : List EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hvalid : ∀ uid ∈ ls, (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
    (ls.map (fun e => Expr.lit (.entityUID e))).mapM
      (fun x => justType (typeOf x caps env)) =
    .ok (ls.map (fun uid => TypedExpr.lit (.entityUID uid) (.entity uid.ty))) := by
  induction ls with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [justType_typeOf_entityUID_lit (hvalid hd (.head _))]
    simp only [Except.bind_ok]
    rw [ih (fun uid huid => hvalid uid (.tail _ huid))]
    rfl

/--
`typeOf` on a set of entity UID literals gives the same result regardless of env/caps,
as long as all UIDs are valid in both environments.
-/
theorem typeOf_entityUID_set_deterministic
    {ls : List EntityUID} {env₁ env₂ : TypeEnv} {caps₁ caps₂ : Capabilities}
    (hvalid₁ : ∀ uid ∈ ls, (env₁.ets.isValidEntityUID uid || env₁.acts.contains uid) = true)
    (hvalid₂ : ∀ uid ∈ ls, (env₂.ets.isValidEntityUID uid || env₂.acts.contains uid) = true) :
    typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps₁ env₁ =
    typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps₂ env₂ := by
  simp only [typeOf,
    List.mapM₁_eq_mapM (fun x => justType (typeOf x caps₁ env₁)),
    List.mapM₁_eq_mapM (fun x => justType (typeOf x caps₂ env₂)),
    mapM_justType_entityUID_lits hvalid₁,
    mapM_justType_entityUID_lits hvalid₂]

private theorem foldlM_lub_entity_same {tl : List EntityUID} {ety : EntityType}
    (hsame : ∀ uid ∈ tl, uid.ty = ety) :
    (tl.map (fun uid => CedarType.entity uid.ty)).foldlM lub? (.entity ety) = some (.entity ety) := by
  induction tl with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldlM_cons]
    have hhd : hd.ty = ety := hsame hd (.head _)
    simp only [hhd, lub?, ↓reduceIte, Option.bind_some_fun]
    exact ih (fun uid huid => hsame uid (.tail _ huid))

private theorem map_typeOf_entityUID_lits {ls : List EntityUID} :
    (ls.map (fun uid => TypedExpr.lit (.entityUID uid) (.entity uid.ty))).map TypedExpr.typeOf =
    ls.map (fun uid => CedarType.entity uid.ty) := by
  simp [List.map_map, Function.comp, TypedExpr.typeOf]

/--
If a list of entity UIDs is non-empty, all UIDs are valid, and all have the same entity type,
then `typeOf` on the corresponding set expression succeeds with type `.set (.entity ety)`.
-/
theorem actionInAny_set_types
    {ls : List EntityUID} {env : TypeEnv} {caps : Capabilities}
    (hne : ls ≠ [])
    (hvalid : ∀ uid ∈ ls, (env.ets.isValidEntityUID uid || env.acts.contains uid) = true)
    (hsame : ∃ ety, ∀ uid ∈ ls, uid.ty = ety) :
    ∃ tx_set c_set ety,
      typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps env = .ok (tx_set, c_set) ∧
      tx_set.typeOf = .set (.entity ety) := by
  obtain ⟨ety, hsame⟩ := hsame
  have hmapM : (ls.map (fun e => Expr.lit (.entityUID e))).mapM (fun x => justType (typeOf x caps env)) =
      .ok (ls.map (fun uid => TypedExpr.lit (.entityUID uid) (.entity uid.ty))) :=
    mapM_justType_entityUID_lits (caps := caps) hvalid
  simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x caps env)), hmapM, Except.bind_ok]
  obtain ⟨hd, tl, hls_eq⟩ : ∃ hd tl, ls = hd :: tl := by
    cases ls with
    | nil => exact absurd rfl hne
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  subst hls_eq
  simp only [typeOfSet, List.map_cons, TypedExpr.typeOf, map_typeOf_entityUID_lits]
  have hhd : hd.ty = ety := hsame hd (.head _)
  rw [hhd]
  have hfold := foldlM_lub_entity_same (fun uid huid => hsame uid (.tail _ huid))
  rw [hfold]
  simp only [ok]
  exact ⟨_, _, ety, rfl, rfl⟩

/-! ### Extracting actionInAny well-formedness from validation success -/

private theorem typeOf_and_left_succeeds {e₁ e₂ : Expr} {c : Capabilities} {env : TypeEnv}
    {tx : TypedExpr} {c' : Capabilities}
    (h : typeOf (.and e₁ e₂) c env = .ok (tx, c')) :
    ∃ tx₁ c₁, typeOf e₁ c env = .ok (tx₁, c₁) := by
  simp only [typeOf] at h
  cases h₁ : typeOf e₁ c env with
  | error => simp [h₁] at h
  | ok val₁ => exact ⟨val₁.1, val₁.2, rfl⟩

private theorem typeOf_and_right_typed {e₁ e₂ : Expr} {c : Capabilities} {env : TypeEnv}
    {tx : TypedExpr} {c' : Capabilities}
    (h : typeOf (.and e₁ e₂) c env = .ok (tx, c'))
    (hnotff : tx.typeOf ≠ .bool .ff) :
    ∃ tx₂ c₂ caps₂, typeOf e₂ caps₂ env = .ok (tx₂, c₂) := by
  simp only [typeOf] at h
  cases h₁ : typeOf e₁ c env with
  | error => simp [h₁] at h
  | ok val₁ =>
    obtain ⟨tx₁, c₁⟩ := val₁
    simp only [h₁, Except.bind_ok] at h
    unfold typeOfAnd at h; simp only at h
    split at h
    · rename_i hff; simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      exact absurd (h.1 ▸ hff) hnotff
    · cases h₂ : typeOf e₂ (c ∪ c₁) env with
      | error => simp [h₂] at h
      | ok val₂ => exact ⟨val₂.1, val₂.2, c ∪ c₁, h₂⟩
    · simp [err] at h

private theorem typeOf_binaryApp_right_succeeds {op : BinaryOp} {e₁ e₂ : Expr}
    {c : Capabilities} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOf (.binaryApp op e₁ e₂) c env = .ok (tx, c')) :
    ∃ tx₂ c₂, typeOf e₂ c env = .ok (tx₂, c₂) := by
  simp only [typeOf] at h
  cases h₁ : typeOf e₁ c env with
  | error => simp [h₁] at h
  | ok val₁ =>
    simp only [h₁, Except.bind_ok] at h
    cases h₂ : typeOf e₂ c env with
    | error => simp [h₂] at h
    | ok val₂ => exact ⟨val₂.1, val₂.2, rfl⟩

private theorem typeOf_set_nil_fails {c : Capabilities} {env : TypeEnv} :
    ∀ tx c', typeOf (.set ([] : List Expr)) c env ≠ .ok (tx, c') := by
  intro tx c' h
  simp [typeOf, List.mapM₁, List.attach, List.mapM, List.mapM.loop,
        typeOfSet, err, pure, Except.pure] at h

private theorem lub_entity_some {ety : EntityType} {x result : CedarType}
    (h : lub? (.entity ety) x = some result) :
    x = .entity ety ∧ result = .entity ety := by
  cases x with
  | entity e => simp [lub?] at h; exact ⟨congrArg _ h.1.symm, h.2.symm⟩
  | _ => simp [lub?] at h

private theorem foldlM_lub_entity_all_eq {ety₀ : EntityType} {tys : List CedarType} {result : CedarType}
    (h : tys.foldlM lub? (.entity ety₀) = some result) :
    ∀ ty ∈ tys, ty = .entity ety₀ := by
  induction tys generalizing result with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldlM_cons] at h
    cases hlub : lub? (.entity ety₀) hd with
    | none => simp [hlub] at h
    | some mid =>
      simp only [hlub] at h
      have ⟨hhd_eq, hmid_eq⟩ := lub_entity_some hlub
      intro ty hty
      simp only [List.mem_cons] at hty
      cases hty with
      | inl heq => exact heq ▸ hhd_eq
      | inr htl => exact ih (hmid_eq ▸ h) ty htl

/--
If a policy with `actionInAny ls` validated successfully (not impossible),
then `ls` is non-empty and all UIDs have the same entity type.
-/
private theorem typecheckPolicy_implies_typeOf {policy : Policy} {env : TypeEnv} {tx : TypedExpr}
    (htc : typecheckPolicy policy env = .ok tx) :
    ∃ c', typeOf (substituteAction env.reqty.action policy.toExpr) ∅ env = .ok (tx, c') := by
  simp only [typecheckPolicy] at htc
  have h := htc; revert h
  cases htypeOf : typeOf (substituteAction env.reqty.action policy.toExpr) ∅ env with
  | error => intro h; simp at h
  | ok val =>
    intro h; obtain ⟨tx', c'⟩ := val
    simp only at h
    split at h
    · exact ⟨c', by simp_all⟩
    · simp at h

private theorem actionInAny_set_typed_from_typecheckPolicy
    {policy : Policy} {env : TypeEnv} {tx : TypedExpr} {ls : List EntityUID}
    (hscope : policy.actionScope = .actionInAny ls)
    (htc : typecheckPolicy policy env = .ok tx)
    (hnotff : tx.typeOf ≠ .bool .ff) :
    ∃ tx_set c_set caps, typeOf (.set (ls.map (fun e => Expr.lit (.entityUID e)))) caps env = .ok (tx_set, c_set) := by
  obtain ⟨c', htypeOf⟩ := typecheckPolicy_implies_typeOf htc
  have hsub : substituteAction env.reqty.action policy.toExpr =
      .and (substituteAction env.reqty.action policy.principalScope.toExpr)
           (.and (substituteAction env.reqty.action policy.actionScope.toExpr)
                 (substituteAction env.reqty.action (.and policy.resourceScope.toExpr policy.condition.toExpr))) := by
    simp [Policy.toExpr, substituteAction, mapOnVars]
  rw [hsub] at htypeOf
  obtain ⟨_, _, caps_inner, hinner⟩ := typeOf_and_right_typed htypeOf hnotff
  obtain ⟨tx_as, c_as, has⟩ := typeOf_and_left_succeeds hinner
  have has_form : substituteAction env.reqty.action (ActionScope.toExpr (.actionInAny ls)) =
      .binaryApp .mem (.lit (.entityUID env.reqty.action)) (.set (ls.map (fun e => .lit (.entityUID e)))) := by
    simp [ActionScope.toExpr, substituteAction, mapOnVars, List.map₁_eq_map, List.map_map, Function.comp]
  rw [hscope] at has; rw [has_form] at has
  obtain ⟨tx_set, c_set, hset⟩ := typeOf_binaryApp_right_succeeds has
  exact ⟨tx_set, c_set, caps_inner, hset⟩

private theorem typeOf_set_nil_fails' {c : Capabilities} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities} :
    typeOf (.set ([] : List Expr)) c env ≠ .ok (tx, c') := by
  simp [typeOf, List.mapM₁, List.attach, List.mapM, List.mapM.loop,
        typeOfSet, err, pure, Except.pure]

theorem actionInAny_wf_of_valid
    {policy : Policy} {schema : Schema} {ls : List EntityUID}
    (hscope : policy.actionScope = .actionInAny ls)
    (hvalid : typecheckPolicyWithEnvironments typecheckPolicy policy schema = .ok ()) :
    ls ≠ [] ∧ ∃ ety, ∀ uid ∈ ls, uid.ty = ety := by
  -- Extract: mapM succeeded, not all false
  simp only [typecheckPolicyWithEnvironments, Except.mapError] at hvalid
  cases hce : checkEntities schema policy.toExpr with
  | error => simp [hce] at hvalid
  | ok _ =>
    simp only [hce, Except.bind_ok] at hvalid
    cases hmapM : List.mapM (typecheckPolicy policy) schema.environments with
    | error => simp [hmapM] at hvalid
    | ok txs =>
      simp only [hmapM, Except.bind_ok, ite_eq_right_iff, allFalse] at hvalid
      -- There's some env with non-ff result
      have hnotallff : ¬ (txs.all fun tx => tx.typeOf == .bool .ff) = true :=
        fun h => absurd (hvalid h) (by simp)
      have ⟨tx, htx_mem, htx_notff⟩ : ∃ tx ∈ txs, tx.typeOf ≠ .bool .ff := by
        by_contra h
        simp only [not_exists, not_and, Classical.not_not] at h
        exact hnotallff (List.all_eq_true.mpr (fun tx htx => by simp [h tx htx]))
      -- tx came from some env
      obtain ⟨env, henv_mem, henv_ok⟩ := List.mapM_ok_implies_all_from_ok hmapM tx htx_mem
      -- From typecheckPolicy giving non-ff, the set was typed
      obtain ⟨tx_set, c_set, caps, hset_ok⟩ :=
        actionInAny_set_typed_from_typecheckPolicy hscope henv_ok htx_notff
      -- From typeOf (.set (ls.map ...)) succeeding:
      -- 1. ls ≠ [] (typeOf_set_nil_fails')
      -- 2. typeOfSet succeeded → foldlM lub? succeeded → all same type
      constructor
      · -- ls ≠ []
        intro hnil; subst hnil
        exact typeOf_set_nil_fails' hset_ok
      · -- all same type
        -- ls ≠ [] (from typeOf_set_nil_fails')
        cases ls with
        | nil => exact absurd hset_ok typeOf_set_nil_fails'
        | cons hd tl =>
          -- From checkEntities on the policy, UIDs in ls are valid
          have henv_schema := env_mem_environments_schema henv_mem
          have hce_env : checkEntities ⟨env.ets, env.acts⟩ policy.toExpr = .ok () := by
            rw [henv_schema.1, henv_schema.2]; exact hce
          have hvalid_uids := actionInAny_uids_valid_from_policy hce_env hscope
          have hmapM_det := mapM_justType_entityUID_lits (caps := caps) hvalid_uids
          simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x caps env)),
                     hmapM_det, Except.bind_ok] at hset_ok
          simp only [typeOfSet, List.map_cons, TypedExpr.typeOf, map_typeOf_entityUID_lits] at hset_ok
          cases hfold : (tl.map (fun uid => CedarType.entity uid.ty)).foldlM lub? (.entity hd.ty) with
          | none => simp [hfold, err] at hset_ok
          | some result =>
            have hall := foldlM_lub_entity_all_eq hfold
            exact ⟨hd.ty, fun uid huid => by
              cases huid with
              | head => rfl
              | tail _ htl =>
                have hmem : CedarType.entity uid.ty ∈ tl.map (fun uid => CedarType.entity uid.ty) :=
                  List.mem_map.mpr ⟨uid, htl, rfl⟩
                have := hall (.entity uid.ty) hmem
                exact CedarType.entity.inj this⟩

end Cedar.Thm

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
import Cedar.Thm.Data

/-!
This file proves that `typeOf` is congruent in the environment: if two `TypeEnv`s
agree on all queries the typechecker makes, then `typeOf` gives the same result.

This is the key enabler for `single_policy_single_change_preserved`: it shows that
for environments corresponding to unchanged actions, typechecking gives the same
result regardless of which schema's action map is used.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 12800000

theorem acts_descendentOf_agree {acts₁ acts₂ : ActionSchema}
    (hsame : ∀ uid, acts₁.contains uid = acts₂.contains uid)
    (hancestors : ∀ (action : EntityUID) (entry₁ entry₂ : ActionSchemaEntry),
      acts₁.find? action = some entry₁ →
      acts₂.find? action = some entry₂ →
      entry₁.ancestors = entry₂.ancestors) :
    ∀ uid₁ uid₂, acts₁.descendentOf uid₁ uid₂ = acts₂.descendentOf uid₁ uid₂ := by
  intro uid₁ uid₂
  simp only [ActionSchema.descendentOf]
  split
  · rfl
  · cases h₁ : acts₁.find? uid₁ with
    | none =>
      have hc₂ : acts₂.contains uid₁ = false := by
        rw [← hsame]; simp [ActionSchema.contains, h₁]
      have h₂ : acts₂.find? uid₁ = none := by
        cases h : acts₂.find? uid₁ <;> simp_all [ActionSchema.contains]
      simp [h₂]
    | some entry₁ =>
      have hc₂ : acts₂.contains uid₁ = true := by
        rw [← hsame]; simp [ActionSchema.contains, h₁]
      have ⟨entry₂, h₂⟩ : ∃ e, acts₂.find? uid₁ = some e := by
        cases h : acts₂.find? uid₁ <;> simp_all [ActionSchema.contains]
      simp [h₂, hancestors uid₁ entry₁ entry₂ h₁ h₂]

/-- Two TypeEnvs agree on all queries the typechecker makes. -/
structure TypeEnvAgreement (env₁ env₂ : TypeEnv) : Prop where
  ets_eq : env₁.ets = env₂.ets
  reqty_eq : env₁.reqty = env₂.reqty
  acts_contains : ∀ uid, env₁.acts.contains uid = env₂.acts.contains uid
  acts_actionType : ∀ ety, env₁.acts.actionType? ety = env₂.acts.actionType? ety
  acts_descendentOf : ∀ uid₁ uid₂, env₁.acts.descendentOf uid₁ uid₂ = env₂.acts.descendentOf uid₁ uid₂
  acts_maybeDescendentOf : ∀ ety₁ ety₂, env₁.acts.maybeDescendentOf ety₁ ety₂ = env₂.acts.maybeDescendentOf ety₁ ety₂

/--
If two TypeEnvs agree on all queries, `typeOf` gives the same result for any
expression and capabilities.
-/
theorem typeOf_env_congr (expr : Expr) (c : Capabilities) {env₁ env₂ : TypeEnv}
    (h : TypeEnvAgreement env₁ env₂) :
    typeOf expr c env₁ = typeOf expr c env₂ := by
  match expr with
  | .lit p => simp [typeOf, typeOfLit, h.ets_eq, h.acts_contains]
  | .var v => simp [typeOf, typeOfVar, h.reqty_eq]
  | .unaryApp op x₁ =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h]
  | .and x₁ x₂ =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_env_congr x₂ (c ∪ c₁) h]
  | .or x₁ x₂ =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_env_congr x₂ c h]
  | .ite x₁ x₂ x₃ =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h]
    congr 1; funext ⟨tx₁, c₁⟩
    simp only [typeOfIf]
    split <;> try rfl
    · rw [typeOf_env_congr x₂ (c ∪ c₁) h]
    · rw [typeOf_env_congr x₃ c h]
    · rw [typeOf_env_congr x₂ (c ∪ c₁) h, typeOf_env_congr x₃ c h]
  | .binaryApp op x₁ x₂ =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h, typeOf_env_congr x₂ c h]
    congr 1; funext ⟨tx₁, _⟩; congr 1; funext ⟨tx₂, _⟩
    unfold typeOfBinaryApp
    simp only [typeOfInₑ, typeOfInₛ, TypeEnv.descendentOf, actionUID?,
               h.ets_eq, h.acts_contains, h.acts_descendentOf,
               h.acts_maybeDescendentOf]
    split <;> simp_all [typeOfHasTag, typeOfGetTag, h.ets_eq, h.acts_actionType]
  | .hasAttr x₁ a =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h]
    congr 1; funext ⟨tx₁, _⟩
    simp [typeOfHasAttr, h.ets_eq, h.acts_actionType]
  | .getAttr x₁ a =>
    simp only [typeOf]
    rw [typeOf_env_congr x₁ c h]
    congr 1; funext ⟨tx₁, _⟩
    simp [typeOfGetAttr, h.ets_eq]
  | .set xs =>
    have hmapM : List.mapM (fun x => justType (typeOf x c env₁)) xs =
                 List.mapM (fun x => justType (typeOf x c env₂)) xs :=
      List.mapM_congr (fun x hx => congrArg justType (typeOf_env_congr x c h))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  | .record axs =>
    have hmapM : List.mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs =
                 List.mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs :=
      List.mapM_congr (fun ax hax => by
        have := List.sizeOf_snd_lt_sizeOf_list hax
        rw [typeOf_env_congr ax.snd c h])
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs,
      hmapM]
  | .call xfn xs =>
    have hmapM : List.mapM (fun x => justType (typeOf x c env₁)) xs =
                 List.mapM (fun x => justType (typeOf x c env₂)) xs :=
      List.mapM_congr (fun x hx => congrArg justType (typeOf_env_congr x c h))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  termination_by sizeOf expr

/--
Weaker agreement sufficient for congruence when `checkEntities` passes on env₁.
Requires only forward containment for `acts.contains` and `acts.actionType?`,
plus disjointness of new schema's action types from entity schema.
-/
structure WeakTypeEnvAgreement (env₁ env₂ : TypeEnv) : Prop where
  ets_eq : env₁.ets = env₂.ets
  reqty_eq : env₁.reqty = env₂.reqty
  acts_contains_fwd : ∀ uid, env₁.acts.contains uid = true → env₂.acts.contains uid = true
  acts_disjoint : ∀ uid, env₂.acts.contains uid = true → env₂.ets.isValidEntityUID uid = false
  acts_actionType : ∀ ety, env₁.acts.actionType? ety = env₂.acts.actionType? ety
  acts_descendentOf : ∀ uid₁ uid₂, env₁.acts.descendentOf uid₁ uid₂ = env₂.acts.descendentOf uid₁ uid₂
  acts_maybeDescendentOf : ∀ ety₁ ety₂, env₁.acts.maybeDescendentOf ety₁ ety₂ = env₂.acts.maybeDescendentOf ety₁ ety₂

/-- Every `TypeEnvAgreement` with disjointness is a `WeakTypeEnvAgreement`. -/
theorem TypeEnvAgreement.toWeak {env₁ env₂ : TypeEnv} (h : TypeEnvAgreement env₁ env₂)
    (hdisj : ∀ uid, env₂.acts.contains uid = true → env₂.ets.isValidEntityUID uid = false) :
    WeakTypeEnvAgreement env₁ env₂ where
  ets_eq := h.ets_eq
  reqty_eq := h.reqty_eq
  acts_contains_fwd := fun uid hc => by rw [← h.acts_contains]; exact hc
  acts_disjoint := hdisj
  acts_actionType := h.acts_actionType
  acts_descendentOf := h.acts_descendentOf
  acts_maybeDescendentOf := h.acts_maybeDescendentOf

/--
For entity UIDs valid on env₁ (via ets or acts), `acts.contains` agrees between
the two envs. This is the key lemma that makes WeakTypeEnvAgreement sufficient.
-/
private theorem acts_contains_agree_for_valid {env₁ env₂ : TypeEnv}
    (h : WeakTypeEnvAgreement env₁ env₂)
    {uid : EntityUID}
    (hvalid : (env₁.ets.isValidEntityUID uid || env₁.acts.contains uid) = true) :
    env₁.acts.contains uid = env₂.acts.contains uid := by
  cases hc : env₁.acts.contains uid with
  | true => exact (h.acts_contains_fwd uid hc).symm ▸ rfl
  | false =>
    simp [hc] at hvalid
    -- uid is valid via ets, so by disjointness of env₂, it's not in acts₂
    have hvalid₂ := hvalid; rw [h.ets_eq] at hvalid₂
    have hnotacts₂ : env₂.acts.contains uid = false := by
      by_contra habs
      simp at habs
      exact absurd hvalid₂ (by simp [h.acts_disjoint uid habs])
    rw [hnotacts₂]


/--
Conditioned congruence: if `checkEntities` passes on env₁ and the environments
have `WeakTypeEnvAgreement`, then `typeOf` gives the same result. The key insight
is that `checkEntities` guarantees all literal entity UIDs are valid on env₁, so
forward containment + disjointness suffices to derive full agreement.
-/
private theorem checkEntities_pair {schema : Schema} {e₁ e₂ : Expr}
    (h : (do checkEntities schema e₁; checkEntities schema e₂) = .ok ()) :
    checkEntities schema e₁ = .ok () ∧ checkEntities schema e₂ = .ok () := by
  cases h₁ : checkEntities schema e₁ with
  | error e => simp [h₁] at h
  | ok _ => simp [h₁] at h; exact ⟨rfl, h⟩

/--
`actionUID?` agrees between two envs under `WeakTypeEnvAgreement` for expressions
whose entity UIDs are all valid on env₁.
-/
private theorem actionUID_agree {env₁ env₂ : TypeEnv} (h : WeakTypeEnvAgreement env₁ env₂)
    (x : Expr) (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ x = .ok ()) :
    actionUID? x env₁.acts = actionUID? x env₂.acts := by
  unfold actionUID?
  cases heu : entityUID? x with
  | none => simp
  | some uid =>
    have hvalid : (env₁.ets.isValidEntityUID uid || env₁.acts.contains uid) = true := by
      have hx_form : x = .lit (.entityUID uid) := by
        cases x with
        | lit p => cases p with
          | entityUID u => simp [entityUID?] at heu; subst heu; rfl
          | _ => simp [entityUID?] at heu
        | _ => simp [entityUID?] at heu
      subst hx_form
      simp only [checkEntities] at hce
      split at hce
      · assumption
      · contradiction
    have heq := acts_contains_agree_for_valid h hvalid
    simp [heq]

theorem typeOf_env_congr_weak (expr : Expr) (c : Capabilities) {env₁ env₂ : TypeEnv}
    (h : WeakTypeEnvAgreement env₁ env₂)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ expr = .ok ()) :
    typeOf expr c env₁ = typeOf expr c env₂ := by
  match expr with
  | .lit (.bool true) => simp [typeOf, typeOfLit]
  | .lit (.bool false) => simp [typeOf, typeOfLit]
  | .lit (.int _) => simp [typeOf, typeOfLit]
  | .lit (.string _) => simp [typeOf, typeOfLit]
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at hce
    split at hce
    · rename_i hvalid
      have hcontains := acts_contains_agree_for_valid h hvalid
      simp [typeOf, typeOfLit, h.ets_eq, hcontains]
    · contradiction
  | .var v => simp [typeOf, typeOfVar, h.reqty_eq]
  | .unaryApp (.is ety) x₁ =>
    simp only [checkEntities] at hce
    split at hce
    · simp only [typeOf]
      rw [typeOf_env_congr_weak x₁ c h hce]
    · contradiction
  | .unaryApp (.not) x₁ | .unaryApp (.neg) x₁ | .unaryApp (.like _) x₁ | .unaryApp (.isEmpty) x₁ =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁]
  | .and x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_env_congr_weak x₂ (c ∪ c₁) h hce₂]
  | .or x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_env_congr_weak x₂ c h hce₂]
  | .ite x₁ x₂ x₃ =>
    unfold checkEntities at hce
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      cases h₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ <;> simp_all
    have hce₂ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₂ = .ok () := by
      cases h₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ <;> simp_all
      cases h₂ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₂ <;> simp_all
    have hce₃ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₃ = .ok () := by
      simp [hce₁, hce₂] at hce; exact hce
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    simp only [typeOfIf]
    split <;> try rfl
    · rw [typeOf_env_congr_weak x₂ (c ∪ c₁) h hce₂]
    · rw [typeOf_env_congr_weak x₃ c h hce₃]
    · rw [typeOf_env_congr_weak x₂ (c ∪ c₁) h hce₂, typeOf_env_congr_weak x₃ c h hce₃]
  | .binaryApp op x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁, typeOf_env_congr_weak x₂ c h hce₂]
    congr 1; funext ⟨tx₁, _⟩; congr 1; funext ⟨tx₂, _⟩
    unfold typeOfBinaryApp
    simp only [typeOfInₑ, typeOfInₛ, TypeEnv.descendentOf,
               actionUID_agree h x₁ hce₁,
               h.ets_eq, h.acts_descendentOf, h.acts_maybeDescendentOf]
    split <;> simp_all [typeOfHasTag, typeOfGetTag, h.ets_eq, h.acts_actionType]
  | .hasAttr x₁ a =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁]
    congr 1; funext ⟨tx₁, _⟩
    simp [typeOfHasAttr, h.ets_eq, h.acts_actionType]
  | .getAttr x₁ a =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_env_congr_weak x₁ c h hce₁]
    congr 1; funext ⟨tx₁, _⟩
    simp [typeOfGetAttr, h.ets_eq]
  | .set xs =>
    have hce_all : ∀ x ∈ xs, checkEntities ⟨env₁.ets, env₁.acts⟩ x = .ok () := by
      intro x hx
      have hce' : xs.attach.forM (fun ⟨x, _⟩ => checkEntities ⟨env₁.ets, env₁.acts⟩ x) = .ok () := by
        simp only [checkEntities] at hce; exact hce
      have := List.forM_ok_implies_all_ok' hce' ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩)
      simpa using this
    have hmapM : List.mapM (fun x => justType (typeOf x c env₁)) xs =
                 List.mapM (fun x => justType (typeOf x c env₂)) xs :=
      List.mapM_congr (fun x hx => congrArg justType (typeOf_env_congr_weak x c h (hce_all x hx)))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  | .record axs =>
    have hce_all : ∀ ax ∈ axs, checkEntities ⟨env₁.ets, env₁.acts⟩ ax.snd = .ok () := by
      intro ax hax
      have hce' := hce; simp only [checkEntities] at hce'
      have hmem : ⟨ax, List.sizeOf_snd_lt_sizeOf_list hax⟩ ∈ axs.attach₂ := by
        simp only [List.attach₂, List.mem_pmap]
        exact ⟨ax, hax, rfl⟩
      exact List.forM_ok_implies_all_ok' hce' _ hmem
    have hmapM : List.mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs =
                 List.mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs :=
      List.mapM_congr (fun ax hax => by
        have := List.sizeOf_snd_lt_sizeOf_list hax
        rw [typeOf_env_congr_weak ax.snd c h (hce_all ax hax)])
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs,
      hmapM]
  | .call xfn xs =>
    have hce_all : ∀ x ∈ xs, checkEntities ⟨env₁.ets, env₁.acts⟩ x = .ok () := by
      intro x hx
      have hce' : xs.attach.forM (fun ⟨x, _⟩ => checkEntities ⟨env₁.ets, env₁.acts⟩ x) = .ok () := by
        simp only [checkEntities] at hce; exact hce
      have := List.forM_ok_implies_all_ok' hce' ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩)
      simpa using this
    have hmapM : List.mapM (fun x => justType (typeOf x c env₁)) xs =
                 List.mapM (fun x => justType (typeOf x c env₂)) xs :=
      List.mapM_congr (fun x hx => congrArg justType (typeOf_env_congr_weak x c h (hce_all x hx)))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  termination_by sizeOf expr

end Cedar.Thm

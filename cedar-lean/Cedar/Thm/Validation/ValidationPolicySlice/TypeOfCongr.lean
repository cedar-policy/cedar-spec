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

end Cedar.Thm

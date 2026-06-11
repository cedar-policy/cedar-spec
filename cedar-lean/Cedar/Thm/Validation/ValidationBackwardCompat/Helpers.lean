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

import Cedar.Thm.Validation.ValidationPolicySlice
import Cedar.Thm.WellTyped.Expr.WF
import Cedar.Thm.Data

/-!
# Backward Compatibility for Entity Schema Extensions

Adding new entity types to the entity schema never invalidates existing policies.
This is because:
1. `checkEntities` is monotone in the entity schema (more valid UIDs/types)
2. `typeOf` only queries the entity schema for types that exist in the old schema
   (validated by `checkEntities` on the old schema)
3. The environments have the same reqtys (since actions are unchanged)

This gives a standalone backward-compatibility theorem that is independent of the
validation slicing proof.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 12800000

/-! ## Core helpers -/

theorem actionType_implies_contains {acts : ActionSchema} {ety : EntityType}
    (h : acts.actionType? ety = true) :
    ∃ uid, acts.contains uid = true ∧ uid.ty = ety := by
  simp only [ActionSchema.actionType?, Set.any] at h
  rw [List.any_eq_true] at h
  obtain ⟨uid, hmem, hty⟩ := h
  exact ⟨uid, Map.in_keys_iff_contains.mp hmem, beq_iff_eq.mp hty⟩

/-- Convert `EntityType.WellFormed` (Prop) to `ets.contains ∨ acts.actionType?` (Bool). -/
theorem entityType_wf_to_bool {env : TypeEnv} {ety : EntityType}
    (h : EntityType.WellFormed env ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType] at h
  cases h with
  | inl h => exact Or.inl h
  | inr h =>
    right
    obtain ⟨uid, hc, heq⟩ := h
    simp only [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
    exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩

/-! ## Entity schema forward preservation -/

theorem ets_find_eq_of_contains
    {ets₁ ets₂ : EntitySchema}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    {ety : EntityType}
    (hc : ets₁.contains ety) :
    ets₁.find? ety = ets₂.find? ety := by
  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨entry, hf⟩ := hc
  rw [hf, hfwd ety entry hf]

theorem ets_contains_of_find
    {ets : EntitySchema} {ety : EntityType} {entry : EntitySchemaEntry}
    (hf : ets.find? ety = some entry) :
    ets.contains ety := by
  simp [EntitySchema.contains, hf]


/-! ## Type invariant from existing typechecked_has_well_formed_type -/

/-- Entity types produced by `typeOf` are in ets or are action types. -/
theorem typeOf_entity_type_in_ets (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities} {ety : EntityType}
    (hwf : env.WellFormed)
    (hok : typeOf expr c env = .ok (tx, c'))
    (hty : tx.typeOf = .entity ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  have h := typechecked_has_well_formed_type hwf hok
  rw [hty] at h; cases h with | entity_wf h => exact entityType_wf_to_bool h

/-! ## typeOf congruence under entity schema extension -/

/--
If `env₁.ets.find?` gives `none` and `ety` is an action type, then
`env₂.ets.find?` also gives `none` (by disjointness on env₂).
-/
theorem ets_find_none_of_actionType
    {ets : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hdisjoint : ∀ uid, acts.contains uid = true → ¬ ets.contains uid.ty)
    (hact : acts.actionType? ety = true) :
    ets.find? ety = none := by
  obtain ⟨uid, hcontains, heq⟩ := actionType_implies_contains hact
  cases hf : ets.find? ety with
  | none => rfl
  | some entry =>
    have hc : ets.contains ety := ets_contains_of_find hf
    exact absurd (heq ▸ hc) (hdisjoint uid hcontains)

theorem ets_find_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.find? ety = ets₂.find? ety := by
  cases hinv with
  | inl hc => exact ets_find_eq_of_contains hfwd hc
  | inr hact =>
    have h₁ : ets₁.find? ety = none := by
      obtain ⟨uid, hcontains, heq⟩ := actionType_implies_contains hact
      cases hf : ets₁.find? ety with
      | none => rfl
      | some entry =>
        exact absurd (heq ▸ ets_contains_of_find (hfwd ety entry hf)) (hdisjoint₂ uid hcontains)
    rw [h₁, ets_find_none_of_actionType hdisjoint₂ hact]

theorem ets_attrs_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.attrs? ety = ets₂.attrs? ety := by
  simp only [EntitySchema.attrs?, ets_find_agree hfwd hdisjoint₂ hinv]

theorem ets_tags_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.tags? ety = ets₂.tags? ety := by
  simp only [EntitySchema.tags?, ets_find_agree hfwd hdisjoint₂ hinv]

theorem descendentOf_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety₁ ety₂ : EntityType}
    {reqty : RequestType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety₁ ∨ acts.actionType? ety₁) :
    TypeEnv.descendentOf ⟨ets₁, acts, reqty⟩ ety₁ ety₂ =
    TypeEnv.descendentOf ⟨ets₂, acts, reqty⟩ ety₁ ety₂ := by
  simp only [TypeEnv.descendentOf]
  split
  · rfl
  · rw [ets_find_agree hfwd hdisjoint₂ hinv]

/-- Two environments where env₂ extends env₁'s entity schema. -/
structure EtsExtension (env₁ env₂ : TypeEnv) : Prop where
  reqty_eq : env₁.reqty = env₂.reqty
  acts_eq : env₁.acts = env₂.acts
  ets_fwd : ∀ ety entry, env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry
  disjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty
  wf₁ : env₁.WellFormed

theorem disjoint_backward
    {env₁ env₂ : TypeEnv}
    (hets_fwd : ∀ ety entry, env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry)
    (hacts : env₁.acts = env₂.acts)
    (hdisjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty) :
    ∀ uid, env₁.acts.contains uid = true → ¬ env₁.ets.contains uid.ty := by
  intro uid hc hc₁
  have hc₂ : env₂.ets.contains uid.ty := by
    simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
    obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩
  exact hdisjoint₂ uid (hacts ▸ hc) hc₂

theorem isValidEntityUID_fwd
    {ets₁ ets₂ : EntitySchema}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    {uid : EntityUID}
    (hv : ets₁.isValidEntityUID uid = true) :
    ets₂.isValidEntityUID uid = true := by
  simp only [EntitySchema.isValidEntityUID] at hv ⊢
  cases hf : ets₁.find? uid.ty with
  | none => simp [hf] at hv
  | some entry => rw [hfwd uid.ty entry hf]; simp [hf] at hv; exact hv

theorem isValidOrContains_fwd
    {ets₁ ets₂ : EntitySchema} {acts₁ acts₂ : ActionSchema}
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hacts : acts₁ = acts₂)
    {uid : EntityUID}
    (hv : (ets₁.isValidEntityUID uid || acts₁.contains uid) = true) :
    (ets₂.isValidEntityUID uid || acts₂.contains uid) = true := by
  cases hv₁ : ets₁.isValidEntityUID uid
  · simp [hv₁] at hv; rw [← hacts]; simp [hv]
  · simp [isValidEntityUID_fwd hets_fwd hv₁]

theorem contains_or_actionType_fwd
    {ets₁ ets₂ : EntitySchema} {acts₁ acts₂ : ActionSchema}
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hacts : acts₁ = acts₂)
    {ety : EntityType}
    (hv : (ets₁.contains ety || acts₁.actionType? ety) = true) :
    (ets₂.contains ety || acts₂.actionType? ety) = true := by
  cases hc : ets₁.contains ety
  · simp [hc] at hv; rw [← hacts]; simp [hv]
  · simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨entry, hf⟩ := hc
    simp [EntitySchema.contains, hets_fwd ety entry hf]

theorem checkEntities_pair' {schema : Schema} {e₁ e₂ : Expr}
    (h : (do checkEntities schema e₁; checkEntities schema e₂) = .ok ()) :
    checkEntities schema e₁ = .ok () ∧ checkEntities schema e₂ = .ok () := by
  cases h₁ : checkEntities schema e₁ with
  | error e => simp [h₁] at h
  | ok _ => simp [h₁] at h; exact ⟨rfl, h⟩


end Cedar.Thm

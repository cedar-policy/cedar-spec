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
import Cedar.Thm.Validation.ValidationPolicySlice.TypeOfCongr
import Cedar.Thm.Validation.ValidationPolicySlice.CheckEntities
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.EnvironmentValidation
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

/-! ## Helper: actionType? implies there exists a containing uid -/

private theorem actionType_implies_contains {acts : ActionSchema} {ety : EntityType}
    (h : acts.actionType? ety = true) :
    ∃ uid, acts.contains uid = true ∧ uid.ty = ety := by
  simp only [ActionSchema.actionType?, Set.any] at h
  rw [List.any_eq_true] at h
  obtain ⟨uid, hmem, hty⟩ := h
  exact ⟨uid, Map.in_keys_iff_contains.mp hmem, beq_iff_eq.mp hty⟩

/-! ## Helper lemmas for entity schema forward preservation -/

private theorem ets_attrs_eq_of_contains
    {ets₁ ets₂ : EntitySchema}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    {ety : EntityType}
    (hc : ets₁.contains ety) :
    ets₁.attrs? ety = ets₂.attrs? ety := by
  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨entry, hf⟩ := hc
  simp only [EntitySchema.attrs?, hf, hfwd ety entry hf]

private theorem ets_tags_eq_of_contains
    {ets₁ ets₂ : EntitySchema}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    {ety : EntityType}
    (hc : ets₁.contains ety) :
    ets₁.tags? ety = ets₂.tags? ety := by
  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨entry, hf⟩ := hc
  simp only [EntitySchema.tags?, hf, hfwd ety entry hf]

private theorem ets_find_eq_of_contains
    {ets₁ ets₂ : EntitySchema}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    {ety : EntityType}
    (hc : ets₁.contains ety) :
    ets₁.find? ety = ets₂.find? ety := by
  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨entry, hf⟩ := hc
  rw [hf, hfwd ety entry hf]

private theorem ets_contains_of_find
    {ets : EntitySchema} {ety : EntityType} {entry : EntitySchemaEntry}
    (hf : ets.find? ety = some entry) :
    ets.contains ety := by
  simp [EntitySchema.contains, hf]

private theorem ets_contains_of_attrs
    {ets : EntitySchema} {ety : EntityType} {rty : RecordType}
    (h : ets.attrs? ety = some rty) :
    ets.contains ety := by
  simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h
  obtain ⟨entry, hf, _⟩ := h
  exact ets_contains_of_find hf

private theorem ets_contains_of_tags
    {ets : EntitySchema} {ety : EntityType} {t : Option CedarType}
    (h : ets.tags? ety = some t) :
    ets.contains ety := by
  simp only [EntitySchema.tags?] at h
  cases hf : ets.find? ety with
  | none => simp [hf] at h
  | some entry => exact ets_contains_of_find hf


/-! ## Helpers: entity types from schema are well-formed -/

private theorem entity_type_wf_from_tags
    {env : TypeEnv} {ety_parent : EntityType} {ty : CedarType} {ety : EntityType}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (htags : env.ets.tags? ety_parent = some (some ty))
    (hty : ty = .entity ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htags
  obtain ⟨entry, hfind_e, htags_eq⟩ := htags
  have hentry_wf := hets_wf.2 ety_parent entry hfind_e
  cases entry with
  | standard s =>
    simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
    have ⟨_, _, _, _, htag_wf⟩ := hentry_wf
    simp [EntitySchemaEntry.tags?] at htags_eq
    have hsome_ty := htag_wf ty htags_eq
    have htype_wf : CedarType.WellFormed env (.entity ety) := by rw [← hty]; exact hsome_ty.1
    cases htype_wf with
    | entity_wf hwf =>
      simp [EntityType.WellFormed, ActionSchema.IsActionEntityType] at hwf
      cases hwf with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨uid, hc, heq⟩ := h
        simp [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
        exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩
  | enum _ =>
    simp [EntitySchemaEntry.tags?] at htags_eq

private theorem entity_type_wf_from_attrs
    {env : TypeEnv} {ety_parent : EntityType} {rty : RecordType} {a : Attr}
    {qty : Qualified CedarType} {ety : EntityType}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (hattrs : env.ets.attrs? ety_parent = some rty)
    (hfind_a : rty.find? a = some qty)
    (hty : qty.getType = .entity ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  -- attrs? = (find? ety_parent).map _.attrs, so find? ety_parent = some entry
  simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
  obtain ⟨entry, hfind_e, hattrs_eq⟩ := hattrs
  have hentry_wf := hets_wf.2 ety_parent entry hfind_e
  -- Get (CedarType.record entry.attrs).WellFormed env
  have hwf_record : (CedarType.record rty).WellFormed env := by
    cases entry with
    | standard s =>
      simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
      have ⟨_, _, hwf, _⟩ := hentry_wf
      simpa [EntitySchemaEntry.attrs, ← hattrs_eq] using hwf
    | enum _ =>
      simp [EntitySchemaEntry.attrs] at hattrs_eq
      subst hattrs_eq
      exact .record_wf (by constructor) (by intro _ _ h; simp [Map.find?] at h)
  -- Extract: qty is well-formed → its type is well-formed → entity type well-formed
  cases hwf_record with
  | record_wf _ hattr_wf =>
    have hqty_wf := hattr_wf a qty hfind_a
    have htype_wf : CedarType.WellFormed env (.entity ety) := by
      rw [← hty]
      cases qty with
      | required ty => cases hqty_wf with | required_wf h => exact h
      | optional ty => cases hqty_wf with | optional_wf h => exact h
    cases htype_wf with
    | entity_wf hwf =>
      simp [EntityType.WellFormed, ActionSchema.IsActionEntityType] at hwf
      cases hwf with
      | inl h => left; exact h
      | inr h =>
        right
        obtain ⟨uid, hc, heq⟩ := h
        simp [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
        exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩

/-! ## Helper: entity types from well-formed record types -/

private theorem entity_type_wf_from_record_wf
    {env : TypeEnv} {rty : RecordType} {a : Attr}
    {qty : Qualified CedarType} {ety : EntityType}
    (hwf : (CedarType.record rty).WellFormed env)
    (hfind_a : rty.find? a = some qty)
    (hty : qty.getType = .entity ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  cases hwf with
  | record_wf _ hattr_wf =>
    have hqty_wf := hattr_wf a qty hfind_a
    have htype_wf : CedarType.WellFormed env (.entity ety) := by
      rw [← hty]
      cases qty with
      | required ty => cases hqty_wf with | required_wf h => exact h
      | optional ty => cases hqty_wf with | optional_wf h => exact h
    cases htype_wf with
    | entity_wf hwf =>
      simp [EntityType.WellFormed, ActionSchema.IsActionEntityType] at hwf
      cases hwf with
      | inl h => left; exact h
      | inr h =>
        right
        obtain ⟨uid, hc, heq⟩ := h
        simp [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
        exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩

private theorem lubQualifiedType_entity_implies_input_entity
    {qty₁ qty₂ qty : Qualified CedarType} {ety : EntityType}
    (hlub : lubQualifiedType qty₁ qty₂ = some qty)
    (hty : qty.getType = .entity ety) :
    qty₁.getType = .entity ety := by
  unfold lubQualifiedType at hlub
  split at hlub <;> try (simp at hlub)
  · rename_i ty₁ ty₂
    cases hlu : lub? ty₁ ty₂ <;> simp [hlu] at hlub
    subst hlub; simp [Qualified.getType] at hty
    unfold lub? at hlu
    split at hlu
    · simp [lubBool] at hlu; subst hlu; simp at hty
    · rename_i s₁ s₂; cases h : @lub? s₁ s₂ <;> simp [h] at hlu; subst hlu; simp at hty
    · rename_i r₁ r₂; cases h : lubRecordType r₁ r₂ <;> simp [h] at hlu; subst hlu; simp at hty
    · split at hlu
      · simp at hlu; subst hlu; simp [Qualified.getType, hty]
      · simp at hlu
  · rename_i ty₁ ty₂
    cases hlu : lub? ty₁ ty₂ <;> simp [hlu] at hlub
    subst hlub; simp [Qualified.getType] at hty
    unfold lub? at hlu
    split at hlu
    · simp [lubBool] at hlu; subst hlu; simp at hty
    · rename_i s₁ s₂; cases h : @lub? s₁ s₂ <;> simp [h] at hlu; subst hlu; simp at hty
    · rename_i r₁ r₂; cases h : lubRecordType r₁ r₂ <;> simp [h] at hlu; subst hlu; simp at hty
    · split at hlu
      · simp at hlu; subst hlu; simp [Qualified.getType, hty]
      · simp at hlu

/-! ## lub preserves well-formedness -/

private theorem lubRecordType_preserves_keys
    {r₁ r₂ r : List (Attr × Qualified CedarType)}
    (hlub : lubRecordType r₁ r₂ = some r) :
    r.map Prod.fst = r₁.map Prod.fst := by
  induction r₁ generalizing r₂ r with
  | nil =>
    cases r₂ <;> simp [lubRecordType] at hlub
    subst hlub; simp
  | cons hd₁ tl₁ ih =>
    cases r₂ with
    | nil => simp [lubRecordType] at hlub
    | cons hd₂ tl₂ =>
      unfold lubRecordType at hlub
      cases hk : (hd₁.fst != hd₂.fst) with
      | true => simp [hk] at hlub
      | false =>
        simp [hk] at hlub
        simp [bne_iff_ne, ne_eq, Decidable.not_not] at hk
        cases hq : lubQualifiedType hd₁.snd hd₂.snd <;> simp [hq] at hlub
        cases hr : lubRecordType tl₁ tl₂ <;> simp [hr] at hlub
        subst hlub; simp [hk, ih hr]

private theorem sortedBy_of_same_keys {α β₁ β₂ : Type} [LT α]
    {r₁ : List (α × β₁)} {r : List (α × β₂)}
    (hsorted : r₁.SortedBy Prod.fst)
    (hkeys : r.map Prod.fst = r₁.map Prod.fst) :
    r.SortedBy Prod.fst := by
  induction r generalizing r₁ with
  | nil => exact .nil
  | cons hd tl ih =>
    cases r₁ with
    | nil => simp at hkeys
    | cons hd₁ tl₁ =>
      simp at hkeys
      obtain ⟨hfst, htl_keys⟩ := hkeys
      cases tl with
      | nil => exact .cons_nil
      | cons hd' tl' =>
        cases tl₁ with
        | nil => simp at htl_keys
        | cons hd₁' tl₁' =>
          simp at htl_keys
          obtain ⟨hfst', htl'_keys⟩ := htl_keys
          have hsorted_tl₁ : (hd₁' :: tl₁').SortedBy Prod.fst := by
            cases hsorted with
            | cons_cons _ h => exact h
          apply List.SortedBy.cons_cons
          · rw [hfst, hfst']
            cases hsorted with
            | cons_cons hlt _ => exact hlt
          · exact ih hsorted_tl₁ (by simp [hfst', htl'_keys])

private theorem lubRecordType_preserves_map_wf
    {r₁ r₂ r : List (Attr × Qualified CedarType)}
    (hwf : Map.WellFormed (Map.mk r₁))
    (hlub : lubRecordType r₁ r₂ = some r) :
    Map.WellFormed (Map.mk r) := by
  rw [Map.wf_iff_sorted]; simp only [Map.toList_mk_id]
  have hsorted := (Map.wf_iff_sorted.mp hwf)
  simp only [Map.toList_mk_id] at hsorted
  exact sortedBy_of_same_keys hsorted (lubRecordType_preserves_keys hlub)

private theorem lub_preserves_wf_left {env : TypeEnv} {ty₁ ty₂ ty : CedarType}
    (hwf : CedarType.WellFormed env ty₁)
    (hlub : lub? ty₁ ty₂ = some ty) :
    CedarType.WellFormed env ty := by
  unfold lub? at hlub
  split at hlub
  · -- bool case
    simp [lubBool] at hlub; subst hlub; exact .bool_wf
  · -- set case
    rename_i s₁ s₂
    cases hlu : @lub? s₁ s₂ <;> simp [hlu] at hlub
    subst hlub; cases hwf with | set_wf h => exact .set_wf (lub_preserves_wf_left h hlu)
  · -- record case
    rename_i r₁ r₂
    cases hlubr : lubRecordType r₁ r₂ <;> simp [hlubr] at hlub
    subst hlub; cases hwf with
    | record_wf hwf_map hattr_wf =>
      apply CedarType.WellFormed.record_wf
      · exact lubRecordType_preserves_map_wf hwf_map hlubr
      · intro attr qty hfind
        have hlub_rel := lubRecordType_is_lub_of_record_types hlubr
        have ⟨qty₁', qty₂', hfind₁, _, hlubq⟩ := lubRecord_find_implies_find hlub_rel hfind
        have hqty₁_wf := hattr_wf attr qty₁' hfind₁
        -- qty₁' is WF. Need to show qty (= lubQualifiedType qty₁' qty₂') is WF.
        -- The inner type of qty₁' is strictly smaller than ty₁ = .record (Map.mk r₁).
        cases qty₁' with
        | required ty_inner =>
          cases hqty₁_wf with
          | required_wf hwf_inner =>
            cases qty₂' with
            | required ty_inner₂ =>
              simp [lubQualifiedType] at hlubq
              cases hlu : lub? ty_inner ty_inner₂ <;> simp [hlu] at hlubq
              subst hlubq
              have _hsz : sizeOf ty_inner < sizeOf (CedarType.record (Map.mk r₁)) :=
                sizeOf_attr_type_lt_sizeOf_record_type rfl hfind₁
              exact .required_wf (lub_preserves_wf_left hwf_inner hlu)
            | optional _ => simp [lubQualifiedType] at hlubq
        | optional ty_inner =>
          cases hqty₁_wf with
          | optional_wf hwf_inner =>
            cases qty₂' with
            | optional ty_inner₂ =>
              simp [lubQualifiedType] at hlubq
              cases hlu : lub? ty_inner ty_inner₂ <;> simp [hlu] at hlubq
              subst hlubq
              have _hsz : sizeOf ty_inner < sizeOf (CedarType.record (Map.mk r₁)) :=
                sizeOf_attr_type_lt_sizeOf_record_type rfl hfind₁
              exact .optional_wf (lub_preserves_wf_left hwf_inner hlu)
            | required _ => simp [lubQualifiedType] at hlubq
  · -- catch-all case
    split at hlub
    · simp at hlub; subst hlub; exact hwf
    · simp at hlub
  termination_by sizeOf ty₁

/-! ## Type invariant: typeOf produces well-formed types -/

/--
`typeOf` always produces well-formed types. This is the key type soundness property
needed for backward compatibility: entity types in the output are always known to
the entity schema or are action types.
-/
private theorem actionType_implies_IsActionEntityType {acts : ActionSchema} {ety : EntityType}
    (h : acts.actionType? ety = true) :
    acts.IsActionEntityType ety := by
  simp [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨uid, hmem, heq⟩ := h
  exact ⟨uid, Map.in_keys_iff_contains.mp hmem, heq⟩

private theorem isValidEntityUID_implies_contains_ty {ets : EntitySchema} {uid : EntityUID}
    (h : ets.isValidEntityUID uid = true) :
    ets.contains uid.ty := by
  simp only [EntitySchema.isValidEntityUID] at h
  cases hf : ets.find? uid.ty with
  | none => simp [hf] at h
  | some _ => simp [EntitySchema.contains, hf]

private theorem typeOf_produces_wf_type (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (hce : checkEntities ⟨env.ets, env.acts⟩ expr = .ok ())
    (hok : typeOf expr c env = .ok (tx, c'))
    (hdisjoint : ∀ uid, env.acts.contains uid = true → ¬ env.ets.contains uid.ty)
    (hreqty_action : env.acts.contains env.reqty.action = true)
    (hreqty_principal : env.ets.contains env.reqty.principal ∨ env.acts.actionType? env.reqty.principal)
    (hreqty_resource : env.ets.contains env.reqty.resource ∨ env.acts.actionType? env.reqty.resource)
    (hctx_wf : (CedarType.record env.reqty.context).WellFormed env) :
    CedarType.WellFormed env tx.typeOf := by
  match expr with
  | .lit (.bool true) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .bool_wf
  | .lit (.bool false) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .bool_wf
  | .lit (.int _) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .int_wf
  | .lit (.string _) =>
    simp [typeOf, typeOfLit, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]; exact .string_wf
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at hce
    split at hce
    · rename_i hvalid
      simp [typeOf, typeOfLit, hvalid, ok, Function.comp] at hok
      obtain ⟨h₁, _⟩ := hok; subst h₁
      simp [TypedExpr.typeOf]
      apply CedarType.WellFormed.entity_wf
      simp [EntityType.WellFormed]
      cases hv : env.ets.isValidEntityUID uid
      · simp [hv] at hvalid
        right
        exact ⟨uid, hvalid, rfl⟩
      · left
        exact isValidEntityUID_implies_contains_ty hv
    · contradiction
  | .var .principal =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp [EntityType.WellFormed]
    cases hreqty_principal with
    | inl h => left; exact h
    | inr h => right; exact actionType_implies_IsActionEntityType h
  | .var .action =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp [EntityType.WellFormed]
    right; exact ⟨env.reqty.action, hreqty_action, rfl⟩
  | .var .resource =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp [EntityType.WellFormed]
    cases hreqty_resource with
    | inl h => left; exact h
    | inr h => right; exact actionType_implies_IsActionEntityType h
  | .var .context =>
    simp [typeOf, typeOfVar, ok, Function.comp] at hok
    obtain ⟨h₁, _⟩ := hok; subst h₁
    simp [TypedExpr.typeOf]
    exact hctx_wf
  | .ite x₁ x₂ x₃ =>
    unfold checkEntities at hce
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      cases h₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ <;> simp_all
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      cases h₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ <;> simp_all
      cases h₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ <;> simp_all
    have hce₃ : checkEntities ⟨env.ets, env.acts⟩ x₃ = .ok () := by
      simp [hce₁, hce₂] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfIf] at hok
      split at hok
      · -- .bool .tt: result is from x₂
        cases h₂ : typeOf x₂ (c ∪ c₁) env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂, ok] at hok
          obtain ⟨h, _⟩ := hok; subst h
          simp [TypedExpr.typeOf]
          exact typeOf_produces_wf_type x₂ (c ∪ c₁) hets_wf hce₂ h₂ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool .ff: result is from x₃
        cases h₃ : typeOf x₃ c env with
        | error => simp [h₃] at hok
        | ok val₃ =>
          obtain ⟨tx₃, c₃⟩ := val₃
          simp [h₃, ok] at hok
          obtain ⟨h, _⟩ := hok; subst h
          simp [TypedExpr.typeOf]
          exact typeOf_produces_wf_type x₃ c hets_wf hce₃ h₃ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool .anyBool: result is lub? of x₂.typeOf and x₃.typeOf
        cases h₂ : typeOf x₂ (c ∪ c₁) env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          cases h₃ : typeOf x₃ c env with
          | error => simp [h₃] at hok
          | ok val₃ =>
            obtain ⟨tx₃, c₃⟩ := val₃
            simp [h₃] at hok
            split at hok
            · rename_i ty hlub
              simp [ok] at hok
              obtain ⟨h, _⟩ := hok; subst h
              simp [TypedExpr.typeOf]
              have hwf₂ := typeOf_produces_wf_type x₂ (c ∪ c₁) hets_wf hce₂ h₂ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
              exact lub_preserves_wf_left hwf₂ hlub
            · simp [err] at hok
      · simp [err] at hok
  | .and x₁ x₂ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce
      cases h : checkEntities ⟨env.ets, env.acts⟩ x₁ with
      | error => simp [h] at hce
      | ok u => cases u; rfl
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      unfold checkEntities at hce; simp [hce₁] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfAnd] at hok
      split at hok
      · -- .bool .ff: result is tx₁ itself which has type .bool .ff
        simp [ok] at hok
        obtain ⟨h, _⟩ := hok; subst h
        simp [TypedExpr.typeOf]
        have := typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
        exact this
      · -- .bool ty₁: typeOfAnd continued
        cases h₂ : typeOf x₂ (c ∪ c₁) env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          -- hok now contains the result of matching on tx₂.typeOf
          -- All successful arms produce (.bool _) as result type
          split at hok
          all_goals (simp [ok, err] at hok)
          all_goals (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
      · -- unexpectedType case
        simp [err] at hok
  | .or x₁ x₂ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce
      cases h : checkEntities ⟨env.ets, env.acts⟩ x₁ with
      | error => simp [h] at hce
      | ok u => cases u; rfl
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      unfold checkEntities at hce; simp [hce₁] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfOr] at hok
      split at hok
      · -- .bool .tt: result is tx₁ itself
        simp [ok] at hok
        obtain ⟨h, _⟩ := hok; subst h
        simp [TypedExpr.typeOf]
        exact typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool .ff
        cases h₂ : typeOf x₂ c env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          split at hok
          all_goals (simp [ok, err] at hok)
          all_goals (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf])
          all_goals exact typeOf_produces_wf_type x₂ c hets_wf hce₂ h₂ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
      · -- .bool _
        cases h₂ : typeOf x₂ c env with
        | error => simp [h₂] at hok
        | ok val₂ =>
          obtain ⟨tx₂, c₂⟩ := val₂
          simp [h₂] at hok
          split at hok
          all_goals (simp [ok, err] at hok)
          all_goals (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
      · simp [err] at hok
  | .unaryApp op x₁ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      cases op with
      | not | neg | like | isEmpty =>
        simp only [checkEntities] at hce; exact hce
      | is ety =>
        simp only [checkEntities] at hce
        split at hce
        · exact hce
        · contradiction
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfUnaryApp] at hok
      split at hok
      · -- .not, .bool x
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .neg, .int
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
      · -- .isEmpty, .set _
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .like _, .string
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .is ety₁, .entity ety₂
        simp [ok, Function.comp] at hok
        obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- catch-all error
        simp [err] at hok
  | .binaryApp op x₁ x₂ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce
      cases h : checkEntities ⟨env.ets, env.acts⟩ x₁ with
      | error => simp [h] at hce
      | ok => cases ‹Unit›; rfl
    have hce₂ : checkEntities ⟨env.ets, env.acts⟩ x₂ = .ok () := by
      unfold checkEntities at hce; simp [hce₁] at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      cases h₂ : typeOf x₂ c env with
      | error => simp [h₂] at hok
      | ok val₂ =>
        obtain ⟨tx₂, c₂⟩ := val₂
        simp [h₂] at hok
        simp only [typeOfBinaryApp] at hok
        -- Most arms produce .bool _ or .int → trivially WF
        -- .getTag may produce a type from the schema
        split at hok
        · -- .eq: typeOfEq produces .bool _
          simp only [typeOfEq] at hok
          split at hok
          · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
          · split at hok
            · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
            · split at hok
              · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
              · simp [err] at hok
        · -- .mem entity entity: produces .bool _
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · -- .mem entity (set entity): produces .bool _
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · -- .hasTag entity string: produces .bool _ via typeOfHasTag
          simp only [typeOfHasTag] at hok
          split at hok
          · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
          · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
          · split at hok
            · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
            · simp [err] at hok
        · -- .getTag entity string: produces ty from tags?
          rename_i ety₁ _ _
          simp only [typeOfGetTag] at hok
          split at hok
          · simp [err] at hok
          · rename_i htags
            split at hok
            · simp [ok] at hok
              obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
              -- ty comes from ets.tags? ety₁ = some (some ty)
              -- Use schema WF to show ty is WF
              simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htags
              obtain ⟨entry, hfind_e, htags_eq⟩ := htags
              have hentry_wf := hets_wf.2 ety₁ entry hfind_e
              cases entry with
              | standard s =>
                simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
                have ⟨_, _, _, _, htag_wf⟩ := hentry_wf
                simp [EntitySchemaEntry.tags?] at htags_eq
                exact (htag_wf _ htags_eq).1
              | enum _ =>
                simp [EntitySchemaEntry.tags?] at htags_eq
            · simp [err] at hok
          · simp [err] at hok
        · -- .less int int: produces .bool _
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · -- .add: produces .int
          simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .int_wf
        · -- .contains: ifLubThenBool → .bool _
          simp only [ifLubThenBool] at hok
          split at hok <;> simp [ok, err] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp only [ifLubThenBool] at hok
          split at hok <;> simp [ok, err] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp only [ifLubThenBool] at hok
          split at hok <;> simp [ok, err] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · simp [err] at hok
  | .hasAttr x₁ _ =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfHasAttr] at hok
      split at hok
      · -- .record: hasAttrInRecord → .bool _
        simp only [hasAttrInRecord] at hok
        split at hok
        · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
        · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
      · -- .entity: hasAttrInRecord or .bool .ff or error
        split at hok
        · simp only [hasAttrInRecord] at hok
          split at hok
          · split at hok <;> simp [ok] at hok <;> (obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf)
          · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
        · split at hok
          · simp [ok] at hok; obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]; exact .bool_wf
          · simp [err] at hok
      · simp [err] at hok
  | .getAttr x₁ a =>
    have hce₁ : checkEntities ⟨env.ets, env.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf] at hok
    cases h₁ : typeOf x₁ c env with
    | error => simp [h₁] at hok
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp [h₁] at hok
      simp only [typeOfGetAttr] at hok
      split at hok
      · -- .record rty: getAttrInRecord → aty where rty.find? a = some qty
        rename_i rty _
        simp only [getAttrInRecord] at hok
        split at hok
        · -- .some (.required aty)
          rename_i aty hfind
          simp [ok] at hok
          obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
          -- tx₁.typeOf = .record rty, and by IH it's WF
          have hwf₁ := typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
          -- hwf₁ : CedarType.WellFormed env (.record rty)
          -- But wait - tx₁.typeOf might not be exactly .record rty if tx₁ is more complex
          -- Actually, the split on tx₁.typeOf = .record rty already establishes this
          have hwf_record : (CedarType.record rty).WellFormed env := by
            have : tx₁.typeOf = .record rty := by assumption
            rw [← this]; exact hwf₁
          cases hwf_record with
          | record_wf _ hattr =>
            have hqty_wf := hattr a (.required aty) hfind
            cases hqty_wf with
            | required_wf h => exact h
        · -- .some (.optional aty)
          rename_i aty hfind
          split at hok
          · simp [ok] at hok
            obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
            have hwf₁ := typeOf_produces_wf_type x₁ c hets_wf hce₁ h₁ hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
            have hwf_record : (CedarType.record rty).WellFormed env := by
              have : tx₁.typeOf = .record rty := by assumption
              rw [← this]; exact hwf₁
            cases hwf_record with
            | record_wf _ hattr =>
              have hqty_wf := hattr a (.optional aty) hfind
              cases hqty_wf with
              | optional_wf h => exact h
          · simp [err] at hok
        · simp [err] at hok
      · -- .entity ety: getAttrInRecord on ets.attrs? ety
        rename_i ety _
        split at hok
        · rename_i rty hattrs
          simp only [getAttrInRecord] at hok
          split at hok
          · rename_i aty hfind
            simp [ok] at hok
            obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
            -- ety is in ets (from attrs? succeeding), attrs? gives WF record from schema WF
            have hwf_record : (CedarType.record rty).WellFormed env := by
              simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
              obtain ⟨entry, hfind_e, hattrs_eq⟩ := hattrs
              have hentry_wf := hets_wf.2 ety entry hfind_e
              cases entry with
              | standard s =>
                simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
                have ⟨_, _, hwf, _⟩ := hentry_wf
                simpa [EntitySchemaEntry.attrs, ← hattrs_eq] using hwf
              | enum _ =>
                simp [EntitySchemaEntry.attrs] at hattrs_eq
                subst hattrs_eq
                exact .record_wf (by constructor) (by intro _ _ h; simp [Map.find?] at h)
            cases hwf_record with
            | record_wf _ hattr =>
              have hqty_wf := hattr a (.required aty) hfind
              cases hqty_wf with
              | required_wf h => exact h
          · rename_i aty hfind
            split at hok
            · simp [ok] at hok
              obtain ⟨h, _⟩ := hok; subst h; simp [TypedExpr.typeOf]
              have hwf_record : (CedarType.record rty).WellFormed env := by
                simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
                obtain ⟨entry, hfind_e, hattrs_eq⟩ := hattrs
                have hentry_wf := hets_wf.2 ety entry hfind_e
                cases entry with
                | standard s =>
                  simp [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry_wf
                  have ⟨_, _, hwf, _⟩ := hentry_wf
                  simpa [EntitySchemaEntry.attrs, ← hattrs_eq] using hwf
                | enum _ =>
                  simp [EntitySchemaEntry.attrs] at hattrs_eq
                  subst hattrs_eq
                  exact .record_wf (by constructor) (by intro _ _ h; simp [Map.find?] at h)
              cases hwf_record with
              | record_wf _ hattr =>
                have hqty_wf := hattr a (.optional aty) hfind
                cases hqty_wf with
                | optional_wf h => exact h
            · simp [err] at hok
          · simp [err] at hok
        · simp [err] at hok
      · simp [err] at hok
  | .set (x₀ :: xtl) =>
    have hce_all : ∀ x ∈ (x₀ :: xtl), checkEntities ⟨env.ets, env.acts⟩ x = .ok () := by
      intro x hx
      have hce' : (x₀ :: xtl).attach.forM (fun ⟨x, _⟩ => checkEntities ⟨env.ets, env.acts⟩ x) = .ok () := by
        simp only [checkEntities] at hce; exact hce
      have := List.forM_ok_implies_all_ok' hce' ⟨x, hx⟩ (List.mem_attach _ ⟨x, hx⟩)
      simpa using this
    have ⟨_, txs, ty, htx_eq, helem⟩ := type_of_set_inversion hok
    rw [htx_eq]; simp [TypedExpr.typeOf]
    have hx₀_mem : x₀ ∈ (x₀ :: xtl) := List.Mem.head _
    obtain ⟨tx₀, c₀, _, htypeOf₀, hlub₀⟩ := helem x₀ hx₀_mem
    have hwf₀ := typeOf_produces_wf_type x₀ c hets_wf (hce_all x₀ hx₀_mem) htypeOf₀
      hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
    exact .set_wf (lub_preserves_wf_left hwf₀ hlub₀)
  | .set [] =>
    simp [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)),
      typeOfSet, ok, err] at hok
  | .record axs =>
    have hce_all : ∀ ax ∈ axs, checkEntities ⟨env.ets, env.acts⟩ ax.snd = .ok () := by
      intro ax hax
      have hce' := hce; simp only [checkEntities] at hce'
      have hmem : ⟨ax, List.sizeOf_snd_lt_sizeOf_list hax⟩ ∈ axs.attach₂ := by
        simp only [List.attach₂, List.mem_pmap]
        exact ⟨ax, hax, rfl⟩
      exact List.forM_ok_implies_all_ok' hce' _ hmem
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env).map (fun (ty, _) => (ax.fst, ty))) axs] at hok
    -- Extract mapM result
    have hbind := hok
    simp only [bind, Except.bind] at hbind
    split at hbind
    · exact absurd hbind (by simp)
    · rename_i atys hmapM_eq
      simp [ok] at hbind
      obtain ⟨h, _⟩ := hbind; subst h; simp [TypedExpr.typeOf]
      apply CedarType.WellFormed.record_wf
      · exact Map.make_wf _
      · intro attr qty hfind
        -- From (Map.make mapped_list).find? attr = some qty, derive qty is in mapped_list
        have hfind_list : (List.find? (fun x => x.fst == attr) (atys.map (fun (a, ty) => (a, Qualified.required ty.typeOf)))).map Prod.snd = some qty := by
          rw [← Map.make_find?_eq_list_find?]; exact hfind
        -- Extract the found element
        cases hfl : List.find? (fun x => x.fst == attr) (atys.map (fun (a, ty) => (a, Qualified.required ty.typeOf))) with
        | none => simp [hfl] at hfind_list
        | some p =>
          simp [hfl] at hfind_list
          subst hfind_list
          -- p ∈ mapped_list and p.fst == attr
          have hp_mem := List.mem_of_find?_eq_some hfl
          rw [List.mem_map] at hp_mem
          obtain ⟨⟨a_i, ty_i⟩, hmem_atys, heq_p⟩ := hp_mem
          -- p = (a_i, .required ty_i.typeOf)
          -- Goal is QualifiedType.WellFormed env p.snd
          have h_snd : p.snd = Qualified.required ty_i.typeOf := by
            have := congrArg Prod.snd heq_p; exact this.symm
          rw [h_snd]
          -- ty_i ∈ atys came from mapM
          have ⟨ax_i, hax_mem, hmap_ok⟩ := List.mapM_ok_implies_all_from_ok hmapM_eq (a_i, ty_i) hmem_atys
          -- hmap_ok : (typeOf ax_i.snd c env).map (fun (ty, _) => (ax_i.fst, ty)) = .ok (a_i, ty_i)
          -- Extract the typeOf result from the Except.map
          cases htypeOf_ok : typeOf ax_i.snd c env with
          | error => simp [Except.map, htypeOf_ok] at hmap_ok
          | ok val =>
            obtain ⟨tx_i, c_i⟩ := val
            simp [Except.map, htypeOf_ok] at hmap_ok
            obtain ⟨_, h_ty⟩ := hmap_ok
            subst h_ty
            have _hlt : sizeOf ax_i.snd < 1 + sizeOf axs :=
              List.sizeOf_snd_lt_sizeOf_list hax_mem
            have hwf_i := typeOf_produces_wf_type ax_i.snd c hets_wf
              (hce_all ax_i hax_mem) htypeOf_ok
              hdisjoint hreqty_action hreqty_principal hreqty_resource hctx_wf
            exact .required_wf hwf_i
  | .call xfn xs =>
    simp only [typeOf] at hok
    -- Extract the mapM₁ result
    have hbind := hok
    simp only [bind, Except.bind] at hbind
    split at hbind
    · exact absurd hbind (by simp)
    · rename_i tys _
      -- Now tys is the result of mapM₁ and hbind : typeOfCall xfn tys xs = .ok (tx, c')
      simp only [typeOfCall] at hbind
      -- All arms produce .ext _, .bool _, or .int
      split at hbind
      all_goals (try (simp only [typeOfConstructor] at hbind))
      all_goals (try (split at hbind))
      all_goals (try (split at hbind))
      all_goals (simp [ok, err] at hbind)
      all_goals (try (obtain ⟨h, _⟩ := hbind; subst h; simp [TypedExpr.typeOf]))
      all_goals (first | exact .ext_wf | exact .bool_wf | exact .int_wf)
  termination_by sizeOf expr

/--
Corollary: entity types in record type attributes produced by `typeOf` are well-formed.
-/
private theorem typeOf_produces_wf_type_entity (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    {rty : RecordType} {a : Attr} {qty : Qualified CedarType} {ety : EntityType}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (hce : checkEntities ⟨env.ets, env.acts⟩ expr = .ok ())
    (hok : typeOf expr c env = .ok (tx, c'))
    (hrecord : tx.typeOf = .record rty)
    (hfind_a : rty.find? a = some qty)
    (hty : qty.getType = .entity ety)
    (hdisjoint : ∀ uid, env.acts.contains uid = true → ¬ env.ets.contains uid.ty)
    (hreqty_action : env.acts.contains env.reqty.action = true)
    (hreqty_principal : env.ets.contains env.reqty.principal ∨ env.acts.actionType? env.reqty.principal)
    (hreqty_resource : env.ets.contains env.reqty.resource ∨ env.acts.actionType? env.reqty.resource)
    (hctx_wf : (CedarType.record env.reqty.context).WellFormed env) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  have hwf := typeOf_produces_wf_type expr c hets_wf hce hok hdisjoint hreqty_action
    hreqty_principal hreqty_resource hctx_wf
  rw [hrecord] at hwf
  exact entity_type_wf_from_record_wf hwf hfind_a hty

/-! ## Type invariant: entity types from typeOf are in ets or are action types -/

/--
Entity types produced by `typeOf` are always known to the entity schema or are
action types. This is the key invariant for backward compatibility.

The proof requires schema well-formedness to handle the `getAttr` case, where
the result type comes from the entity schema entry's attribute types.
-/
private theorem typeOf_entity_type_in_ets (expr : Expr) (c : Capabilities)
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities} {ety : EntityType}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (hce : checkEntities ⟨env.ets, env.acts⟩ expr = .ok ())
    (hok : typeOf expr c env = .ok (tx, c'))
    (hty : tx.typeOf = .entity ety)
    (hdisjoint : ∀ uid, env.acts.contains uid = true → ¬ env.ets.contains uid.ty)
    (hreqty_action : env.acts.contains env.reqty.action = true)
    (hreqty_principal : env.ets.contains env.reqty.principal ∨ env.acts.actionType? env.reqty.principal)
    (hreqty_resource : env.ets.contains env.reqty.resource ∨ env.acts.actionType? env.reqty.resource)
    (hctx_wf : (CedarType.record env.reqty.context).WellFormed env) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  have hwf := typeOf_produces_wf_type expr c hets_wf hce hok hdisjoint hreqty_action
    hreqty_principal hreqty_resource hctx_wf
  rw [hty] at hwf
  cases hwf with
  | entity_wf h =>
    simp [EntityType.WellFormed, ActionSchema.IsActionEntityType] at h
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      right
      obtain ⟨uid, hc, heq⟩ := h
      simp [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
      exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩

/-! ## typeOf congruence under entity schema extension -/

/--
If `env₁.ets.find?` gives `none` and `ety` is an action type, then
`env₂.ets.find?` also gives `none` (by disjointness on env₂).
-/
private theorem ets_find_none_of_actionType
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

private theorem ets_attrs_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.attrs? ety = ets₂.attrs? ety := by
  cases hinv with
  | inl hc => exact ets_attrs_eq_of_contains hfwd hc
  | inr hact =>
    have h₁ : ets₁.find? ety = none := by
      obtain ⟨uid, hcontains, heq⟩ := actionType_implies_contains hact
      cases hf : ets₁.find? ety with
      | none => rfl
      | some entry =>
        exact absurd (heq ▸ ets_contains_of_find (hfwd ety entry hf)) (hdisjoint₂ uid hcontains)
    have h₂ : ets₂.find? ety = none := ets_find_none_of_actionType hdisjoint₂ hact
    simp only [EntitySchema.attrs?, h₁, h₂]

private theorem ets_tags_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.tags? ety = ets₂.tags? ety := by
  cases hinv with
  | inl hc => exact ets_tags_eq_of_contains hfwd hc
  | inr hact =>
    have h₁ : ets₁.find? ety = none := by
      obtain ⟨uid, hcontains, heq⟩ := actionType_implies_contains hact
      cases hf : ets₁.find? ety with
      | none => rfl
      | some entry =>
        exact absurd (heq ▸ ets_contains_of_find (hfwd ety entry hf)) (hdisjoint₂ uid hcontains)
    have h₂ : ets₂.find? ety = none := ets_find_none_of_actionType hdisjoint₂ hact
    simp only [EntitySchema.tags?, h₁, h₂]

private theorem descendentOf_agree
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
  · cases hinv with
    | inl hc =>
      have heq := ets_find_eq_of_contains hfwd hc
      rw [heq]
    | inr hact =>
      have h₁ : ets₁.find? ety₁ = none := by
        obtain ⟨uid, hcontains, heq⟩ := actionType_implies_contains hact
        cases hf : ets₁.find? ety₁ with
        | none => rfl
        | some entry =>
          exact absurd (heq ▸ ets_contains_of_find (hfwd ety₁ entry hf)) (hdisjoint₂ uid hcontains)
      have h₂ : ets₂.find? ety₁ = none := ets_find_none_of_actionType hdisjoint₂ hact
      simp [h₁, h₂]

/--
If two schemas have the same actions and the new entity schema preserves all old
entries, then `typeOf` gives the same result for any expression that passes
`checkEntities` on the old schema. Requires entity schema well-formedness for
the type invariant needed at `getAttr`/`hasAttr`/`binaryApp` cases.
-/
private theorem isValidEntityUID_fwd
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

private theorem isValidOrContains_fwd
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

private theorem contains_or_actionType_fwd
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
    have hf₂ := hets_fwd ety entry hf
    simp [EntitySchema.contains, hf₂]

private theorem checkEntities_pair' {schema : Schema} {e₁ e₂ : Expr}
    (h : (do checkEntities schema e₁; checkEntities schema e₂) = .ok ()) :
    checkEntities schema e₁ = .ok () ∧ checkEntities schema e₂ = .ok () := by
  cases h₁ : checkEntities schema e₁ with
  | error e => simp [h₁] at h
  | ok _ => simp [h₁] at h; exact ⟨rfl, h⟩


theorem typeOf_preserved_of_ets_extension (expr : Expr) (c : Capabilities)
    {env₁ env₂ : TypeEnv}
    (hreqty : env₁.reqty = env₂.reqty)
    (hacts : env₁.acts = env₂.acts)
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ expr = .ok ())
    (hdisjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty)
    (hets_wf : EntitySchema.WellFormed env₁ env₁.ets)
    (hreqty_action : env₁.acts.contains env₁.reqty.action = true)
    (hreqty_principal : env₁.ets.contains env₁.reqty.principal ∨ env₁.acts.actionType? env₁.reqty.principal)
    (hreqty_resource : env₁.ets.contains env₁.reqty.resource ∨ env₁.acts.actionType? env₁.reqty.resource)
    (hctx_wf : (CedarType.record env₁.reqty.context).WellFormed env₁) :
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
      simp only [typeOf, typeOfLit]
      have hvalid₂ := isValidOrContains_fwd hets_fwd hacts hvalid
      simp [hvalid, hvalid₂]
    · contradiction
  | .var v => simp [typeOf, typeOfVar, hreqty]
  | .unaryApp (.is ety) x₁ =>
    simp only [checkEntities] at hce
    split at hce
    · simp only [typeOf]
      rw [typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
    · contradiction
  | .unaryApp (.not) x₁ | .unaryApp (.neg) x₁ | .unaryApp (.like _) x₁ | .unaryApp (.isEmpty) x₁ =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
  | .and x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair' hce'
    simp only [typeOf]
    rw [typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_preserved_of_ets_extension x₂ (c ∪ c₁) hreqty hacts hets_fwd hce₂ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
  | .or x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair' hce'
    simp only [typeOf]
    rw [typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_preserved_of_ets_extension x₂ c hreqty hacts hets_fwd hce₂ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
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
    rw [typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
    congr 1; funext ⟨tx₁, c₁⟩
    simp only [typeOfIf]
    split <;> try rfl
    · rw [typeOf_preserved_of_ets_extension x₂ (c ∪ c₁) hreqty hacts hets_fwd hce₂ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
    · rw [typeOf_preserved_of_ets_extension x₃ c hreqty hacts hets_fwd hce₃ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
    · rw [typeOf_preserved_of_ets_extension x₂ (c ∪ c₁) hreqty hacts hets_fwd hce₂ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf,
           typeOf_preserved_of_ets_extension x₃ c hreqty hacts hets_fwd hce₃ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf]
  | .binaryApp op x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair' hce'
    simp only [typeOf]
    have hih₁ := typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf
    have hih₂ := typeOf_preserved_of_ets_extension x₂ c hreqty hacts hets_fwd hce₂ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf
    rw [hih₁, hih₂]
    -- After rewriting, both sides bind on the same typeOf x₁/x₂ results from env₂
    -- The remaining difference is in typeOfBinaryApp which queries env
    -- For most ops, no env query. For mem/hasTag/getTag, need type invariant.
    -- Use cases on the result to get access to the actual typed exprs
    cases hr₁ : typeOf x₁ c env₂ with
    | error => simp
    | ok val₁ =>
      obtain ⟨tx₁, c₁⟩ := val₁
      simp only [Except.bind_ok]
      cases hr₂ : typeOf x₂ c env₂ with
      | error => simp
      | ok val₂ =>
        obtain ⟨tx₂, c₂⟩ := val₂
        simp only [Except.bind_ok]
        have hr₁' : typeOf x₁ c env₁ = .ok (tx₁, c₁) := hih₁ ▸ hr₁
        -- Get type invariant for tx₁ entity types
        have hinv₁ : ∀ ety, tx₁.typeOf = .entity ety →
            env₁.ets.contains ety ∨ env₁.acts.actionType? ety :=
          fun ety hety => typeOf_entity_type_in_ets x₁ c hets_wf hce₁ hr₁' hety
            (fun uid hc => fun hc₁ => hdisjoint₂ uid (hacts ▸ hc) (by
              simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
              obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩))
            hreqty_action hreqty_principal hreqty_resource hctx_wf
        -- typeOfBinaryApp queries env at entity types from tx₁/tx₂
        -- Strategy: show all env-dependent operations agree between env₁ and env₂
        -- The env-dependent operations are:
        -- - TypeEnv.descendentOf (for .mem with entity types)
        -- - typeOfHasTag/typeOfGetTag (for .hasTag/.getTag)
        -- - acts.descendentOf/maybeDescendentOf (same by hacts)
        -- For TypeEnv.descendentOf and tags?, we use the type invariant on tx₁
        -- Since ets.find? agrees on types in env₁.ets or action types,
        -- and acts are the same, all these give the same result.
        -- Convert to WeakTypeEnvAgreement-style proof by showing all queries agree
        have henv_desc : ∀ ety₁ ety₂, tx₁.typeOf = .entity ety₁ →
            env₁.descendentOf ety₁ ety₂ = env₂.descendentOf ety₁ ety₂ := by
          intro ety₁ ety₂ hety
          simp only [TypeEnv.descendentOf]
          split
          · rfl
          · have hinv := hinv₁ ety₁ hety
            cases hinv with
            | inl hc =>
              have heq := ets_find_eq_of_contains hets_fwd hc
              rw [heq, hacts]
            | inr hact =>
              have h₁ : env₁.ets.find? ety₁ = none := by
                obtain ⟨uid, hcontains, heq'⟩ := actionType_implies_contains hact
                cases hf : env₁.ets.find? ety₁ with
                | none => rfl
                | some entry =>
                  have hc₂ := ets_contains_of_find (hets_fwd ety₁ entry hf)
                  exact absurd (heq' ▸ hc₂) (hdisjoint₂ uid (hacts ▸ hcontains))
              have h₂ : env₂.ets.find? ety₁ = none :=
                ets_find_none_of_actionType (hacts ▸ hdisjoint₂) hact
              simp [h₁, h₂, hacts]
        have henv_tags : ∀ ety₁, tx₁.typeOf = .entity ety₁ →
            env₁.ets.tags? ety₁ = env₂.ets.tags? ety₁ := by
          intro ety₁ hety
          exact ets_tags_agree hets_fwd (hacts ▸ hdisjoint₂) (hinv₁ ety₁ hety)
        -- Show typeOfBinaryApp gives same result using split on the big match
        unfold typeOfBinaryApp
        split
        -- .eq: typeOfEq doesn't query env
        · rfl
        -- .mem entity entity: uses typeOfInₑ which uses actionUID?, descendentOf
        · rename_i ety₁ ety₂ heq_tx₁ _
          have hinv := hinv₁ ety₁ heq_tx₁
          have hfind_eq : env₁.ets.find? ety₁ = env₂.ets.find? ety₁ := by
            cases hinv with
            | inl hc => exact ets_find_eq_of_contains hets_fwd hc
            | inr hact =>
              rw [ets_find_none_of_actionType (fun uid hc => by
                intro hc₁; exact hdisjoint₂ uid (hacts ▸ hc) (by
                  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
                  obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩)) hact,
                ets_find_none_of_actionType (hacts ▸ hdisjoint₂) hact]
          simp [typeOfInₑ, actionUID?, hacts, TypeEnv.descendentOf, hfind_eq]
        -- .mem entity (set entity): uses typeOfInₛ
        · rename_i ety₁ ety₂ heq_tx₁ _
          have hinv := hinv₁ ety₁ heq_tx₁
          have hfind_eq : env₁.ets.find? ety₁ = env₂.ets.find? ety₁ := by
            cases hinv with
            | inl hc => exact ets_find_eq_of_contains hets_fwd hc
            | inr hact =>
              rw [ets_find_none_of_actionType (fun uid hc => by
                intro hc₁; exact hdisjoint₂ uid (hacts ▸ hc) (by
                  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
                  obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩)) hact,
                ets_find_none_of_actionType (hacts ▸ hdisjoint₂) hact]
          simp [typeOfInₛ, actionUID?, hacts, TypeEnv.descendentOf, hfind_eq]
        -- .hasTag entity string: uses typeOfHasTag which uses ets.tags?
        · rename_i ety₁ heq_tx₁ _
          have htags := henv_tags ety₁ heq_tx₁
          simp [typeOfHasTag, htags, hacts]
        -- .getTag entity string: uses typeOfGetTag which uses ets.tags?
        · rename_i ety₁ heq_tx₁ _
          have htags := henv_tags ety₁ heq_tx₁
          simp [typeOfGetTag, htags]
        -- All remaining arms: no env dependency
        all_goals rfl
  | .hasAttr x₁ a =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    have hih := typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf
    cases hr : typeOf x₁ c env₁ with
    | error e => simp [hih ▸ hr]
    | ok val =>
      obtain ⟨tx₁, c₁⟩ := val
      simp only [Except.bind_ok]
      rw [show typeOf x₁ c env₂ = .ok (tx₁, c₁) from hih ▸ hr]
      simp only [Except.bind_ok]
      unfold typeOfHasAttr
      cases htx : tx₁.typeOf with
      | entity ety =>
        have hinv : env₁.ets.contains ety ∨ env₁.acts.actionType? ety :=
          typeOf_entity_type_in_ets x₁ c hets_wf hce₁ hr htx
            (fun uid hc => fun hc₁ => hdisjoint₂ uid (hacts ▸ hc) (by
              simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
              obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩))
            hreqty_action hreqty_principal hreqty_resource hctx_wf
        have hattrs := ets_attrs_agree hets_fwd (hacts ▸ hdisjoint₂) hinv
        simp [hattrs, hacts]
      | record _ => rfl
      | _ => rfl
  | .getAttr x₁ a =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    have hih := typeOf_preserved_of_ets_extension x₁ c hreqty hacts hets_fwd hce₁ hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf
    cases hr : typeOf x₁ c env₁ with
    | error e => simp [hih ▸ hr]
    | ok val =>
      obtain ⟨tx₁, c₁⟩ := val
      simp only [Except.bind_ok]
      rw [show typeOf x₁ c env₂ = .ok (tx₁, c₁) from hih ▸ hr]
      simp only [Except.bind_ok]
      unfold typeOfGetAttr
      cases htx : tx₁.typeOf with
      | entity ety =>
        have hinv : env₁.ets.contains ety ∨ env₁.acts.actionType? ety :=
          typeOf_entity_type_in_ets x₁ c hets_wf hce₁ hr htx
            (fun uid hc => fun hc₁ => hdisjoint₂ uid (hacts ▸ hc) (by
              simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
              obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩))
            hreqty_action hreqty_principal hreqty_resource hctx_wf
        have hattrs := ets_attrs_agree hets_fwd (hacts ▸ hdisjoint₂) hinv
        simp [hattrs]
      | record _ => rfl
      | _ => rfl
  | .set xs =>
    have hce_all : ∀ x ∈ xs, checkEntities ⟨env₁.ets, env₁.acts⟩ x = .ok () := by
      intro x hx
      have hce' : xs.attach.forM (fun ⟨x, _⟩ => checkEntities ⟨env₁.ets, env₁.acts⟩ x) = .ok () := by
        simp only [checkEntities] at hce; exact hce
      have := List.forM_ok_implies_all_ok' hce' ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩)
      simpa using this
    have hmapM : List.mapM (fun x => justType (typeOf x c env₁)) xs =
                 List.mapM (fun x => justType (typeOf x c env₂)) xs :=
      List.mapM_congr (fun x hx => congrArg justType
        (typeOf_preserved_of_ets_extension x c hreqty hacts hets_fwd (hce_all x hx) hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf))
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
        rw [typeOf_preserved_of_ets_extension ax.snd c hreqty hacts hets_fwd (hce_all ax hax) hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf])
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
      List.mapM_congr (fun x hx => congrArg justType
        (typeOf_preserved_of_ets_extension x c hreqty hacts hets_fwd (hce_all x hx) hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  termination_by sizeOf expr

/-! ## Policy-level preservation -/

/--
If two schemas have the same actions and the new entity schema preserves all old
entries, then `typecheckPolicy` gives the same result for any policy that passes
`checkEntities` on the old schema.
-/
theorem typecheckPolicy_preserved_of_ets_extension
    {policy : Policy} {env₁ env₂ : TypeEnv}
    (hreqty : env₁.reqty = env₂.reqty)
    (hacts : env₁.acts = env₂.acts)
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok ())
    (hdisjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty)
    (hreqty_action : env₁.acts.contains env₁.reqty.action = true)
    (hets_wf : EntitySchema.WellFormed env₁ env₁.ets)
    (hreqty_principal : env₁.ets.contains env₁.reqty.principal ∨ env₁.acts.actionType? env₁.reqty.principal)
    (hreqty_resource : env₁.ets.contains env₁.reqty.resource ∨ env₁.acts.actionType? env₁.reqty.resource)
    (hctx_wf : (CedarType.record env₁.reqty.context).WellFormed env₁) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  simp only [typecheckPolicy]
  have haction_valid : (env₁.ets.isValidEntityUID env₁.reqty.action ||
                        env₁.acts.contains env₁.reqty.action) = true := by
    simp [hreqty_action]
  have hce_sub := checkEntities_substituteAction hce haction_valid
  have := typeOf_preserved_of_ets_extension
    (substituteAction env₁.reqty.action policy.toExpr) ∅
    hreqty hacts hets_fwd hce_sub hdisjoint₂ hets_wf hreqty_action hreqty_principal hreqty_resource hctx_wf
  simp only [hreqty] at this ⊢
  rw [this]

/-! ## Top-level theorem -/

/--
**Backward compatibility**: adding new entity types to the entity schema never
invalidates existing policies. If policies validate on schema₁, and schema₂ has
the same actions but an extended entity schema (all old entries preserved), then
policies also validate on schema₂.
-/
private theorem environments_same_reqtys
    {schema₁ schema₂ : Schema}
    (hacts_eq : schema₁.acts = schema₂.acts) :
    (schema₁.environments.map TypeEnv.reqty) = (schema₂.environments.map TypeEnv.reqty) := by
  simp only [Schema.environments, List.map_map]
  congr 1
  rw [hacts_eq]

private theorem environments_ets_acts
    {schema : Schema} {env : TypeEnv}
    (hmem : env ∈ schema.environments) :
    env.ets = schema.ets ∧ env.acts = schema.acts := by
  simp only [Schema.environments, List.mem_map] at hmem
  obtain ⟨reqty, _, heq⟩ := hmem
  have h₁ : env.ets = schema.ets := by rw [← heq]
  have h₂ : env.acts = schema.acts := by rw [← heq]
  exact ⟨h₁, h₂⟩

theorem validate_preserved_of_ets_extension
    (schema₁ schema₂ : Schema)
    (policies : Policies)
    (hacts_eq : schema₁.acts = schema₂.acts)
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      schema₁.ets.find? ety = some entry → schema₂.ets.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, schema₂.acts.contains uid = true →
      ¬ schema₂.ets.contains uid.ty)
    (hwf₁ : Schema.validateWellFormed schema₁ = .ok ())
    (hold : validate policies schema₁ = .ok ()) :
    validate policies schema₂ = .ok () := by
  -- validate = policies.forM (typecheckPolicyWithEnvironments typecheckPolicy · schema)
  simp only [validate] at hold ⊢
  apply List.all_ok_implies_forM_ok
  intro p hp
  have hp₁ := List.forM_ok_implies_all_ok' hold p hp
  -- hp₁: typecheckPolicyWithEnvironments typecheckPolicy p schema₁ = .ok ()
  -- Goal: typecheckPolicyWithEnvironments typecheckPolicy p schema₂ = .ok ()
  -- typecheckPolicyWithEnvironments does checkEntities + mapM + allFalse check
  simp only [typecheckPolicyWithEnvironments] at hp₁ ⊢
  -- Step 1: Extract that checkEntities passes on schema₁
  have hce₁ : checkEntities schema₁ p.toExpr = .ok () := by
    cases hce : checkEntities schema₁ p.toExpr with
    | ok _ => rfl
    | error e => simp [Except.mapError, hce] at hp₁
  -- Step 2: checkEntities passes on schema₂ by monotonicity
  have hce₂ : checkEntities schema₂ p.toExpr = .ok () := by
    exact checkEntities_monotone p.toExpr
      (fun uid h => isValidOrContains_fwd hets_fwd hacts_eq h)
      (fun ety h => contains_or_actionType_fwd hets_fwd hacts_eq h)
      hce₁
  -- Step 3: Show mapM gives same result on both schemas' environments
  -- schema.environments = (schema.acts.toList.flatMap ...).map (fun rt => {ets, acts, reqty := rt})
  -- Both have same reqtys, different ets. typecheckPolicy gives same result.
  have hmapM : schema₁.environments.mapM (typecheckPolicy p) =
               schema₂.environments.mapM (typecheckPolicy p) := by
    -- Express environments in terms of a common reqtys list
    simp only [Schema.environments, hacts_eq]
    rw [List.mapM_map, List.mapM_map]
    -- Now both sides map over the same reqtys list (from schema₂.acts since we rewrote hacts_eq)
    apply List.mapM_congr
    intro rt hrt
    simp only [Function.comp]
    -- Goal: typecheckPolicy p {ets := schema₁.ets, acts := schema₂.acts, reqty := rt} =
    --       typecheckPolicy p {ets := schema₂.ets, acts := schema₂.acts, reqty := rt}
    -- This follows from typecheckPolicy_preserved_of_ets_extension with preconditions
    -- derived from Schema.validateWellFormed schema₁ (env is in schema₁.environments).
    -- The preconditions (hce, haction_valid, hets_wf, hreqty_principal/resource)
    -- all follow from TypeEnv.WellFormed which is derived from Schema.validateWellFormed.
    -- rt is in the flatMap from schema₂.acts, so rt.action is in acts
    have hrt_action_in_acts : schema₂.acts.contains rt.action = true := by
      simp only [List.mem_flatMap] at hrt
      obtain ⟨⟨action, entry⟩, hmem_acts, hrt_in⟩ := hrt
      simp only [ActionSchemaEntry.requestTypes, List.mem_map] at hrt_in
      obtain ⟨⟨principal, resource⟩, _, heq⟩ := hrt_in
      have haction_eq : rt.action = action := by
        have := congrArg RequestType.action heq; simp at this; exact this.symm
      rw [haction_eq]
      exact Map.in_list_implies_contains hmem_acts
    -- The env {ets := schema₁.ets, acts := schema₂.acts, reqty := rt} is in schema₁.environments
    have henv_in_schema₁ : ({ ets := schema₁.ets, acts := schema₂.acts, reqty := rt } : TypeEnv) ∈
        schema₁.environments := by
      simp only [Schema.environments, hacts_eq, List.mem_map]
      exact ⟨rt, hrt, rfl⟩
    -- Derive TypeEnv.WellFormed from Schema.validateWellFormed
    have henv_wf : TypeEnv.WellFormed { ets := schema₁.ets, acts := schema₂.acts, reqty := rt } :=
      env_validate_well_formed_is_sound (List.forM_ok_implies_all_ok' hwf₁ _ henv_in_schema₁)
    exact typecheckPolicy_preserved_of_ets_extension rfl rfl hets_fwd
      (by rw [← hacts_eq]; exact hce₁) hdisjoint₂
      hrt_action_in_acts -- hreqty_action: acts.contains rt.action
      henv_wf.1 -- hets_wf: EntitySchema.WellFormed from TypeEnv.WellFormed
      (by -- hreqty_principal ∨ actionType?
        have hreqty_wf := henv_wf.2.2
        have hacts_wf := henv_wf.2.1
        obtain ⟨entry, hfind, hprinc, _, _⟩ := hreqty_wf
        -- ActionSchemaEntry.WellFormed env entry
        have hentry_wf := hacts_wf.2.1 rt.action entry hfind
        -- hentry_wf.2.2.2.1 : ∀ ety, appliesToPrincipal.contains ety → EntityType.WellFormed
        have hprinc_wf := hentry_wf.2.2.2.1 rt.principal (Set.contains_prop_bool_equiv.mpr hprinc)
        simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType] at hprinc_wf
        cases hprinc_wf with
        | inl h => exact Or.inl h
        | inr h =>
          right
          obtain ⟨uid, hc, heq⟩ := h
          simp only [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
          exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩)
      (by -- hreqty_resource ∨ actionType?
        have hreqty_wf := henv_wf.2.2
        have hacts_wf := henv_wf.2.1
        obtain ⟨entry, hfind, _, hres, _⟩ := hreqty_wf
        have hentry_wf := hacts_wf.2.1 rt.action entry hfind
        have hres_wf := hentry_wf.2.2.2.2.1 rt.resource (Set.contains_prop_bool_equiv.mpr hres)
        simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType] at hres_wf
        cases hres_wf with
        | inl h => exact Or.inl h
        | inr h =>
          right
          obtain ⟨uid, hc, heq⟩ := h
          simp only [ActionSchema.actionType?, Set.any, List.any_eq_true, beq_iff_eq]
          exact ⟨uid, Map.in_keys_iff_contains.mpr hc, heq⟩)
      (wf_env_implies_wf_request henv_wf).2.2.2 -- hctx_wf
  -- Step 4: Combine
  -- Simplify the goal using hce₂
  simp only [Except.mapError, hce₂, Except.bind_ok]
  -- Simplify hp₁ using hce₁
  simp only [Except.mapError, hce₁, Except.bind_ok] at hp₁
  -- Now hp₁: (do let pt ← schema₁.environments.mapM ..; if allFalse ..) = .ok ()
  -- Goal: (do let pt ← schema₂.environments.mapM ..; if allFalse ..) = .ok ()
  rw [← hmapM]
  exact hp₁

end Cedar.Thm

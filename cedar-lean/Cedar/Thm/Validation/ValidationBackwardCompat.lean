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
import Cedar.Thm.Validation.ValidationBackwardCompat.LubWF
import Cedar.Thm.Validation.ValidationBackwardCompat.TypeOfWF
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

private theorem actionType_implies_contains {acts : ActionSchema} {ety : EntityType}
    (h : acts.actionType? ety = true) :
    ∃ uid, acts.contains uid = true ∧ uid.ty = ety := by
  simp only [ActionSchema.actionType?, Set.any] at h
  rw [List.any_eq_true] at h
  obtain ⟨uid, hmem, hty⟩ := h
  exact ⟨uid, Map.in_keys_iff_contains.mp hmem, beq_iff_eq.mp hty⟩

/-- Convert `EntityType.WellFormed` (Prop) to `ets.contains ∨ acts.actionType?` (Bool). -/
private theorem entityType_wf_to_bool {env : TypeEnv} {ety : EntityType}
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

/-! ## Helpers: entity types from schema are well-formed -/

private theorem entity_type_wf_from_record_wf
    {env : TypeEnv} {rty : RecordType} {a : Attr}
    {qty : Qualified CedarType} {ety : EntityType}
    (hwf : (CedarType.record rty).WellFormed env)
    (hfind_a : rty.find? a = some qty)
    (hty : qty.getType = .entity ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  cases hwf with
  | record_wf _ hattr_wf =>
    have htype_wf : CedarType.WellFormed env (.entity ety) := by
      rw [← hty]; exact qty_wf_implies_type_of_wf (hattr_wf a qty hfind_a)
    cases htype_wf with | entity_wf h => exact entityType_wf_to_bool h

private theorem entity_type_wf_from_attrs
    {env : TypeEnv} {ety_parent : EntityType} {rty : RecordType} {a : Attr}
    {qty : Qualified CedarType} {ety : EntityType}
    (hets_wf : EntitySchema.WellFormed env env.ets)
    (hattrs : env.ets.attrs? ety_parent = some rty)
    (hfind_a : rty.find? a = some qty)
    (hty : qty.getType = .entity ety) :
    env.ets.contains ety ∨ env.acts.actionType? ety := by
  simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
  obtain ⟨entry, hfind_e, hattrs_eq⟩ := hattrs
  have hentry_wf := hets_wf.2 ety_parent entry hfind_e
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
  exact entity_type_wf_from_record_wf hwf_record hfind_a hty

/-! ## Corollaries of typeOf_produces_wf_type (defined in TypeOfWF.lean) -/
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
  rw [hty] at hwf; cases hwf with | entity_wf h => exact entityType_wf_to_bool h

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

private theorem ets_find_agree
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

private theorem ets_attrs_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.attrs? ety = ets₂.attrs? ety := by
  simp only [EntitySchema.attrs?, ets_find_agree hfwd hdisjoint₂ hinv]

private theorem ets_tags_agree
    {ets₁ ets₂ : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hfwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hdisjoint₂ : ∀ uid, acts.contains uid = true → ¬ ets₂.contains uid.ty)
    (hinv : ets₁.contains ety ∨ acts.actionType? ety) :
    ets₁.tags? ety = ets₂.tags? ety := by
  simp only [EntitySchema.tags?, ets_find_agree hfwd hdisjoint₂ hinv]

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
  · rw [ets_find_agree hfwd hdisjoint₂ hinv]

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

/-- Derive all preconditions for `typeOf_preserved` from `TypeEnv.WellFormed`. -/
private theorem typeEnv_wf_preconditions {env : TypeEnv} (hwf : env.WellFormed) :
    env.acts.contains env.reqty.action = true ∧
    (env.ets.contains env.reqty.principal ∨ env.acts.actionType? env.reqty.principal) ∧
    (env.ets.contains env.reqty.resource ∨ env.acts.actionType? env.reqty.resource) ∧
    (CedarType.record env.reqty.context).WellFormed env := by
  have ⟨hp, ha, hr, hc⟩ := wf_env_implies_wf_request hwf
  exact ⟨ha, entityType_wf_to_bool hp, entityType_wf_to_bool hr, hc⟩

theorem typecheckPolicy_preserved_of_ets_extension
    {policy : Policy} {env₁ env₂ : TypeEnv}
    (hreqty : env₁.reqty = env₂.reqty)
    (hacts : env₁.acts = env₂.acts)
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok ())
    (hdisjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty)
    (hwf₁ : env₁.WellFormed) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  have ⟨haction, hprinc, hres, hctx⟩ := typeEnv_wf_preconditions hwf₁
  simp only [typecheckPolicy]
  have haction_valid : (env₁.ets.isValidEntityUID env₁.reqty.action ||
                        env₁.acts.contains env₁.reqty.action) = true := by
    simp [haction]
  have hce_sub := checkEntities_substituteAction hce haction_valid
  have := typeOf_preserved_of_ets_extension
    (substituteAction env₁.reqty.action policy.toExpr) ∅
    hreqty hacts hets_fwd hce_sub hdisjoint₂ hwf₁.1 haction hprinc hres hctx
  simp only [hreqty] at this ⊢
  rw [this]

/-! ## Top-level theorem -/

/--
**Backward compatibility**: adding new entity types to the entity schema never
invalidates existing policies. If policies validate on schema₁, and schema₂ has
the same actions but an extended entity schema (all old entries preserved), then
policies also validate on schema₂.
-/
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
      (by rw [← hacts_eq]; exact hce₁) hdisjoint₂ henv_wf
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

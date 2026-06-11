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
import Cedar.Thm.WellTyped.Expr.WF
import Cedar.Thm.Validation.ValidationPolicySlice
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


/-! ## Type invariant from existing typechecked_has_well_formed_type -/

/-- Entity types produced by `typeOf` are in ets or are action types. -/
private theorem typeOf_entity_type_in_ets (expr : Expr) (c : Capabilities)
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

/-- Two environments where env₂ extends env₁'s entity schema. -/
structure EtsExtension (env₁ env₂ : TypeEnv) : Prop where
  reqty_eq : env₁.reqty = env₂.reqty
  acts_eq : env₁.acts = env₂.acts
  ets_fwd : ∀ ety entry, env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry
  disjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty
  wf₁ : env₁.WellFormed

private theorem disjoint_backward
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
    simp [EntitySchema.contains, hets_fwd ety entry hf]

private theorem checkEntities_pair' {schema : Schema} {e₁ e₂ : Expr}
    (h : (do checkEntities schema e₁; checkEntities schema e₂) = .ok ()) :
    checkEntities schema e₁ = .ok () ∧ checkEntities schema e₂ = .ok () := by
  cases h₁ : checkEntities schema e₁ with
  | error e => simp [h₁] at h
  | ok _ => simp [h₁] at h; exact ⟨rfl, h⟩


theorem typeOf_preserved_of_ets_extension (expr : Expr) (c : Capabilities)
    {env₁ env₂ : TypeEnv} (h : EtsExtension env₁ env₂)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ expr = .ok ()) :
    typeOf expr c env₁ = typeOf expr c env₂ := by
  have hreqty := h.reqty_eq
  have hacts := h.acts_eq
  have hets_fwd := h.ets_fwd
  have hdisjoint₂ := h.disjoint₂
  have hwf₁ := h.wf₁
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
      rw [typeOf_preserved_of_ets_extension x₁ c h hce]
    · contradiction
  | .unaryApp (.not) x₁ | .unaryApp (.neg) x₁ | .unaryApp (.like _) x₁ | .unaryApp (.isEmpty) x₁ =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_preserved_of_ets_extension x₁ c h hce₁]
  | .and x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair' hce'
    simp only [typeOf]
    rw [typeOf_preserved_of_ets_extension x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_preserved_of_ets_extension x₂ (c ∪ c₁) h hce₂]
  | .or x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair' hce'
    simp only [typeOf]
    rw [typeOf_preserved_of_ets_extension x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_preserved_of_ets_extension x₂ c h hce₂]
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
    rw [typeOf_preserved_of_ets_extension x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    simp only [typeOfIf]
    split <;> try rfl
    · rw [typeOf_preserved_of_ets_extension x₂ (c ∪ c₁) h hce₂]
    · rw [typeOf_preserved_of_ets_extension x₃ c h hce₃]
    · rw [typeOf_preserved_of_ets_extension x₂ (c ∪ c₁) h hce₂,
           typeOf_preserved_of_ets_extension x₃ c h hce₃]
  | .binaryApp op x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair' hce'
    simp only [typeOf]
    have hih₁ := typeOf_preserved_of_ets_extension x₁ c h hce₁
    have hih₂ := typeOf_preserved_of_ets_extension x₂ c h hce₂
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
        have hinv₁ : ∀ ety, tx₁.typeOf = .entity ety →
            env₁.ets.contains ety ∨ env₁.acts.actionType? ety :=
          fun ety hety => typeOf_entity_type_in_ets x₁ c hwf₁ hr₁' hety
        have hdisjoint₁ := disjoint_backward hets_fwd hacts hdisjoint₂
        unfold typeOfBinaryApp
        split
        · rfl
        · rename_i ety₁ _ heq_tx₁ _
          simp [typeOfInₑ, actionUID?, hacts, TypeEnv.descendentOf,
            ets_find_agree hets_fwd (hacts ▸ hdisjoint₂) (hinv₁ ety₁ heq_tx₁)]
        · rename_i ety₁ _ heq_tx₁ _
          simp [typeOfInₛ, actionUID?, hacts, TypeEnv.descendentOf,
            ets_find_agree hets_fwd (hacts ▸ hdisjoint₂) (hinv₁ ety₁ heq_tx₁)]
        · rename_i ety₁ heq_tx₁ _
          simp [typeOfHasTag, ets_tags_agree hets_fwd (hacts ▸ hdisjoint₂) (hinv₁ ety₁ heq_tx₁), hacts]
        · rename_i ety₁ heq_tx₁ _
          simp [typeOfGetTag, ets_tags_agree hets_fwd (hacts ▸ hdisjoint₂) (hinv₁ ety₁ heq_tx₁)]
        all_goals rfl
  | .hasAttr x₁ _ | .getAttr x₁ _ =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    have hih := typeOf_preserved_of_ets_extension x₁ c h hce₁
    simp only [typeOf]
    cases hr : typeOf x₁ c env₁ with
    | error e => simp [hih ▸ hr]
    | ok val =>
      obtain ⟨tx₁, c₁⟩ := val
      simp only [Except.bind_ok]
      rw [show typeOf x₁ c env₂ = .ok (tx₁, c₁) from hih ▸ hr]
      simp only [Except.bind_ok, typeOfHasAttr, typeOfGetAttr]
      cases htx : tx₁.typeOf with
      | entity ety =>
        simp [ets_attrs_agree hets_fwd (hacts ▸ hdisjoint₂) (typeOf_entity_type_in_ets x₁ c hwf₁ hr htx), hacts]
      | record _ => rfl
      | _ => rfl
  | .set xs | .call _ xs =>
    have hce_all : ∀ x ∈ xs, checkEntities ⟨env₁.ets, env₁.acts⟩ x = .ok () := by
      intro x hx
      have hce' : xs.attach.forM (fun ⟨x, _⟩ => checkEntities ⟨env₁.ets, env₁.acts⟩ x) = .ok () := by
        simp only [checkEntities] at hce; exact hce
      have := List.forM_ok_implies_all_ok' hce' ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩)
      simpa using this
    have hmapM : List.mapM (fun x => justType (typeOf x c env₁)) xs =
                 List.mapM (fun x => justType (typeOf x c env₂)) xs :=
      List.mapM_congr (fun x hx => congrArg justType
        (typeOf_preserved_of_ets_extension x c h (hce_all x hx)))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  | .record axs =>
    have hce_all : ∀ ax ∈ axs, checkEntities ⟨env₁.ets, env₁.acts⟩ ax.snd = .ok () := by
      intro ax hax
      have hce' := hce; simp only [checkEntities] at hce'
      have hmem : ⟨ax, List.sizeOf_snd_lt_sizeOf_list hax⟩ ∈ axs.attach₂ := by
        simp only [List.attach₂, List.mem_pmap]; exact ⟨ax, hax, rfl⟩
      exact List.forM_ok_implies_all_ok' hce' _ hmem
    have hmapM : List.mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs =
                 List.mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs :=
      List.mapM_congr (fun ax hax => by
        have := List.sizeOf_snd_lt_sizeOf_list hax
        rw [typeOf_preserved_of_ets_extension ax.snd c h (hce_all ax hax)])
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs,
      hmapM]
  termination_by sizeOf expr

/-! ## Policy-level preservation -/

theorem typecheckPolicy_preserved_of_ets_extension
    {policy : Policy} {env₁ env₂ : TypeEnv}
    (h : EtsExtension env₁ env₂)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ policy.toExpr = .ok ()) :
    typecheckPolicy policy env₁ = typecheckPolicy policy env₂ := by
  simp only [typecheckPolicy]
  have haction_valid : (env₁.ets.isValidEntityUID env₁.reqty.action ||
                        env₁.acts.contains env₁.reqty.action) = true := by
    simp [(wf_env_implies_wf_request h.wf₁).2.1]
  have := typeOf_preserved_of_ets_extension _ ∅ h (checkEntities_substituteAction hce haction_valid)
  simp only [h.reqty_eq] at this ⊢; rw [this]

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
  simp only [validate] at hold ⊢
  apply List.all_ok_implies_forM_ok
  intro p hp
  have hp₁ := List.forM_ok_implies_all_ok' hold p hp
  simp only [typecheckPolicyWithEnvironments] at hp₁ ⊢
  have hce₁ : checkEntities schema₁ p.toExpr = .ok () := by
    cases hce : checkEntities schema₁ p.toExpr with
    | ok _ => rfl
    | error e => simp [Except.mapError, hce] at hp₁
  have hce₂ : checkEntities schema₂ p.toExpr = .ok () :=
    checkEntities_monotone p.toExpr
      (fun uid hv => isValidOrContains_fwd hets_fwd hacts_eq hv)
      (fun ety hv => contains_or_actionType_fwd hets_fwd hacts_eq hv) hce₁
  have hmapM : schema₁.environments.mapM (typecheckPolicy p) =
               schema₂.environments.mapM (typecheckPolicy p) := by
    simp only [Schema.environments, hacts_eq]
    rw [List.mapM_map, List.mapM_map]
    apply List.mapM_congr
    intro rt hrt
    simp only [Function.comp]
    have henv_in : ({ ets := schema₁.ets, acts := schema₂.acts, reqty := rt } : TypeEnv) ∈
        schema₁.environments := by
      simp only [Schema.environments, hacts_eq, List.mem_map]; exact ⟨rt, hrt, rfl⟩
    exact typecheckPolicy_preserved_of_ets_extension
      ⟨rfl, rfl, hets_fwd, hdisjoint₂,
       env_validate_well_formed_is_sound (List.forM_ok_implies_all_ok' hwf₁ _ henv_in)⟩
      (by rw [← hacts_eq]; exact hce₁)
  simp only [Except.mapError, hce₂, Except.bind_ok]
  simp only [Except.mapError, hce₁, Except.bind_ok] at hp₁
  rw [← hmapM]; exact hp₁

/-! ## Executable backward-compatibility check -/

private instance : DecidableEq ActionSchemaEntry := by
  intro a b
  cases a; cases b
  simp only [ActionSchemaEntry.mk.injEq]
  exact inferInstance

/--
Decidable check that `schema₂` is a backward-compatible entity-schema extension
of `schema₁`. Returns `true` when:
- The action schemas are identical
- Every entity type entry in `schema₁` has the same entry in `schema₂`
- No action uid's entity type collides with `schema₂.ets`
-/
def isValidEtsExtension (schema₁ schema₂ : Schema) : Bool :=
  (schema₁.acts.toList == schema₂.acts.toList) &&
  schema₁.ets.toList.all (fun (ety, entry) => schema₂.ets.find? ety == some entry) &&
  schema₂.acts.toList.all (fun (uid, _) => !schema₂.ets.contains uid.ty)


private theorem ets_fwd_of_all_find
    {ets₁ ets₂ : EntitySchema}
    (h : ets₁.toList.all (fun (ety, entry) => ets₂.find? ety == some entry) = true) :
    ∀ ety entry, ets₁.find? ety = some entry → ets₂.find? ety = some entry := by
  intro ety entry hfind
  have hmem := Map.find?_mem_toList hfind
  have := List.all_eq_true.mp h (ety, entry) hmem
  simp [beq_iff_eq] at this
  exact this

private theorem disjoint_of_acts_all
    {acts : ActionSchema} {ets : EntitySchema}
    (h : acts.toList.all (fun (uid, _) => !ets.contains uid.ty) = true) :
    ∀ uid, acts.contains uid = true → ¬ ets.contains uid.ty := by
  intro uid hc hets
  have ⟨entry, hfind⟩ := Map.contains_iff_some_find?.mp hc
  have hmem := Map.find?_mem_toList hfind
  have hall := List.all_eq_true.mp h (uid, entry) hmem
  simp only [Bool.not_eq_true'] at hall
  rw [hets] at hall
  exact absurd hall (by simp)

/--
**Executable backward compatibility**: if `isValidEtsExtension schema₁ schema₂`
returns `true` and policies validate on `schema₁`, they also validate on `schema₂`.

This is a fully decidable algorithm: given two schemas, run `isValidEtsExtension`
to determine whether adding entity types to schema₁ to produce schema₂ preserves
validation of all policies.
-/
theorem validate_of_isValidEtsExtension
    (schema₁ schema₂ : Schema)
    (policies : Policies)
    (hext : isValidEtsExtension schema₁ schema₂ = true)
    (hwf₁ : schema₁.validateWellFormed = .ok ())
    (hold : validate policies schema₁ = .ok ()) :
    validate policies schema₂ = .ok () := by
  simp only [isValidEtsExtension, Bool.and_eq_true] at hext
  obtain ⟨⟨hacts_list, hets_all⟩, hdisj_all⟩ := hext
  have hacts : schema₁.acts = schema₂.acts :=
    Map.eq_iff_toList_eq.mp ((beq_iff_eq (α := List _)).mp hacts_list)
  exact validate_preserved_of_ets_extension schema₁ schema₂ policies
    hacts (ets_fwd_of_all_find hets_all) (disjoint_of_acts_all hdisj_all) hwf₁ hold

/-! ## Backward compatibility for appliesTo removal -/

/--
Check that `newSchema` is an "appliesTo restriction" of `oldSchema`: same entity
types, and for each action, the context and ancestors are unchanged and the
appliesTo sets have only shrunk (new ⊆ old).
-/
def isAppliesToRestriction (oldSchema newSchema : Schema) : Bool :=
  (oldSchema.ets.toList == newSchema.ets.toList) &&
  -- Every old action exists in new with same ancestors
  oldSchema.acts.toList.all (fun (action, oldEntry) =>
    match newSchema.acts.find? action with
    | none => false
    | some newEntry => decide (oldEntry.ancestors = newEntry.ancestors)) &&
  -- Every new action exists in old with same context/ancestors, appliesTo ⊆ old and well-formed
  newSchema.acts.toList.all (fun (action, newEntry) =>
    match oldSchema.acts.find? action with
    | none => false
    | some oldEntry =>
      decide (oldEntry.context = newEntry.context) &&
      newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal &&
      newEntry.appliesToResource.subset oldEntry.appliesToResource &&
      newEntry.appliesToPrincipal.wellFormed &&
      newEntry.appliesToResource.wellFormed) &&
  -- newSchema.acts is a well-formed map
  newSchema.acts.wellFormed

private theorem isAppliesToRestriction_implies_rfr_false
    {oldSchema newSchema : Schema}
    (h : isAppliesToRestriction oldSchema newSchema = true) :
    Cedar.Slice.requiresFullRevalidation oldSchema newSchema = false := by
  simp only [isAppliesToRestriction, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hets, hold_all⟩, hnew_all⟩, _⟩ := h
  have hets_eq : oldSchema.ets = newSchema.ets :=
    Map.eq_iff_toList_eq.mp ((beq_iff_eq (α := List _)).mp hets)
  have h1 : (oldSchema.ets != newSchema.ets) = false := by simp [bne_iff_ne, hets_eq]
  have h2 : oldSchema.acts.toList.any (fun x =>
      match newSchema.acts.find? x.1 with
      | none => true
      | some newEntry => x.2.ancestors != newEntry.ancestors) = false := by
    rw [List.any_eq_false]
    intro ⟨action, oldEntry⟩ hmem
    have h_entry := List.all_eq_true.mp hold_all _ hmem
    simp only at h_entry
    cases hfn : newSchema.acts.find? action with
    | none => simp [hfn] at h_entry
    | some newEntry =>
      simp only [hfn, decide_eq_true_eq] at h_entry
      simp [hfn, bne_iff_ne, h_entry]
  have h3 : newSchema.acts.toList.any (fun x =>
      !(oldSchema.acts.contains x.1) &&
      (!x.2.ancestors.isEmpty || !(oldSchema.acts.actionType? x.1.ty))) = false := by
    rw [List.any_eq_false]
    intro ⟨action, newEntry⟩ hmem
    have h_entry := List.all_eq_true.mp hnew_all _ hmem
    simp only at h_entry
    cases hfo : oldSchema.acts.find? action with
    | none => simp [hfo] at h_entry
    | some _ => simp [ActionSchema.contains, hfo]
  have key : ∀ (a b c : Bool), a = false → b = false → c = false → (a || b || c) = false := by
    intros; simp_all
  exact key _ _ _ h1 h2 h3

private theorem isAppliesToRestriction_implies_no_changes
    {oldSchema newSchema : Schema}
    (h : isAppliesToRestriction oldSchema newSchema = true) :
    Cedar.Slice.computeActionChanges oldSchema newSchema = [] := by
  simp only [isAppliesToRestriction, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, hnew_all⟩, _⟩ := h
  simp only [Cedar.Slice.computeActionChanges]
  rw [List.filterMap_eq_nil_iff]
  intro ⟨action, newEntry⟩ hmem
  have h_entry := List.all_eq_true.mp hnew_all _ hmem
  simp only at h_entry
  cases hfo : oldSchema.acts.find? action with
  | none => simp [hfo] at h_entry
  | some oldEntry =>
    simp only [hfo, Bool.and_eq_true, decide_eq_true_eq] at h_entry
    obtain ⟨⟨hctx, hprinc⟩, hres⟩ := h_entry
    simp [hfo, bne_iff_ne, hctx.symm, hprinc, hres]

/--
**Backward compatibility for appliesTo removal**: if `isAppliesToRestriction`
passes (same entity types, same action hierarchy, appliesTo only shrunk) and
policies validate on `oldSchema`, then `validateOrImpossible` passes on
`newSchema`.

Policies may become "impossible" (all environments produce `.bool .ff`) when
appliesTo entries are removed, but cannot acquire new type errors.
-/
private theorem mem_of_subset_toList {α : Type} [DecidableEq α] {s₁ s₂ : Set α} {a : α}
    (hmem : a ∈ s₁.toList) (hsub : s₁.subset s₂ = true) : a ∈ s₂.toList := by
  unfold Set.subset at hsub
  unfold Set.toList at hmem ⊢
  have h := List.all_eq_true.mp hsub a hmem
  unfold Set.contains at h
  rw [List.elem_eq_mem] at h
  grind

/-- Extract `ets_eq` from `isAppliesToRestriction`. -/
private theorem isAppliesToRestriction_ets_eq
    {oldSchema newSchema : Schema}
    (hrestr : isAppliesToRestriction oldSchema newSchema = true) :
    oldSchema.ets = newSchema.ets := by
  simp only [isAppliesToRestriction, Bool.and_eq_true] at hrestr
  exact Map.eq_iff_toList_eq.mp ((beq_iff_eq (α := List _)).mp hrestr.1.1.1)

/-- From `isAppliesToRestriction`, every new action has a corresponding old entry. -/
private theorem isAppliesToRestriction_new_in_old
    {oldSchema newSchema : Schema}
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    {action : EntityUID} {newEntry : ActionSchemaEntry}
    (hmem : (action, newEntry) ∈ newSchema.acts.toList) :
    ∃ oldEntry, oldSchema.acts.find? action = some oldEntry ∧
      oldEntry.context = newEntry.context ∧
      newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal = true ∧
      newEntry.appliesToResource.subset oldEntry.appliesToResource = true := by
  simp only [isAppliesToRestriction, Bool.and_eq_true] at hrestr
  have h_entry := List.all_eq_true.mp hrestr.1.2 _ hmem
  simp only at h_entry
  cases hfo : oldSchema.acts.find? action with
  | none => simp [hfo] at h_entry
  | some oldEntry =>
    simp only [hfo, Bool.and_eq_true, decide_eq_true_eq] at h_entry
    exact ⟨oldEntry, by grind, h_entry.1.1.1.1, by grind, by grind⟩

/-- If new schema has non-empty environments and appliesTo restricted, old is also non-empty. -/
private theorem appliesTo_restriction_envs_ne
    {oldSchema newSchema : Schema}
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    (henvs_new : newSchema.environments ≠ []) :
    oldSchema.environments ≠ [] := by
  intro h_empty
  apply henvs_new
  simp only [Schema.environments, List.map_eq_nil_iff] at h_empty ⊢
  rw [List.flatMap_eq_nil_iff] at h_empty ⊢
  intro ⟨action, newEntry⟩ hmem_new
  obtain ⟨oldEntry, hfind_old, _, hprinc_sub, hres_sub⟩ :=
    isAppliesToRestriction_new_in_old hrestr hmem_new
  have hold_empty := h_empty (action, oldEntry) (Map.find?_mem_toList hfind_old)
  simp only [ActionSchemaEntry.requestTypes, List.map_eq_nil_iff] at hold_empty ⊢
  by_contra h_ne
  have h_ne' : newEntry.appliesToPrincipal.toList.product newEntry.appliesToResource.toList ≠ [] := by
    intro h_eq; exact h_ne (by simp [h_eq])
  obtain ⟨⟨p, r⟩, hpr_mem⟩ := List.exists_mem_of_ne_nil _ h_ne'
  have ⟨hp, hr⟩ : p ∈ newEntry.appliesToPrincipal.toList ∧ r ∈ newEntry.appliesToResource.toList := by
    simp [List.product, List.mem_flatMap, List.mem_map] at hpr_mem; exact hpr_mem
  have hp_old := mem_of_subset_toList hp (show newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal = true by grind)
  have hr_old := mem_of_subset_toList hr (show newEntry.appliesToResource.subset oldEntry.appliesToResource = true by grind)
  have hpr_old : (p, r) ∈ oldEntry.appliesToPrincipal.toList.product oldEntry.appliesToResource.toList := by
    simp [List.product, List.mem_flatMap, List.mem_map]; exact ⟨hp_old, hr_old⟩
  simp [hold_empty] at hpr_old

theorem validateOrImpossible_of_appliesTo_restriction
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    (hwf₁ : Schema.validateWellFormed oldSchema = .ok ())
    (hold : validate policies oldSchema = .ok ()) :
    Cedar.Slice.validateOrImpossible policies newSchema = true := by
  have hno_full := isAppliesToRestriction_implies_rfr_false hrestr
  have hno_changes := isAppliesToRestriction_implies_no_changes hrestr
  have hacts_wf₂ : newSchema.acts.wellFormed := by
    simp only [isAppliesToRestriction, Bool.and_eq_true] at hrestr; exact hrestr.2
  have hets_eq := isAppliesToRestriction_ets_eq hrestr
  by_cases henvs_new : newSchema.environments = []
  · exact validateOrImpossible_of_empty_envs henvs_new hno_full hold
  have ⟨hacts_wf₁, hdisjoint_old⟩ :=
    validateWellFormed_gives_wf_and_disjoint hwf₁
      (List.exists_mem_of_ne_nil _ (appliesTo_restriction_envs_ne hrestr henvs_new)).choose_spec
  have hdisjoint : ∀ uid, newSchema.acts.contains uid = true →
      newSchema.ets.isValidEntityUID uid = false := by
    intro uid hc
    rw [← hets_eq]
    obtain ⟨_, hfind_old, _, _, _⟩ :=
      isAppliesToRestriction_new_in_old hrestr (Map.find?_mem_toList (Map.contains_iff_some_find?.mp hc).choose_spec)
    exact hdisjoint_old uid (by simp [ActionSchema.contains, hfind_old])
  simp only [Cedar.Slice.validateOrImpossible, List.all_eq_true]
  intro p hp
  exact nonslice_policy_noTypeErrors hno_full
    (List.forM_ok_implies_all_ok' (by simp [validate] at hold; exact hold) p hp)
    (by simp [hno_changes, Cedar.Slice.actionScopeMatchesAnyChangedAction])
    hacts_wf₁ hacts_wf₂ hdisjoint

end Cedar.Thm

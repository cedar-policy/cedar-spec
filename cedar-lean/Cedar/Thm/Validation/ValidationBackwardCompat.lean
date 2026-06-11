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
        have hdisjoint₁ : ∀ uid, env₁.acts.contains uid = true → ¬ env₁.ets.contains uid.ty :=
          fun uid hc hc₁ => hdisjoint₂ uid (hacts ▸ hc) (by
            simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc₁ ⊢
            obtain ⟨e, hf⟩ := hc₁; exact ⟨e, hets_fwd uid.ty e hf⟩)
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
    simp only [typeOf]
    have hih := typeOf_preserved_of_ets_extension x₁ c h hce₁
    cases hr : typeOf x₁ c env₁ with
    | error e => simp [hih ▸ hr]
    | ok val =>
      obtain ⟨tx₁, c₁⟩ := val
      simp only [Except.bind_ok]
      rw [show typeOf x₁ c env₂ = .ok (tx₁, c₁) from hih ▸ hr]
      simp only [Except.bind_ok]
      simp only [typeOfHasAttr, typeOfGetAttr]
      cases htx : tx₁.typeOf with
      | entity ety =>
        have hinv := typeOf_entity_type_in_ets x₁ c hwf₁ hr htx
        simp [ets_attrs_agree hets_fwd (hacts ▸ hdisjoint₂) hinv, hacts]
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

end Cedar.Thm

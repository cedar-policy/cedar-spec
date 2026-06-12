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
import Cedar.Thm.WellTyped.Expr.WF
import Cedar.Thm.Validation.ValidationPolicySlice.CheckEntities
import Cedar.Thm.Data

/-!
# typeOf Congruence Theorems

Two independent congruence results for the Cedar typechecker:

## `typeOf_congr_acts` (same entity schema, different actions)

If two environments have the same entity schema and agree on action schema queries,
then `typeOf` gives the same result. Requires `checkEntities` to pass on env₁.

## `typeOf_congr_ets` (same actions, extended entity schema)

If two environments have the same actions and the entity schema is forward-preserved,
then `typeOf` gives the same result. Requires `checkEntities` to pass on env₁ and
`env₁.WellFormed`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 12800000

/-! ## typeOf congruence: same ets, different acts -/

/-- Preconditions for `typeOf_congr_acts`: same ets, acts queries agree. -/
structure ActsAgreement (env₁ env₂ : TypeEnv) : Prop where
  reqty_eq : env₁.reqty = env₂.reqty
  ets_eq : env₁.ets = env₂.ets
  acts_contains_fwd : ∀ uid, env₁.acts.contains uid = true → env₂.acts.contains uid = true
  acts_actionType : ∀ ety, env₁.acts.actionType? ety = env₂.acts.actionType? ety
  acts_descendentOf : ∀ uid₁ uid₂, env₁.acts.descendentOf uid₁ uid₂ = env₂.acts.descendentOf uid₁ uid₂
  acts_maybeDescendentOf : ∀ ety₁ ety₂, env₁.acts.maybeDescendentOf ety₁ ety₂ = env₂.acts.maybeDescendentOf ety₁ ety₂
  disjoint₂ : ∀ uid, env₂.acts.contains uid = true → env₂.ets.isValidEntityUID uid = false


/--
For entity UIDs valid on env₁ (via ets or acts), `acts.contains` agrees between
the two envs. This is the key lemma that makes ActsAgreement sufficient.
-/
private theorem ets_isValidEntityUID_fwd {env₁ env₂ : TypeEnv}
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry)
    {uid : EntityUID}
    (hvalid : env₁.ets.isValidEntityUID uid = true) :
    env₂.ets.isValidEntityUID uid = true := by
  simp only [EntitySchema.isValidEntityUID] at hvalid ⊢
  cases hf : env₁.ets.find? uid.ty with
  | none => simp [hf] at hvalid
  | some entry => rw [hets_fwd uid.ty entry hf]; simp [hf] at hvalid; exact hvalid

private theorem acts_contains_agree_for_valid {env₁ env₂ : TypeEnv}
    (h : ActsAgreement env₁ env₂)
    {uid : EntityUID}
    (hvalid : (env₁.ets.isValidEntityUID uid || env₁.acts.contains uid) = true) :
    env₁.acts.contains uid = env₂.acts.contains uid := by
  cases hc : env₁.acts.contains uid with
  | true => exact (h.acts_contains_fwd uid hc).symm ▸ rfl
  | false =>
    simp [hc] at hvalid
    have hvalid₂ : env₂.ets.isValidEntityUID uid = true := by rw [← h.ets_eq]; exact hvalid
    have hnotacts₂ : env₂.acts.contains uid = false := by
      by_contra habs; simp at habs
      exact absurd hvalid₂ (by simp [h.disjoint₂ uid habs])
    rw [hnotacts₂]



/--
`actionUID?` agrees between two envs under `ActsAgreement` for expressions
whose entity UIDs are all valid on env₁.
-/
private theorem actionUID_agree {env₁ env₂ : TypeEnv} (h : ActsAgreement env₁ env₂)
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

theorem typeOf_congr_acts (expr : Expr) (c : Capabilities) {env₁ env₂ : TypeEnv}
    (h : ActsAgreement env₁ env₂)
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
      rw [typeOf_congr_acts x₁ c h hce]
    · contradiction
  | .unaryApp (.not) x₁ | .unaryApp (.neg) x₁ | .unaryApp (.like _) x₁ | .unaryApp (.isEmpty) x₁ =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_congr_acts x₁ c h hce₁]
  | .and x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_congr_acts x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_congr_acts x₂ (c ∪ c₁) h hce₂]
  | .or x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_congr_acts x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_congr_acts x₂ c h hce₂]
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
    rw [typeOf_congr_acts x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    simp only [typeOfIf]
    split <;> try rfl
    · rw [typeOf_congr_acts x₂ (c ∪ c₁) h hce₂]
    · rw [typeOf_congr_acts x₃ c h hce₃]
    · rw [typeOf_congr_acts x₂ (c ∪ c₁) h hce₂, typeOf_congr_acts x₃ c h hce₃]
  | .binaryApp op x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_congr_acts x₁ c h hce₁, typeOf_congr_acts x₂ c h hce₂]
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
    rw [typeOf_congr_acts x₁ c h hce₁]
    congr 1; funext ⟨tx₁, _⟩
    simp [typeOfHasAttr, h.ets_eq, h.acts_actionType]
  | .getAttr x₁ a =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_congr_acts x₁ c h hce₁]
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
      List.mapM_congr (fun x hx => congrArg justType (typeOf_congr_acts x c h (hce_all x hx)))
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
        rw [typeOf_congr_acts ax.snd c h (hce_all ax hax)])
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
      List.mapM_congr (fun x hx => congrArg justType (typeOf_congr_acts x c h (hce_all x hx)))
    simp only [typeOf,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁)) xs,
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₂)) xs, hmapM]
  termination_by sizeOf expr


/-! ## Helpers for ets extension congruence -/

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

/-- Preconditions for `typeOf_congr_ets`: same acts, ets forward-preserved. -/
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

/-! ## typeOf congruence: same acts, extended ets -/

theorem typeOf_congr_ets (expr : Expr) (c : Capabilities)
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
      rw [typeOf_congr_ets x₁ c h hce]
    · contradiction
  | .unaryApp (.not) x₁ | .unaryApp (.neg) x₁ | .unaryApp (.like _) x₁ | .unaryApp (.isEmpty) x₁ =>
    have hce₁ : checkEntities ⟨env₁.ets, env₁.acts⟩ x₁ = .ok () := by
      unfold checkEntities at hce; exact hce
    simp only [typeOf]
    rw [typeOf_congr_ets x₁ c h hce₁]
  | .and x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_congr_ets x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_congr_ets x₂ (c ∪ c₁) h hce₂]
  | .or x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    rw [typeOf_congr_ets x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    rw [typeOf_congr_ets x₂ c h hce₂]
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
    rw [typeOf_congr_ets x₁ c h hce₁]
    congr 1; funext ⟨tx₁, c₁⟩
    simp only [typeOfIf]
    split <;> try rfl
    · rw [typeOf_congr_ets x₂ (c ∪ c₁) h hce₂]
    · rw [typeOf_congr_ets x₃ c h hce₃]
    · rw [typeOf_congr_ets x₂ (c ∪ c₁) h hce₂,
           typeOf_congr_ets x₃ c h hce₃]
  | .binaryApp op x₁ x₂ =>
    have hce' := hce; unfold checkEntities at hce'
    have ⟨hce₁, hce₂⟩ := checkEntities_pair hce'
    simp only [typeOf]
    have hih₁ := typeOf_congr_ets x₁ c h hce₁
    have hih₂ := typeOf_congr_ets x₂ c h hce₂
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
    have hih := typeOf_congr_ets x₁ c h hce₁
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
        (typeOf_congr_ets x c h (hce_all x hx)))
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
        rw [typeOf_congr_ets ax.snd c h (hce_all ax hax)])
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₁).map (fun (ty, _) => (ax.fst, ty))) axs,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => (typeOf ax.snd c env₂).map (fun (ty, _) => (ax.fst, ty))) axs,
      hmapM]
  termination_by sizeOf expr



/-! ## Combined congruence: both ets and acts may differ -/

/-- Preconditions for `typeOf_congr`: ets forward-preserved, acts queries agree. -/
structure EnvAgreement (env₁ env₂ : TypeEnv) : Prop where
  reqty_eq : env₁.reqty = env₂.reqty
  ets_fwd : ∀ ety entry, env₁.ets.find? ety = some entry → env₂.ets.find? ety = some entry
  acts_contains_fwd : ∀ uid, env₁.acts.contains uid = true → env₂.acts.contains uid = true
  acts_actionType : ∀ ety, env₁.acts.actionType? ety = env₂.acts.actionType? ety
  acts_descendentOf : ∀ uid₁ uid₂, env₁.acts.descendentOf uid₁ uid₂ = env₂.acts.descendentOf uid₁ uid₂
  acts_maybeDescendentOf : ∀ ety₁ ety₂, env₁.acts.maybeDescendentOf ety₁ ety₂ = env₂.acts.maybeDescendentOf ety₁ ety₂
  disjoint₂ : ∀ uid, env₂.acts.contains uid = true → ¬ env₂.ets.contains uid.ty
  wf₁ : env₁.WellFormed

/-- The most general typeOf congruence: both ets and acts may differ. -/
theorem typeOf_congr (expr : Expr) (c : Capabilities)
    {env₁ env₂ : TypeEnv} (h : EnvAgreement env₁ env₂)
    (hce : checkEntities ⟨env₁.ets, env₁.acts⟩ expr = .ok ()) :
    typeOf expr c env₁ = typeOf expr c env₂ := by
  -- Factor through intermediate: env_mid = { ets := env₂.ets, acts := env₁.acts, reqty := env₁.reqty }
  -- Step 1: env₁ → env_mid via typeOf_congr_ets (same acts, extended ets)
  -- Step 2: env_mid → env₂ via typeOf_congr_acts (same ets, different acts)
  let env_mid : TypeEnv := { ets := env₂.ets, acts := env₁.acts, reqty := env₁.reqty }
  have hstep1 : typeOf expr c env₁ = typeOf expr c env_mid :=
    typeOf_congr_ets expr c
      ⟨rfl, rfl, h.ets_fwd, fun uid hc => h.disjoint₂ uid (h.acts_contains_fwd uid hc), h.wf₁⟩ hce
  have hce_mid : checkEntities ⟨env_mid.ets, env_mid.acts⟩ expr = .ok () :=
    checkEntities_monotone (schema₁ := ⟨env₁.ets, env₁.acts⟩) (schema₂ := ⟨env₂.ets, env₁.acts⟩) expr
      (fun uid hv => isValidOrContains_fwd h.ets_fwd rfl hv)
      (fun ety hv => by
        cases hc : env₁.ets.contains ety
        · simp [hc] at hv; simp [hv]
        · simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
          obtain ⟨entry, hf⟩ := hc
          simp [EntitySchema.contains, h.ets_fwd ety entry hf])
      hce
  have hstep2 : typeOf expr c env_mid = typeOf expr c env₂ :=
    typeOf_congr_acts expr c
      ⟨h.reqty_eq, rfl, h.acts_contains_fwd, h.acts_actionType, h.acts_descendentOf,
       h.acts_maybeDescendentOf, fun uid hc => by
         simp only [EntitySchema.isValidEntityUID]
         cases hf : env₂.ets.find? uid.ty with
         | none => rfl
         | some _ => exact absurd (ets_contains_of_find hf) (h.disjoint₂ uid hc)⟩
      hce_mid
  rw [hstep1, hstep2]

end Cedar.Thm

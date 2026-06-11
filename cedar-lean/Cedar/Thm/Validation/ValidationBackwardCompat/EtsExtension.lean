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

import Cedar.Thm.Validation.ValidationBackwardCompat.Helpers
import Cedar.Validation.BackwardCompatibility

/-!
# Backward compatibility: entity schema extension

Adding new entity types to the entity schema never invalidates existing policies.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 12800000

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



theorem ets_fwd_of_all_find
    {ets₁ ets₂ : EntitySchema}
    (h : ets₁.toList.all (fun (ety, entry) => ets₂.find? ety == some entry) = true) :
    ∀ ety entry, ets₁.find? ety = some entry → ets₂.find? ety = some entry := by
  intro ety entry hfind
  have hmem := Map.find?_mem_toList hfind
  have := List.all_eq_true.mp h (ety, entry) hmem
  simp [beq_iff_eq] at this
  exact this

theorem disjoint_of_acts_all
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
theorem validate_of_isValidEtsExtension'
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

end Cedar.Thm

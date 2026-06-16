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

import Cedar.Thm.Validation.ValidationBackwardCompat.EtsExtension
import Cedar.Thm.Validation.ValidationBackwardCompat.AppliesToRestriction
import Cedar.Validation.BackwardCompatibility

/-!
# Backward Compatibility for Cedar Schema Changes

This module proves that certain schema changes cannot break policy validation:

## 1. Entity Schema Extension (`validate_of_isValidEtsExtension`)

Adding new entity types to the entity schema never invalidates existing policies.
The executable check `isValidEtsExtension` determines whether a schema change
qualifies.

## 2. AppliesTo Restriction (`validateOrImpossible_of_appliesTo_restriction`)

Removing items from `appliesToPrincipal`/`appliesToResource` on actions cannot
introduce new type errors. Policies may become "impossible" (all environments
produce `.bool .ff`) but cannot acquire type errors. The executable check
`isAppliesToRestriction` determines whether a schema change qualifies.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
**Executable backward compatibility for entity schema extension**: if
`isValidEtsExtension schema₁ schema₂` returns `true` (same actions, all old
entity type entries preserved, action/entity disjointness) and `schema₁` is
well-formed, then policies validated against `schema₁` also validate against
`schema₂`.
-/
theorem validate_of_isValidEtsExtension
    (schema₁ schema₂ : Schema)
    (policies : Policies)
    (hext : isValidEtsExtension schema₁ schema₂ = true)
    (hwf₁ : schema₁.validateWellFormed = .ok ())
    (hold : validate policies schema₁ = .ok ()) :
    validate policies schema₂ = .ok () :=
  validate_of_isValidEtsExtension' schema₁ schema₂ policies hext hwf₁ hold

/--
**Executable backward compatibility for appliesTo restriction**: if
`isAppliesToRestriction oldSchema newSchema` returns `true` (same entity types,
same action hierarchy, appliesTo only shrunk, well-formed new acts) and `oldSchema`
is well-formed, then `validateOrImpossible` passes on `newSchema`.

Policies may become "impossible" when appliesTo entries are removed, but cannot
acquire new type errors.
-/
theorem validateOrImpossible_of_appliesTo_restriction
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    (hwf₁ : Schema.validateWellFormed oldSchema = .ok ())
    (hold : validate policies oldSchema = .ok ()) :
    Cedar.Slice.validateOrImpossible policies newSchema = true :=
  validateOrImpossible_of_appliesTo_restriction' oldSchema newSchema policies hrestr hwf₁ hold

/-! ## Combined: entity schema extension + appliesTo restriction -/

private theorem disjoint_contains_from_ets_ext_and_appliesTo_restr
    {schema₁ schema₃ : Schema}
    (hets_ext : isValidEtsExtension schema₁ { ets := schema₃.ets, acts := schema₁.acts } = true)
    (happlies_restr : isAppliesToRestriction { ets := schema₃.ets, acts := schema₁.acts } schema₃ = true) :
    ∀ uid, schema₃.acts.contains uid = true → ¬ schema₃.ets.contains uid.ty := by
  intro uid hc hets_c
  simp only [isValidEtsExtension, Bool.and_eq_true] at hets_ext
  have hdisj_all := hets_ext.2
  obtain ⟨_, hfind_old, _, _, _⟩ :=
    isAppliesToRestriction_new_in_old happlies_restr
      (Map.find?_mem_toList (Map.contains_iff_some_find?.mp hc).choose_spec)
  have hmem := Map.find?_mem_toList hfind_old
  have h_not := List.all_eq_true.mp hdisj_all _ hmem
  simp only [Bool.not_eq_true'] at h_not
  exact absurd hets_c (by simp [h_not])


/--
**Combined backward compatibility**: if `isBackwardCompatible schema₁ schema₃`
returns `true` and `schema₁` is well-formed, then:
- Adding entity types cannot break validation
- Restricting appliesTo cannot introduce type errors (only "impossible" policies)

The result is `validateOrImpossible`, which allows policies to become impossible
but not to acquire type errors.
-/
theorem validateOrImpossible_of_backward_compatible
    (schema₁ schema₃ : Schema)
    (policies : Policies)
    (hcompat : isBackwardCompatible schema₁ schema₃ = true)
    (hwf₁ : Schema.validateWellFormed schema₁ = .ok ())
    (hold : validate policies schema₁ = .ok ()) :
    Cedar.Slice.validateOrImpossible policies schema₃ = true := by
  simp only [isBackwardCompatible, Bool.and_eq_true] at hcompat
  obtain ⟨⟨⟨hets_ext, happlies_restr⟩, hacts_wf_old⟩, hets_wf₃⟩ := hcompat
  -- Use validateOrImpossible_of_appliesTo_restriction' via a helper that avoids Schema.validateWellFormed
  -- Step 1: entity schema extension
  have hvalid₂ : validate policies ⟨schema₃.ets, schema₁.acts⟩ = .ok () :=
    validate_of_isValidEtsExtension schema₁ ⟨schema₃.ets, schema₁.acts⟩ policies hets_ext hwf₁ hold
  -- Step 2: directly prove validateOrImpossible using the structure from AppliesToRestriction
  -- Since all schema₃ actions are in schema₁.acts (from happlies_restr) and
  -- schema₃.ets extends schema₁.ets, every schema₃ environment has a matching intermediate env
  have hacts_wf₃ : schema₃.acts.wellFormed := by
    simp only [isAppliesToRestriction, Bool.and_eq_true] at happlies_restr; exact happlies_restr.2
  have hacts_wf₁' : Map.WellFormed schema₁.acts :=
    Map.wf_iff_sorted.mpr (List.isSortedBy_correct.mpr hacts_wf_old)
  have hacts_wf₃' : Map.WellFormed schema₃.acts :=
    Map.wf_iff_sorted.mpr (List.isSortedBy_correct.mpr hacts_wf₃)
  have hdisjoint_contains₃ := disjoint_contains_from_ets_ext_and_appliesTo_restr hets_ext happlies_restr
  have hets_wf₃' : Map.WellFormed schema₃.ets := Map.wellFormed_correct.mp hets_wf₃
  have hno_full : Cedar.Slice.requiresFullRevalidation ⟨schema₃.ets, schema₁.acts⟩ schema₃ = false :=
    isAppliesToRestriction_implies_rfr_false happlies_restr hdisjoint_contains₃ hets_wf₃'
  have hincr := rfr_false_implies_incr hno_full hacts_wf₁' hacts_wf₃'
  simp only [Cedar.Slice.validateOrImpossible, List.all_eq_true]
  intro p hp
  have hvalid_p := List.forM_ok_implies_all_ok' (by simp [validate] at hvalid₂; exact hvalid₂) p hp
  simp only [typecheckPolicyWithEnvironments, Except.mapError] at hvalid_p ⊢
  have hce_mid : checkEntities ⟨schema₃.ets, schema₁.acts⟩ p.toExpr = .ok () := by
    cases hce : checkEntities ⟨schema₃.ets, schema₁.acts⟩ p.toExpr with
    | ok _ => rfl
    | error e => simp [hce] at hvalid_p
  have hce₃ : checkEntities schema₃ p.toExpr = .ok () :=
    checkEntities_preserved hincr hce_mid
  rw [show (checkEntities schema₃ p.toExpr) = .ok () from hce₃]
  simp only [Except.bind_ok]
  simp only [hce_mid, Except.bind_ok] at hvalid_p
  cases h_mapM : List.mapM (typecheckPolicy p) (Schema.environments ⟨schema₃.ets, schema₁.acts⟩) with
  | error => simp [h_mapM] at hvalid_p
  | ok txs =>
  have hall_ok : ∀ env₃ ∈ schema₃.environments, ∃ tx, typecheckPolicy p env₃ = .ok tx := by
    intro env₃ henv₃_mem
    have ⟨henv₃_ets, henv₃_acts⟩ := env_mem_environments_schema henv₃_mem
    have henv₃_contains := env_mem_environments_action_contained henv₃_mem
    have hfind₃ := (Map.contains_iff_some_find?.mp henv₃_contains).choose_spec
    have h_entry := List.all_eq_true.mp
      (by simp only [isAppliesToRestriction, Bool.and_eq_true] at happlies_restr; exact happlies_restr.1.2)
      _ (Map.find?_mem_toList hfind₃)
    simp only at h_entry
    cases hfo : schema₁.acts.find? env₃.reqty.action with
    | none => simp [hfo] at h_entry
    | some oldEntry =>
    simp only [hfo, Bool.and_eq_true, decide_eq_true_eq] at h_entry
    obtain ⟨⟨⟨⟨hctx, hprinc⟩, hres⟩, _⟩, _⟩ := h_entry
    obtain ⟨env_mid, henv_mid_mem, hreqty_eq⟩ := env_in_other_schema_environments_subset
      henv₃_mem (show (Schema.mk schema₃.ets schema₁.acts).acts.find? env₃.reqty.action = some oldEntry from hfo)
      hfind₃ hctx hprinc hres hacts_wf₃'
    have ⟨henv_mid_ets, henv_mid_acts⟩ := env_mem_environments_schema henv_mid_mem
    have hagree : ActsAgreement env_mid env₃ :=
      mk_actsAgreement_from_schemas hincr henv_mid_ets henv_mid_acts henv₃_ets henv₃_acts hreqty_eq rfl
    have hce_env : checkEntities ⟨env_mid.ets, env_mid.acts⟩ p.toExpr = .ok () := by
      rw [henv_mid_ets, henv_mid_acts]; exact hce_mid
    have hcontains : env_mid.acts.contains env_mid.reqty.action = true := by
      rw [henv_mid_acts]; exact env_mem_environments_action_contained henv_mid_mem
    have ⟨tx, _, htx⟩ := List.mapM_ok_implies_all_ok h_mapM env_mid henv_mid_mem
    rw [typecheckPolicy_congr_acts hagree hce_env hcontains] at htx
    exact ⟨tx, htx⟩
  obtain ⟨txs₃, h_mapM₃⟩ := List.all_ok_implies_mapM_ok hall_ok
  simp only [Except.bind_ok, h_mapM₃]
  cases hallff : allFalse txs₃ <;> simp

/--
**Backward-compatible schemas require no revalidation**: if `isBackwardCompatible`
passes, the validation slice is empty — no policies need to be rechecked.
Combined with `validateOrImpossible_of_backward_compatible`, this means the new
schema is guaranteed to pass without running the validator at all.
-/
theorem validationSlice_empty_of_backward_compatible
    (schema₁ schema₃ : Schema)
    (policies : Policies)
    (hcompat : isBackwardCompatible schema₁ schema₃ = true) :
    Cedar.Slice.validationSlice schema₁ schema₃ policies = [] := by
  simp only [isBackwardCompatible, Bool.and_eq_true] at hcompat
  obtain ⟨⟨⟨_, happlies_restr⟩, _⟩, _⟩ := hcompat
  have hno_changes := isAppliesToRestriction_implies_no_changes happlies_restr
  have h : Cedar.Slice.computeActionChanges schema₁ schema₃ = [] := hno_changes
  simp [Cedar.Slice.validationSlice, Cedar.Slice.validationSliceByChanges,
    Cedar.Slice.policyMatchesAnyChange, h]

end Cedar.Thm

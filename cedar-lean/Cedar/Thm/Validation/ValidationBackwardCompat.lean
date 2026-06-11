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


/--
**Combined backward compatibility**: if `isBackwardCompatible schema₁ schema₃`
returns `true` and `schema₁` is well-formed, then:
- Adding entity types cannot break validation
- Restricting appliesTo cannot introduce type errors (only "impossible" policies)

The result is `validateOrImpossible`, which allows policies to become impossible
but not to acquire type errors.
-/
private theorem disjoint_from_ets_ext_and_appliesTo_restr
    {schema₁ schema₃ : Schema}
    (hets_ext : isValidEtsExtension schema₁ { ets := schema₃.ets, acts := schema₁.acts } = true)
    (happlies_restr : isAppliesToRestriction { ets := schema₃.ets, acts := schema₁.acts } schema₃ = true) :
    ∀ uid, schema₃.acts.contains uid = true → schema₃.ets.isValidEntityUID uid = false := by
  intro uid hc
  simp only [isValidEtsExtension, Bool.and_eq_true] at hets_ext
  have hdisj_all := hets_ext.2
  obtain ⟨_, hfind_old, _, _, _⟩ :=
    isAppliesToRestriction_new_in_old happlies_restr
      (Map.find?_mem_toList (Map.contains_iff_some_find?.mp hc).choose_spec)
  have hmem := Map.find?_mem_toList hfind_old
  have h_not := List.all_eq_true.mp hdisj_all _ hmem
  simp only [Bool.not_eq_true'] at h_not
  simp only [EntitySchema.isValidEntityUID]
  cases hf : schema₃.ets.find? uid.ty with
  | none => rfl
  | some _ => simp [EntitySchema.contains, hf] at h_not

theorem validateOrImpossible_of_backward_compatible
    (schema₁ schema₃ : Schema)
    (policies : Policies)
    (hcompat : isBackwardCompatible schema₁ schema₃ = true)
    (hwf₁ : Schema.validateWellFormed schema₁ = .ok ())
    (hold : validate policies schema₁ = .ok ()) :
    Cedar.Slice.validateOrImpossible policies schema₃ = true := by
  simp only [isBackwardCompatible, Bool.and_eq_true] at hcompat
  obtain ⟨⟨hets_ext, happlies_restr⟩, hacts_wf_old⟩ := hcompat
  -- Step 1: entity schema extension (schema₁ → schema₂)
  let schema₂ : Schema := { ets := schema₃.ets, acts := schema₁.acts }
  have hvalid₂ : validate policies schema₂ = .ok () :=
    validate_of_isValidEtsExtension schema₁ schema₂ policies hets_ext hwf₁ hold
  -- Step 2: appliesTo restriction (schema₂ → schema₃)
  have hno_full := isAppliesToRestriction_implies_rfr_false happlies_restr
  have hno_changes := isAppliesToRestriction_implies_no_changes happlies_restr
  have hdisjoint₃ := disjoint_from_ets_ext_and_appliesTo_restr hets_ext happlies_restr
  have hacts_wf₃ : schema₃.acts.wellFormed := by
    simp only [isAppliesToRestriction, Bool.and_eq_true] at happlies_restr; exact happlies_restr.2
  by_cases henvs_new : schema₃.environments = []
  · exact validateOrImpossible_of_empty_envs henvs_new hno_full hvalid₂
  simp only [Cedar.Slice.validateOrImpossible, List.all_eq_true]
  intro p hp
  exact nonslice_policy_noTypeErrors hno_full
    (List.forM_ok_implies_all_ok' (by simp [validate] at hvalid₂; exact hvalid₂) p hp)
    (by simp [hno_changes, Cedar.Slice.actionScopeMatchesAnyChangedAction])
    hacts_wf_old hacts_wf₃ hdisjoint₃

end Cedar.Thm

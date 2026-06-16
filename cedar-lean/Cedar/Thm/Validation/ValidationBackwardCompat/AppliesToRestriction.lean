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
# Backward compatibility: appliesTo restriction

Removing items from `appliesToPrincipal`/`appliesToResource` on actions cannot
introduce new type errors — policies may become "impossible" but cannot break.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 12800000

/-! ## Backward compatibility for appliesTo removal -/

theorem isAppliesToRestriction_implies_rfr_false
    {oldSchema newSchema : Schema}
    (h : isAppliesToRestriction oldSchema newSchema = true)
    (hdisjoint : ∀ uid, newSchema.acts.contains uid = true → ¬ newSchema.ets.contains uid.ty)
    (hets_wf : Map.WellFormed oldSchema.ets) :
    Cedar.Slice.requiresFullRevalidation oldSchema newSchema = false := by
  simp only [isAppliesToRestriction, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hets, hold_all⟩, hnew_all⟩, _⟩ := h
  have hets_eq : oldSchema.ets = newSchema.ets :=
    Map.eq_iff_toList_eq.mp ((beq_iff_eq (α := List _)).mp hets)
  -- Prove directly: requiresFullRevalidation unfolds to !(a && b) || c || d
  -- where a && b = true (so !(a&&b) = false), c = false, d = false
  have hall_ets : oldSchema.ets.toList.all (fun x => newSchema.ets.find? x.1 == some x.2) = true := by
    rw [List.all_eq_true]; intro ⟨ety, entry⟩ hmem
    simp only [beq_iff_eq, ← hets_eq]
    exact (Map.in_list_iff_find?_some hets_wf).mp hmem
  have hall_disj : newSchema.acts.toList.all (fun x => !newSchema.ets.contains x.1.ty) = true := by
    rw [List.all_eq_true]; intro ⟨uid, _⟩ hmem
    simp only [Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (hdisjoint uid (Map.in_list_implies_contains hmem))
  have hany_anc : oldSchema.acts.toList.any (fun x =>
      match newSchema.acts.find? x.1 with
      | none => true | some e => x.2.ancestors != e.ancestors) = false := by
    rw [List.any_eq_false]; intro ⟨action, oldEntry⟩ hmem
    have h_entry := List.all_eq_true.mp hold_all _ hmem; simp only at h_entry
    cases hfn : newSchema.acts.find? action with
    | none => simp [hfn] at h_entry
    | some newEntry => simp only [hfn, decide_eq_true_eq] at h_entry; simp [h_entry]
  have hany_new : newSchema.acts.toList.any (fun x =>
      !(oldSchema.acts.contains x.1) && (!x.2.ancestors.isEmpty || !(oldSchema.acts.actionType? x.1.ty))) = false := by
    rw [List.any_eq_false]; intro ⟨action, newEntry⟩ hmem
    have h_entry := List.all_eq_true.mp hnew_all _ hmem; simp only at h_entry
    cases hfo : oldSchema.acts.find? action with
    | none => simp [hfo] at h_entry
    | some _ => simp [ActionSchema.contains, hfo]
  have h : (!(oldSchema.ets.toList.all (fun x => newSchema.ets.find? x.1 == some x.2) &&
              newSchema.acts.toList.all (fun x => !newSchema.ets.contains x.1.ty)) ||
            oldSchema.acts.toList.any (fun x =>
              match newSchema.acts.find? x.1 with
              | none => true | some e => x.2.ancestors != e.ancestors) ||
            newSchema.acts.toList.any (fun x =>
              !(oldSchema.acts.contains x.1) && (!x.2.ancestors.isEmpty || !(oldSchema.acts.actionType? x.1.ty)))) = false := by
    simp [hall_ets, hall_disj, hany_anc, hany_new]
  exact h

theorem isAppliesToRestriction_implies_no_changes
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
    obtain ⟨⟨⟨⟨hctx, hprinc⟩, hres⟩, _⟩, _⟩ := h_entry
    have hctx_ne : (oldEntry.context != newEntry.context) = false := by simp [bne, beq_iff_eq, hctx]
    have hprinc_nil : (newEntry.appliesToPrincipal.toList.filter
        (fun p => !(oldEntry.appliesToPrincipal.contains p))) = [] := by
      rw [List.filter_eq_nil_iff]; intro p hp
      simp only [Bool.not_eq_true', decide_eq_true_eq]
      have := List.all_eq_true.mp (show newEntry.appliesToPrincipal.toList.all
        oldEntry.appliesToPrincipal.contains = true from hprinc) p hp
      simp [this]
    have hres_nil : (newEntry.appliesToResource.toList.filter
        (fun r => !(oldEntry.appliesToResource.contains r))) = [] := by
      rw [List.filter_eq_nil_iff]; intro r hr
      simp only [Bool.not_eq_true', decide_eq_true_eq]
      have := List.all_eq_true.mp (show newEntry.appliesToResource.toList.all
        oldEntry.appliesToResource.contains = true from hres) r hr
      simp [this]
    simp [hctx_ne, hprinc_nil, hres_nil]

/-! ## Helpers -/

theorem mem_of_subset_toList {α : Type} [DecidableEq α] {s₁ s₂ : Set α} {a : α}
    (hmem : a ∈ s₁.toList) (hsub : s₁.subset s₂ = true) : a ∈ s₂.toList := by
  unfold Set.subset at hsub
  unfold Set.toList at hmem ⊢
  have h := List.all_eq_true.mp hsub a hmem
  unfold Set.contains at h
  rw [List.elem_eq_mem] at h
  grind

/-- Extract `ets_eq` from `isAppliesToRestriction`. -/
theorem isAppliesToRestriction_ets_eq
    {oldSchema newSchema : Schema}
    (hrestr : isAppliesToRestriction oldSchema newSchema = true) :
    oldSchema.ets = newSchema.ets := by
  simp only [isAppliesToRestriction, Bool.and_eq_true] at hrestr
  exact Map.eq_iff_toList_eq.mp ((beq_iff_eq (α := List _)).mp hrestr.1.1.1)

/-- From `isAppliesToRestriction`, every new action has a corresponding old entry. -/
theorem isAppliesToRestriction_new_in_old
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
theorem appliesTo_restriction_envs_ne
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

/-- The strong disjointness: acts UIDs' types don't appear in ets.
    Derived from `isAppliesToRestriction` + old schema well-formedness. -/
theorem isAppliesToRestriction_disjoint
    {oldSchema newSchema : Schema}
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    (hwf₁ : Schema.validateWellFormed oldSchema = .ok ())
    (henvs_old : oldSchema.environments ≠ []) :
    ∀ uid, newSchema.acts.contains uid = true → ¬ newSchema.ets.contains uid.ty := by
  have ⟨env_old, henv_old_mem⟩ := List.exists_mem_of_ne_nil _ henvs_old
  have hwf_env := env_validate_well_formed_is_sound
    (List.forM_ok_implies_all_ok' (schema_validateWellFormed_forM hwf₁) _ henv_old_mem)
  have ⟨henv_ets, henv_acts⟩ := env_mem_environments_schema henv_old_mem
  have hold_disj : ∀ uid, oldSchema.acts.contains uid = true → ¬ oldSchema.ets.contains uid.ty := by
    intro uid hc
    have hdisj := hwf_env.2.1.2.2.1 uid (henv_acts ▸ hc)
    rw [henv_ets] at hdisj; exact hdisj
  intro uid hc_new
  rw [← isAppliesToRestriction_ets_eq hrestr]
  have ⟨_, hfind_old, _, _, _⟩ :=
    isAppliesToRestriction_new_in_old hrestr
      (Map.find?_mem_toList (Map.contains_iff_some_find?.mp hc_new).choose_spec)
  exact hold_disj uid (by simp [ActionSchema.contains, hfind_old])

private theorem ets_wf_of_schema_wf
    {schema : Schema}
    (hwf₁ : Schema.validateWellFormed schema = .ok ())
    {env : TypeEnv} (henv : env ∈ schema.environments) :
    Map.WellFormed schema.ets := by
  have hwf_env := env_validate_well_formed_is_sound
    (List.forM_ok_implies_all_ok' (schema_validateWellFormed_forM hwf₁) _ henv)
  have ⟨henv_ets, _⟩ := env_mem_environments_schema henv
  rw [← henv_ets]; exact hwf_env.1.1

theorem validateOrImpossible_of_appliesTo_restriction'
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    (hwf₁ : Schema.validateWellFormed oldSchema = .ok ())
    (hold : validate policies oldSchema = .ok ()) :
    Cedar.Slice.validateOrImpossible policies newSchema = true := by
  have hacts_wf₂ : newSchema.acts.wellFormed := by
    simp only [isAppliesToRestriction, Bool.and_eq_true] at hrestr; exact hrestr.2
  by_cases henvs_new : newSchema.environments = []
  · by_cases henvs_old : oldSchema.environments = []
    · simp only [Cedar.Slice.validateOrImpossible, List.all_eq_true]
      intro p hp
      have hvalid_p := policy_validated_of_validate hold hp
      simp only [typecheckPolicyWithEnvironments, Except.mapError] at hvalid_p
      simp_do_let (checkEntities oldSchema p.toExpr) as hce at hvalid_p
      simp [henvs_old, allFalse] at hvalid_p
    · have henv_mem := (List.exists_mem_of_ne_nil _ henvs_old).choose_spec
      have hno_full := isAppliesToRestriction_implies_rfr_false hrestr
        (isAppliesToRestriction_disjoint hrestr hwf₁ henvs_old)
        (ets_wf_of_schema_wf hwf₁ henv_mem)
      exact validateOrImpossible_of_empty_envs henvs_new hno_full hold
  have henvs_old := appliesTo_restriction_envs_ne hrestr henvs_new
  have henv₁_mem := (List.exists_mem_of_ne_nil _ henvs_old).choose_spec
  have ⟨hacts_wf₁, _⟩ := validateWellFormed_gives_wf_and_disjoint hwf₁ henv₁_mem
  have hno_full := isAppliesToRestriction_implies_rfr_false hrestr
    (isAppliesToRestriction_disjoint hrestr hwf₁ henvs_old) (ets_wf_of_schema_wf hwf₁ henv₁_mem)
  simp only [Cedar.Slice.validateOrImpossible, List.all_eq_true]
  intro p hp
  exact nonslice_policy_noTypeErrors hno_full
    (policy_validated_of_validate hold hp)
    (by simp [isAppliesToRestriction_implies_no_changes hrestr,
              Cedar.Slice.actionScopeMatchesAnyChangedAction])
    hacts_wf₁ hacts_wf₂ hwf₁

end Cedar.Thm

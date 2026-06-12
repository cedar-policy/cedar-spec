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
  have := typeOf_congr_ets _ ∅ h (checkEntities_substituteAction hce haction_valid)
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

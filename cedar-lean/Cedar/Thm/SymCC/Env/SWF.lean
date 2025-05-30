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

import Cedar.Thm.SymCC.Data.Hierarchy
import Cedar.Thm.SymCC.Env.WF

/-!
# Basic properties of strongly well-formed symbolic environments

This file proves basic lemmas about the strong well-formedness predicate on environments.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

theorem swf_εnv_implies_wf {εnv : SymEnv} :
   εnv.StronglyWellFormed → εnv.WellFormed
:= by
  intro hwε
  simp only [SymEnv.WellFormed, hwε.left.left, hwε.right.left, and_self]

theorem swf_εnv_all_implies_swf_all {εnv : SymEnv} {xs : List Expr} :
  εnv.StronglyWellFormedForAll xs →
  ∀ x ∈ xs, εnv.StronglyWellFormedFor x
:= by
  intro hwε x hin
  exact And.intro hwε.left (hwε.right x hin)

theorem swf_εnv_all_implies_wf_all {εnv : SymEnv} {xs : List Expr} :
  εnv.StronglyWellFormedForAll xs →
  ∀ x ∈ xs, εnv.WellFormedFor x
:= by
  intro hwε x hin
  simp only [SymEnv.WellFormedFor, swf_εnv_implies_wf hwε.left, hwε.right x hin, and_self]

theorem swf_εnv_for_implies_wf_for {εnv : SymEnv} {x : Expr} :
  εnv.StronglyWellFormedFor x →
  εnv.WellFormedFor x
:= by
  intro hwε
  exact And.intro (swf_εnv_implies_wf hwε.left) hwε.right

theorem swf_env_implies_wf {env : Env} :
   env.StronglyWellFormed → env.WellFormed
:= by
  intro hwe
  simp only [Env.WellFormed, hwe.left, hwe.right.left, and_self]

theorem swf_env_all_implies_swf_all {env : Env} {xs : List Expr} :
  env.StronglyWellFormedForAll xs →
  ∀ x ∈ xs, env.StronglyWellFormedFor x
:= by
  intro hwe x hin
  exact And.intro hwe.left (hwe.right x hin)

theorem swf_env_all_implies_wf_all {env : Env} {xs : List Expr} :
  env.StronglyWellFormedForAll xs →
  ∀ x ∈ xs, env.WellFormedFor x
:= by
  intro hwe x hin
  simp only [Env.WellFormedFor, swf_env_implies_wf hwe.left, hwe.right x hin, and_self]

theorem swf_env_for_implies_wf_for {env : Env} {x : Expr} :
  env.StronglyWellFormedFor x →
  env.WellFormedFor x
:= by
  intro hwe
  exact And.intro (swf_env_implies_wf hwe.left) hwe.right

theorem swf_εnv_for_policy_iff_swf_for_polices {εnv : SymEnv} {p : Policy} :
  εnv.StronglyWellFormedForPolicy p ↔
  εnv.StronglyWellFormedForPolicies [p]
:= by
  constructor
  · intro ⟨hwε, hvr⟩
    constructor
    · exact hwε
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq, hvr]
  · intro hwε
    apply swf_εnv_all_implies_swf_all hwε p.toExpr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]

theorem swf_env_for_policy_iff_swf_for_polices {env : Env} {p : Policy} :
  env.StronglyWellFormedForPolicy p ↔
  env.StronglyWellFormedForPolicies [p]
:= by
  constructor
  · intro ⟨hwe, hvr⟩
    constructor
    · exact hwe
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq, hvr]
  · intro hwe
    apply swf_env_all_implies_swf_all hwe p.toExpr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]

theorem swf_εnv_for_policies_iff_swf_for_append {εnv : SymEnv} {ps₁ ps₂ : Policies} :
  εnv.StronglyWellFormedForPolicies ps₁ ∧ εnv.StronglyWellFormedForPolicies ps₂ ↔
  εnv.StronglyWellFormedForPolicies (ps₁ ++ ps₂)
:= by
  simp only [SymEnv.StronglyWellFormedForPolicies, SymEnv.StronglyWellFormedForAll, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.map_append, List.mem_append]
  constructor
  · intro ⟨hwε₁, hwε₂⟩
    simp only [hwε₁.left, true_and]
    intro x hx
    rcases hx with hx | hx <;>
    replace ⟨p, hin, hx⟩ := hx <;>
    subst hx
    · exact hwε₁.right p hin
    · exact hwε₂.right p hin
  · intro hwε
    simp only [hwε.left, true_and]
    constructor <;> intro p hin
    · apply hwε.right ; apply Or.inl ; exists p
    · apply hwε.right ; apply Or.inr ; exists p

theorem swf_env_for_policies_iff_swf_for_append {env : Env} {ps₁ ps₂ : Policies} :
  env.StronglyWellFormedForPolicies ps₁ ∧ env.StronglyWellFormedForPolicies ps₂ ↔
  env.StronglyWellFormedForPolicies (ps₁ ++ ps₂)
:= by
  simp only [Env.StronglyWellFormedForPolicies, Env.StronglyWellFormedForAll, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.map_append, List.mem_append]
  constructor
  · intro ⟨hwe₁, hwe₂⟩
    simp only [hwe₂.left, true_and]
    intro x hx
    rcases hx with hx | hx <;>
    replace ⟨p, hin, hx⟩ := hx <;>
    subst hx
    · exact hwe₁.right p hin
    · exact hwe₂.right p hin
  · intro hwe
    simp only [hwe.left, true_and]
    constructor <;> intro p hin
    · apply hwe.right ; apply Or.inl ; exists p
    · apply hwe.right ; apply Or.inr ; exists p

theorem swf_εnv_for_policies_implies_wf_for_policies {εnv : SymEnv} {ps : Policies} :
  εnv.StronglyWellFormedForPolicies ps →
  εnv.WellFormedForPolicies ps
:= by
  intro hwε
  simp only [SymEnv.StronglyWellFormedForPolicies, SymEnv.StronglyWellFormedForAll, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hwε
  simp only [SymEnv.WellFormedForPolicies, swf_εnv_implies_wf hwε.left, true_and]
  intro p hin
  exact hwε.right p hin

theorem swf_env_for_policies_implies_wf_for_policies {env : Env} {ps : Policies} :
  env.StronglyWellFormedForPolicies ps →
  env.WellFormedForPolicies ps
:= by
  intro hwe
  simp only [Env.StronglyWellFormedForPolicies, Env.StronglyWellFormedForAll, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hwe
  simp only [Env.WellFormedForPolicies, swf_env_implies_wf hwe.left, true_and]
  intro p hin
  exact hwe.right p hin

end Cedar.Thm

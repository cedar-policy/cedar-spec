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

import Cedar.Slice.CstPolicySlice
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Authorization.CstPolicySlice

/-!
This file defines what it means for a CST (concrete syntax tree) policy slice to
be sound. It is the CST-level counterpart of `Cedar/Thm/PolicySlice.lean`.

We state two main theorems:

* Authorization returns the same response for a sound CST policy slice as for the
  original collection of CST policies
  (`Cst.isAuthorized_eq_for_sound_policy_slice`).
* It is sound to slice CST policies based on scope constraints (see
  `Cst.isAuthorized_eq_for_scope_based_policy_slice`). As in the AST development,
  this rests on a more general lemma
  (`Cst.sound_bound_analysis_produces_sound_slices`) covering all forms of slicing
  based on identifying "bound" principal and resource entities for a policy.

Unlike the AST versions, the CST `BoundAnalysis`/`scopeAnalysis` require a
well-formedness witness (`(prVars? policy).isSome`) for each policy, which appears
as an extra hypothesis.
--/

-- The slicing soundness theorems in this file assumes that the translation
-- from CST to AST is successful.
-- The soundness itself does not depend on the translation. These proofs
-- are for demonstration purposes. The soundness can be proved without the
-- translation soundness hypotheses.

namespace Cedar.Thm

open Cedar.Spec Cedar.Slice Cedar.Slice.Cst
open Cedar.Frontend
open Cedar.Frontend.Cst hiding Expr ExprImpl ExprData OrExpr AndExpr AddExpr MultExpr Name Policy PolicyImpl Policies Ident Literal Primary Member MemAccess Unary Relation RelOp Cond VariableDef Ref RecInit Str


/--
Scope analysis computed natively on a CST policy agrees with scope analysis
computed on the AST policy it translates to.
-/
theorem Cst.translation_preserves_scopeAnalysis
  {cp : Cst.Policy} {ap : Policy}
  (htrans : cp.toPolicy? = some ap) :
  ∃ h : (prVars? cp).isSome,
  Cedar.Slice.Cst.scopeAnalysis cp h = Cedar.Slice.scopeAnalysis ap := by
  exists (policy_translation_success_prVars_isSome' htrans)
  apply translation_preserves_scopeAnalysis' htrans

/--
CST policy slicing soundness: `Cst.isAuthorized` produces the same result for a
sound slice (subset) of a collection of CST policies as it does for the original
policies.
-/
theorem Cst.isAuthorized_eq_for_sound_policy_slice
    (req : Request) (entities : Entities) (slice policies : Cst.Policies)
    (htrans : (policies.toPolicies?).isSome) :
    Cst.IsSoundPolicySlice req entities slice policies →
    Cst.isAuthorized req entities slice = Cst.isAuthorized req entities policies := by
  intro hsound
  obtain ⟨aps, haps⟩ := Option.isSome_iff_exists.mp htrans
  obtain ⟨sps, hsps⟩ := slice_toPolicies?_isSome hsound.1 haps
  have hast := cst_sound_slice_translates hsound hsps haps
  rw [translation_is_sound _ _ req entities hsps,
      _root_.Cedar.Thm.isAuthorized_eq_for_sound_policy_slice req entities sps aps hast,
      ← translation_is_sound _ _ req entities haps]

/--
A sound CST bound analysis produces sound CST policy slices.
-/
theorem Cst.sound_bound_analysis_produces_sound_slices
    (ba : Cedar.Slice.Cst.BoundAnalysis) (request : Request) (entities : Entities)
    (policies : Cst.Policies)
    (htrans : (policies.toPolicies?).isSome) :
    Cst.IsSoundBoundAnalysis ba →
    ∃ (h : ∀ policy ∈ policies.ps, (prVars? policy).isSome),
    Cst.IsSoundPolicySlice request entities
      (Cedar.Slice.Cst.BoundAnalysis.slice ba request entities policies h) policies := by
  intro hba
  have hwf := policies_translation_success_prVars_isSome htrans
  exists hwf
  refine ⟨cst_bound_slice_subset ba request entities policies hwf, ?_⟩
  intro policy hmem hnotin
  obtain ⟨hsat_imp, herr_imp⟩ := hba policy (hwf policy hmem)
    (policy_toPolicy?_isSome_of_mem htrans hmem) request entities
  exact ⟨
    fun hsat => hnotin (cst_bound_slice_kept ba request entities policies hwf hmem (hsat_imp hsat)),
    fun herr => hnotin (cst_bound_slice_kept ba request entities policies hwf hmem (herr_imp herr))⟩

/--
CST scope-based bounds are sound.
-/
theorem Cst.scope_bound_is_sound (policy : Cst.Policy)
    (htrans : (policy.toPolicy?).isSome) :
    ∃ h : (prVars? policy).isSome,
    Cst.IsSoundPolicyBound (Cedar.Slice.Cst.scopeAnalysis policy h) policy := by
  obtain ⟨ap, hap⟩ := Option.isSome_iff_exists.mp htrans
  exists (policy_translation_success_prVars_isSome' hap)
  intro req es
  have hscope := translation_preserves_scopeAnalysis' hap (policy_translation_success_prVars_isSome' hap)
  have hsat := policy_satisfied_agrees policy ap req es hap
  have herr := policy_hasError_agrees policy ap req es hap
  rw [hscope, hsat, herr]
  exact _root_.Cedar.Thm.scope_bound_is_sound ap req es

/--
CST scope-based bound analysis is sound.
-/
theorem Cst.scope_analysis_is_sound :
    Cst.IsSoundBoundAnalysis Cedar.Slice.Cst.scopeAnalysis := by
  intro policy _ hpt
  obtain ⟨_, hsound⟩ := Cst.scope_bound_is_sound policy hpt
  exact hsound

/--
CST scope-based slicing is sound: `Cst.isAuthorized` produces the same result for
a scope-based slice of a collection of CST policies as it does for the original
policies.
-/
theorem Cst.isAuthorized_eq_for_scope_based_policy_slice
    (request : Request) (entities : Entities) (policies : Cst.Policies)
    (htrans : (policies.toPolicies?).isSome) :
    ∃ (hwf : ∀ policy ∈ policies.ps, (prVars? policy).isSome),
    Cst.isAuthorized request entities
      (Cedar.Slice.Cst.BoundAnalysis.slice Cedar.Slice.Cst.scopeAnalysis request entities policies hwf) =
    Cst.isAuthorized request entities policies := by
  exists (policies_translation_success_prVars_isSome htrans)
  obtain ⟨aps, htrans'⟩ := Option.isSome_iff_exists.mp htrans
  have hslice := cst_slice_chooses_same_policies' request entities htrans'
    (policies_translation_success_prVars_isSome htrans)
  rw [translation_is_sound _ _ request entities hslice,
      _root_.Cedar.Thm.isAuthorized_eq_for_scope_based_policy_slice request entities aps,
      ← translation_is_sound _ _ request entities htrans']

end Cedar.Thm

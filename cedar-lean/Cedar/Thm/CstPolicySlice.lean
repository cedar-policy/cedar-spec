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

namespace Cedar.Thm

open Cedar.Spec Cedar.Slice Cedar.Slice.Cst

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
  sorry

/--
A sound CST bound analysis produces sound CST policy slices.
-/
theorem Cst.sound_bound_analysis_produces_sound_slices
    (ba : Cedar.Slice.Cst.BoundAnalysis) (request : Request) (entities : Entities)
    (policies : Cst.Policies) (hwf : ∀ policy ∈ policies.ps, (prVars? policy).isSome)
    (htrans : (policies.toPolicies?).isSome) :
    Cst.IsSoundBoundAnalysis ba →
    Cst.IsSoundPolicySlice request entities
      (Cedar.Slice.Cst.BoundAnalysis.slice ba request entities policies hwf) policies := by
  sorry

/--
CST scope-based bounds are sound.
-/
theorem Cst.scope_bound_is_sound (policy : Cst.Policy) (h : (prVars? policy).isSome)
    (htrans : (policy.toPolicy?).isSome) :
    Cst.IsSoundPolicyBound (Cedar.Slice.Cst.scopeAnalysis policy h) policy := by
  sorry

/--
CST scope-based bound analysis is sound.
-/
theorem Cst.scope_analysis_is_sound :
    Cst.IsSoundBoundAnalysis Cedar.Slice.Cst.scopeAnalysis := by
  sorry

/--
CST scope-based slicing is sound: `Cst.isAuthorized` produces the same result for
a scope-based slice of a collection of CST policies as it does for the original
policies.
-/
theorem Cst.isAuthorized_eq_for_scope_based_policy_slice
    (request : Request) (entities : Entities) (policies : Cst.Policies)
    (hwf : ∀ policy ∈ policies.ps, (prVars? policy).isSome)
    (htrans : (policies.toPolicies?).isSome) :
    Cst.isAuthorized request entities
      (Cedar.Slice.Cst.BoundAnalysis.slice Cedar.Slice.Cst.scopeAnalysis request entities policies hwf) =
    Cst.isAuthorized request entities policies := by
  sorry

end Cedar.Thm

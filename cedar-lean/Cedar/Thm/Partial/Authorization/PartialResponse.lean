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

import Cedar.Partial.Response
import Cedar.Thm.Data.Set

namespace Cedar.Thm.Partial.Response

open Cedar.Data
open Cedar.Spec (Effect PolicyID)
open Cedar.Partial (Residual)

theorem mayBeSatisfied_wf {resp : Partial.Response} {eff : Effect} :
  (resp.mayBeSatisfied eff).WellFormed
:= by
  unfold Set.WellFormed Partial.Response.mayBeSatisfied Set.toList
  simp only [Set.make_make_eqv]
  apply List.Equiv.symm
  exact Set.elts_make_equiv

theorem mustBeSatisfied_wf {resp : Partial.Response} {eff : Effect} :
  (resp.mustBeSatisfied eff).WellFormed
:= by
  unfold Set.WellFormed Partial.Response.mustBeSatisfied Set.toList
  simp only [Set.make_make_eqv]
  apply List.Equiv.symm
  exact Set.elts_make_equiv

theorem permits_wf {resp : Partial.Response} :
  resp.permits.WellFormed
:= by
  unfold Partial.Response.permits
  apply mayBeSatisfied_wf (eff := .permit)

theorem knownPermits_wf {resp : Partial.Response} :
  resp.knownPermits.WellFormed
:= by
  unfold Partial.Response.knownPermits
  apply mustBeSatisfied_wf (eff := .permit)

theorem forbids_wf {resp : Partial.Response} :
  resp.forbids.WellFormed
:= by
  unfold Partial.Response.forbids
  apply mayBeSatisfied_wf (eff := .forbid)

theorem knownForbids_wf {resp : Partial.Response} :
  resp.knownForbids.WellFormed
:= by
  unfold Partial.Response.knownForbids
  apply mustBeSatisfied_wf (eff := .forbid)

theorem overapproximateDeterminingPolicies_wf {resp : Partial.Response} :
  resp.overapproximateDeterminingPolicies.WellFormed
:= by
  unfold Partial.Response.overapproximateDeterminingPolicies
  cases resp.decision <;> simp only
  case allow => exact permits_wf
  case deny => exact forbids_wf
  case unknown => exact Set.union_wf resp.permits resp.forbids

theorem underapproximateDeterminingPolicies_wf {resp : Partial.Response} :
  resp.underapproximateDeterminingPolicies.WellFormed
:= by
  unfold Partial.Response.underapproximateDeterminingPolicies
  cases resp.decision <;> simp only
  case allow => exact knownPermits_wf
  case deny => exact knownForbids_wf
  case unknown => exact Set.empty_wf

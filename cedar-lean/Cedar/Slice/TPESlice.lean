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

import Cedar.Slice.PolicySlice
import Cedar.TPE.Evaluator
import Cedar.TPE.Input

/-!
This file defines policy slicing for type-aware partial evaluation (TPE).

A TPE slicer takes a *partial* request and entity store and returns the subset
of the policies that must be considered. Unlike the concrete slicing in
`Cedar.Slice.PolicySlice`, a slicer only has partial information available, so
it must be conservative wherever the partial store is unknown.

Crucially, the slicers here are purely syntactic: they inspect only the policy
scope, never the conditions, and therefore do not require the policies to be
well-typed. This is what allows a slice to be typechecked and partially
evaluated even when the full policy set could not be (see
`Cedar.Thm.TPE.PolicySlice`).

For proofs of correctness, see `Cedar.Thm.TPE.PolicySlice`.
-/

namespace Cedar.Slice

open Cedar.Spec Cedar.TPE

/--
A TPE policy slicer takes a partial request and partial entities and returns a
subset of the policies to consider.
-/
abbrev PartialSlicer := PartialRequest → PartialEntities → Policies → Policies

/--
Conservative reading of `TPE.inₑ`, which returns `none` when the ancestors of
`uid₁` are unknown in the partial entity store. We must then assume membership,
since a later concretization could supply any ancestors at all.
-/
def partialInₑ (uid₁ uid₂ : EntityUID) (pes : PartialEntities) : Bool :=
  (TPE.inₑ uid₁ uid₂ pes).getD true

/--
Partial analogue of `isPolicyRelevantForAction`.

The action of a partial request is always concrete
(`PartialRequest.action : EntityUID`), so `==` and `is` constraints are decided
exactly. Only the group-membership constraints consult the action's ancestors,
which may be unknown.
-/
def isPolicyRelevantForPartialAction (policy : Policy) (preq : PartialRequest) (pes : PartialEntities) : Bool :=
  isPolicyRelevantForActionBy (partialInₑ · · pes) preq.action policy

/--
Action-based slicing for TPE: keep only the policies whose action scope is
relevant to the (concrete) action of the partial request.
-/
def partialActionSlice : PartialSlicer := fun preq pes policies =>
  policies.filter (isPolicyRelevantForPartialAction · preq pes)

end Cedar.Slice

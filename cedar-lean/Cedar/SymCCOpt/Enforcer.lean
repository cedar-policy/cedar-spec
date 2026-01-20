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

import Cedar.SymCC.Enforcer
import Cedar.SymCCOpt.CompiledPolicies

namespace Cedar.SymCC

open Cedar.Data Cedar.Spec Factory

/--
Returns the ground acyclicity and transitivity assumptions for a single `CompiledPolicy`.
-/
def enforceCompiledPolicy (cp : CompiledPolicy) : Set Term :=
  let tr := cp.footprint.elts.flatMap (λ t => cp.footprint.elts.map (transitivity t · cp.εnv.entities))
  Set.make (cp.acyclicity.elts ++ tr)

/--
Returns the ground acyclicity and transitivity assumptions for a single `CompiledPolicySet`.
-/
def enforceCompiledPolicySet (cpset : CompiledPolicySet) : Set Term :=
  let tr := cpset.footprint.elts.flatMap (λ t => cpset.footprint.elts.map (transitivity t · cpset.εnv.entities))
  Set.make (cpset.acyclicity.elts ++ tr)

/--
Returns the ground acyclicity and transitivity assumptions for a pair of `CompiledPolicy`.
Caller guarantees that `cp₁` and `cp₂` were compiled for the same `εnv`.
-/
def enforcePairCompiledPolicy (cp₁ : CompiledPolicy) (cp₂ : CompiledPolicy) : Set Term :=
  assert! cp₁.εnv = cp₂.εnv
  let footprint := cp₁.footprint ++ cp₂.footprint
  let tr := footprint.elts.flatMap (λ t => footprint.elts.map (transitivity t · cp₁.εnv.entities))
  Set.make (cp₁.acyclicity.elts ++ cp₂.acyclicity.elts ++ tr)

/--
Returns the ground acyclicity and transitivity assumptions for a pair of `CompiledPolicySet`.
Caller guarantees that `cpset₁` and `cpset₂` were compiled for the same `εnv`.
-/
def enforcePairCompiledPolicySet (cpset₁ : CompiledPolicySet) (cpset₂ : CompiledPolicySet) : Set Term :=
  assert! cpset₁.εnv = cpset₂.εnv
  let footprint := cpset₁.footprint ++ cpset₂.footprint
  let tr := footprint.elts.flatMap (λ t => footprint.elts.map (transitivity t · cpset₁.εnv.entities))
  Set.make (cpset₁.acyclicity.elts ++ cpset₂.acyclicity.elts ++ tr)

namespace Cedar.SymCC

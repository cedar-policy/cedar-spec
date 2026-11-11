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

import CedarGen.Relational.SchemaGen
import Specimen.Correctness.Workers

/-! The derived schema generator only produces what its relation allows. Its workers' laws `W.sound`
come with the derivation (`specimen.emitSound`); here, what they give for whole environments. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound
open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Basalt

/-- **Every environment is well formed.** Every environment the derived schema generator produces, at any
fuel, size and leaf size, is well formed and has at most `budget` request environments. -/
theorem genTypeEnvB_generated (fuel iS sz budget : Nat) (r : HierMode) (env : TypeEnv)
    (h : Produces ((worker% gen SchemaGen.GenTypeEnvB [0, 2])
      fuel iS sz budget : SGen _) (r, env)) :
    WfTypeEnv env ∧ env.schema.environments.length ≤ budget :=
  genTypeEnvB_iff.mp ⟨r, (worker% gen SchemaGen.GenTypeEnvB [0, 2] sound)
    fuel iS sz budget (r, env) h⟩

/-- …and so is every environment of the generator as its instance runs it. -/
theorem genTypeEnvB_instance_generated (budget s l : Nat) (r : HierMode) (env : TypeEnv)
    (h : Produces (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
      (G := SGen) s l) (r, env)) :
    WfTypeEnv env ∧ env.schema.environments.length ≤ budget :=
  genTypeEnvB_generated _ _ _ budget r env h

/-- **Complete as well.** Every well-formed environment with at most `budget` request environments is
generated, in some mode, at every large enough size and leaf size. -/
theorem genTypeEnvB_instance_complete (budget : Nat) (env : TypeEnv)
    (h : WfTypeEnv env ∧ env.schema.environments.length ≤ budget) :
    ∃ r n, ∀ s l, n ≤ s → n ≤ l →
      Produces (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) (r, env) := by
  obtain ⟨r, hr⟩ := genTypeEnvB_iff.mpr h
  exact ⟨r, BacktrackGenForComplete.complete (r, env) hr⟩

end Cedar.Validation.Relational.SchemaGen.Sound

#print axioms Cedar.Validation.Relational.SchemaGen.Sound.genTypeEnvB_instance_complete
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.genTypeEnvB_generated
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.genTypeEnvB_instance_generated

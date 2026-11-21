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

import CedarGen.Relational.PolicyGen
import Specimen.Correctness.Workers

/-! # The multi-environment policy generator is sound

The derived policy generator's soundness comes with its derivation (`specimen.emitSound`); here,
what it gives: every policy it produces, for well-formed environments, is valid in all of them. -/

namespace Cedar.Validation.Relational.PolicyGen.Sound

open Cedar.Spec Cedar.Validation Specimen.Correctness Basalt

/-- **Every generated policy is valid.** For environments with unique entity and action keys that
satisfy the validator's assumptions, every policy the derived generator produces, at any fuel, size
and leaf size, is accepted by the validator in every one of them. -/
theorem validGuidedPolicy_generated (fuel iS sz : Nat) (ets : EntitySchema) (acts : ActionSchema)
    (envs : List TypeEnv) (p : Policy)
    (h : Produces ((worker% gen PolicyGen.ValidGuidedPolicy [3])
      fuel iS sz ets acts envs : SGen _) p)
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup)
    (hwf : ∀ env ∈ envs, EnvAssumptions env) :
    ValidPolicy ets acts envs p :=
  ((worker% gen PolicyGen.ValidGuidedPolicy [3] sound)
    fuel iS sz ets acts envs p h).valid hndE hndA hwf

/-- `validIn` over a schema's own environments is the validator's verdict on the policy. -/
theorem validate_of_validIn {S : Schema} {p : Policy}
    (h : validIn S.ets S.acts S.environments p = true) : validate [p] S = .ok () := by
  unfold validIn at h
  simp only [validate, typecheckPolicyWithEnvironments]
  split at h
  · next hce hm =>
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp [hce, hm, h, Except.mapError, bind, Except.bind, pure, Except.pure]
  · simp at h

/-- **Every generated policy passes Cedar's validator.** For a schema `S`, every policy the derived
generator produces over `S`'s environments is accepted by the validator. No assumption on `S`:
the generator's last check is the validator's own run. -/
theorem validate_generated (fuel iS sz : Nat) (S : Schema) (p : Policy)
    (h : Produces ((worker% gen PolicyGen.ValidGuidedPolicy [3])
      fuel iS sz S.ets S.acts S.environments : SGen _) p) :
    validate [p] S = .ok () := by
  have := (worker% gen PolicyGen.ValidGuidedPolicy [3] sound)
    fuel iS sz S.ets S.acts S.environments p h
  cases this with
  | mk _ hv => exact validate_of_validIn hv

end Cedar.Validation.Relational.PolicyGen.Sound

#print axioms Cedar.Validation.Relational.PolicyGen.Sound.validate_generated

/--
info: 'Cedar.Validation.Relational.PolicyGen.Sound.validGuidedPolicy_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cedar.Validation.Relational.PolicyGen.Sound.validGuidedPolicy_generated

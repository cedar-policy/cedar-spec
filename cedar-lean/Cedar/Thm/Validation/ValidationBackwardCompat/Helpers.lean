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

import Cedar.Thm.Validation.TypeOfCongruence
import Cedar.Thm.Validation.ValidationPolicySlice

/-!
# Backward compatibility helpers

Additional helpers beyond the typeOf congruence theorems, used by the
backward-compatibility proofs.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem contains_or_actionType_fwd
    {ets₁ ets₂ : EntitySchema} {acts₁ acts₂ : ActionSchema}
    (hets_fwd : ∀ (ety : EntityType) (entry : EntitySchemaEntry),
      ets₁.find? ety = some entry → ets₂.find? ety = some entry)
    (hacts : acts₁ = acts₂)
    {ety : EntityType}
    (hv : (ets₁.contains ety || acts₁.actionType? ety) = true) :
    (ets₂.contains ety || acts₂.actionType? ety) = true := by
  cases hc : ets₁.contains ety
  · simp [hc] at hv; rw [← hacts]; simp [hv]
  · simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨entry, hf⟩ := hc
    simp [EntitySchema.contains, hets_fwd ety entry hf]

/-- Extract a single policy's validation result from `validate policies schema = .ok ()`. -/
theorem policy_validated_of_validate {policies : Policies} {schema : Schema} {p : Policy}
    (hval : validate policies schema = .ok ())
    (hp : p ∈ policies) :
    typecheckPolicyWithEnvironments typecheckPolicy p schema = .ok () :=
  List.forM_ok_implies_all_ok' (by simp [validate] at hval; exact hval) p hp

end Cedar.Thm

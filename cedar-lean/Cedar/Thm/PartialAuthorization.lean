/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec.Value
import Cedar.Spec.PartialAuthorizer
import Cedar.Spec.PartialResponse
import Cedar.Thm.PartialEval
import Cedar.Thm.PartialEval.And
import Cedar.Thm.Utils

/-! This file contains theorems about Cedar's partial evaluator. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Except

/--
  just a sanity-check theorem about implementation details of isAuthorizedPartial:
  for any given set of partial inputs, every policy is either knownSatisfied,
  knownUnsatisfied, knownErroring, or residual
-/
theorem policy_cases {policy : Policy} {req : PartialRequest} {entities : PartialEntities} :
  knownSatisfied policy req entities ∨
  knownUnsatisfied policy req entities ∨
  knownErroring policy req entities ∨
  (residual policy req entities).isSome
:= by
  unfold knownSatisfied knownUnsatisfied knownErroring residual
  cases h₁ : (partialEvaluate policy.toExpr req entities) <;> simp [h₁]
  case ok pval =>
    unfold Policy.toExpr at h₁
    have h₂ := @partial_exprand_produces_bool_residual_or_error policy.principalScope.toExpr (Expr.and policy.actionScope.toExpr (Expr.and policy.resourceScope.toExpr policy.condition)) req entities
    simp [h₁] at h₂
    cases pval <;> try cases h₂
    case residual r => simp
    case value v =>
      cases v <;> try cases h₂
      case prim p =>
        cases p <;> try cases h₂
        case bool.intro b =>
          cases b <;> simp

/--
  helper lemma:
  residualPolicies produces the empty set when applied to concrete inputs
-/
theorem residualPolicies_empty_on_concrete {policies : Policies} {req : Request} {entities : Entities} :
  residualPolicies policies req entities = []
:= by
  unfold residualPolicies residual
  simp [partial_eval_on_concrete_eqv_concrete_eval, Except.map]
  simp [List.filterMap_empty_iff_f_returns_none]
  intro p _
  split <;> simp
  rename_i r h₂
  generalize (evaluate p.toExpr req entities) = res at h₂
  split at h₂ <;> simp at h₂

/--
  helper lemma:
  knownSatisfied is the same as satisfied if all inputs are concrete
-/
theorem knownSatisfied_eqv_satisfied_on_concrete {policy : Policy} {req : Request} {entities : Entities} :
  knownSatisfied policy req entities = satisfied policy req entities
:= by
  unfold knownSatisfied satisfied
  simp [partial_eval_on_concrete_eqv_concrete_eval, Except.map]
  split <;> rename_i h <;> simp [h]

/--
  helper lemma:
  knownSatisfiedPolicies is the same as satisfiedPolicies if all inputs are concrete
-/
theorem knownSatisfiedPolicies_eqv_satisfiedPolicies_on_concrete {effect : Effect} {policies : Policies} {req : Request} {entities : Entities} :
  knownSatisfiedPolicies effect policies req entities = satisfiedPolicies effect policies req entities
:= by
  unfold knownSatisfiedPolicies satisfiedPolicies
  rw [Set.make_make_eqv]
  unfold knownSatisfiedWithEffect satisfiedWithEffect
  simp [knownSatisfied_eqv_satisfied_on_concrete, List.Equiv]

/--
  helper lemma:
  knownErroring is the same as hasError if all inputs are concrete
-/
theorem knownErroring_eqv_hasError_on_concrete {policy : Policy} {req : Request} {entities : Entities} :
  knownErroring policy req entities = hasError policy req entities
:= by
  unfold knownErroring hasError
  simp [partial_eval_on_concrete_eqv_concrete_eval, Except.map]
  split <;> rename_i h₁ <;> split at h₁
  case _ => simp at h₁
  case _ => rename_i h₂ ; simp [h₂]
  case _ => rename_i h₂ ; simp [h₂]
  case _ => simp at h₁

/--
  helper lemma:
  knownErroringPolicies is the same as errorPolicies if all inputs are concrete
-/
theorem knownErroringPolicies_eqv_errorPolicies_on_concrete {policies : Policies} {req : Request} {entities : Entities} :
  knownErroringPolicies policies req entities = errorPolicies policies req entities
:= by
  unfold knownErroringPolicies errorPolicies
  rw [Set.make_make_eqv]
  unfold knownErroring' errored
  simp [knownErroring_eqv_hasError_on_concrete, List.Equiv]

/--
  Partial-authorizing with concrete inputs gives the same concrete outputs as
  concrete-authorizing with those inputs.

  Corollary to this: partial-authorizing with concrete inputs never gives a
  residual response.
-/
theorem partial_authz_eqv_authz_on_concrete {policies : Policies} {req : Request} {entities : Entities} :
  isAuthorizedPartial req entities policies = .known (isAuthorized req entities policies)
:= by
  unfold isAuthorizedPartial isAuthorized
  simp [knownSatisfiedPolicies_eqv_satisfiedPolicies_on_concrete, knownErroringPolicies_eqv_errorPolicies_on_concrete, residualPolicies_empty_on_concrete, Set.isEmpty]
  split <;> rename_i h₁ <;> simp [h₁]
  split <;> simp

/--
  helper lemma: if partial authorization returns .known, then residualPolicies
  is the empty set
-/
theorem partial_authz_known_then_residualPolicies_empty {policies : Policies} {req : PartialRequest} {entities : PartialEntities} {resp : Response} :
  isAuthorizedPartial req entities policies = .known resp →
  residualPolicies policies req entities = []
:= by
  sorry

/--
  If partial authorization returns .known, then that result is identical
  (including diagnostics) to the result you'd get with any (valid) substitution
  for the unknowns.
-/
theorem partial_authz_known_then_unknown_agnostic {policies : Policies} {req req': PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  req.subst subsmap = some req' →
  isAuthorizedPartial req entities policies = .known resp →
  isAuthorizedPartial req' (entities.subst subsmap) policies = .known resp
:= by
  intro h₁ h₂
  have h₃ := partial_authz_known_then_residualPolicies_empty h₂
  simp [isAuthorizedPartial]
  sorry

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

import Cedar.Thm.SymCC.Verifier

/-!
This file proves the soundness and completeness of the verification queries in
`Cedar.SymCC.Verifier`, which are based on Cedar's reduction to SMT. For
soundness, we show that if the result of a query is unsatisfiable, then the
property checked by the query holds for all _strongly well-formed_ concrete
environments `env` that are represented by a given strongly well-formed symbolic
environment `εnv`. For completeness, we show that if the result of the query is
satisfiable, then there is a strongly-well formed concrete environment `env`
represented by `εnv` for which the queried property is violated.

An environment is strongly well-formed if (1) it is free of dangling entity
references, and (2) its ancestor relation is the transitive closure of a DAG.
Cedar verification queries (dis)prove properties with respect to strongly
well-formed environments.
--/

namespace Cedar.Thm

open Spec SymCC

/--
The `verifyNeverError` analysis is sound: if the assertions
`verifyNeverErrors p εnv` are unsatisfiable for the policy `p` and
the strongly well-formed symbolic environment `εnv`, then the
evaluator will not error when applied to `p` and any
strongly well-formed concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyNeverErrors_is_sound  {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverErrors p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    (evaluate p.toExpr env.request env.entities).isOk
:= by
  exact verifyEvaluate_is_sound verifyNeverErrors_wbeq

/--
The `verifyNeverError` analysis is complete: if the assertions
`verifyNeverErrors p εnv` are satisfiable for the policy `p` and the strongly
well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the evaluator
will error when applied to `p` and `env`.
-/
theorem verifyNeverErrors_is_complete {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverErrors p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ (evaluate p.toExpr env.request env.entities).isOk
:= by
  simp only [Bool.not_eq_true]
  exact verifyEvaluate_is_complete verifyNeverErrors_wbeq

/--
The `verifyAlwaysMatches` analysis is sound: if the assertions
`verifyAlwaysMatches p εnv` are unsatisfiable for the policy `p` and the
strongly well-formed symbolic environment `εnv`, then the evaluator will return
`.ok true` when applied to `p` and any strongly well-formed concrete environment
`env ∈ᵢ εnv`.
-/
theorem verifyAlwaysMatches_is_sound {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyAlwaysMatches p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    evaluate p.toExpr env.request env.entities = .ok true
:= by
  simp only [verifyAlwaysMatches]
  have := verifyEvaluate_is_sound verifyAlwaysMatches_wbeq (p := p) (εnv := εnv) (asserts := asserts)
  simp only [beq_iff_eq] at this
  exact this

/--
Alternate definition of soundness for alwaysMatches:

For a singleton policyset, if symcc says the policy alwaysMatches, then the spec
authorizer should say it always appears in determiningPolicies
-/
theorem verifyAlwaysMatches_is_sound' {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyAlwaysMatches p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    p.id ∈ (Spec.isAuthorized env.request env.entities [p]).determiningPolicies
:= by
  intro h₁ h₂ h₃ env h₄ h₅
  have := verifyAlwaysMatches_is_sound h₁ h₂ h₃ env h₄ h₅
  simp only [Spec.isAuthorized, Data.Set.isEmpty, Spec.satisfiedPolicies, satisfiedWithEffect,
    satisfied, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.filterMap_cons, this, and_true,
    List.filterMap_nil, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  cases p.effect
  all_goals simp [Data.Set.make_nil, Data.Set.make_singleton_nonempty, ← Data.Set.make_mem]

/--
The `verifyAlwaysMatches` analysis is complete: if the assertions
`verifyAlwaysMatches p εnv` are satisfiable for the policy `p` and the
strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the evaluator
will not return `.ok true` when applied to `p` and `env`.
-/
theorem verifyAlwaysMatches_is_complete {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyAlwaysMatches p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    evaluate p.toExpr env.request env.entities ≠ .ok true
:= by
  sorry

/--
Alternate definition of completeness for alwaysMatches:

For a singleton policyset, if symcc says the policy does not alwaysMatch, then
there exists a concrete environment where the policy does not appear in
determiningPolicies.
-/
theorem verifyAlwaysMatches_is_complete' {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyAlwaysMatches p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    p.id ∉ (Spec.isAuthorized env.request env.entities [p]).determiningPolicies
:= by
  sorry

/--
The `verifyEquivalent` analysis is sound: if the assertions
`verifyEquivalent ps₁ ps₂ εnv` are unsatisfiable for the policies `ps₁` and `ps₂`
and the strongly well-formed symbolic environment `εnv`, then the authorizer
will produce the same authorization decision when applied to `ps₁`, `ps₂`, and
any strongly well-formed concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyEquivalent_is_sound  {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyEquivalent ps₁ ps₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    env.StronglyWellFormedForPolicies ps₂ →
    bothAllowOrBothDeny
      (Spec.isAuthorized env.request env.entities ps₁)
      (Spec.isAuthorized env.request env.entities ps₂)
:= by
  exact verifyIsAuthorized_is_sound verifyEquivalent_wbaq

/--
The `verifyEquivalent` analysis is complete: if the assertions
`verifyEquivalent ps₁ ps₂ εnv` are satisfiable for the policies `ps₁` and `ps₂`
and the strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the authorizer
will produce different authorization decisions when applied to `ps₁`, `ps₂`,
and `env`.
-/
theorem verifyEquivalent_is_complete  {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyEquivalent ps₁ ps₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicies ps₁ ∧
    env.StronglyWellFormedForPolicies ps₂ ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ bothAllowOrBothDeny
      (Spec.isAuthorized env.request env.entities ps₁)
      (Spec.isAuthorized env.request env.entities ps₂)
:= by
  simp only [Bool.not_eq_true]
  exact verifyIsAuthorized_is_complete verifyEquivalent_wbaq

/--
The `verifyDisjoint` analysis is sound: if the assertions
`verifyDisjoint ps₁ ps₂ εnv` are unsatisfiable for the policies `ps₁` and `ps₂`
and the strongly well-formed symbolic environment `εnv`, then the authorizer
will not produce two `allow` decisions when applied to `ps₁`, `ps₂`, and
any strongly well-formed concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyDisjoint_is_sound  {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyDisjoint ps₁ ps₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    env.StronglyWellFormedForPolicies ps₂ →
    atLeastOneDenies
      (Spec.isAuthorized env.request env.entities ps₁)
      (Spec.isAuthorized env.request env.entities ps₂)
:= by
  exact verifyIsAuthorized_is_sound verifyDisjoint_wbaq

/--
The `verifyDisjoint` analysis is complete: if the assertions
`verifyDisjoint ps₁ ps₂ εnv` are satisfiable for the policies `ps₁` and `ps₂`
and the strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the authorizer
will produce two `allow` decisions when applied to `ps₁`, `ps₂`,
and `env`.
-/
theorem verifyDisjoint_is_complete  {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyDisjoint ps₁ ps₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicies ps₁ ∧
    env.StronglyWellFormedForPolicies ps₂ ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ atLeastOneDenies
      (Spec.isAuthorized env.request env.entities ps₁)
      (Spec.isAuthorized env.request env.entities ps₂)
:= by
  simp only [Bool.not_eq_true]
  exact verifyIsAuthorized_is_complete verifyDisjoint_wbaq

/--
The `verifyImplies` analysis is sound: if the assertions
`verifyImplies ps₁ ps₂ εnv` are unsatisfiable for the policies `ps₁` and `ps₂`
and the strongly well-formed symbolic environment `εnv`, then if the authorizer
returns `allow` for `ps₁`, it also returns `allow` for `ps₂` in
any strongly well-formed concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyImplies_is_sound  {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyImplies ps₁ ps₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    env.StronglyWellFormedForPolicies ps₂ →
    ifFirstAllowsSoDoesSecond
      (Spec.isAuthorized env.request env.entities ps₁)
      (Spec.isAuthorized env.request env.entities ps₂)
:= by
  exact verifyIsAuthorized_is_sound verifyImplies_wbaq

/--
The `verifyImplies` analysis is complete: if the assertions
`verifyImplies ps₁ ps₂ εnv` are satisfiable for the policies `ps₁` and `ps₂`
and the strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the authorizer
will produce `allow` for `ps₁` but `deny` for `ps₂` in `env`.
-/
theorem verifyImplies_is_complete  {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyImplies ps₁ ps₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicies ps₁ ∧
    env.StronglyWellFormedForPolicies ps₂ ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ ifFirstAllowsSoDoesSecond
      (Spec.isAuthorized env.request env.entities ps₁)
      (Spec.isAuthorized env.request env.entities ps₂)
:= by
  simp only [Bool.not_eq_true]
  exact verifyIsAuthorized_is_complete verifyImplies_wbaq

/--
The `verifyAlwaysDenies` analysis is sound: if the assertions
`verifyAlwaysDenies ps₁ εnv` are unsatisfiable for the policies `ps₁`
and the strongly well-formed symbolic environment `εnv`, then the authorizer
will return `deny` when applied to `ps₁` and any strongly well-formed
concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyAlwaysDenies_is_sound  {ps₁ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  verifyAlwaysDenies ps₁ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    denies (Spec.isAuthorized env.request env.entities ps₁)
:= by
  intro hwε₁ hvc hsat env hin hwe₁
  unfold verifyAlwaysDenies at hvc
  rw [denies_eq_implies_false _ env]
  exact verifyIsAuthorized_is_sound verifyImplies_wbaq hwε₁
    (swf_εnv_for_empty_policies hwε₁.left) hvc hsat env hin
    hwe₁ (swf_env_for_empty_policies hwe₁.left)

/--
The `verifyAlwaysDenies` analysis is sound: if the assertions
`verifyAlwaysDenies ps₁ εnv` are satisfiable for the policies `ps₁`
and the strongly well-formed symbolic environment `εnv`, then there
exists a strongly well-formed concrete environment `env ∈ᵢ εnv` such
that the authorizer will not return `deny` when applied to `ps₁` and `env`.
-/
theorem verifyAlwaysDenies_is_complete {ps₁ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  verifyAlwaysDenies ps₁ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicies ps₁ ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ denies (Spec.isAuthorized env.request env.entities ps₁)
:= by
  intro hwε₁ hvc hsat
  unfold verifyAlwaysDenies at hvc
  have ⟨env, h⟩ := verifyIsAuthorized_is_complete verifyImplies_wbaq hwε₁
    (swf_εnv_for_empty_policies hwε₁.left) hvc hsat
  exists env
  rw [denies_eq_implies_false _ env]
  simp [h]

/--
The `verifyAlwaysAllows` analysis is sound: if the assertions
`verifyAlwaysAllows ps₁ εnv` are unsatisfiable for the policies `ps₁`
and the strongly well-formed symbolic environment `εnv`, then the authorizer
will return `allow` when applied to `ps₁` and any strongly well-formed
concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyAlwaysAllows_is_sound  {ps₁ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  verifyAlwaysAllows ps₁ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    allows (Spec.isAuthorized env.request env.entities ps₁)
:= by
  intro hwε₁ hvc hsat env hin hwe₁
  unfold verifyAlwaysAllows at hvc
  rw [allows_eq_allowAll_implies _ env]
  exact verifyIsAuthorized_is_sound verifyImplies_wbaq
    (swf_εnv_for_allowAll_policies hwε₁.left) hwε₁ hvc hsat env hin
    (swf_env_for_allowAll_policies hwe₁.left) hwe₁


/--
The `verifyAlwaysAllows` analysis is sound: if the assertions
`verifyAlwaysAllows ps₁ εnv` are satisfiable for the policies `ps₁`
and the strongly well-formed symbolic environment `εnv`, then there
exists a strongly well-formed concrete environment `env ∈ᵢ εnv` such
that the authorizer will not return `allow` when applied to `ps₁` and `env`.
-/
theorem verifyAlwaysAllows_is_complete {ps₁ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicies ps₁ →
  verifyAlwaysAllows ps₁ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicies ps₁ ∧
    Env.EnumCompleteFor env εnv ∧
    ¬ allows (Spec.isAuthorized env.request env.entities ps₁)
:= by
  intro hwε₁ hvc hsat
  unfold verifyAlwaysAllows at hvc
  have ⟨env, h⟩ := verifyIsAuthorized_is_complete verifyImplies_wbaq
    (swf_εnv_for_allowAll_policies hwε₁.left) hwε₁ hvc hsat
  exists env
  rw [allows_eq_allowAll_implies _ env]
  simp [h]


end Cedar.Thm

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
  intro h₁ h₂ h₃
  unfold verifyAlwaysMatches at h₂
  have ⟨env, h₄, h₅, h₆, h₇⟩ := verifyEvaluate_is_complete verifyAlwaysMatches_wbeq h₁ h₂ h₃
  exists env
  rw [beq_eq_false_iff_ne, ne_eq] at h₇
  exact ⟨h₄, h₅, h₆, h₇⟩

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
  intro h₁ h₂ h₃
  have ⟨env, h₄, h₅, h₆, h₇⟩ := verifyAlwaysMatches_is_complete h₁ h₂ h₃
  exists env
  apply And.intro h₄
  apply And.intro h₅
  apply And.intro h₆
  simp only [Spec.isAuthorized, Data.Set.isEmpty, Spec.satisfiedPolicies, satisfiedWithEffect,
    satisfied, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.filterMap_cons,
    List.filterMap_nil, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  cases p.effect <;> simp [Data.Set.make_nil, Data.Set.empty_no_elts, h₇]

/--
The `verifyNeverMatches` analysis is sound: if the assertions
`verifyNeverMatches p εnv` are unsatisfiable for the policy `p` and the
strongly well-formed symbolic environment `εnv`, then the evaluator will never
return `.ok true` when applied to `p` and any strongly well-formed concrete
environment `env ∈ᵢ εnv`.
-/
theorem verifyNeverMatches_is_sound {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverMatches p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    evaluate p.toExpr env.request env.entities ≠ .ok true
:= by
  simp only [verifyNeverMatches]
  have := verifyEvaluate_is_sound verifyNeverMatches_wbeq (p := p) (εnv := εnv) (asserts := asserts)
  simp only [bne_iff_ne, ne_eq] at this
  exact this

/--
Alternate definition of soundness for neverMatches:

For a singleton policyset, if symcc says the policy neverMatches, then the spec
authorizer should say it never appears in determiningPolicies.
-/
theorem verifyNeverMatches_is_sound' {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverMatches p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    p.id ∉ (Spec.isAuthorized env.request env.entities [p]).determiningPolicies
:= by
  intro h₁ h₂ h₃ env h₄ h₅
  have := verifyNeverMatches_is_sound h₁ h₂ h₃ env h₄ h₅
  simp only [Spec.isAuthorized, Data.Set.isEmpty, Spec.satisfiedPolicies, satisfiedWithEffect,
    satisfied, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.filterMap_cons,
    List.filterMap_nil, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  cases p.effect <;> simp [Data.Set.make_nil, Data.Set.empty_no_elts, this]

/--
The `verifyNeverMatches` analysis is complete: if the assertions
`verifyNeverMatches p εnv` are satisfiable for the policy `p` and the
strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the evaluator
will return `.ok true` when applied to `p` and `env`.
-/
theorem verifyNeverMatches_is_complete {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverMatches p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    evaluate p.toExpr env.request env.entities = .ok true
:= by
  intro h₁ h₂ h₃
  unfold verifyNeverMatches at h₂
  have ⟨env, h₄, h₅, h₆, h₇⟩ := verifyEvaluate_is_complete verifyNeverMatches_wbeq h₁ h₂ h₃
  exists env
  have : evaluate p.toExpr env.request env.entities = .ok true := by
    cases heval : evaluate p.toExpr env.request env.entities
    · simp [bne, heval] at h₇
    · simp [bne, heval] at h₇; simp [h₇]
  exact ⟨h₄, h₅, h₆, this⟩

/--
Alternate definition of completeness for neverMatches:

For a singleton policyset, if symcc says the policy does not neverMatch, then
there exists a concrete environment where the policy appears in
determiningPolicies.
-/
theorem verifyNeverMatches_is_complete' {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p →
  verifyNeverMatches p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    p.id ∈ (Spec.isAuthorized env.request env.entities [p]).determiningPolicies
:= by
  intro h₁ h₂ h₃
  have ⟨env, h₄, h₅, h₆, h₇⟩ := verifyNeverMatches_is_complete h₁ h₂ h₃
  exists env
  apply And.intro h₄
  apply And.intro h₅
  apply And.intro h₆
  simp only [Spec.isAuthorized, Data.Set.isEmpty, Spec.satisfiedPolicies, satisfiedWithEffect,
    satisfied, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.filterMap_cons, h₇, and_true,
    List.filterMap_nil, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  cases p.effect <;> simp [Data.Set.make_nil, Data.Set.make_singleton_nonempty, ← Data.Set.make_mem]

/--
The `verifyMatchesEquivalent` analysis is sound: if the assertions
`verifyMatchesEquivalent p₁ p₂ εnv` are unsatisfiable for the policies `p₁` and `p₂`
and the strongly well-formed symbolic environment `εnv`, then the policies
will have the same matching behavior (both match or both don't match) when
applied to any strongly well-formed concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyMatchesEquivalent_is_sound {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyMatchesEquivalent p₁ p₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p₁ →
    env.StronglyWellFormedForPolicy p₂ →
    (evaluate p₁.toExpr env.request env.entities = .ok true) =
    (evaluate p₂.toExpr env.request env.entities = .ok true)
:= by
  intro h₁ h₂ h₃ h₄ env h₅ h₆ h₇
  have h_sound := verifyEvaluatePair_is_sound verifyMatchesEquivalent_wbepq h₁ h₂ h₃ h₄ env h₅ h₆ h₇
  rw [beq_iff_eq] at h_sound
  cases hev₁ : (evaluate p₁.toExpr env.request env.entities == .ok (.prim (.bool true)))
  · simp only [hev₁, Bool.false_eq, beq_eq_false_iff_ne, ne_eq] at h_sound
    simp only [beq_eq_false_iff_ne, ne_eq] at hev₁
    simp [*]
  · simp only [hev₁, Bool.true_eq, beq_iff_eq] at h_sound
    simp only [beq_iff_eq] at hev₁
    simp [*]

/--
The `verifyMatchesEquivalent` analysis is complete: if the assertions
`verifyMatchesEquivalent p₁ p₂ εnv` are satisfiable for the policies `p₁` and `p₂`
and the strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that the policies
will have different matching behavior (one matches and the other doesn't) when
applied to `env`.
-/
theorem verifyMatchesEquivalent_is_complete {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyMatchesEquivalent p₁ p₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p₁ ∧
    env.StronglyWellFormedForPolicy p₂ ∧
    Env.EnumCompleteFor env εnv ∧
    (evaluate p₁.toExpr env.request env.entities = .ok true) ≠
    (evaluate p₂.toExpr env.request env.entities = .ok true)
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨env, h₅, h₆, h₇, h₈, h₉⟩ := verifyEvaluatePair_is_complete verifyMatchesEquivalent_wbepq h₁ h₂ h₃ h₄
  exists env
  simp only [beq_eq_false_iff_ne, ne_eq] at h₉
  apply And.intro h₅
  apply And.intro h₆
  apply And.intro h₇
  apply And.intro h₈
  cases hev₁ : evaluate p₁.toExpr env.request env.entities == .ok (.prim (.bool true))
  · simp only [hev₁, Bool.false_eq, beq_eq_false_iff_ne, ne_eq, Decidable.not_not] at h₉
    simp only [beq_eq_false_iff_ne, ne_eq] at hev₁
    simp [*]
  · simp only [hev₁, Bool.true_eq, beq_iff_eq] at h₉
    simp only [beq_iff_eq] at hev₁
    simp [*]

/--
The `verifyMatchesImplies` analysis is sound: if the assertions
`verifyMatchesImplies p₁ p₂ εnv` are unsatisfiable for the policies `p₁` and `p₂`
and the strongly well-formed symbolic environment `εnv`, then if `p₁` matches
in any strongly well-formed concrete environment `env ∈ᵢ εnv`, then `p₂` also matches.
-/
theorem verifyMatchesImplies_is_sound {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyMatchesImplies p₁ p₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p₁ →
    env.StronglyWellFormedForPolicy p₂ →
    evaluate p₁.toExpr env.request env.entities = .ok true →
    evaluate p₂.toExpr env.request env.entities = .ok true
:= by
  intro h₁ h₂ h₃ h₄ env h₅ h₆ h₇ h₈
  have := verifyEvaluatePair_is_sound verifyMatchesImplies_wbepq h₁ h₂ h₃ h₄ env h₅ h₆ h₇
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  cases this with
  | inl h => contradiction
  | inr h => exact h

/--
The `verifyMatchesImplies` analysis is complete: if the assertions
`verifyMatchesImplies p₁ p₂ εnv` are satisfiable for the policies `p₁` and `p₂`
and the strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that `p₁` matches
but `p₂` does not match in `env`.
-/
theorem verifyMatchesImplies_is_complete {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyMatchesImplies p₁ p₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p₁ ∧
    env.StronglyWellFormedForPolicy p₂ ∧
    Env.EnumCompleteFor env εnv ∧
    evaluate p₁.toExpr env.request env.entities = .ok true ∧
    evaluate p₂.toExpr env.request env.entities ≠ .ok true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨env, h₅, h₆, h₇, h₈, h₉⟩ := verifyEvaluatePair_is_complete verifyMatchesImplies_wbepq h₁ h₂ h₃ h₄
  exists env
  rw [Bool.or_eq_false_iff] at h₉
  simp_all

/--
The `verifyMatchesDisjoint` analysis is sound: if the assertions
`verifyMatchesDisjoint p₁ p₂ εnv` are unsatisfiable for the policies `p₁` and `p₂`
and the strongly well-formed symbolic environment `εnv`, then the policies
cannot both match in any strongly well-formed concrete environment `env ∈ᵢ εnv`.
-/
theorem verifyMatchesDisjoint_is_sound {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyMatchesDisjoint p₁ p₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p₁ →
    env.StronglyWellFormedForPolicy p₂ →
    ¬ (evaluate p₁.toExpr env.request env.entities = .ok true ∧
       evaluate p₂.toExpr env.request env.entities = .ok true)
:= by
  intro h₁ h₂ h₃ h₄ env h₅ h₆ h₇
  have := verifyEvaluatePair_is_sound verifyMatchesDisjoint_wbepq h₁ h₂ h₃ h₄ env h₅ h₆ h₇
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_eq_false_iff_ne, ne_eq] at this
  cases this with
  | inl h => simp [h]
  | inr h => simp [h]

/--
The `verifyMatchesDisjoint` analysis is complete: if the assertions
`verifyMatchesDisjoint p₁ p₂ εnv` are satisfiable for the policies `p₁` and `p₂`
and the strongly well-formed symbolic environment `εnv`, then there exists a
strongly well-formed concrete environment `env ∈ᵢ εnv` such that both policies
match in `env`.
-/
theorem verifyMatchesDisjoint_is_complete {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyMatchesDisjoint p₁ p₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p₁ ∧
    env.StronglyWellFormedForPolicy p₂ ∧
    Env.EnumCompleteFor env εnv ∧
    evaluate p₁.toExpr env.request env.entities = .ok true ∧
    evaluate p₂.toExpr env.request env.entities = .ok true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨env, h₅, h₆, h₇, h₈, h₉⟩ := verifyEvaluatePair_is_complete verifyMatchesDisjoint_wbepq h₁ h₂ h₃ h₄
  exists env
  simp only [Bool.not_and, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
    beq_iff_eq] at h₉
  simp [*]

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

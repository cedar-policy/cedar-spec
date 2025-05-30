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

import Cedar.Thm.SymCC.Authorizer
import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.SymCC.Compiler

/-!
This file defines the top-level correctness properties for the symbolic
evaluator. We show the encoding is sound and complete with respect to the
concrete semantics of Cedar. That is, the symbolic semantics both
overapproximates (soundness) and underapproximates (completeness) the concrete
semantics.
--/

namespace Cedar.Thm

open Spec SymCC

/--
Let `x` be a Cedar expression, `env` a concrete evaluation environment (request
and entities), `εnv` a symbolic evaluation environment, and `t` the outcome of
reducing `x` to a Term with respect to `εnv`.

Let `x` and `env` be a well-formed input to the concrete evaluator, i.e.,
`env.WellFormedFor x`.  This means that the entity store `env.entities` has
no dangling entity references, and all entity references that occur in `x` and
`env.request` are included in `env.entities`.

Let `x` and `εnv` be a well-formed input to the symbolic evaluator, i.e.,
`εnv.WellFormedFor x`.  This means that the symbolic entity store `εnv.entities`
has no dangling (undefined) entity types or references; all term types contained
in `εnv.entities` represent valid Cedar types; and all entity references that
occur in `x` and `εnv.request` are valid according to
`εnv.entities.isValidEntityUID`.

Let `εnv` represent a set of concrete environments that includes `env`, i.e.,
`env ∈ᵢ εnv`.  We relate concrete structures to their symbolic counterparts via
interpretations, which map from term variables and uninterpreted functions to
literals.  For example, `env ∈ᵢ εnv` if there exists a well-formed interpretation
`I` such that `env ∼ εnv.interpret I` are equivalent according to the sameness
relation `∼`.  Note that we can't use equality here, because interpreting a
symbolic structure with respect to an `Interpretation` produces a literal
symbolic structure (without any unknowns), which is then compared to the
corresponding concrete structure using a suitable sameness relation.

Given the above, the soundness theorem says that the output of the concrete
evaluator on `x` and `env` is contained in the set of concrete outcomes
represented by the output of the symbolic evaluator on `x` and `εnv`. We state
soundness in terms of `Outcome`s rather than `Result`s because the symbolic
evaluator does not distinguish between different kinds of errors---only between
normal and erroring executions.
-/
theorem compile_is_sound {x : Expr} {env : Env} {εnv : SymEnv} {t : Term.Outcome εnv} :
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  env ∈ᵢ εnv →
  compile x εnv = .ok t →
  ∃ (o : Outcome Value),
    o ∈ₒ t ∧
    evaluate x env.request env.entities ∼ o
:= by
  intros h₁ h₂ h₃ h₄
  replace ⟨I, h₃, h₅⟩ := h₃
  have ⟨o, h₆, h₇⟩ := same_results_implies_exists_outcome (compile_bisimulation h₁ h₂ h₃ h₅ h₄)
  exists o
  simp only [h₆, and_true]
  exists I

/--
Let `x` be a Cedar expression and `εnv` a symbolic evaluation environment, where
`x` and `εnv` are a well-formed input to the symbolic evaluator, i.e.,
`εnv.WellFormedFor x`.

Let `t` the outcome of reducing `x` to a Term with respect to `εnv`, and `o` a
concrete outcome represented by `t`.

Then, the completeness theorem says that there exists a concrete environment
`env` represented by `εnv` such that `x` and `env` are well-formed inputs to the
concrete evaluator and evaluating `x` against `env` produces the outcome `o`.
-/
theorem compile_is_complete {x : Expr} {εnv : SymEnv} {t : Term.Outcome εnv} {o : Outcome Value} :
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  o ∈ₒ t →
  ∃ (env : Env),
    env.WellFormedFor x ∧
    env ∈ᵢ εnv ∧
    evaluate x env.request env.entities ∼ o
:= by
  intros h₁ h₂ h₃
  replace ⟨I, h₃, h₅⟩ := h₃
  have ⟨env, h₆, h₇⟩ := exists_wf_env h₁ h₃
  exists env
  simp only [h₇, true_and]
  constructor
  · exists I
  · have ⟨o', h₈, h₉⟩ := same_results_implies_exists_outcome (compile_bisimulation h₁ h₇ h₃ h₆ h₂)
    have h₁₀ := same_outcomes_implies_eq h₅ h₉
    subst h₁₀
    exact h₈

/--
Let `ps` be Cedar policies, `env` a concrete evaluation environment (request and
entities), `εnv` a symbolic evaluation environment, and `t` the term resulting
from symbolically authorizing `ps` with respect to `εnv`, i.e.,
`SymCC.isAuthorized ps εnv = .ok t`.

Let `ps` and `env` be a well-formed input to the concrete authorizer, i.e.,
`env.WellFormedForPolicies ps`.  This means that the entity store `env.entities`
has no dangling entity references, and all entity references that occur in `ps`
and `env.request` are included in `env.entities`.

Let `ps` and `εnv` be a well-formed input to the symbolic authorizer, i.e.,
`εnv.WellFormedForPolices ps`.  This means that the symbolic entity store
`εnv.entities` has no dangling (undefined) entity types or references; all term
types contained in `εnv.entities` represent valid Cedar types; and all entity
references that occur in `ps` and `εnv.request` are valid according to
`εnv.entities.isValidEntityUID`.

Let `εnv` represent a set of concrete environments that includes `env`, i.e.,
`env ∈ᵢ εnv`.  We relate concrete structures to their symbolic counterparts via
interpretations, which map from term variables and uninterpreted functions to
literals.  For example, `env ∈ᵢ εnv` if there exists a well-formed interpretation
`I` such that `env ∼ εnv.interpret I` are equivalent according to the sameness
relation `∼`.  Note that we can't use equality here, because interpreting a
symbolic structure with respect to an `Interpretation` produces a literal
symbolic structure (without any unknowns), which is then compared to the
corresponding concrete structure using a suitable sameness relation.

Given the above, the soundness theorem says that the decision of the concrete
authorizer on `ps` and `env` is contained in the set of concrete decisions
represented by the output of the symbolic authorizer on `ps` and `εnv`. We state
soundness in terms of `Decision`s rather than `Response`s because the symbolic
authorizer computes only decision (and not the extra diagnostics contained in a
concrete `Response`).
-/
theorem isAuthorized_is_sound  {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term.Outcome εnv} :
  εnv.WellFormedForPolicies ps →
  env.WellFormedForPolicies ps →
  env ∈ᵢ εnv →
  SymCC.isAuthorized ps εnv = .ok t →
  ∃ (decision : Spec.Decision),
    decision ∈ₒ t ∧
    Spec.isAuthorized env.request env.entities ps ∼ decision
:= by
  intro hεnv henv hinᵢ hok
  replace ⟨I, hI, hinᵢ⟩ := hinᵢ
  have heq := isAuthorized_bisimulation hεnv henv hI hinᵢ hok
  exists (Spec.isAuthorized env.request env.entities ps).decision
  simp only [same_responses_self_decision, and_true]
  exists I

/--
Let `ps` be Cedar policies and `εnv` a symbolic evaluation environment, where
`ps` and `εnv` are a well-formed input to the symbolic authorizer, i.e.,
`εnv.WellFormedForPolicies ps`.

Let `t` the outcome of symbolically authorizing `ps` with respect to `εnv`, and `d` a
concrete authorization decision represented by `t`.

Then, the completeness theorem says that there exists a concrete environment
`env` represented by `εnv` such that `ps` and `env` are well-formed inputs to the
concrete authorizer and authorizing `os` against `env` produces the decision `d`.
-/
theorem isAuthorized_is_complete {ps : Policies} {εnv : SymEnv} {t : Term.Outcome εnv} {decision : Spec.Decision} :
  εnv.WellFormedForPolicies ps →
  SymCC.isAuthorized ps εnv = .ok t →
  decision ∈ₒ t →
  ∃ (env : Env),
    env.WellFormedForPolicies ps ∧
    env ∈ᵢ εnv ∧
    Spec.isAuthorized env.request env.entities ps ∼ decision
:= by
  intro hεnv hok hinₒ
  replace ⟨I, hI, hinₒ⟩ := hinₒ
  have ⟨env, heq, henv⟩ := exists_wf_env_for_policies hεnv hI
  exists env
  simp only [henv, true_and]
  constructor
  · exists I
  · replace heq := isAuthorized_bisimulation hεnv henv hI heq hok
    exact same_decision_and_response_implies_same_decision hinₒ heq

end Cedar.Thm

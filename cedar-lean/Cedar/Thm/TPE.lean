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

import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Soundness
import Cedar.Thm.Validation

/-!
This file defines the main theorem of TPE soundness and its associated lemmas.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-- The main lemma: Evaluating a residual derived from partially evaluating
a well-typed expression is equivalent to that of evaluating the original
expression, provided that requests and entities are consistent. The equivalency
is defined using `Except.toOption`.
-/
theorem partial_evaluate_is_sound
  {x : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {env : TypeEnv} :
  Residual.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  (x.evaluate req es).toOption = ((Cedar.TPE.evaluate x preq pes).evaluate req es).toOption
:= by
  intro h₁ h₂ h₃
  induction h₁
  case val =>
    exact partial_evaluate_is_sound_val
  case var =>
    exact partial_evaluate_is_sound_var h₃
  case ite x₁ x₂ x₃ hwt _ _ hₜ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact partial_evaluate_is_sound_ite h₂ hwt hₜ hᵢ₁ hᵢ₂ hᵢ₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_and h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_or h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case unaryApp op₁ x₁ ty hᵢ₁ =>
    exact partial_evaluate_is_sound_unary_app hᵢ₁
  case binaryApp op₂ x₁ x₂ ty _ hwt howt hᵢ₁ hᵢ₂ =>
    exact partial_evaluate_is_sound_binary_app h₂ h₃ hwt howt hᵢ₁ hᵢ₂
  case hasAttr_entity ety x₁ attr hᵢ₁ =>
    exact partial_evaluate_is_sound_has_attr h₃ hᵢ₁
  case hasAttr_record rty x₁ attr hᵢ₁ =>
    exact partial_evaluate_is_sound_has_attr h₃ hᵢ₁
  case getAttr_entity ety rty x₁ attr ty hᵢ₁ =>
    exact partial_evaluate_is_sound_get_attr h₃ hᵢ₁
  case getAttr_record rty x₁ attr ty hᵢ₁ =>
    exact partial_evaluate_is_sound_get_attr h₃ hᵢ₁
  case set ls ty hᵢ₁ =>
    exact partial_evaluate_is_sound_set hᵢ₁
  case record rty m hᵢ₁ hᵢ₁ =>
    exact partial_evaluate_is_sound_record hᵢ₁
  case call xfn args ty hᵢ₁ =>
    exact partial_evaluate_is_sound_call hᵢ₁

/-- The main theorem of TPE: Evaluating a result residual is equivalent to
evaluating the input policy, given valid and consistent requests and entities.
The equivalence is w.r.t authorization results. That is, the evaluation results
are strictly equal when they are `.ok` or both errors (captured by
`Except.toOption`). We do not care if the error types match because they do not
impact authorization results. As a matter of fact, they do not match because all
errors encountered during TPE are represented by an `error` residual, whose
interpretation always produces an `extensionError`.
-/
theorem partial_evaluate_policy_is_sound
  {schema : Schema}
  {residual : Residual}
  {policy : Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities} :
  evaluatePolicy schema policy preq pes = .ok residual   →
  isValidAndConsistent schema req es preq pes = .ok () →
  (Spec.evaluate policy.toExpr req es).toOption = (Residual.evaluate residual req es).toOption
:= by
  intro h₁ h₂
  have h₃ := consistent_checks_ensure_refinement h₂
  simp [evaluatePolicy] at h₁
  split at h₁ <;> try cases h₁
  split at h₁ <;> try cases h₁
  simp [do_ok_eq_ok] at h₁
  rcases h₁ with ⟨_, ⟨_, h₁₁⟩, h₁₂⟩
  simp [Except.mapError] at h₁₁
  split at h₁₁ <;> try cases h₁₁
  rename_i env heq₁ _ ty _ _ heq₂
  simp [isValidAndConsistent] at h₂
  split at h₂ <;> try cases h₂
  rename_i heq₃
  simp [heq₁] at heq₃
  subst heq₃
  have ⟨h₂₁, h₂₂⟩ := do_eq_ok₂ h₂
  simp only [isValidAndConsistent.requestIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_true, decide_eq_true_eq] at h₂₁
  split at h₂₁ <;> try cases h₂₁
  rename_i heq₃
  simp only [not_or, Bool.not_eq_false] at heq₃
  rcases heq₃ with ⟨_, heq₃⟩
  simp only [isValidAndConsistent.entitiesIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h₂₂
  split at h₂₂ <;> try cases h₂₂
  rename_i heq₄
  simp only [not_or, Bool.not_eq_false] at heq₄
  rcases heq₄ with ⟨_, heq₄⟩
  simp [Except.isOk, Except.toBool] at heq₄
  split at heq₄ <;> cases heq₄
  rename_i heq₄
  simp only [bind, Except.bind, isValidAndConsistent.envIsWellFormed, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h₂₂
  split at h₂₂ <;> try cases h₂₂
  simp only [ite_eq_right_iff, reduceCtorEq, imp_false, Bool.not_eq_false] at h₂₂
  have heq₅ := h₂₂
  simp [Except.isOk, Except.toBool] at heq₅
  split at heq₅ <;> cases heq₅
  rename_i heq₅
  have h₄ := instance_of_well_formed_env heq₅ heq₃ heq₄
  have h₅ := typechecked_is_well_typed_after_lifting heq₂
  have h₆ := partial_evaluate_is_sound h₅ h₄ h₃
  subst h₁₂
  have h₇ := type_of_preserves_evaluation_results (empty_capabilities_invariant req es) h₄ heq₂
  have h₈ : Spec.evaluate (substituteAction env.reqty.action policy.toExpr) req es = Spec.evaluate policy.toExpr req es := by
    simp [InstanceOfWellFormedEnvironment] at h₄
    rcases h₄ with ⟨_, h₄, _⟩
    simp [InstanceOfRequestType] at h₄
    rcases h₄ with ⟨_, h₄, _⟩
    rw [←h₄]
    exact substitute_action_preserves_evaluation policy.toExpr req es
  simp [h₈] at h₇
  rw [h₇, type_lifting_preserves_expr]
  exact h₆
end Cedar.Thm

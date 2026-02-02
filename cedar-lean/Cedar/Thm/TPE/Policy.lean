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
import Cedar.TPE.Authorizer
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Conversion
import Cedar.Thm.TPE.Soundness
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.Authorization

namespace Cedar.Thm

open Cedar.Data
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem isValidAndConsistent_implies_InstanceOfWellFormedEnvironment
  {schema : Schema}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities} :
  isValidAndConsistent schema req es preq pes = .ok () →
  ∃ env, schema.environment? preq.principal.ty preq.resource.ty preq.action = some env ∧
        InstanceOfWellFormedEnvironment req es env
:= by
  intro hvalid
  simp only [isValidAndConsistent] at hvalid
  split at hvalid <;> try contradiction
  rename_i env henv
  have ⟨hvalid₁, hvalid₂⟩ := do_eq_ok₂ hvalid
  replace ⟨hvalid₂, hvalid₃⟩ := do_eq_ok₂ hvalid₂

  have hreq : requestMatchesEnvironment env req = true := by
    simp only [isValidAndConsistent.requestIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hvalid₁
    split at hvalid₁ <;> try contradiction
    clear hvalid₁ ; rename_i hvalid₁
    simp only [not_or, Bool.not_eq_false] at hvalid₁
    exact hvalid₁.right

  have hent : entitiesMatchEnvironment env es = .ok () := by
    simp only [isValidAndConsistent.entitiesIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hvalid₂
    split at hvalid₂ <;> try contradiction
    rename_i hvalid₃
    simp only [Except.isOk, Except.toBool, not_or, Bool.not_eq_false] at hvalid₃
    replace hvalid₃ := hvalid₃.right
    split at hvalid₃ <;> trivial

  have hwf : env.validateWellFormed = .ok () := by
    simp only [isValidAndConsistent.envIsWellFormed, Bool.not_eq_eq_eq_not, Bool.not_true] at hvalid₃
    split at hvalid₃ <;> try contradiction
    clear hvalid₃; rename_i hvalid₃
    simp only [Except.isOk, Except.toBool, Bool.not_eq_false] at hvalid₃
    split at hvalid₃ <;> trivial

  exists env
  exact .intro henv (instance_of_well_formed_env hwf hreq hent)

/-- Policy evaluation soundness for TPE: Evaluating a result residual is equivalent to
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
  intro heval hvalid
  have hvalid' := consistent_checks_ensure_refinement hvalid

  obtain ⟨env, tx, _, henv, htx, rfl⟩ : ∃ env ty c,
    schema.environment? preq.principal.ty preq.resource.ty preq.action = some env ∧
    typeOf (substituteAction env.reqty.action policy.toExpr) [] env = Except.ok (ty, c) ∧
    TPE.evaluate ty.liftBoolTypes.toResidual preq pes = residual
  := by
    simp only [evaluatePolicy] at heval
    split at heval <;> try contradiction
    rename_i henv
    split at heval <;> try contradiction
    simp only [List.empty_eq, do_ok_eq_ok, Prod.exists, exists_and_right] at heval
    rcases heval with ⟨_, ⟨_, heval₁⟩, heval₂⟩
    simp only [Except.mapError] at heval₁
    split at heval₁ <;> try contradiction
    cases heval₁
    rename_i hty
    simp [henv, hty, heval₂]

  have ⟨env', henv', h₄⟩ := isValidAndConsistent_implies_InstanceOfWellFormedEnvironment hvalid
  obtain rfl : env = env' := by
    simpa [henv] using henv'

  have htx' : Residual.WellTyped env (TypedExpr.toResidual tx.liftBoolTypes) :=
    conversion_preserves_typedness ∘ typechecked_is_well_typed_after_lifting $ htx
  have h₆ := partial_evaluate_is_sound htx' h₄ hvalid'
  have h₇ := type_of_preserves_evaluation_results (empty_capabilities_invariant req es) h₄ htx
  have h₈ : Spec.evaluate (substituteAction env.reqty.action policy.toExpr) req es = Spec.evaluate policy.toExpr req es := by
    simp [InstanceOfWellFormedEnvironment] at h₄
    rcases h₄ with ⟨_, h₄, _⟩
    simp [InstanceOfRequestType] at h₄
    rcases h₄ with ⟨_, h₄, _⟩
    rw [←h₄]
    exact substitute_action_preserves_evaluation policy.toExpr req es
  simp [h₈] at h₇
  rw [h₇, ←h₆, type_lifting_preserves_expr]
  simp [conversion_preserves_evaluation]

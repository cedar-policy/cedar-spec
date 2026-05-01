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
  {pes : PartialEntities}
  {env : TypeEnv} :
  evaluatePolicy schema policy preq pes = .ok residual →
  schema.environment? preq.principal.ty preq.resource.ty preq.action = .some env →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  (Spec.evaluate policy.toExpr req es).toOption = (Residual.evaluate residual req es).toOption
:= by
  intro h₁ h_schema_env h₄ h₃
  simp [evaluatePolicy, h_schema_env] at h₁
  split at h₁ <;> try cases h₁
  cases hcheck : Except.mapError Error.invalidPolicy (checkEntities schema policy.toExpr) <;>
    simp only [hcheck, Except.bind_err, reduceCtorEq] at h₁
  simp [do_ok_eq_ok] at h₁
  rcases h₁ with ⟨_, ⟨_, h₁₁⟩, h₁₂⟩
  simp [Except.mapError] at h₁₁
  split at h₁₁ <;> try cases h₁₁
  rename_i ty _ _ heq₂
  have h₅ := typechecked_is_well_typed_after_lifting heq₂
  have h₉ : Residual.WellTyped env (TypedExpr.toResidual ty.liftBoolTypes) :=
    conversion_preserves_typedness h₅
  have h₆ := partial_evaluate_is_sound h₉ h₄ h₃
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
  rw [h₇, type_lifting_preserves_expr, ← h₆]
  congr
  apply conversion_preserves_evaluation

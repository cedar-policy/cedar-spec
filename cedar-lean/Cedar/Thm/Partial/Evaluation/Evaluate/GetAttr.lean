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

import Cedar.Partial.Evaluator
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.LT
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.EvaluateGetAttr
import Cedar.Thm.Partial.Evaluation.EvaluateValue
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Evaluate.GetAttr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error Expr Result)

/--
  Inductive argument that, for an `Expr.getAttr` with concrete request/entities,
  partial evaluation and concrete evaluation give the same output
-/
theorem on_concrete_eqv_concrete_eval {x₁ : Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval (Expr.getAttr x₁ attr) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp only [ih₁]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case error e => simp only [Except.map, Except.bind_err]
  case ok v₁ => exact EvaluateGetAttr.on_concrete_eqv_concrete

/--
  Inductive argument that if partial-evaluating an `Expr.getAttr` on
  a well-formed value and well-formed entities returns `ok` with some value,
  that is a well-formed value as well
-/
theorem partial_eval_wf {x₁ : Expr} {attr : Attr} {entities : Partial.Entities} {request : Partial.Request}
  (ih₁ : EvaluatesToWellFormed x₁ request entities)
  (ih₂ : ∀ {pval pval' : Partial.Value}, pval.WellFormed → Partial.evaluateValue pval entities = .ok pval' → pval'.WellFormed)
  (wf_e : entities.WellFormed) :
  EvaluatesToWellFormed (Expr.getAttr x₁ attr) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  cases hx₁ : Partial.evaluate x₁ request entities <;> simp [hx₁]
  case ok pval₁ => exact EvaluateGetAttr.evaluateGetAttr_wf (ih₁ pval₁ hx₁) wf_e ih₂

/--
  Inductive argument that if partial-evaluation of an `Expr.getAttr`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns

  This takes the proof of `Evaluate.partial_eval_wf` as an argument, because this
  file can't directly import `Thm/Partial/Evaluation/Evaluate.lean` to get it.
  See #372.
-/
theorem subst_preserves_evaluation_to_value {x₁ : Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (h_pewf : ∀ x r es pv, r.WellFormed → es.WellFormed → Partial.evaluate x r es = .ok pv → pv.WellFormed) :
  SubstPreservesEvaluationToConcrete (Expr.getAttr x₁ attr) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate
  intro h_req v
  specialize ih₁ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, false_implies, implies_true, Except.ok.injEq] at ih₁
  <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
  case ok pv₁  =>
    cases pv₁
    case residual r₁ => simp [Partial.evaluateGetAttr]
    case value v₁ =>
      simp only [Partial.Value.value.injEq, forall_eq'] at *
      simp only [ih₁, Except.bind_ok]
      apply EvaluateGetAttr.subst_preserves_evaluation_to_value _ wf_e wf_s
      intro v v' pv wf_v h₁
      apply EvaluateValue.subst_preserves_evaluation_to_value subsmap (EvaluateGetAttr.getAttr_wf wf_v wf_e _ h₁)
      exact h_pewf _ _ _ (.value v₁) (Subst.req_subst_preserves_wf wf_r wf_s h_req) (Subst.entities_subst_preserves_wf wf_e wf_s) ih₁

/--
  Inductive argument that if partial-evaluation of an `Expr.getAttr`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation/Evaluate.lean` to access it.
  See #372.

  The proof of `partial_eval_wf` for `x₁` is passed in as an argument, because
  this file can't import `Thm/Partial/Evaluation/Evaluate.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {x₁ : Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (h_pewf : ∀ pv, Partial.evaluate x₁ req entities = .ok pv → pv.WellFormed)
  (ih₁ : SubstPreservesEvaluationToError x₁ req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.getAttr x₁ attr) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  unfold Partial.evaluate
  intro h_req ; specialize ih₁ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, false_implies, implies_true, Except.error.injEq] at ih₁
  case error e₁ =>
    replace ⟨e₁', ih₁⟩ := ih₁ e₁ rfl
    simp [ih₁]
  case ok pval₁ =>
    simp only [Except.bind_ok]
    specialize h_pewf pval₁ hx₁
    intro e₁ h₁
    cases hx₁' : Partial.evaluate x₁ req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok pval₁' =>
      simp only [Except.bind_ok]
      cases pval₁
      case residual r₁ => simp [Partial.evaluateGetAttr] at h₁
      case value v₁ =>
        simp only [h_spetv x₁ h_req v₁ hx₁, Except.ok.injEq] at hx₁' ; subst pval₁'
        apply EvaluateGetAttr.subst_preserves_errors h_pewf wf_e wf_s _ h₁
        intro v pv wf_v h₂
        apply EvaluateValue.subst_preserves_errors _ wf_e wf_s
        exact EvaluateGetAttr.getAttr_wf wf_v wf_e _ h₂


end Cedar.Thm.Partial.Evaluation.Evaluate.GetAttr

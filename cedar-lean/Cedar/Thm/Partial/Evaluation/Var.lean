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
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.Var

open Cedar.Data
open Cedar.Spec (Var)

/--
  `Partial.evaluateVar` on concrete arguments gives the same output as
  `Spec.evaluate` on those arguments
-/
theorem partialEvaluateVar_on_concrete_eqv_concrete_eval (v : Var) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  Partial.evaluateVar v request = (Spec.evaluate (Spec.Expr.var v) request entities).map Partial.Value.value
:= by
  unfold Partial.evaluateVar Spec.evaluate
  unfold Spec.Request.WellFormed at wf
  cases v <;> simp only [Spec.Request.asPartialRequest, Except.map]
  case context =>
    split
    case h_1 m h₁ =>
      simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
      rw [← Map.eq_iff_kvs_equiv (wf₁ := Map.mapMOnValues_wf (Map.mapOnValues_wf.mp wf) h₁) (wf₂ := wf)]
      simp only [List.Equiv, List.subset_def]
      constructor
      case left =>
        intro (k, v) h₂
        rw [Map.mapOnValues_eq_make_map _ wf] at h₁
        unfold Map.toList at h₁
        replace ⟨pv, h₁, h₃⟩ := Map.mapMOnValues_some_implies_all_from_some h₁ (k, v) h₂
        replace h₁ := Map.make_mem_list_mem h₁
        cases pv <;> simp only [Option.some.injEq] at h₃
        case value v =>
          subst v
          rw [List.mem_map] at h₁
          replace ⟨(k', v'), h₁, h₃⟩ := h₁
          simp only [Prod.mk.injEq, Partial.Value.value.injEq] at h₃
          replace ⟨h₃, h₃'⟩ := h₃
          subst k' v'
          exact h₁
      case right =>
        intro (k, v) h₂
        have ⟨v', h₃, h₄⟩ := Map.mapMOnValues_some_implies_all_some h₁ (k, v) (Map.in_kvs_in_mapOnValues h₂)
        simp only [Option.some.injEq] at h₄
        subst h₄
        simp [h₃]
    case h_2 h₁ =>
      exfalso
      replace ⟨v, h₁, h₂⟩ := Map.mapMOnValues_none_iff_exists_none.mp h₁
      cases v <;> simp only at h₂
      case residual r =>
        rw [Map.mapOnValues_eq_make_map _ wf] at h₁
        replace h₁ := Map.mem_values_make h₁
        simp [List.mem_map] at h₁

/--
  Partial-evaluating a concrete `Var` expression gives the same output as
  concrete-evaluating the `Var`
-/
theorem on_concrete_eqv_concrete_eval (v : Var) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  PartialEvalEquivConcreteEval (Spec.Expr.var v) request entities
:= by
  unfold PartialEvalEquivConcreteEval Spec.Expr.asPartialExpr Partial.evaluate
  exact partialEvaluateVar_on_concrete_eqv_concrete_eval v request entities wf

end Cedar.Thm.Partial.Evaluation.Var

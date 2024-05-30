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
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.WellFormed
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.HasAttr

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Attr Error Prim Result)

/--
  `Partial.attrsOf` on concrete arguments is the same as `Spec.attrsOf` on those
  arguments

  Note that the "concrete arguments" provided to `Partial.attrsOf` and
  `Spec.attrsOf` in this theorem are different from the "concrete arguments"
  provided in the theorem of the same name in Partial/Evaluation/GetAttr.lean
-/
theorem attrsOf_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (λ uid => .ok (entities.asPartialEntities.attrsOrEmpty uid)) =
  (Spec.attrsOf v (λ uid => .ok (entities.attrsOrEmpty uid))).map λ m => m.mapOnValues Partial.Value.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp only
  case prim p =>
    cases p <;> simp only
    case entityUID uid =>
      unfold Partial.Entities.attrsOrEmpty Spec.Entities.attrsOrEmpty Spec.Entities.asPartialEntities
      cases h₁ : (entities.mapOnValues Spec.EntityData.asPartialEntityData).find? uid
      <;> simp only [Except.ok.injEq]
      <;> cases h₂ : entities.find? uid <;> simp only
      <;> unfold Spec.EntityData.asPartialEntityData at h₁
      <;> simp only [← Map.find?_mapOnValues, Option.map_eq_none', Option.map_eq_some'] at h₁
      case none.none => simp [Map.mapOnValues_empty]
      case none.some => simp [h₁] at h₂
      case some.none => simp [h₂] at h₁
      case some.some edata₁ edata₂ =>
        replace ⟨edata₁, ⟨h₁, h₃⟩⟩ := h₁
        simp only [h₂, Option.some.injEq] at h₁
        subst h₁ h₃
        simp [Map.mapOnValues]

/--
  `Partial.hasAttr` on concrete arguments is the same as `Spec.hasAttr` on those
  arguments
-/
theorem hasAttr_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.hasAttr v attr entities = Spec.hasAttr v attr entities
:= by
  unfold Partial.hasAttr Spec.hasAttr
  simp only [attrsOf_on_concrete_eqv_concrete, Except.map]
  cases Spec.attrsOf v λ uid => .ok (entities.attrsOrEmpty uid)
  <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
  case ok m => simp [← Map.mapOnValues_contains]

/--
  `Partial.evaluateHasAttr` on concrete arguments is the same as `Spec.hasAttr`
  on those arguments
-/
theorem evaluateHasAttr_on_concrete_eqv_concrete {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateHasAttr v a entities = Spec.hasAttr v a entities
:= by
  simp [Partial.evaluateHasAttr, hasAttr_on_concrete_eqv_concrete, pure, Except.pure]

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.hasAttr`
  expression gives the same output as concrete-evaluating the
  `Spec.Expr.hasAttr` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.hasAttr x₁ attr) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case error e => simp only [Except.map, Except.bind_err]
  case ok v₁ => exact evaluateHasAttr_on_concrete_eqv_concrete

/--
  if `Partial.hasAttr` returns `ok` with some value, that is a well-formed value
-/
theorem partialHasAttr_wf {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} :
  ∀ v, Partial.hasAttr v₁ attr entities = .ok v → v.WellFormed
:= by
  unfold Partial.hasAttr
  cases Partial.attrsOf v₁ λ uid => .ok (entities.attrsOrEmpty uid) <;> simp
  case ok m => simp [Spec.Value.WellFormed, Prim.WellFormed]


/--
  if `Partial.evaluateHasAttr` returns `ok` with some value, that is a
  well-formed value
-/
theorem partialEvaluateHasAttr_wf {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} :
  ∀ pval, Partial.evaluateHasAttr pval₁ attr entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateHasAttr
  split
  · rename_i v
    cases h₁ : Partial.hasAttr v attr entities <;> simp
    case ok v =>
      simp [Partial.Value.WellFormed]
      exact partialHasAttr_wf v h₁
  · intro pval h₁ ; simp at h₁ ; subst h₁ ; simp [Partial.Value.WellFormed]

/--
  if partial-evaluating a `Partial.Expr.hasAttr` returns `ok` with some value,
  that is a well-formed value
-/
theorem partial_eval_wf {x₁ : Partial.Expr} {attr : Attr} {entities : Partial.Entities} {request : Partial.Request} :
  EvaluatesToWellFormed (Partial.Expr.hasAttr x₁ attr) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  cases hx₁ : Partial.evaluate x₁ request entities <;> simp [hx₁]
  case ok pval₁ =>
    exact HasAttr.partialEvaluateHasAttr_wf

/--
  If `Partial.evaluateHasAttr` produces `ok` with a concrete value, then so
  would partial-evaluating its operand
-/
theorem evaluateHasAttr_returns_concrete_then_operand_evals_to_concrete {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} :
  Partial.evaluateHasAttr pval₁ attr entities = .ok (.value v) →
  ∃ v₁, pval₁ = .value v₁
:= by
  unfold Partial.evaluateHasAttr
  intro h₁
  cases pval₁
  case value v₁ => exists v₁
  case residual r₁ => simp only [Except.ok.injEq] at h₁

/--
  If partial-evaluating a `Partial.Expr.hasAttr` produces `ok` with a concrete
  value, then so would partial-evaluating its operand
-/
theorem evals_to_concrete_then_operand_evals_to_concrete {x₁ : Partial.Expr} {attr : Attr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.hasAttr x₁ attr) request entities →
  EvaluatesToConcrete x₁ request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> simp only [hx₁, Except.bind_ok, Except.bind_err] at h₁
  case ok pval₁ =>
    have ⟨v₁, hv₁⟩ := evaluateHasAttr_returns_concrete_then_operand_evals_to_concrete h₁
    subst pval₁
    exists v₁

/--
  The return value of `Partial.hasAttr` is not affected by substitution of
  unknowns in `entities`
-/
theorem hasAttr_subst_const {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (wf : entities.AllWellFormed) :
  Partial.hasAttr v₁ attr entities = Partial.hasAttr v₁ attr (entities.subst subsmap)
:= by
  unfold Partial.hasAttr Partial.attrsOf
  cases v₁ <;> simp only [Except.bind_ok, Except.bind_err]
  case prim p₁ =>
    cases p₁
    <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
    case entityUID uid =>
      exact Subst.entities_subst_preserves_contains_on_attrsOrEmpty entities uid attr subsmap wf

/--
  If `Partial.evaluateHasAttr` returns a concrete value, then it returns the
  same value after any substitution of unknowns in `entities`
-/
theorem evaluateHasAttr_subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (wf : entities.AllWellFormed) :
  Partial.evaluateHasAttr pval₁ attr entities = .ok (.value v) →
  Partial.evaluateHasAttr pval₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateHasAttr
  cases pval₁ <;> simp only [Except.ok.injEq, imp_self]
  case value v₁ => simp only [← hasAttr_subst_const wf, imp_self]

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.hasAttr`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ : Partial.Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (wf : entities.AllWellFormed)
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.hasAttr x₁ attr) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate Spec.Value.asBool
  intro h_req v
  specialize ih₁ h_req
  unfold Partial.Expr.subst
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, false_implies, forall_const, Except.bind_err, Except.bind_ok, Except.ok.injEq] at *
  case ok pval₁  =>
    cases pval₁
    case value v₁ =>
      simp only [Partial.Value.value.injEq, forall_eq'] at *
      simp only [ih₁, Except.bind_ok]
      exact evaluateHasAttr_subst_preserves_evaluation_to_value wf
    case residual r₁ => simp only [Partial.evaluateHasAttr, Except.ok.injEq, false_implies]

end Cedar.Thm.Partial.Evaluation.HasAttr

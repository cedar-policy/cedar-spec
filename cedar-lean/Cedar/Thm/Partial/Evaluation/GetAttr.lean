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
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.WellFormed
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.GetAttr

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Attr EntityUID Error Result)

/--
  if `entities.attrs uid` is `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem partialEntities_attrs_wf {entities : Partial.Entities} {uid : EntityUID} {attrs: Map String Partial.Value} :
  entities.AllWellFormed →
  entities.attrs uid = .ok attrs →
  attrs.WellFormed
:= by
  unfold Partial.Entities.attrs Partial.Entities.AllWellFormed Partial.EntityData.WellFormed
  intro wf h₁
  cases h₂ : entities.findOrErr uid Error.entityDoesNotExist
  <;> simp only [h₂, Except.bind_err, Except.bind_ok, Except.ok.injEq] at h₁
  case ok attrs =>
    subst h₁
    have ⟨wf_m, wf_edata⟩ := wf ; clear wf
    apply (wf_edata _ _).left
    have h₃ := Map.in_values_iff_findOrErr_ok (v := attrs) (e := Error.entityDoesNotExist) wf_m
    simp only [h₃]
    exists uid

/--
  if `Partial.attrsOf` returns `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem attrsOf_wf {entities : Partial.Entities} {v : Spec.Value} {attrs : Map String Partial.Value} :
  entities.AllWellFormed →
  v.WellFormed →
  Partial.attrsOf v entities.attrs = .ok attrs →
  attrs.WellFormed
:= by
  intro wf_e wf_v
  unfold Partial.attrsOf
  cases v <;> try simp only [false_implies, Except.ok.injEq]
  case prim p =>
    cases p <;> simp only [false_implies]
    case entityUID uid => exact partialEntities_attrs_wf wf_e
  case record r =>
    intro h₁
    subst h₁
    apply Map.mapOnValues_wf.mp wf_v

/--
  `Partial.attrsOf` on concrete arguments is the same as `Spec.attrsOf` on those
  arguments
-/
theorem attrsOf_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (Partial.Entities.attrs entities) = (Spec.attrsOf v (Spec.Entities.attrs entities)).map λ m => m.mapOnValues Partial.Value.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp only
  case prim p =>
    cases p <;> simp only
    case entityUID uid =>
      unfold Partial.Entities.attrs Spec.Entities.attrs Spec.Entities.asPartialEntities
      cases h₁ : entities.findOrErr uid Error.entityDoesNotExist
      <;> simp only [h₁, Map.findOrErr_mapOnValues, Except.map, Spec.EntityData.asPartialEntityData,
        Except.bind_ok, Except.bind_err]

/--
  `Partial.getAttr` on concrete arguments is the same as `Spec.getAttr` on those
  arguments
-/
theorem getAttr_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.getAttr v attr entities = (Spec.getAttr v attr entities).map Partial.Value.value
:= by
  unfold Partial.getAttr Spec.getAttr
  simp only [attrsOf_on_concrete_eqv_concrete, Except.map]
  cases Spec.attrsOf v entities.attrs <;> simp only [Except.bind_err, Except.bind_ok]
  case ok m => simp only [Map.findOrErr_mapOnValues, Except.map]

/--
  `Partial.evaluateGetAttr` on concrete arguments is the same as `Spec.getAttr`
  on those arguments
-/
theorem evaluateGetAttr_on_concrete_eqv_concrete {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateGetAttr v a entities = Spec.getAttr v a entities
:= by
  simp only [Partial.evaluateGetAttr, getAttr_on_concrete_eqv_concrete, pure, Except.pure, Except.map]
  cases Spec.getAttr v a entities <;> simp only [Except.bind_ok, Except.bind_err]

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.getAttr`
  expression gives the same output as concrete-evaluating the
  `Spec.Expr.getAttr` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.getAttr x₁ attr) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case error e => simp only [Except.map, Except.bind_err]
  case ok v₁ => exact evaluateGetAttr_on_concrete_eqv_concrete

/--
  If `Partial.evaluateGetAttr` produces `ok` with a concrete value, then so
  would partial-evaluating its operand
-/
theorem evaluateGetAttr_returns_concrete_then_operand_evals_to_concrete {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} :
  Partial.evaluateGetAttr pval₁ attr entities = .ok (.value v) →
  ∃ v₁, pval₁ = .value v₁
:= by
  unfold Partial.evaluateGetAttr
  intro h₁
  cases pval₁
  case value v₁ => exists v₁
  case residual r₁ => simp only [Except.ok.injEq] at h₁

/--
  If partial-evaluating a `Partial.Expr.getAttr` produces `ok` with a concrete
  value, then so would partial-evaluating its operand
-/
theorem evals_to_concrete_then_operand_evals_to_concrete {x₁ : Partial.Expr} {attr : Attr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.getAttr x₁ attr) request entities →
  EvaluatesToConcrete x₁ request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> simp only [hx₁, Except.bind_ok, Except.bind_err] at h₁
  case ok pval₁ =>
    have ⟨v₁, hv₁⟩ := evaluateGetAttr_returns_concrete_then_operand_evals_to_concrete h₁
    subst pval₁
    exists v₁

/--
  If `Partial.getAttr` returns a concrete value, then it returns the same value
  after any substitution of unknowns in `entities`
-/
theorem getAttr_subst_preserves_evaluation_to_value {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (wf : entities.AllWellFormed) :
  Partial.getAttr v₁ attr entities = .ok (.value v) →
  Partial.getAttr v₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.getAttr
  unfold Partial.attrsOf
  cases v₁
  case prim p₁ =>
    cases p₁ <;> simp only [Except.bind_err, imp_self]
    case entityUID uid₁ =>
      cases h₁ : entities.attrs uid₁
      <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
      case ok attrs =>
        intro h₂
        replace h₂ := Map.findOrErr_ok_iff_find?_some.mp h₂
        replace h₂ := Map.find?_mem_toList h₂
        unfold Map.toList at h₂
        have ⟨attrs', h₃, h₄⟩ := Partial.Subst.entities_subst_preserves_concrete_attrs subsmap h₁ h₂
        simp only [h₃, Except.bind_ok]
        simp only [Map.findOrErr_ok_iff_find?_some]
        apply (Map.in_list_iff_find?_some _).mp h₄
        have wf' := Partial.Subst.entities_subst_preserves_wf subsmap wf
        exact partialEntities_attrs_wf wf' h₃
  case set | record => simp
  case ext x => cases x <;> simp

/--
  If `Partial.evaluateGetAttr` returns a concrete value, then it returns the
  same value after any substitution of unknowns in `entities`
-/
theorem evaluateGetAttr_subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (wf : entities.AllWellFormed) :
  Partial.evaluateGetAttr pval₁ attr entities = .ok (.value v) →
  Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.ok.injEq, imp_self]
  case value v₁ => exact getAttr_subst_preserves_evaluation_to_value wf

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.getAttr`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ : Partial.Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (wf : entities.AllWellFormed)
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.getAttr x₁ attr) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate Spec.Value.asBool
  intro h_req v
  specialize ih₁ h_req
  unfold Partial.Expr.subst
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, false_implies, forall_const, Except.bind_ok, Except.bind_err, Except.ok.injEq] at *
  case ok pval₁  =>
    cases pval₁
    case value v₁ =>
      simp only [Partial.Value.value.injEq, forall_eq'] at *
      simp only [ih₁, Except.bind_ok]
      exact evaluateGetAttr_subst_preserves_evaluation_to_value wf
    case residual r₁ => simp only [Partial.evaluateGetAttr, Except.ok.injEq, false_implies]

end Cedar.Thm.Partial.Evaluation.GetAttr

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
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error Expr Result)

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
  case ok v₁ => exact evaluateGetAttr_on_concrete_eqv_concrete

/--
  if `entities.attrs uid` is `ok` with some attrs, those attrs are a
  well-formed `Map`, and all the values in those attrs are well-formed
-/
theorem partialEntities_attrs_wf {entities : Partial.Entities} {uid : EntityUID} {attrs: Map String Partial.Value}
  (wf_e : entities.WellFormed) :
  entities.attrs uid = .ok attrs →
  attrs.WellFormed ∧ ∀ v ∈ attrs.values, v.WellFormed
:= by
  unfold Partial.Entities.attrs
  intro h₁
  cases h₂ : entities.es.findOrErr uid Error.entityDoesNotExist
  <;> simp only [h₂, Except.bind_err, Except.bind_ok, Except.ok.injEq] at h₁
  case ok attrs =>
    subst h₁
    unfold Partial.Entities.WellFormed Partial.EntityData.WellFormed at wf_e
    have ⟨wf_m, wf_edata⟩ := wf_e ; clear wf_e
    constructor
    · apply (wf_edata _ _).left
      simp only [← Map.findOrErr_ok_iff_in_values (v := attrs) (e := Error.entityDoesNotExist) wf_m]
      exists uid
    · intro pval h₃
      replace h₂ := Map.findOrErr_ok_implies_in_values h₂
      exact (wf_edata attrs h₂).right.right pval h₃

/--
  if `Partial.attrsOf` returns `ok` with some attrs, those attrs are a
  well-formed `Map`, and all the values in those attrs are well-formed
-/
theorem attrsOf_wf {entities : Partial.Entities} {v : Spec.Value} {attrs : Map String Partial.Value}
  (wf₁ : v.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.attrsOf v entities.attrs = .ok attrs →
  attrs.WellFormed ∧ ∀ v ∈ attrs.values, v.WellFormed
:= by
  unfold Partial.attrsOf
  cases v <;> try simp only [false_implies, Except.ok.injEq]
  case prim p =>
    cases p <;> simp only [false_implies]
    case entityUID uid => exact partialEntities_attrs_wf wf_e
  case record m =>
    intro h₁ ; subst h₁
    unfold Spec.Value.WellFormed at wf₁
    replace ⟨wf₁, wf_vs⟩ := wf₁
    apply And.intro (Map.mapOnValues_wf.mp wf₁)
    intro pval h₁
    have ⟨k, h₁'⟩ := Map.in_values_exists_key h₁
    rw [Map.values_mapOnValues] at h₁
    replace ⟨v, _, h₃⟩ := List.mem_map.mp h₁
    subst h₃
    simp [Partial.Value.WellFormed]
    apply wf_vs (k, v)
    exact Map.in_mapOnValues_in_kvs wf₁ h₁' (by simp)

/--
  if `Partial.getAttr` on a well-formed value and well-formed entities returns
  `ok` with some value, that is a well-formed value as well
-/
theorem getAttr_wf {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities}
  (wf₁ : v₁.WellFormed)
  (wf_e : entities.WellFormed) :
  ∀ v, Partial.getAttr v₁ attr entities = .ok v → v.WellFormed
:= by
  unfold Partial.getAttr
  cases h₁ : Partial.attrsOf v₁ entities.attrs <;> simp
  case ok attrs =>
    have ⟨_, wf_vs⟩ := attrsOf_wf wf₁ wf_e h₁
    intro pval h₂
    exact wf_vs pval (Map.findOrErr_ok_implies_in_values h₂)

/--
  if `Partial.evaluateGetAttr` on a well-formed value and well-formed entities
  returns `ok` with some value, that is a well-formed value as well
-/
theorem evaluateGetAttr_wf {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities}
  (wf₁ : pval₁.WellFormed)
  (wf_e : entities.WellFormed) :
  ∀ pval, Partial.evaluateGetAttr pval₁ attr entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.ok.injEq, forall_eq']
  case residual r₁ => simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
  case value v₁ =>
    simp [Partial.Value.WellFormed] at wf₁
    exact getAttr_wf wf₁ wf_e

/--
  Inductive argument that if partial-evaluating an `Expr.getAttr` on
  a well-formed value and well-formed entities returns `ok` with some value,
  that is a well-formed value as well
-/
theorem partial_eval_wf {x₁ : Expr} {attr : Attr} {entities : Partial.Entities} {request : Partial.Request}
  (ih₁ : EvaluatesToWellFormed x₁ request entities)
  (wf_e : entities.WellFormed) :
  EvaluatesToWellFormed (Expr.getAttr x₁ attr) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  cases hx₁ : Partial.evaluate x₁ request entities <;> simp [hx₁]
  case ok pval₁ => exact evaluateGetAttr_wf (ih₁ pval₁ hx₁) wf_e

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
  If partial-evaluating an `Expr.getAttr` produces `ok` with a concrete
  value, then so would partial-evaluating its operand
-/
theorem evals_to_concrete_then_operand_evals_to_concrete {x₁ : Expr} {attr : Attr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Expr.getAttr x₁ attr) request entities →
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
theorem getAttr_subst_preserves_evaluation_to_value {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
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
        replace h₂ := Map.findOrErr_ok_implies_in_kvs h₂
        unfold Map.toList at h₂
        have ⟨attrs', h₃, h₄⟩ := Subst.entities_subst_preserves_concrete_attrs subsmap h₁ h₂
        simp only [h₃, Except.bind_ok]
        apply (Map.findOrErr_ok_iff_in_kvs _).mpr h₄
        have wf' := Subst.entities_subst_preserves_wf wf_e wf_s
        exact (partialEntities_attrs_wf wf' h₃).left
  case set | record => simp
  case ext x => cases x <;> simp

/--
  If `Partial.evaluateGetAttr` returns a concrete value, then it returns the
  same value after any substitution of unknowns in `entities`
-/
theorem evaluateGetAttr_subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateGetAttr pval₁ attr entities = .ok (.value v) →
  Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.ok.injEq, imp_self]
  case value v₁ => exact getAttr_subst_preserves_evaluation_to_value wf_e wf_s

/--
  Inductive argument that if partial-evaluation of an `ExprAttr`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ : Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Expr.getAttr x₁ attr) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate
  intro h_req v
  specialize ih₁ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, false_implies, forall_const, Except.bind_ok, Except.bind_err, Except.ok.injEq] at *
  case ok pval₁  =>
    cases pval₁
    case residual r₁ => simp only [Partial.evaluateGetAttr, Except.ok.injEq, false_implies]
    case value v₁ =>
      simp only [Partial.Value.value.injEq, forall_eq'] at *
      simp only [ih₁, Except.bind_ok]
      exact evaluateGetAttr_subst_preserves_evaluation_to_value wf_e wf_s

/--
  If `Partial.getAttr` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns in `entities`
-/
theorem getAttr_subst_preserves_errors {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.getAttr v₁ attr entities = .error e →
  ∃ e', Partial.getAttr v₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.getAttr, Partial.attrsOf]
  exact match v₁ with
  | .prim (.entityUID uid) => match ha : entities.attrs uid with
    | .ok attrs => match ha' : (entities.subst subsmap).attrs uid with
      | .ok attrs' => match e with
        | .attrDoesNotExist => by
          simp only [ha, ha', Except.bind_ok]
          have wf_attrs := partialEntities_attrs_wf wf_e ha
          have wf_attrs' := partialEntities_attrs_wf (Subst.entities_subst_preserves_wf wf_e wf_s) ha'
          intro h₁
          exists .attrDoesNotExist
          simp only [Map.findOrErr_err_iff_not_in_keys (wf_attrs.left)] at h₁
          simp only [Map.findOrErr_err_iff_not_in_keys (wf_attrs'.left)]
          replace ⟨attrs'', ha'', h₁⟩ := Subst.entities_subst_preserves_absent_attrs subsmap ha h₁
          simp [ha'] at ha'' ; subst attrs''
          exact h₁
        | .entityDoesNotExist | .typeError | .arithBoundsError | .extensionError => by
          simp only [ha, ha', Except.bind_ok]
          intro h₁ ; rcases Map.findOrErr_returns attrs attr Error.attrDoesNotExist with h₂ | h₂
          · simp only [h₁, exists_const] at h₂
          · simp only [h₁, Except.error.injEq] at h₂
      | .error e => by
        simp only [ha, ha', Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq',
          implies_true]
    | .error e' => by
      simp only [ha, Except.bind_err, Except.error.injEq]
      intro h ; subst e'
      simp [(Subst.entities_subst_preserves_error_attrs subsmap).mp ha]
  | .record attrs => by
    simp only [Except.bind_ok]
    intro _ ; exists e
  | .prim (.bool _) | .prim (.int _) | .prim (.string _) => by simp
  | .set _ | .ext _ => by simp

/--
  If `Partial.evaluateGetAttr` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns in
  `entities`
-/
theorem evaluateGetAttr_subst_preserves_errors {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateGetAttr pval₁ attr entities = .error e →
  ∃ e', Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.evaluateGetAttr]
  cases pval₁ <;> simp only [exists_false, imp_self]
  case value v₁ => exact getAttr_subst_preserves_errors wf_e wf_s

/--
  Inductive argument that if partial-evaluation of an `Expr.getAttr`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {x₁ : Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
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
    intro e₁ h₁
    cases hx₁' : Partial.evaluate x₁ req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok pval₁' =>
      simp only [Except.bind_ok]
      cases pval₁
      case residual r₁ => exists e₁
      case value v₁ =>
        simp only [h_spetv x₁ h_req v₁ hx₁, Except.ok.injEq] at hx₁' ; subst pval₁'
        exact evaluateGetAttr_subst_preserves_errors subsmap wf_e wf_s h₁


end Cedar.Thm.Partial.Evaluation.GetAttr

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

namespace Cedar.Thm.Partial.Evaluation.Binary

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (BinaryOp EntityUID intOrErr Prim Result)

/--
  `Partial.Entities.ancestorsOrEmpty` on concrete entities is the same as
  `Spec.Entities.ancestorsOrEmpty` on those entities
-/
theorem ancestorsOrEmpty_on_concrete_eqv_concrete {entities : Spec.Entities} {uid : EntityUID} :
  Partial.Entities.ancestorsOrEmpty entities uid = Spec.Entities.ancestorsOrEmpty entities uid
:= by
  unfold Partial.Entities.ancestorsOrEmpty Spec.Entities.ancestorsOrEmpty
  unfold Spec.Entities.asPartialEntities Spec.EntityData.asPartialEntityData
  rw [← Map.find?_mapOnValues]
  cases entities.find? uid <;> simp

/--
  `Partial.inₑ` on concrete arguments is the same as `Spec.inₑ` on those arguments
-/
theorem partialInₑ_on_concrete_eqv_concrete {uid₁ uid₂ : EntityUID} {entities : Spec.Entities} :
  Partial.inₑ uid₁ uid₂ entities = Spec.inₑ uid₁ uid₂ entities
:= by
  unfold Partial.inₑ Spec.inₑ
  cases uid₁ == uid₂ <;> simp only [Bool.true_or, Bool.false_or]
  case false => simp only [ancestorsOrEmpty_on_concrete_eqv_concrete]

/--
  `Partial.inₛ` on concrete arguments is the same as `Spec.inₛ` on those arguments
-/
theorem partialInₛ_on_concrete_eqv_concrete {uid : EntityUID} {vs : Set Spec.Value} {entities : Spec.Entities} :
  Partial.inₛ uid vs entities = Spec.inₛ uid vs entities
:= by
  unfold Partial.inₛ Spec.inₛ
  simp only [partialInₑ_on_concrete_eqv_concrete]

/--
  `Partial.apply₂` on concrete arguments is the same as `Spec.apply₂` on those
  arguments
-/
theorem partialApply₂_on_concrete_eqv_concrete {op : BinaryOp} {v₁ v₂ : Spec.Value} {entities : Spec.Entities} :
  Partial.apply₂ op v₁ v₂ entities = (Spec.apply₂ op v₁ v₂ entities).map Partial.Value.value
:= by
  unfold Partial.apply₂ Spec.apply₂ Except.map
  cases op <;> split <;> rename_i h
  <;> simp only [false_implies, forall_const] at h
  <;> try simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
  case add | sub | mul => split <;> rename_i h <;> simp [h]
  case mem.h_10 uid₁ uid₂ => simp only [partialInₑ_on_concrete_eqv_concrete]
  case mem.h_11 uid vs =>
    simp only [partialInₛ_on_concrete_eqv_concrete]
    cases Spec.inₛ uid vs entities <;> simp only [Except.bind_ok, Except.bind_err]
  case mem.h_12 =>
    split <;> rename_i h₂ <;> split at h₂
    <;> simp only [imp_self, false_implies, implies_true, forall_const, forall_eq',
      Except.error.injEq, Spec.Value.prim.injEq, Spec.Value.set.injEq, Spec.Prim.entityUID.injEq,
      forall_apply_eq_imp_iff] at *
    exact h₂

/--
  `Partial.evaluateBinaryApp` on concrete arguments is the same as `Spec.apply₂` on
  those arguments
-/
theorem evaluateBinaryApp_on_concrete_eqv_concrete {op : BinaryOp} {v₁ v₂ : Spec.Value} {entities : Spec.Entities} :
  Partial.evaluateBinaryApp op v₁ v₂ entities = (Spec.apply₂ op v₁ v₂ entities).map Partial.Value.value
:= by
  simp only [Partial.evaluateBinaryApp, partialApply₂_on_concrete_eqv_concrete]

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.binaryApp`
  expression gives the same output as concrete-evaluating the
  `Spec.Expr.binaryApp` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ x₂ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {op : BinaryOp} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval x₂ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.binaryApp op x₁ x₂) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁ ih₂
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁, ih₂, Except.map]
  cases h₁ : Spec.evaluate x₁ request entities <;> simp only [h₁, Except.bind_err, Except.bind_ok]
  case ok v₁ =>
    cases h₂ : Spec.evaluate x₂ request entities <;> simp only [h₂, Except.bind_err, Except.bind_ok]
    case ok v₂ => simp only [evaluateBinaryApp_on_concrete_eqv_concrete, Except.map]

/--
  if `Partial.inₛ` returns `ok` with some value, that is a well-formed value
-/
theorem partialInₛ_wf {uid : EntityUID} {vs : Set Spec.Value} :
  ∀ pval, Partial.inₛ uid vs entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.inₛ
  intro pval
  cases vs.mapOrErr Spec.Value.asEntityUID Spec.Error.typeError <;> simp
  case ok uids =>
    intro h ; subst h ; simp [Spec.Value.WellFormed, Prim.WellFormed]

/--
  if `Partial.apply₂` on two well-formed values and well-formed entities
  returns `ok` with some value, that is a well-formed value as well
-/
theorem partialApply₂_wf {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities}
  (wf₁ : v₁.WellFormed)
  (wf₂ : v₂.WellFormed) :
  ∀ pval, Partial.apply₂ op v₁ v₂ entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.apply₂
  intro pval
  split <;> intro h₁ <;> try simp at h₁ <;> subst h₁
  all_goals try {
    simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  }
  · rename_i i j
    cases h₂ : intOrErr (i.add? j) <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      unfold intOrErr at h₂
      split at h₂ <;> simp at h₂
      subst h₂
      simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  · rename_i i j
    cases h₂ : intOrErr (i.sub? j) <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      unfold intOrErr at h₂
      split at h₂ <;> simp at h₂
      subst h₂
      simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  · rename_i i j
    cases h₂ : intOrErr (i.mul? j) <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      unfold intOrErr at h₂
      split at h₂ <;> simp at h₂
      subst h₂
      simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  · rename_i uid vs
    cases h₂ : Partial.inₛ uid vs entities <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      simp [Partial.Value.WellFormed]
      exact partialInₛ_wf v h₂

/--
  if `Partial.evaluateBinaryApp` on two well-formed values and well-formed
  entities returns `ok` with some value, that is a well-formed value as well
-/
theorem partialEvaluateBinaryApp_wf {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities}
  (wf₁ : pval₁.WellFormed)
  (wf₂ : pval₂.WellFormed) :
  ∀ pval, Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateBinaryApp
  split
  · rename_i v₁ v₂ h₁
    simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
    simp [Partial.Value.WellFormed] at wf₁ wf₂
    exact partialApply₂_wf wf₁ wf₂
  all_goals {
    intro pval h₁ ; simp at h₁ ; subst h₁
    simp [Partial.Value.WellFormed]
  }

/--
  Inductive argument that if evaluating a `Partial.Expr.binaryApp` on
  well-formed arguments produces `ok` with some value, that is a well-formed
  value as well
-/
theorem partial_eval_wf {x₁ x₂ : Partial.Expr} {op : BinaryOp} {request : Partial.Request} {entities : Partial.Entities}
  (ih₁ : EvaluatesToWellFormed x₁ request entities)
  (ih₂ : EvaluatesToWellFormed x₂ request entities) :
  EvaluatesToWellFormed (Partial.Expr.binaryApp op x₁ x₂) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  intro pval
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> cases hx₂ : Partial.evaluate x₂ request entities
  <;> simp [hx₁, hx₂]
  case ok.ok pval₁ pval₂ =>
    exact partialEvaluateBinaryApp_wf (ih₁ pval₁ hx₁) (ih₂ pval₂ hx₂) pval

/--
  If `Partial.evaluateBinaryApp` produces `ok` with a concrete value, then so
  would partial-evaluating either of the operands
-/
theorem evaluateBinaryApp_returns_concrete_then_operands_eval_to_concrete {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok (.value v) →
  (∃ v₁, pval₁ = .value v₁) ∧ (∃ v₂, pval₂ = .value v₂)
:= by
  unfold Partial.evaluateBinaryApp
  intro h₁
  cases pval₁ <;> cases pval₂
  case value.value v₁ v₂ =>
    exact And.intro (by exists v₁) (by exists v₂)
  all_goals simp only [Except.ok.injEq] at h₁

/--
  If partial-evaluating a `Partial.Expr.binaryApp` produces `ok` with a concrete
  value, then so would partial-evaluating either of the operands
-/
theorem evals_to_concrete_then_operands_eval_to_concrete {x₁ x₂ : Partial.Expr} {op : BinaryOp} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.binaryApp op x₁ x₂) request entities →
  (EvaluatesToConcrete x₁ request entities ∧ EvaluatesToConcrete x₂ request entities)
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> cases hx₂ : Partial.evaluate x₂ request entities
  <;> simp only [hx₁, hx₂, Except.bind_ok, Except.bind_err] at h₁
  case ok.ok pval₁ pval₂ =>
    have ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := evaluateBinaryApp_returns_concrete_then_operands_eval_to_concrete h₁
    subst pval₁ pval₂
    exact And.intro (by exists v₁) (by exists v₂)

/--
  The return value of `Partial.inₑ` is not affected by substitution of unknowns
  in `entities`
-/
theorem partialInₑ_subst_const {uid₁ uid₂ : EntityUID} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.inₑ uid₁ uid₂ entities = Partial.inₑ uid₁ uid₂ (entities.subst subsmap)
:= by
  unfold Partial.inₑ
  cases uid₁ == uid₂ <;> simp only [Bool.false_or, Bool.true_or]
  case false =>
    rw [← Subst.entities_subst_preserves_ancestorsOrEmpty entities uid₁ subsmap]

/--
  The return value of `Partial.inₛ` is not affected by substitution of unknowns
  in `entities`
-/
theorem partialInₛ_subst_const {uid₁ : EntityUID} {s₂ : Set Spec.Value} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.inₛ uid₁ s₂ entities = Partial.inₛ uid₁ s₂ (entities.subst subsmap)
:= by
  unfold Partial.inₛ
  cases s₂.mapOrErr Spec.Value.asEntityUID .typeError
  case error e => simp only [Except.bind_err]
  case ok uids => simp only [← partialInₑ_subst_const, Except.bind_ok]

/--
  If `Partial.apply₂` returns a concrete value, then it returns the same value
  after any substitution of unknowns in `entities`
-/
theorem partialApply₂_subst_preserves_evaluation_to_value {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.apply₂ op v₁ v₂ entities = .ok (.value v) →
  Partial.apply₂ op v₁ v₂ (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.apply₂
  cases op
  case eq => simp only [Except.ok.injEq, Partial.Value.value.injEq, imp_self]
  case mem =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, imp_self]
      case entityUID.entityUID uid₁ uid₂ =>
        rw [← partialInₑ_subst_const]
        simp only [imp_self]
    case prim.set p₁ s₂ =>
      cases p₁ <;> simp only [imp_self]
      case entityUID uid₁ =>
        rw [← partialInₛ_subst_const]
        simp only [imp_self]
    all_goals simp only [Partial.apply₂.match_1.eq_12, imp_self]
  all_goals {
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, imp_self]
    all_goals simp only [Partial.apply₂.match_1.eq_12, imp_self]
  }

/--
  If `Partial.evaluateBinaryApp` returns a concrete value, then it returns
  the same value after any substitution of unknowns in `entities`
-/
theorem evaluateBinaryApp_subst_preserves_evaluation_to_value {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok (.value v) →
  Partial.evaluateBinaryApp op pval₁ pval₂ (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateBinaryApp
  cases pval₁ <;> cases pval₂ <;> simp only [Except.ok.injEq, imp_self]
  case value.value v₁ v₂ => exact partialApply₂_subst_preserves_evaluation_to_value

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.binaryApp`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ : Partial.Expr} {op : BinaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToConcrete x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.binaryApp op x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate Spec.Value.asBool
  intro h_req v
  specialize ih₁ h_req
  specialize ih₂ h_req
  unfold Partial.Expr.subst
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> cases hx₂ : Partial.evaluate x₂ req entities
  <;> simp only [hx₁, hx₂, Except.ok.injEq, false_implies, forall_const,
    Except.bind_err, Except.bind_ok] at *
  case ok.ok pval₁ pval₂ =>
    cases pval₁ <;> cases pval₂
    <;> simp only [Partial.Value.value.injEq, forall_eq', false_implies, forall_const] at *
    case value.value v₁ v₂ =>
      simp only [ih₁, ih₂, Except.bind_ok]
      exact evaluateBinaryApp_subst_preserves_evaluation_to_value
    all_goals simp only [Partial.evaluateBinaryApp, Except.ok.injEq, false_implies]

/--
  If `Partial.apply₂` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns in `entities`
-/
theorem partialApply₂_subst_preserves_errors {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.apply₂ op v₁ v₂ entities = .error e →
  ∃ e', Partial.apply₂ op v₁ v₂ (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.apply₂]
  cases op
  case eq => simp only [exists_false, imp_self]
  case mem =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
    case prim.set p₁ s₂ =>
      cases p₁ <;> simp only [Except.error.injEq, exists_eq', implies_true]
      case entityUID uid₁ =>
        rw [← partialInₛ_subst_const]
        intro _ ; exists e
    all_goals simp only [Partial.apply₂.match_1.eq_12, Except.error.injEq, exists_eq', implies_true]
  case add | sub | mul =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
      case int.int i₁ i₂ => intro _ ; exists e
    all_goals simp only [Partial.apply₂.match_1.eq_12, Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
  all_goals {
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
    all_goals simp only [Partial.apply₂.match_1.eq_12, Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
  }

/--
  If `Partial.evaluateBinaryApp` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns in
  `entities`
-/
theorem evaluateBinaryApp_subst_preserves_errors {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} (subsmap : Subsmap) :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .error e →
  ∃ e', Partial.evaluateBinaryApp op pval₁ pval₂ (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.evaluateBinaryApp]
  cases pval₁ <;> cases pval₂ <;> simp only [exists_false, imp_self]
  case value.value v₁ v₂ => exact partialApply₂_subst_preserves_errors

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.binaryApp`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  Alternately, this entire inductive proof could live in its own set of files,
  all of which could depend on `Thm/Partial/Evaluation.lean` and its theorems
  like `subst_preserves_evaluation_to_value`.
-/
theorem subst_preserves_errors {x₁ x₂ : Partial.Expr} {op : BinaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (ih₁ : SubstPreservesEvaluationToError x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToError x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToError (Partial.Expr.binaryApp op x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  unfold Partial.evaluate Partial.Expr.subst
  intro h_req ; specialize ih₁ h_req ; specialize ih₂ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> cases hx₂ : Partial.evaluate x₂ req entities
  <;> simp only [hx₁, hx₂, false_implies, implies_true, Except.error.injEq] at ih₁ ih₂
  case error.error e₁ e₂ | error.ok e₁ pval₂ =>
    replace ⟨e₁', ih₁⟩ := ih₁ e₁ rfl
    simp [ih₁]
  case ok.error pval₁ e₂ =>
    replace ⟨e₂', ih₂⟩ := ih₂ e₂ rfl
    simp [ih₂]
    cases Partial.evaluate (x₁.subst subsmap) req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok => exists e₂'
  case ok.ok pval₁ pval₂ =>
    simp only [Except.bind_ok]
    intro e h₁
    have ⟨e', h₂⟩ := evaluateBinaryApp_subst_preserves_errors subsmap h₁
    cases hx₁' : Partial.evaluate (x₁.subst subsmap) req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok pval₁' =>
      cases hx₂' : Partial.evaluate (x₂.subst subsmap) req' (entities.subst subsmap)
      case error e₂' => exists e₂'
      case ok pval₂' =>
        simp only [Except.bind_ok]
        cases pval₁ <;> cases pval₂
        case value.value v₁ v₂ =>
          simp only [h_spetv x₁ h_req v₁ hx₁, Except.ok.injEq] at hx₁' ; subst pval₁'
          simp only [h_spetv x₂ h_req v₂ hx₂, Except.ok.injEq] at hx₂' ; subst pval₂'
          exists e'
        case value.residual v₁ r₂ => exists e
        case residual.value r₁ v₂ => exists e'
        case residual.residual r₁ r₂ => exists e

end Cedar.Thm.Partial.Evaluation.Binary

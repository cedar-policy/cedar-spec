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
import Cedar.Thm.Partial.Evaluation.Basic
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.Binary

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (BinaryOp EntityUID intOrErr Result)

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
  case false => simp [ancestorsOrEmpty_on_concrete_eqv_concrete]

/--
  `Partial.inₛ` on concrete arguments is the same as `Spec.inₛ` on those arguments
-/
theorem partialInₛ_on_concrete_eqv_concrete {uid : EntityUID} {vs : Set Spec.Value} {entities : Spec.Entities} :
  Partial.inₛ uid vs entities = Spec.inₛ uid vs entities
:= by
  unfold Partial.inₛ Spec.inₛ
  simp [partialInₑ_on_concrete_eqv_concrete]

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
  case mem.h_10 uid₁ uid₂ => simp [partialInₑ_on_concrete_eqv_concrete]
  case mem.h_11 uid vs =>
    simp only [partialInₛ_on_concrete_eqv_concrete]
    cases Spec.inₛ uid vs entities <;> simp
  case mem.h_12 =>
    split <;> rename_i h₂ <;> split at h₂ <;> simp at *
    assumption

/--
  `Partial.evaluateBinaryApp` on concrete arguments is the same as `Spec.apply₂` on
  those arguments
-/
theorem evaluateBinaryApp_on_concrete_eqv_concrete {op : BinaryOp} {v₁ v₂ : Spec.Value} {entities : Spec.Entities} :
  Partial.evaluateBinaryApp op v₁ v₂ entities = (Spec.apply₂ op v₁ v₂ entities).map Partial.Value.value
:= by
  simp [Partial.evaluateBinaryApp, partialApply₂_on_concrete_eqv_concrete]

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
    case ok v₂ => simp [evaluateBinaryApp_on_concrete_eqv_concrete, Except.map]

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
  case value.residual v₁ r₂ =>
    cases v₁ <;> simp at h₁
  case residual.value r₁ v₂ =>
    cases v₂ <;> simp at h₁
  case residual.residual r₁ r₂ =>
    simp at h₁

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
  <;> simp [hx₁, hx₂] at h₁
  case ok.ok pval₁ pval₂ =>
    have ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := evaluateBinaryApp_returns_concrete_then_operands_eval_to_concrete h₁
    subst pval₁ pval₂
    exact And.intro (by exists v₁) (by exists v₂)

/--
  The return value of `Partial.inₑ` is not affected by substitution of unknowns
  in `entities`
-/
theorem partialInₑ_subst_const {uid₁ uid₂ : EntityUID} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value} :
  Partial.inₑ uid₁ uid₂ entities = Partial.inₑ uid₁ uid₂ (entities.subst subsmap)
:= by
  unfold Partial.inₑ
  cases uid₁ == uid₂ <;> simp
  case false =>
    rw [← Partial.Subst.entities_subst_preserves_ancestorsOrEmpty entities uid₁ subsmap]

/--
  The return value of `Partial.inₛ` is not affected by substitution of unknowns
  in `entities`
-/
theorem partialInₛ_subst_const {uid₁ : EntityUID} {s₂ : Set Spec.Value} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value} :
  Partial.inₛ uid₁ s₂ entities = Partial.inₛ uid₁ s₂ (entities.subst subsmap)
:= by
  unfold Partial.inₛ
  cases s₂.mapOrErr Spec.Value.asEntityUID .typeError <;> simp
  case ok uids => simp [← partialInₑ_subst_const]

/--
  If `Partial.apply₂` returns a concrete value, then it returns the same value
  after any substitution of unknowns in `entities`
-/
theorem partialApply₂_subst_preserves_evaluation_to_value {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value} :
  Partial.apply₂ op v₁ v₂ entities = .ok (.value v) →
  Partial.apply₂ op v₁ v₂ (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.apply₂
  cases op
  case eq => simp
  case mem =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂ <;> simp
      case entityUID.entityUID uid₁ uid₂ =>
        rw [← partialInₑ_subst_const]
        simp
    case prim.set p₁ s₂ =>
      cases p₁ <;> simp
      case entityUID uid₁ =>
        rw [← partialInₛ_subst_const]
        simp
    all_goals simp
  all_goals {
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂ <;> simp
    all_goals simp
  }

/--
  If `Partial.evaluateBinaryApp` returns a concrete value, then it returns
  the same value after any substitution of unknowns in `entities`
-/
theorem evaluateBinaryApp_subst_preserves_evaluation_to_value {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value} :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok (.value v) →
  Partial.evaluateBinaryApp op pval₁ pval₂ (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateBinaryApp
  cases pval₁ <;> cases pval₂ <;> simp
  case value.value v₁ v₂ => exact partialApply₂_subst_preserves_evaluation_to_value

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.binaryApp`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ : Partial.Expr} {op : BinaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
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
  <;> simp [hx₁, hx₂] at *
  case ok.ok pval₁ pval₂ =>
    cases pval₁ <;> cases pval₂ <;> simp at *
    case value.value v₁ v₂ =>
      simp [ih₁, ih₂]
      exact evaluateBinaryApp_subst_preserves_evaluation_to_value
    case value.residual v₁ r₂ => simp [Partial.evaluateBinaryApp]
    case residual.value r₁ v₂ => simp [Partial.evaluateBinaryApp]
    case residual.residual r₁ r₂ => simp [Partial.evaluateBinaryApp]

end Cedar.Thm.Partial.Evaluation.Binary

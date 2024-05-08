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

namespace Cedar.Thm.Partial.Evaluation.Binary

open Cedar.Data
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

end Cedar.Thm.Partial.Evaluation.Binary

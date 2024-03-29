/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec.PartialEvaluator
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.PartialEval.Basic

namespace Cedar.Thm.PartialEval.Binary

open Cedar.Data
open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁ op x₂)
-/
theorem lhs_subexpression {x₁ x₂ x : PartialExpr} {op : BinaryOp} :
  x ∈ x₁.subexpressions → x ∈ (PartialExpr.binaryApp op x₁ x₂).subexpressions
:= by
  intro h₁
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right ; left ; assumption

/--
  helper lemma: any subexpression of x₂ is a subexpression of (x₁ op x₂)
-/
theorem rhs_subexpression {x₁ x₂ x : PartialExpr} {op : BinaryOp} :
  x ∈ x₂.subexpressions → x ∈ (PartialExpr.binaryApp op x₁ x₂).subexpressions
:= by
  intro h₁
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right ; right ; assumption

/--
  helper lemma: if LHS of a `PartialExpr.binaryApp` contains an unknown, the whole expression does
-/
theorem lhs_unknown {x₁ x₂ : PartialExpr} {op : BinaryOp} :
  x₁.containsUnknown → (PartialExpr.binaryApp op x₁ x₂).containsUnknown
:= by
  unfold PartialExpr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply lhs_subexpression h₁.left
  case right => exact h₁.right

/--
  helper lemma: if RHS of a `PartialExpr.binaryApp` contains an unknown, the whole expression does
-/
theorem rhs_unknown {x₁ x₂ : PartialExpr} {op : BinaryOp} :
  x₂.containsUnknown → (PartialExpr.binaryApp op x₁ x₂).containsUnknown
:= by
  unfold PartialExpr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply rhs_subexpression h₁.left
  case right => exact h₁.right

/--
  `PartialEntities.ancestorsOrEmpty` on concrete entities is the same as `Entities.ancestorsOrEmpty` on those entities
-/
theorem partial_ancestorsOrEmpty_on_concrete_eqv_ancestorsOrEmpty {entities : Entities} {uid : EntityUID} :
  PartialEntities.ancestorsOrEmpty entities uid = Entities.ancestorsOrEmpty entities uid
:= by
  unfold PartialEntities.ancestorsOrEmpty Entities.ancestorsOrEmpty
  unfold Entities.asPartialEntities EntityData.asPartialEntityData
  rw [← Map.find?_mapOnValues]
  cases h₁ : entities.find? uid <;> simp

/--
  `partialInₑ` on concrete arguments is the same as `inₑ` on those arguments
-/
theorem partialInₑ_on_concrete_eqv_inₑ {uid₁ uid₂ : EntityUID} {entities : Entities} :
  partialInₑ uid₁ uid₂ entities = inₑ uid₁ uid₂ entities
:= by
  unfold partialInₑ inₑ
  cases uid₁ == uid₂ <;> simp
  case false => simp [partial_ancestorsOrEmpty_on_concrete_eqv_ancestorsOrEmpty]

/--
  `partialInₛ` on concrete arguments is the same as `inₛ` on those arguments
-/
theorem partialInₛ_on_concrete_eqv_inₛ {uid : EntityUID} {vs : Set Value} {entities : Entities} :
  partialInₛ uid vs entities = inₛ uid vs entities
:= by
  unfold partialInₛ inₛ
  simp [partialInₑ_on_concrete_eqv_inₑ]

/--
  `partialApply₂` on concrete arguments is the same as `apply₂` on those arguments
-/
theorem partialApply_on_concrete_eqv_apply {op : BinaryOp} {v₁ v₂ : Value} {entities : Entities} :
  partialApply₂ op v₁ v₂ entities = (apply₂ op v₁ v₂ entities).map PartialValue.value
:= by
  unfold partialApply₂ apply₂ Except.map
  cases op <;> split <;> rename_i h <;> simp only [false_implies, forall_const] at h <;> try simp
  case add | sub | mul => split <;> rename_i h <;> simp [h]
  case mem.h_10 uid₁ uid₂ => simp [partialInₑ_on_concrete_eqv_inₑ]
  case mem.h_11 uid vs =>
    simp [partialInₛ_on_concrete_eqv_inₛ]
    cases inₛ uid vs entities <;> simp only [bind_err, bind_ok]
  case mem.h_12 =>
    split <;> simp only [error.injEq] <;> rename_i h₂ <;> split at h₂ <;> try simp at *
    assumption

/--
  Inductive argument that partial evaluating a concrete `PartialExpr.binaryApp`
  expression gives the same output as concrete-evaluating the `Expr.binaryApp` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ x₂ : Expr} {request : Request} {entities : Entities} {op : BinaryOp} :
  partialEvaluate x₁ request entities = (evaluate x₁ request entities).map PartialValue.value →
  partialEvaluate x₂ request entities = (evaluate x₂ request entities).map PartialValue.value →
  partialEvaluate (PartialExpr.binaryApp op x₁ x₂) request entities = (evaluate (Expr.binaryApp op x₁ x₂) request entities).map PartialValue.value
:= by
  intro ih₁ ih₂
  unfold partialEvaluate evaluate
  simp [ih₁, ih₂]
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  split <;> simp
  case h_1 e h₁ => simp [h₁]
  case h_2 v₁ h₁ =>
    simp [h₁]
    split <;> simp
    case h_1 e h₂ => simp [h₂]
    case h_2 v₂ h₂ => simp [h₂, partialApply_on_concrete_eqv_apply, Except.map]

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.binaryApp`
-/
theorem residuals_contain_unknowns {x₁ x₂ : PartialExpr} {request : PartialRequest} {entities : PartialEntities} {op : BinaryOp} :
  @PartialExpr.ResidualsContainUnknowns x₁ request entities →
  @PartialExpr.ResidualsContainUnknowns x₂ request entities →
  @PartialExpr.ResidualsContainUnknowns (PartialExpr.binaryApp op x₁ x₂) request entities
:= by
  unfold PartialExpr.ResidualsContainUnknowns
  intro ih₁ ih₂ r h₁
  unfold partialEvaluate at h₁
  cases h₂ : (partialEvaluate x₁ request entities) <;> simp [h₂] at h₁
  cases h₃ : (partialEvaluate x₂ request entities) <;> simp [h₃] at h₁
  case ok.ok pval₁ pval₂ =>
    cases pval₁ <;> cases pval₂ <;> simp at h₁
    case value.value v₁ v₂ =>
      simp [partialApply₂] at h₁
      cases op <;> split at h₁ <;> rename_i h <;> simp at h <;> try simp at h₁
      case add i j => cases h₄ : intOrErr (Int64.add? i j) <;> simp [h₄] at h₁
      case sub i j => cases h₄ : intOrErr (Int64.sub? i j) <;> simp [h₄] at h₁
      case mul i j => cases h₄ : intOrErr (Int64.mul? i j) <;> simp [h₄] at h₁
      case mem uid vs => cases h₄ : partialInₛ uid vs entities <;> simp [h₄] at h₁
    case residual.value r₁ v₂ | residual.residual r₁ r₂ =>
      subst h₁
      apply lhs_unknown
      apply @ih₁ r₁ h₂
    case value.residual v₁ r₂ =>
      subst h₁
      apply rhs_unknown
      apply @ih₂ r₂ h₃

end Cedar.Thm.PartialEval.Binary

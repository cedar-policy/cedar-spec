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

namespace Cedar.Thm.PartialEval.GetAttr

open Cedar.Data
open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁.attr)
-/
theorem lhs_subexpression {x₁ x : PartialExpr} {attr : String} :
  x ∈ x₁.subexpressions → x ∈ (PartialExpr.getAttr x₁ attr).subexpressions
:= by
  intro h₁
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right ; assumption

/--
  helper lemma: if LHS of a `PartialExpr.getAttr` contains an unknown, the whole expression does
-/
theorem lhs_unknown {x₁ : PartialExpr} {attr : String} :
  x₁.containsUnknown → (PartialExpr.getAttr x₁ attr).containsUnknown
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
  `partialAttrsOf` on concrete arguments is the same as `attrsOf` on those
  arguments
-/
theorem partialAttrsOf_on_concrete_eqv_attrsOf {v : Value} {entities : Entities} :
  partialAttrsOf v (PartialEntities.attrs entities) = (attrsOf v (Entities.attrs entities)).map λ m => m.mapOnValues RestrictedPartialValue.value
:= by
  sorry

/--
  `partialGetAttr` on concrete arguments is the same as `getAttr` on those
  arguments
-/
theorem partialGetAttr_on_concrete_eqv_getAttr {v₁ : Value} {entities : Entities} {attr : String} :
  partialGetAttr v₁ attr entities = (getAttr v₁ attr entities).map RestrictedPartialValue.value
:= by
  unfold partialGetAttr getAttr
  simp [partialAttrsOf_on_concrete_eqv_attrsOf, Except.map]
  cases h₁ : attrsOf v₁ entities.attrs <;> simp
  case ok m => simp [Map.findOrErr_mapOnValues, Except.map]

/--
  Inductive argument that partial evaluating a concrete `PartialExpr.getAttr`
  expression gives the same output as concrete-evaluating the `Expr.getAttr` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ : Expr} {request : Request} {entities : Entities} {attr : String} :
  partialEvaluate x₁ request entities = (evaluate x₁ request entities).map PartialValue.value →
  partialEvaluate (PartialExpr.getAttr x₁ attr) request entities = (evaluate (Expr.getAttr x₁ attr) request entities).map PartialValue.value
:= by
  intro ih₁
  unfold partialEvaluate evaluate
  simp [ih₁]
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  split <;> simp
  case h_1 e h₁ => simp [h₁]
  case h_2 v₁ h₁ =>
    simp [h₁, partialGetAttr_on_concrete_eqv_getAttr, Except.map]
    cases h₂ : getAttr v₁ attr entities <;> simp [h₂, RestrictedPartialValue.asPartialValue]

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.getAttr`
-/
theorem residuals_contain_unknowns {x₁ : PartialExpr} {request : PartialRequest} {entities : PartialEntities} {attr : String} :
  @ResidualsContainUnknowns x₁ request entities →
  @ResidualsContainUnknowns (PartialExpr.getAttr x₁ attr) request entities
:= by
  unfold ResidualsContainUnknowns
  intro ih₁ r h₁
  unfold partialEvaluate at h₁
  cases h₂ : (partialEvaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case value v₁ =>
      -- need to argue that if `partialGetAttr` returns a residual, that residual contains an unknown
      sorry
    case residual r₁ =>
      subst h₁
      apply lhs_unknown
      apply @ih₁ r₁ h₂

end Cedar.Thm.PartialEval.GetAttr

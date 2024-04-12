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

import Cedar.Partial.Evaluator
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.PartialEval.Basic

namespace Cedar.Thm.PartialEval.HasAttr

open Cedar.Data
open Cedar.Spec (Attr Error Result)
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁ has attr)
-/
theorem lhs_subexpression {x₁ x : Partial.Expr} {attr : Attr} :
  x ∈ x₁.subexpressions → x ∈ (Partial.Expr.hasAttr x₁ attr).subexpressions
:= by
  intro h₁
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right ; assumption

/--
  helper lemma: if LHS of a `Partial.Expr.hasAttr` contains an unknown, the whole expression does
-/
theorem lhs_unknown {x₁ : Partial.Expr} {attr : Attr} :
  x₁.containsUnknown → (Partial.Expr.hasAttr x₁ attr).containsUnknown
:= by
  unfold Partial.Expr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply lhs_subexpression h₁.left
  case right => exact h₁.right

/--
  `Partial.attrsOf` on concrete arguments is the same as `attrsOf` on those
  arguments

  Note that the "concrete arguments" provided to `Partial.attrsOf` and `attrsOf`
  in this theorem are different from the "concrete arguments" provided in the
  theorem of the same name in PartialEval/GetAttr.lean
-/
theorem Partial.attrsOf_on_concrete_eqv_attrsOf {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (λ uid => ok (entities.asPartialEntities.attrsOrEmpty uid)) =
  (Spec.attrsOf v (λ uid => ok (entities.attrsOrEmpty uid))).map λ m => m.mapOnValues Partial.RestrictedValue.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp
  case prim p =>
    cases p <;> simp
    case entityUID uid =>
      unfold Partial.Entities.attrsOrEmpty Spec.Entities.attrsOrEmpty Spec.Entities.asPartialEntities
      cases h₁ : (entities.mapOnValues Spec.EntityData.asPartialEntityData).find? uid <;> simp
      <;> cases h₂ : entities.find? uid <;> simp
      <;> unfold Spec.EntityData.asPartialEntityData at h₁
      case none.none => simp [Map.mapOnValues_empty]
      case none.some edata =>
        exfalso -- it should not be the case that Partial.attrsOf returns none and attrsOf returns some
        simp [← Map.find?_mapOnValues] at h₁
        simp [h₁] at h₂
      case some.none edata =>
        exfalso -- it should not be the case that Partial.attrsOf returns some and attrsOf returns none
        simp [← Map.find?_mapOnValues] at h₁
        replace ⟨edata, h₁⟩ := h₁
        simp [h₂] at h₁
      case some.some edata₁ edata₂ =>
        simp [← Map.find?_mapOnValues] at h₁
        replace ⟨edata₁, ⟨h₁, h₃⟩⟩ := h₁
        simp [h₂] at h₁
        subst h₁
        subst h₃
        simp [Map.mapOnValues]

/--
  `Partial.hasAttr` on concrete arguments is the same as `hasAttr` on those
  arguments
-/
theorem Partial.hasAttr_on_concrete_eqv_hasAttr {v₁ : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.hasAttr v₁ attr entities = Spec.hasAttr v₁ attr entities
:= by
  unfold Partial.hasAttr Spec.hasAttr
  simp [Partial.attrsOf_on_concrete_eqv_attrsOf, Except.map]
  cases h₁ : Spec.attrsOf v₁ λ uid => ok (entities.attrsOrEmpty uid) <;> simp
  case ok m => simp [← Map.mapOnValues_contains]

/--
  helper lemma:

  If `ResidualsContainUnknowns` is true for an `Entities`, and `Partial.attrsOf`
  returns `ok`, then `ResidualsContainUnknowns` is also true for all the
  attributes returned by `Partial.attrsOf`
-/
theorem Partial.attrsOf_ResidualsContainUnknowns {entities : Partial.Entities} {v : Spec.Value} :
  entities.WellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.attrsOf v entities.attrs = .ok attrs →
  ∀ rpval ∈ attrs.values, Partial.RestrictedValue.ResidualsContainUnknowns rpval
:= by
  unfold Partial.Entities.ResidualsContainUnknowns Partial.attrsOf
  intro wf h₁ h₂ rpval h₃
  split at h₂
  case h_1 attrs' =>
    simp at h₂
    subst h₂
    unfold Partial.RestrictedValue.ResidualsContainUnknowns
    split <;> try simp
    case h_1 r =>
      exfalso
      rw [Map.values_mapOnValues] at h₃
      generalize attrs'.values = vs at h₃
      induction vs
      case nil => simp at h₃
      case cons h_ind =>
        apply h_ind ; clear h_ind
        unfold List.map at h₃
        simp [List.mem_cons] at h₃
  case h_2 uid =>
    unfold Partial.Entities.attrs at h₂
    cases h₄ : entities.findOrErr uid Error.entityDoesNotExist <;> simp [h₄] at h₂
    case ok edata =>
      subst h₂
      specialize h₁ edata
      unfold Partial.EntityData.ResidualsContainUnknowns at h₁
      have h₅ := (Map.in_values_iff_findOrErr_ok (m := entities) (v := edata) (e := Error.entityDoesNotExist) wf).mpr
      specialize h₅ (by exists uid)
      exact h₁ h₅ rpval h₃
  case h_3 => simp at h₂

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.hasAttr`
  expression gives the same output as concrete-evaluating the `Expr.hasAttr` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  Partial.evaluate x₁ request entities = (Spec.evaluate x₁ request entities).map Partial.Value.value →
  Partial.evaluate (Partial.Expr.hasAttr x₁ attr) request entities = (Spec.evaluate (Spec.Expr.hasAttr x₁ attr) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp [ih₁]
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  split <;> simp
  case h_1 e h₁ => simp [h₁]
  case h_2 v₁ h₁ =>
    simp [h₁, Partial.hasAttr_on_concrete_eqv_hasAttr, Except.map]
    cases h₂ : Spec.hasAttr v₁ attr entities <;> simp [h₂, Partial.RestrictedValue.asPartialValue]

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.getAttr`
-/
theorem residuals_contain_unknowns {x₁ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} {attr : Attr} :
  @Partial.Expr.ResidualsContainUnknowns x₁ request entities →
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.hasAttr x₁ attr) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns
  intro ih₁ r h₁
  unfold Partial.evaluate at h₁
  cases h₂ : (Partial.evaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case value v₁ =>
      exfalso
      cases h₃ : Partial.hasAttr v₁ attr entities <;> simp [h₃] at h₁
    case residual r₁ =>
      subst h₁
      apply lhs_unknown
      apply @ih₁ r₁ h₂

end Cedar.Thm.PartialEval.HasAttr

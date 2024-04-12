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

namespace Cedar.Thm.PartialEval.GetAttr

open Cedar.Data
open Cedar.Spec (Attr EntityUID Error Result)
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁.attr)
-/
theorem lhs_subexpression {x₁ x : Partial.Expr} {attr : Attr} :
  x ∈ x₁.subexpressions → x ∈ (Partial.Expr.getAttr x₁ attr).subexpressions
:= by
  intro h₁
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right ; assumption

/--
  helper lemma: if LHS of a `Partial.Expr.getAttr` contains an unknown, the whole expression does
-/
theorem lhs_unknown {x₁ : Partial.Expr} {attr : Attr} :
  x₁.containsUnknown → (Partial.Expr.getAttr x₁ attr).containsUnknown
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
  if `entities.attrs uid` is `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem partialEntities_attrs_wf {entities : Partial.Entities} {uid : EntityUID} {attrs: Map String Partial.RestrictedValue} :
  entities.AllWellFormed →
  entities.attrs uid = ok attrs →
  attrs.WellFormed
:= by
  unfold Partial.Entities.attrs Partial.Entities.AllWellFormed Partial.EntityData.WellFormed
  intro wf h₁
  cases h₂ : entities.findOrErr uid Error.entityDoesNotExist <;> simp [h₂] at h₁
  case ok attrs =>
    subst h₁
    have ⟨wf_m, wf_edata⟩ := wf ; clear wf
    apply (wf_edata _ _).left
    have h₃ := Map.in_values_iff_findOrErr_ok (v := attrs) (e := Error.entityDoesNotExist) wf_m
    simp [h₃]
    exists uid

/--
  if `Partial.attrsOf` returns `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem Partial.attrsOf_wf {entities : Partial.Entities} {v : Spec.Value} {attrs : Map String Partial.RestrictedValue} :
  entities.AllWellFormed →
  v.WellFormed →
  Partial.attrsOf v entities.attrs = ok attrs →
  attrs.WellFormed
:= by
  intro wf_e wf_v
  unfold Partial.attrsOf
  cases v <;> try simp
  case prim p =>
    cases p <;> simp
    case entityUID uid => exact partialEntities_attrs_wf wf_e
  case record r =>
    intro h₁
    subst h₁
    apply Map.mapOnValues_wf.mp wf_v

/--
  if a `Partial.RestrictedExpr` is an unknown, then it's still an unknown after
  converting it to `Partial.Expr`
-/
theorem restrictedPartialExpr_to_Partial.Expr_preserves_isUnknown {rpexpr : Partial.RestrictedExpr} :
  rpexpr.isUnknown → rpexpr.asPartialExpr.isUnknown
:= by
  unfold Partial.RestrictedExpr.isUnknown Partial.Expr.isUnknown Partial.RestrictedExpr.asPartialExpr
  cases rpexpr <;> simp

/--
  if a `Partial.RestrictedExpr` contains an unknown, then it still does after
  converting it to `Partial.Expr`
-/
theorem restrictedPartialExpr_to_Partial.Expr_preserves_containsUnknown {rpexpr : Partial.RestrictedExpr} :
  rpexpr.containsUnknown → rpexpr.asPartialExpr.containsUnknown
:= by
  unfold Partial.RestrictedExpr.containsUnknown Partial.Expr.containsUnknown
  cases rpexpr <;> simp
  case lit | call =>
    intro x h₁ h₂
    simp [Partial.RestrictedExpr.subexpressions] at h₁
    subst h₁
    simp [Partial.RestrictedExpr.isUnknown] at h₂
  case unknown u =>
    intro x h₁ h₂
    simp [Partial.RestrictedExpr.subexpressions] at h₁
    subst h₁
    exists (.unknown u)
    simp [Partial.Expr.isUnknown, Partial.RestrictedExpr.asPartialExpr, Partial.Expr.subexpressions]
  case set xs | record attrs =>
    intro x h₁ h₂
    simp [Partial.RestrictedExpr.subexpressions] at h₁
    rcases h₁ with h₁ | h₁
    case inl =>
      subst h₁
      simp [Partial.RestrictedExpr.isUnknown] at h₂
    case inr =>
      -- `rpexpr` is a set or record that recursively contains an unknown
      exists x.asPartialExpr
      unfold Partial.RestrictedExpr.asPartialExpr Partial.Expr.subexpressions
      cases x <;> simp [Partial.RestrictedExpr.isUnknown] at h₂
      case unknown u =>
        split <;> simp <;> rename_i h₃ <;> simp at h₃
        case h_5 name' =>
          subst h₃
          simp [Partial.Expr.isUnknown]
          sorry

/--
  `Partial.attrsOf` on concrete arguments is the same as `attrsOf` on those
  arguments
-/
theorem Partial.attrsOf_on_concrete_eqv_attrsOf {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (Partial.Entities.attrs entities) = (Spec.attrsOf v (Spec.Entities.attrs entities)).map λ m => m.mapOnValues Partial.RestrictedValue.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp
  case prim p =>
    cases p <;> simp
    case entityUID uid =>
      unfold Partial.Entities.attrs Spec.Entities.attrs Spec.Entities.asPartialEntities
      cases h₁ : entities.findOrErr uid Error.entityDoesNotExist
      <;> simp [h₁, Map.findOrErr_mapOnValues, Except.map, Spec.EntityData.asPartialEntityData]

/--
  `Partial.getAttr` on concrete arguments is the same as `getAttr` on those
  arguments
-/
theorem Partial.getAttr_on_concrete_eqv_getAttr {v₁ : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.getAttr v₁ attr entities = (Spec.getAttr v₁ attr entities).map Partial.RestrictedValue.value
:= by
  unfold Partial.getAttr Spec.getAttr
  simp [Partial.attrsOf_on_concrete_eqv_attrsOf, Except.map]
  cases h₁ : Spec.attrsOf v₁ entities.attrs <;> simp
  case ok m => simp [Map.findOrErr_mapOnValues, Except.map]

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
  Inductive argument that partial evaluating a concrete `Partial.Expr.getAttr`
  expression gives the same output as concrete-evaluating the `Expr.getAttr` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  Partial.evaluate x₁ request entities = (Spec.evaluate x₁ request entities).map Partial.Value.value →
  Partial.evaluate (Partial.Expr.getAttr x₁ attr) request entities = (Spec.evaluate (Spec.Expr.getAttr x₁ attr) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp [ih₁]
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  split <;> simp
  case h_1 e h₁ => simp [h₁]
  case h_2 v₁ h₁ =>
    simp [h₁, Partial.getAttr_on_concrete_eqv_getAttr, Except.map]
    cases h₂ : Spec.getAttr v₁ attr entities <;> simp [h₂, Partial.RestrictedValue.asPartialValue]

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.getAttr`
-/
theorem residuals_contain_unknowns {x₁ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} {attr : Attr} :
  entities.AllWellFormed →
  @Partial.Expr.ResidualsContainUnknowns x₁ request entities →
  Partial.Entities.ResidualsContainUnknowns entities →
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.getAttr x₁ attr) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns
  intro wf ih₁ ih₂ r h₁
  unfold Partial.evaluate at h₁
  cases h₂ : (Partial.evaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case value v₁ =>
      -- `v₁.attr` can return a residual even though `v₁` is concrete.
      -- Here we argue that if it does, that residual contains an unknown
      unfold Partial.getAttr Except.map at h₁
      split at h₁ <;> simp at h₁
      case h_2 rpval h₃ =>
        simp [Partial.RestrictedValue.asPartialValue] at h₁
        split at h₁ <;> simp at h₁
        case h_2 r' =>
          subst h₁
          apply restrictedPartialExpr_to_Partial.Expr_preserves_containsUnknown
          cases h₄ : Partial.attrsOf v₁ entities.attrs <;> simp [h₄] at h₃
          case a.ok attrs =>
            have h₅ := (Map.in_values_iff_findOrErr_ok (m := attrs) (v := .residual r') (e := Error.attrDoesNotExist) (Partial.attrsOf_wf wf (partial_eval_wf wf h₂) h₄)).mpr
            specialize h₅ (by exists attr)
            unfold Partial.Entities.AllWellFormed at wf
            have h₆ := Partial.attrsOf_ResidualsContainUnknowns wf.left ih₂ h₄ (.residual r')
            simp [Partial.RestrictedValue.ResidualsContainUnknowns] at h₆
            exact h₆ h₅
    case residual r₁ =>
      subst h₁
      apply lhs_unknown
      apply @ih₁ r₁ h₂

end Cedar.Thm.PartialEval.GetAttr

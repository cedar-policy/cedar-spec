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
  if `entities.attrs uid` is `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem partialEntities_attrs_wf {entities : PartialEntities} {uid : EntityUID} {attrs: Map String RestrictedPartialValue} :
  entities.AllWellFormed →
  entities.attrs uid = ok attrs →
  attrs.WellFormed
:= by
  unfold PartialEntities.attrs PartialEntities.AllWellFormed PartialEntityData.WellFormed
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
  if `partialAttrsOf` returns `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem partialAttrsOf_wf {entities : PartialEntities} {v : Value} {attrs : Map String RestrictedPartialValue} :
  entities.AllWellFormed →
  v.WellFormed →
  partialAttrsOf v entities.attrs = ok attrs →
  attrs.WellFormed
:= by
  intro wf_e wf_v
  unfold partialAttrsOf
  cases v <;> try simp
  case prim p =>
    cases p <;> simp
    case entityUID uid => exact partialEntities_attrs_wf wf_e
  case record r =>
    intro h₁
    subst h₁
    apply Map.mapOnValues_wf.mp wf_v

/--
  if a `RestrictedPartialExpr` is an unknown, then it's still an unknown after
  converting it to `PartialExpr`
-/
theorem restrictedPartialExpr_to_PartialExpr_preserves_isUnknown {rpexpr : RestrictedPartialExpr} :
  rpexpr.isUnknown → rpexpr.asPartialExpr.isUnknown
:= by
  unfold RestrictedPartialExpr.isUnknown PartialExpr.isUnknown RestrictedPartialExpr.asPartialExpr
  cases rpexpr <;> simp

/--
  if a `RestrictedPartialExpr` contains an unknown, then it still does after
  converting it to `PartialExpr`
-/
theorem restrictedPartialExpr_to_PartialExpr_preserves_containsUnknown {rpexpr : RestrictedPartialExpr} :
  rpexpr.containsUnknown → rpexpr.asPartialExpr.containsUnknown
:= by
  unfold RestrictedPartialExpr.containsUnknown PartialExpr.containsUnknown
  cases rpexpr <;> simp
  case lit | call =>
    intro x h₁ h₂
    simp [RestrictedPartialExpr.subexpressions] at h₁
    subst h₁
    simp [RestrictedPartialExpr.isUnknown] at h₂
  case unknown name =>
    intro x h₁ h₂
    simp [RestrictedPartialExpr.subexpressions] at h₁
    subst h₁
    exists (.unknown name)
    simp [PartialExpr.isUnknown, RestrictedPartialExpr.asPartialExpr, PartialExpr.subexpressions]
  case set xs | record attrs =>
    intro x h₁ h₂
    simp [RestrictedPartialExpr.subexpressions] at h₁
    rcases h₁ with h₁ | h₁
    case inl =>
      subst h₁
      simp [RestrictedPartialExpr.isUnknown] at h₂
    case inr =>
      -- `rpexpr` is a set or record that recursively contains an unknown
      exists x.asPartialExpr
      unfold RestrictedPartialExpr.asPartialExpr PartialExpr.subexpressions
      cases x <;> simp [RestrictedPartialExpr.isUnknown] at h₂
      case unknown name =>
        split <;> simp <;> rename_i h₃ <;> simp at h₃
        case h_5 name' =>
          subst h₃
          simp [PartialExpr.isUnknown]
          sorry

/--
  `partialAttrsOf` on concrete arguments is the same as `attrsOf` on those
  arguments
-/
theorem partialAttrsOf_on_concrete_eqv_attrsOf {v : Value} {entities : Entities} :
  partialAttrsOf v (PartialEntities.attrs entities) = (attrsOf v (Entities.attrs entities)).map λ m => m.mapOnValues RestrictedPartialValue.value
:= by
  unfold partialAttrsOf attrsOf Except.map
  cases v <;> simp
  case prim p =>
    cases p <;> simp
    case entityUID uid =>
      unfold PartialEntities.attrs Entities.attrs Entities.asPartialEntities
      cases h₁ : entities.findOrErr uid Error.entityDoesNotExist
      <;> simp [h₁, Map.findOrErr_mapOnValues, Except.map, EntityData.asPartialEntityData]

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
  helper lemma:

  If `ResidualsContainUnknowns` is true for an `Entities`, and `partialAttrsOf`
  returns `ok`, then `ResidualsContainUnknowns` is also true for all the
  attributes returned by `partialAttrsOf`
-/
theorem partialAttrsOf_ResidualsContainUnknowns {entities : PartialEntities} {v : Value} :
  entities.WellFormed →
  PartialEntities.ResidualsContainUnknowns entities →
  partialAttrsOf v entities.attrs = .ok attrs →
  ∀ rpval ∈ attrs.values, RestrictedPartialValue.ResidualsContainUnknowns rpval
:= by
  unfold PartialEntities.ResidualsContainUnknowns partialAttrsOf
  intro wf h₁ h₂ rpval h₃
  split at h₂
  case h_1 attrs' =>
    simp at h₂
    subst h₂
    unfold RestrictedPartialValue.ResidualsContainUnknowns
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
    unfold PartialEntities.attrs at h₂
    cases h₄ : entities.findOrErr uid Error.entityDoesNotExist <;> simp [h₄] at h₂
    case ok edata =>
      subst h₂
      specialize h₁ edata
      unfold PartialEntityData.ResidualsContainUnknowns at h₁
      have h₅ := (Map.in_values_iff_findOrErr_ok (m := entities) (v := edata) (e := Error.entityDoesNotExist) wf).mpr
      specialize h₅ (by exists uid)
      exact h₁ h₅ rpval h₃
  case h_3 => simp at h₂

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
  entities.AllWellFormed →
  @PartialExpr.ResidualsContainUnknowns x₁ request entities →
  PartialEntities.ResidualsContainUnknowns entities →
  @PartialExpr.ResidualsContainUnknowns (PartialExpr.getAttr x₁ attr) request entities
:= by
  unfold PartialExpr.ResidualsContainUnknowns
  intro wf ih₁ ih₂ r h₁
  unfold partialEvaluate at h₁
  cases h₂ : (partialEvaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case value v₁ =>
      -- `v₁.attr` can return a residual even though `v₁` is concrete.
      -- Here we argue that if it does, that residual contains an unknown
      unfold partialGetAttr Except.map at h₁
      split at h₁ <;> simp at h₁
      case h_2 rpval h₃ =>
        simp [RestrictedPartialValue.asPartialValue] at h₁
        split at h₁ <;> simp at h₁
        case h_2 r' =>
          subst h₁
          apply restrictedPartialExpr_to_PartialExpr_preserves_containsUnknown
          cases h₄ : partialAttrsOf v₁ entities.attrs <;> simp [h₄] at h₃
          case a.ok attrs =>
            have h₅ := (Map.in_values_iff_findOrErr_ok (m := attrs) (v := .residual r') (e := Error.attrDoesNotExist) (partialAttrsOf_wf wf (partial_eval_wf wf h₂) h₄)).mpr
            specialize h₅ (by exists attr)
            unfold PartialEntities.AllWellFormed at wf
            have h₆ := partialAttrsOf_ResidualsContainUnknowns wf.left ih₂ h₄ (.residual r')
            simp [RestrictedPartialValue.ResidualsContainUnknowns] at h₆
            exact h₆ h₅
    case residual r₁ =>
      subst h₁
      apply lhs_unknown
      apply @ih₁ r₁ h₂

end Cedar.Thm.PartialEval.GetAttr

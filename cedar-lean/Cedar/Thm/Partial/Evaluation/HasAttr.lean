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

namespace Cedar.Thm.Partial.Evaluation.HasAttr

open Cedar.Data
open Cedar.Spec (Attr Error Result)

/--
  `Partial.attrsOf` on concrete arguments is the same as `Spec.attrsOf` on those
  arguments

  Note that the "concrete arguments" provided to `Partial.attrsOf` and
  `Spec.attrsOf` in this theorem are different from the "concrete arguments"
  provided in the theorem of the same name in Partial/Evaluation/GetAttr.lean
-/
theorem Partial.attrsOf_on_concrete_eqv_attrsOf {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (λ uid => .ok (entities.asPartialEntities.attrsOrEmpty uid)) =
  (Spec.attrsOf v (λ uid => .ok (entities.attrsOrEmpty uid))).map λ m => m.mapOnValues Partial.Value.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp only
  case prim p =>
    cases p <;> simp only
    case entityUID uid =>
      unfold Partial.Entities.attrsOrEmpty Spec.Entities.attrsOrEmpty Spec.Entities.asPartialEntities
      cases h₁ : (entities.mapOnValues Spec.EntityData.asPartialEntityData).find? uid
      <;> simp only [Except.ok.injEq]
      <;> cases h₂ : entities.find? uid <;> simp only
      <;> unfold Spec.EntityData.asPartialEntityData at h₁
      <;> simp only [← Map.find?_mapOnValues, Option.map_eq_none', Option.map_eq_some'] at h₁
      case none.none => simp [Map.mapOnValues_empty]
      case none.some => simp [h₁] at h₂
      case some.none => simp [h₂] at h₁
      case some.some edata₁ edata₂ =>
        replace ⟨edata₁, ⟨h₁, h₃⟩⟩ := h₁
        simp only [h₂, Option.some.injEq] at h₁
        subst h₁ h₃
        simp [Map.mapOnValues]

/--
  `Partial.hasAttr` on concrete arguments is the same as `Spec.hasAttr` on those
  arguments
-/
theorem Partial.hasAttr_on_concrete_eqv_hasAttr {v : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.hasAttr v attr entities = Spec.hasAttr v attr entities
:= by
  unfold Partial.hasAttr Spec.hasAttr
  simp only [Partial.attrsOf_on_concrete_eqv_attrsOf, Except.map]
  cases Spec.attrsOf v λ uid => .ok (entities.attrsOrEmpty uid)
  <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
  case ok m => simp [← Map.mapOnValues_contains]

/--
  `Partial.evaluateHasAttr` on concrete arguments is the same as `Spec.hasAttr`
  on those arguments
-/
theorem Partial.evaluateHasAttr_on_concrete_eqv_hasAttr {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateHasAttr v a entities = Spec.hasAttr v a entities
:= by
  simp [Partial.evaluateHasAttr, Partial.hasAttr_on_concrete_eqv_hasAttr, pure, Except.pure]

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.hasAttr`
  expression gives the same output as concrete-evaluating the
  `Spec.Expr.hasAttr` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.hasAttr x₁ attr) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case error e => simp [Except.map]
  case ok v₁ => exact Partial.evaluateHasAttr_on_concrete_eqv_hasAttr

end Cedar.Thm.Partial.Evaluation.HasAttr

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
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.GetAttr

open Cedar.Data
open Cedar.Spec (Attr EntityUID Error Result)

/--
  if `entities.attrs uid` is `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem partialEntities_attrs_wf {entities : Partial.Entities} {uid : EntityUID} {attrs: Map String Partial.Value} :
  entities.AllWellFormed →
  entities.attrs uid = .ok attrs →
  attrs.WellFormed
:= by
  unfold Partial.Entities.attrs Partial.Entities.AllWellFormed Partial.EntityData.WellFormed
  intro wf h₁
  cases h₂ : entities.findOrErr uid Error.entityDoesNotExist
  <;> simp only [h₂, Except.bind_err, Except.bind_ok, Except.ok.injEq] at h₁
  case ok attrs =>
    subst h₁
    have ⟨wf_m, wf_edata⟩ := wf ; clear wf
    apply (wf_edata _ _).left
    have h₃ := Map.in_values_iff_findOrErr_ok (v := attrs) (e := Error.entityDoesNotExist) wf_m
    simp only [h₃]
    exists uid

/--
  if `Partial.attrsOf` returns `ok` with some attrs, those attrs are a
  well-formed `Map`
-/
theorem attrsOf_wf {entities : Partial.Entities} {v : Spec.Value} {attrs : Map String Partial.Value} :
  entities.AllWellFormed →
  v.WellFormed →
  Partial.attrsOf v entities.attrs = .ok attrs →
  attrs.WellFormed
:= by
  intro wf_e wf_v
  unfold Partial.attrsOf
  cases v <;> try simp only [false_implies, Except.ok.injEq]
  case prim p =>
    cases p <;> simp only [false_implies]
    case entityUID uid => exact partialEntities_attrs_wf wf_e
  case record r =>
    intro h₁
    subst h₁
    apply Map.mapOnValues_wf.mp wf_v

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
      <;> simp [h₁, Map.findOrErr_mapOnValues, Except.map, Spec.EntityData.asPartialEntityData]

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
  case ok m => simp [Map.findOrErr_mapOnValues, Except.map]

/--
  `Partial.evaluateGetAttr` on concrete arguments is the same as `Spec.getAttr`
  on those arguments
-/
theorem evaluateGetAttr_on_concrete_eqv_concrete {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateGetAttr v a entities = Spec.getAttr v a entities
:= by
  simp only [Partial.evaluateGetAttr, getAttr_on_concrete_eqv_concrete, pure, Except.pure, Except.map]
  cases h : Spec.getAttr v a entities <;> simp [h]

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.getAttr`
  expression gives the same output as concrete-evaluating the
  `Spec.Expr.getAttr` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {attr : Attr} :
  Partial.evaluate x₁ request entities = (Spec.evaluate x₁ request entities).map Partial.Value.value →
  Partial.evaluate (Partial.Expr.getAttr x₁ attr) request entities = (Spec.evaluate (Spec.Expr.getAttr x₁ attr) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp only [ih₁]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case error e => simp [Except.map]
  case ok v₁ => exact evaluateGetAttr_on_concrete_eqv_concrete

end Cedar.Thm.Partial.Evaluation.GetAttr

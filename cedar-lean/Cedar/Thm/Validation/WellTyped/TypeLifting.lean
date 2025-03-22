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

import Cedar.Validation.TypedExpr
import Cedar.Spec
import Cedar.Thm.Validation
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Data

/-!
This file contains theorems related to `TypedExpr.liftBoolTypes`
-/

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec

theorem type_lifting_preserves_expr (x : TypedExpr):
  x.toExpr = x.liftBoolTypes.toExpr
:= by
  cases x <;> simp only [TypedExpr.toExpr, TypedExpr.liftBoolTypes]
  case ite a b c _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b, type_lifting_preserves_expr c]
  case and a b _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b]
  case or a b _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b]
  case unaryApp a _ =>
    simp only [type_lifting_preserves_expr a]
  case binaryApp a b _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b]
  case getAttr a _ _ =>
    simp only [type_lifting_preserves_expr a]
  case hasAttr a _ _ =>
    simp only [type_lifting_preserves_expr a]
  case set s _ =>
    simp only [List.map₁_eq_map, List.map_map, Expr.set.injEq, List.map_inj_left,
      Function.comp_apply]
    exact λ x _ => type_lifting_preserves_expr x
  case record m _ =>
    simp only [Expr.record.injEq]
    have : m.attach₂.map (λ x => (x.1.fst, x.1.snd.toExpr)) =
      m.map λ x => (x.fst, x.snd.toExpr) := by
      exact List.map_attach₂ λ x : Attr × TypedExpr => (x.fst, x.snd.toExpr)
    rw [this]
    have : m.attach₂.map (λ x => (x.1.fst, x.1.snd.liftBoolTypes)) =
      m.map λ x => (x.fst, x.snd.liftBoolTypes) := by
      exact List.map_attach₂ λ x : Attr × TypedExpr => (x.fst, x.snd.liftBoolTypes)
    rw [this]
    have : (List.map (λ x => (x.fst, x.snd.liftBoolTypes)) m).attach₂.map (λ x => (x.1.fst, x.1.snd.toExpr)) =
      (List.map (λ x => (x.fst, x.snd.liftBoolTypes)) m).map (λ x => (x.fst, x.snd.toExpr)) := by
      exact List.map_attach₂ λ x : Attr × TypedExpr => (x.fst, x.snd.toExpr)
    rw [this]
    simp only [List.map_map, List.map_inj_left, Function.comp_apply, Prod.mk.injEq, true_and,
      Prod.forall]
    exact λ _ x _ => type_lifting_preserves_expr x
  case call args _ =>
    simp only [List.map₁_eq_map, List.map_map, Expr.call.injEq, List.map_inj_left,
      Function.comp_apply, true_and]
    exact λ x _ => type_lifting_preserves_expr x
  termination_by x
  decreasing_by
    all_goals (simp_wf ; try omega)
    all_goals
      rename_i h
      have := List.sizeOf_lt_of_mem h
      simp only [Prod.mk.sizeOf_spec] at this
      omega

theorem type_lifting_preserves_evaluation_results {x : TypedExpr} {request : Request} {entities : Entities} :
  evaluate x.toExpr request entities = evaluate x.liftBoolTypes.toExpr request entities
 := by
 simp only [type_lifting_preserves_expr x]

theorem type_lifting_preserves_instance_of_type {v : Value} {ty : CedarType} :
  InstanceOfType v ty →
  InstanceOfType v ty.liftBoolTypes
:= by
  intro h₁
  induction h₁ <;> simp only [CedarType.liftBoolTypes]
  case instance_of_bool =>
    simp only [BoolType.lift, bool_is_instance_of_anyBool]
  case instance_of_int =>
    exact InstanceOfType.instance_of_int
  case instance_of_string =>
    exact InstanceOfType.instance_of_string
  case instance_of_entity e ety h =>
    exact InstanceOfType.instance_of_entity e ety h
  case instance_of_set s tyᵢ _ hᵢ =>
    exact InstanceOfType.instance_of_set s tyᵢ.liftBoolTypes hᵢ
  case instance_of_record r rty hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ =>
    apply InstanceOfType.instance_of_record
    case h₁ =>
      intro k h₂
      replace hᵢ₁ := hᵢ₁ k h₂
      simp only [List.map₁_eq_map
          (fun (x : Attr × QualifiedType) => (x.fst, QualifiedType.liftBoolTypes x.snd))]
      simp [Data.Map.contains, Data.Map.find?, Data.Map.make, Data.Map.kvs]
      sorry
    case h₂ =>
      intro k v qty h₂
      replace hᵢ₄ := λ qty => hᵢ₄ k v qty h₂
      sorry
    case h₃ =>
      sorry
  case instance_of_ext x xty hᵢ =>
    exact InstanceOfType.instance_of_ext x xty hᵢ

end Cedar.Thm

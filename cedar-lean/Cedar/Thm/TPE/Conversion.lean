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

import Cedar.TPE
import Cedar.Thm.TPE.Soundness
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation.WellTyped.ResidualDefinition

/-!
This file defines the main theorem of TPE soundness and its associated lemmas.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation


mutual
theorem conversion_preserves_evaluation_forall2 :
  List.Forall₂ (fun x y => Spec.evaluate x.toExpr req es = (TypedExpr.toResidual y).evaluate req es) ls ls := by
  cases ls with
  | nil =>
    simp
  | cons head tail =>
    simp
    constructor
    case left =>
      apply conversion_preserves_evaluation
    case right =>
      apply conversion_preserves_evaluation_forall2

theorem conversion_preserves_evaluation_forall2_map {map : List (Attr × TypedExpr)} :
  List.Forall₂
  (fun x y =>
    Prod.mk x.fst <$> Spec.evaluate x.snd.toExpr req es =
      Prod.mk y.fst <$> (TypedExpr.toResidual y.snd).evaluate req es)
  map map := by
  cases map with
  | nil =>
    simp
  | cons head tail =>
    simp
    constructor
    case left =>
      apply conversion_preserves_evaluation
    case right =>
      apply conversion_preserves_evaluation_forall2_map




/--
Theorem stating that converting a TypedExpr to a Residual preserves evaluation semantics.
That is, evaluating the original TypedExpr (converted to Expr) gives the same result
as evaluating the converted Residual.
-/
theorem conversion_preserves_evaluation (te : TypedExpr) (req : Request) (es : Entities) :
  Spec.evaluate te.toExpr req es = (TypedExpr.toResidual te).evaluate req es := by
  cases te with
  | lit p ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
  | var v ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    cases v <;> simp [Spec.evaluate, Residual.evaluate]
  | ite cond thenExpr elseExpr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_cond := conversion_preserves_evaluation cond req es
    have ih_then := conversion_preserves_evaluation thenExpr req es
    have ih_else := conversion_preserves_evaluation elseExpr req es
    rw [←ih_cond]
    simp [Result.as, Value.asBool]
    rw [←ih_then, ←ih_else]
    cases Spec.evaluate cond.toExpr req es
    case ite.error =>
      simp
    case ite.ok =>
      simp
      rename_i a
      cases a
      case prim =>
        simp [bind, Coe.coe, Value.asBool]
      all_goals {
        simp [Coe.coe, Value.asBool]
      }
  | and a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | or a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | unaryApp op expr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | binaryApp op a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | getAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | hasAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | set ls ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    rw [List.map₁_eq_map, List.map₁_eq_map]


    repeat auto_map₁_to_map

    rw [List.mapM_then_map_combiner, List.mapM_then_map_combiner]
    rw [List.forall₂_implies_mapM_eq]
    apply conversion_preserves_evaluation_forall2
  | record map ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1

    repeat auto_map₁_to_map
    unfold bindAttr
    rw [List.mapM_then_map_combiner, List.mapM_then_map_combiner]
    simp
    rw [List.forall₂_implies_mapM_eq]
    apply conversion_preserves_evaluation_forall2_map
  | call xfn args ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    repeat auto_map₁_to_map
    rw [List.mapM_then_map_combiner, List.mapM_then_map_combiner]
    rw [List.forall₂_implies_mapM_eq]
    apply conversion_preserves_evaluation_forall2
end


theorem conversion_preserves_typeof (e: TypedExpr) :
  TypedExpr.typeOf e = Residual.typeOf (TypedExpr.toResidual e) := by
  cases e
  all_goals {
    simp [TypedExpr.toResidual, Residual.typeOf, TypedExpr.typeOf]
  }

theorem conversion_preserves_typedness:
  TypedExpr.WellTyped env expr →
    Residual.WellTyped env (TypedExpr.toResidual expr) := by
  intro h
  cases expr with
  | lit p ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.val
    cases h with
    | lit h₁ =>
      -- Convert Prim.WellTyped to InstanceOfType
      cases h₁ with
      | bool b =>
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
      | int i =>
        apply InstanceOfType.instance_of_int
      | string s =>
        apply InstanceOfType.instance_of_string
      | entityUID uid h₁ =>
        apply InstanceOfType.instance_of_entity
        simp [InstanceOfEntityType]
        unfold EntityUID.WellFormed
        exact h₁
  | var v ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.var
    cases h with
    | var h₁ => exact h₁
  | ite x₁ x₂ x₃ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | ite h₁ h₂ h₃ h₄ h₅ =>
      rw [conversion_preserves_typeof x₂]
      apply Residual.WellTyped.ite
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · apply conversion_preserves_typedness
        exact h₃
      · rw [←conversion_preserves_typeof x₁]
        exact h₄
      · rw [←conversion_preserves_typeof x₂, ←conversion_preserves_typeof x₃]
        exact h₅
  | and x₁ x₂ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | and h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.and
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · rw [←conversion_preserves_typeof x₁]
        exact h₃
      · rw [←conversion_preserves_typeof x₂]
        exact h₄
  | or x₁ x₂ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | or h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.or
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · rw [←conversion_preserves_typeof x₁]
        exact h₃
      · rw [←conversion_preserves_typeof x₂]
        exact h₄
  | unaryApp op₁ x₁ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.unaryApp
    sorry
    sorry
  | binaryApp op₂ x₁ x₂ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.binaryApp
    sorry
    sorry
    sorry
  | getAttr x₁ attr ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | getAttr_entity h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.getAttr_entity
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
      · exact h₃
      · exact h₄
    | getAttr_record h₁ h₂ h₃ =>
      apply Residual.WellTyped.getAttr_record
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
      · exact h₃
  | hasAttr x₁ attr ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | hasAttr_entity h₁ h₂ =>
      apply Residual.WellTyped.hasAttr_entity
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
    | hasAttr_record h₁ h₂ =>
      apply Residual.WellTyped.hasAttr_record
      · apply conversion_preserves_typedness
        exact h₁
      · rw [←conversion_preserves_typeof x₁]
        exact h₂
  | set ls ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    sorry
  | record m ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    sorry
  | call xfn args ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.call
    cases h with
    | call h₁ h₂ =>
      · intro x hx
        sorry
    sorry

end Cedar.Thm

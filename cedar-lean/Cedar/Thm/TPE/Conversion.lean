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
        exact ⟨rfl, h₁⟩
  | var v ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.var
    cases h with
    | var h₁ => exact h₁
  | ite x₁ x₂ x₃ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.ite
    cases h with
    | ite h₁ h₂ h₃ h₄ h₅ =>
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · apply conversion_preserves_typedness
        exact h₃
      · exact h₄
      · exact h₅
  | and x₁ x₂ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.and
    cases h with
    | and h₁ h₂ h₃ h₄ =>
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · exact h₃
      · exact h₄
  | or x₁ x₂ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.or
    cases h with
    | or h₁ h₂ h₃ h₄ =>
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · exact h₃
      · exact h₄
  | unaryApp op₁ x₁ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.unaryApp
    cases h with
    | unaryApp h₁ h₂ =>
      · apply conversion_preserves_typedness
        exact h₁
      · -- Convert UnaryOp.WellTyped to UnaryResidualWellTyped
        cases h₂ with
        | not h₂ =>
          apply UnaryResidualWellTyped.not
          exact h₂
        | neg h₂ =>
          apply UnaryResidualWellTyped.neg
          exact h₂
        | isEmpty h₂ =>
          apply UnaryResidualWellTyped.isEmpty
          exact h₂
        | like h₂ =>
          apply UnaryResidualWellTyped.like
          exact h₂
        | is h₂ =>
          apply UnaryResidualWellTyped.is
          exact h₂
  | binaryApp op₂ x₁ x₂ ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.binaryApp
    cases h with
    | binaryApp h₁ h₂ h₃ =>
      · apply conversion_preserves_typedness
        exact h₁
      · apply conversion_preserves_typedness
        exact h₂
      · -- Convert BinaryOp.WellTyped to BinaryResidualWellTyped
        cases h₃ with
        | eq_lit =>
          apply BinaryResidualWellTyped.eq_val
        | eq_entity h₃ h₄ =>
          apply BinaryResidualWellTyped.eq_entity
          · exact h₃
          · exact h₄
        | eq h₃ =>
          apply BinaryResidualWellTyped.eq
          exact h₃
        | memₑ h₃ h₄ =>
          apply BinaryResidualWellTyped.memₑ
          · exact h₃
          · exact h₄
        | memₛ h₃ h₄ =>
          apply BinaryResidualWellTyped.memₛ
          · exact h₃
          · exact h₄
        | less_int h₃ h₄ =>
          apply BinaryResidualWellTyped.less_int
          · exact h₃
          · exact h₄
        | less_datetime h₃ h₄ =>
          apply BinaryResidualWellTyped.less_datetime
          · exact h₃
          · exact h₄
        | less_duration h₃ h₄ =>
          apply BinaryResidualWellTyped.less_duration
          · exact h₃
          · exact h₄
        | lessEq_int h₃ h₄ =>
          apply BinaryResidualWellTyped.lessEq_int
          · exact h₃
          · exact h₄
        | lessEq_datetime h₃ h₄ =>
          apply BinaryResidualWellTyped.lessEq_datetime
          · exact h₃
          · exact h₄
        | lessEq_duration h₃ h₄ =>
          apply BinaryResidualWellTyped.lessEq_duration
          · exact h₃
          · exact h₄
        | add h₃ h₄ =>
          apply BinaryResidualWellTyped.add
          · exact h₃
          · exact h₄
        | sub h₃ h₄ =>
          apply BinaryResidualWellTyped.sub
          · exact h₃
          · exact h₄
        | mul h₃ h₄ =>
          apply BinaryResidualWellTyped.mul
          · exact h₃
          · exact h₄
        | contains h₃ =>
          apply BinaryResidualWellTyped.contains
          exact h₃
        | containsAll h₃ h₄ =>
          apply BinaryResidualWellTyped.containsAll
          · exact h₃
          · exact h₄
        | containsAny h₃ h₄ =>
          apply BinaryResidualWellTyped.containsAny
          · exact h₃
          · exact h₄
        | hasTag h₃ h₄ =>
          apply BinaryResidualWellTyped.hasTag
          · exact h₃
          · exact h₄
        | getTag h₃ h₄ h₅ =>
          apply BinaryResidualWellTyped.getTag
          · exact h₃
          · exact h₄
          · exact h₅
  | getAttr x₁ attr ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | getAttr_entity h₁ h₂ h₃ h₄ =>
      apply Residual.WellTyped.getAttr_entity
      · apply conversion_preserves_typedness
        exact h₁
      · exact h₂
      · exact h₃
      · exact h₄
    | getAttr_record h₁ h₂ h₃ =>
      apply Residual.WellTyped.getAttr_record
      · apply conversion_preserves_typedness
        exact h₁
      · exact h₂
      · exact h₃
  | hasAttr x₁ attr ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    cases h with
    | hasAttr_entity h₁ h₂ =>
      apply Residual.WellTyped.hasAttr_entity
      · apply conversion_preserves_typedness
        exact h₁
      · exact h₂
    | hasAttr_record h₁ h₂ =>
      apply Residual.WellTyped.hasAttr_record
      · apply conversion_preserves_typedness
        exact h₁
      · exact h₂
  | set ls ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.set
    cases h with
    | set h₁ h₂ h₃ =>
      · intro x hx
        simp [List.mem_map₁] at hx
        rcases hx with ⟨y, hy, hxy⟩
        rw [←hxy]
        apply conversion_preserves_typedness
        exact h₁ y hy
      · intro x hx
        simp [List.mem_map₁] at hx
        rcases hx with ⟨y, hy, hxy⟩
        rw [←hxy]
        simp [Residual.typeOf]
        exact h₂ y hy
      · exact h₃
  | record m ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.record
    cases h with
    | record h₁ h₂ =>
      · intro k v hkv
        -- For record case, we need to handle the conversion differently
        sorry
      · simp [h₂]
        -- Type mapping preservation
        sorry
  | call xfn args ty' =>
    simp [TypedExpr.liftBoolTypes, TypedExpr.toResidual] at h ⊢
    apply Residual.WellTyped.call
    cases h with
    | call h₁ h₂ =>
      · intro x hx
        simp [List.mem_map₁] at hx
        rcases hx with ⟨y, hy, hxy⟩
        rw [←hxy]
        apply conversion_preserves_typedness
        exact h₁ y hy
      · -- Convert ExtFun.WellTyped to ExtResidualWellTyped
        cases h₂ with
        | decimal h₂ =>
          apply ExtResidualWellTyped.decimal
          exact h₂
        | lessThan h₂ h₃ =>
          apply ExtResidualWellTyped.lessThan
          · exact h₂
          · exact h₃
        | lessThanOrEqual h₂ h₃ =>
          apply ExtResidualWellTyped.lessThanOrEqual
          · exact h₂
          · exact h₃
        | greaterThan h₂ h₃ =>
          apply ExtResidualWellTyped.greaterThan
          · exact h₂
          · exact h₃
        | greaterThanOrEqual h₂ h₃ =>
          apply ExtResidualWellTyped.greaterThanOrEqual
          · exact h₂
          · exact h₃
        | ip h₂ =>
          apply ExtResidualWellTyped.ip
          exact h₂
        | isIpv4 h₂ =>
          apply ExtResidualWellTyped.isIpv4
          exact h₂
        | isIpv6 h₂ =>
          apply ExtResidualWellTyped.isIpv6
          exact h₂
        | isLoopback h₂ =>
          apply ExtResidualWellTyped.isLoopback
          exact h₂
        | isMulticast h₂ =>
          apply ExtResidualWellTyped.isMulticast
          exact h₂
        | isInRange h₂ h₃ =>
          apply ExtResidualWellTyped.isInRange
          · exact h₂
          · exact h₃
        | datetime h₂ =>
          apply ExtResidualWellTyped.datetime
          exact h₂
        | duration h₂ =>
          apply ExtResidualWellTyped.duration
          exact h₂
        | offset h₂ h₃ =>
          apply ExtResidualWellTyped.offset
          · exact h₂
          · exact h₃
        | durationSince h₂ h₃ =>
          apply ExtResidualWellTyped.durationSince
          · exact h₂
          · exact h₃
        | toDate h₂ =>
          apply ExtResidualWellTyped.toDate
          exact h₂
        | toTime h₂ =>
          apply ExtResidualWellTyped.toTime
          exact h₂
        | toMilliseconds h₂ =>
          apply ExtResidualWellTyped.toMilliseconds
          exact h₂
        | toSeconds h₂ =>
          apply ExtResidualWellTyped.toSeconds
          exact h₂
        | toMinutes h₂ =>
          apply ExtResidualWellTyped.toMinutes
          exact h₂
        | toHours h₂ =>
          apply ExtResidualWellTyped.toHours
          exact h₂
        | toDays h₂ =>
          apply ExtResidualWellTyped.toDays
          exact h₂


end Cedar.Thm

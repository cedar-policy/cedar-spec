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
import Cedar.Thm.Validation.Typechecker.Types
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

inductive Lifted : CedarType → CedarType → Prop
  | bool {bty : BoolType} :
    Lifted (.bool bty) (.bool .anyBool)
  | int :
    Lifted .int .int
  | string :
    Lifted .string .string
  | entity {ety : EntityType} :
    Lifted (.entity ety) (.entity ety)
  | ext {extTy : ExtType} :
    Lifted (.ext extTy) (.ext extTy)
  | set {ty₁ ty₂ : CedarType}
    (h : Lifted ty₁ ty₂) :
    Lifted (.set ty₁) (.set ty₂)
  | record_nil :
    Lifted (.record (.mk [])) (.record (.mk []))
  | record_fst_optional {ty₁ ty₂ : CedarType} {k : Attr} {m₁ m₂ : List (Attr × QualifiedType)}
    (h₁ : Lifted ty₁ ty₂)
    (h₂ : Lifted (.record (.mk m₁)) (.record (.mk m₂))) :
    Lifted (.record (.mk ((k, .optional ty₁) :: m₁))) (.record (.mk ((k, .optional ty₂) :: m₂)))
  | record_fst_required {ty₁ ty₂ : CedarType} {k : Attr} {m₁ m₂ : List (Attr × QualifiedType)}
    (h₁ : Lifted ty₁ ty₂)
    (h₂ : Lifted (.record (.mk m₁)) (.record (.mk m₂))) :
    Lifted (.record (.mk ((k, .required ty₁) :: m₁))) (.record (.mk ((k, .required ty₂) :: m₂)))

mutual

theorem lifted_record_is_lifted (m : List (Attr × QualifiedType)) :
  Lifted (.record (.mk m)) (.record (.mk (CedarType.liftBoolTypesRecord m)))
:= by
  unfold CedarType.liftBoolTypesRecord
  split
  case _ => exact Lifted.record_nil
  case _ qty l =>
    unfold QualifiedType.liftBoolTypes
    split
    case _ ty =>
      have hᵢ₁ := lifted_type_is_lifted ty
      have hᵢ₂ := lifted_record_is_lifted l
      exact Lifted.record_fst_optional hᵢ₁ hᵢ₂
    case _ ty =>
      have hᵢ₁ := lifted_type_is_lifted ty
      have hᵢ₂ := lifted_record_is_lifted l
      exact Lifted.record_fst_required hᵢ₁ hᵢ₂

theorem lifted_type_is_lifted (ty : CedarType) :
  Lifted ty ty.liftBoolTypes
:= by
  cases ty <;> simp [CedarType.liftBoolTypes]
  case bool =>
    simp [BoolType.lift]
    exact Lifted.bool
  case int =>
    exact Lifted.int
  case string =>
    exact Lifted.string
  case entity =>
    exact Lifted.entity
  case ext =>
    exact Lifted.ext
  case set ty' =>
    have := lifted_type_is_lifted ty'
    exact Lifted.set this
  case record rty =>
    unfold CedarType.liftBoolTypesRecord
    split
    case _ heq =>
      have : rty = (Data.Map.mk []) := by
        simp [Data.Map.kvs_nil_iff_empty, Data.Map.empty] at heq
        exact heq
      simp [this]
      exact Lifted.record_nil
    case _ a qt l heq =>
      have : rty = (Data.Map.mk ((a, qt)::l)) := by
        cases rty
        simp at heq
        simp [heq]
      simp [this]
      clear this
      unfold QualifiedType.liftBoolTypes
      split
      case _ ty' =>
        have hᵢ := lifted_type_is_lifted ty'
        exact Lifted.record_fst_optional hᵢ (lifted_record_is_lifted l)
      case _ ty' =>
        have hᵢ := lifted_type_is_lifted ty'
        exact Lifted.record_fst_required hᵢ (lifted_record_is_lifted l)
end

theorem lifted_type_is_super_type {ty₁ ty₂ : CedarType} :
  Lifted ty₁ ty₂ → subty ty₁ ty₂
:= by
  intro h
  induction h
  case bool =>
    simp [subty, lub?, lubBool]
  case int =>
    simp [subty, lub?]
  case string =>
    simp [subty, lub?]
  case entity =>
    simp [subty, lub?]
  case ext =>
    simp [subty, lub?]
  case set h hᵢ =>
    simp only [subty] at hᵢ
    simp only [subty, lub?]
    split at hᵢ
    case _ heq =>
      simp [heq, hᵢ]
    case _ => cases hᵢ
  case record_nil =>
    simp [subty, lub?, lubRecordType]
  case record_fst_optional hᵢ₁ hᵢ₂ =>
    simp [subty, lub?]
    simp [subty] at hᵢ₁
    simp [subty, lub?] at hᵢ₂
    split at hᵢ₁
    case _ heq =>
      split at hᵢ₂
      case _ m₁ m₂ _ _ _ _ _ _ heq₁ =>
        simp [lubRecordType, lubQualifiedType, heq]
        simp at hᵢ₂
        simp [hᵢ₂] at heq₁
        generalize h : lubRecordType m₁ m₂ = res
        cases res
        case none =>
          simp [h] at heq₁
        case some =>
          simp [h] at heq₁
          simp [h, hᵢ₁, heq₁]
      case _ => cases hᵢ₂
    case _ => cases hᵢ₁
  case record_fst_required hᵢ₁ hᵢ₂ =>
    simp [subty, lub?]
    simp [subty] at hᵢ₁
    simp [subty, lub?] at hᵢ₂
    split at hᵢ₁
    case _ heq =>
      split at hᵢ₂
      case _ m₁ m₂ _ _ _ _ _ _ heq₁ =>
        simp [lubRecordType, lubQualifiedType, heq]
        simp at hᵢ₂
        simp [hᵢ₂] at heq₁
        generalize h : lubRecordType m₁ m₂ = res
        cases res
        case none =>
          simp [h] at heq₁
        case some =>
          simp [h] at heq₁
          simp [h, hᵢ₁, heq₁]
      case _ => cases hᵢ₂
    case _ => cases hᵢ₁

  /-
  unfold CedarType.liftBoolTypes
  split <;> unfold lub?
  case _ =>
    simp only [lubBool, BoolType.lift, Option.some.injEq, CedarType.bool.injEq, ite_eq_right_iff,
      imp_self]
  case _ =>
    simp only [lifted_type_is_super_type, Option.bind_some_fun]
  case _ m =>
    simp only [do_some]
    induction m
    case nil =>
      simp only [CedarType.liftBoolTypesRecord, lubRecordType, Option.some.injEq, List.nil_eq,
        CedarType.record.injEq, Data.Map.mk.injEq, and_self, exists_eq]
    case cons hᵢ =>
      simp at hᵢ
      simp
      unfold lubRecordType
      split
      case _ heq _ =>
        simp only [reduceCtorEq] at heq
      case _ head tail _ _ k₁ v₁ _ k₂ v₂ _ h₁ h₂ =>
        simp [CedarType.liftBoolTypesRecord] at h₂
        rcases h₂ with ⟨⟨h₂₁, h₂₂⟩, h₂₃⟩
        simp only [List.cons.injEq] at h₁
        rcases h₁ with ⟨h₁₁, h₁₂⟩
        have h : head = (head.fst, head.snd) := by rfl
        rw [h] at h₁₁
        clear h
        simp at h₁₁
        rcases h₁₁ with ⟨h₁₃, h₁₄⟩
        have h : lubQualifiedType v₁ v₂ = v₂ := by
          unfold lubQualifiedType
          split
          case _ ty₁ ty₂ =>
            simp [h₁₄] at h₂₂
            simp [QualifiedType.liftBoolTypes] at h₂₂
            rw [←h₂₂]
            simp only [lifted_type_is_super_type, Option.bind_some_fun]
          case _ ty₁ ty₂ =>
            simp [h₁₄] at h₂₂
            simp [QualifiedType.liftBoolTypes] at h₂₂
            rw [←h₂₂]
            simp only [lifted_type_is_super_type, Option.bind_some_fun]
          case _ => sorry
        rw [←h₂₁, ←h₁₃]
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, h, ← h₁₂, ← h₂₃, hᵢ,
          Option.bind_some_fun, Option.some.injEq]
        rw [←h₂₂]
        simp only [CedarType.liftBoolTypesRecord]
      case _ h => sorry
  case _ =>
    sorry
-/

theorem type_lifting_preserves_instance_of_type {v : Value} {ty : CedarType} :
  InstanceOfType v ty →
  InstanceOfType v ty.liftBoolTypes
:= by
  intro h
  have h' := @lifted_type_is_super_type ty ty.liftBoolTypes (lifted_type_is_lifted ty)
  simp [subty] at h'
  split at h'
  case _ heq =>
    simp at h'
    simp [h'] at heq
    exact @instance_of_lub_left v ty.liftBoolTypes ty ty.liftBoolTypes heq h
  case _ => cases h'
end Cedar.Thm

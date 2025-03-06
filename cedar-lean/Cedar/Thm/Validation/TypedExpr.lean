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
import Cedar.Thm.Validation.Subtyping

/-!
This file contains useful definitions and lemmas about well-typedness of `TypedExpr`
-/

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Data

inductive Var.WellTyped (env : Environment) : Var → CedarType → Prop
  | principal (et : EntityType)
    (h : et = env.reqty.principal) :
    Var.WellTyped env (.principal) (.entity et)
  | resource (et : EntityType)
    (h : et = env.reqty.resource ) :
    Var.WellTyped env (.resource) (.entity et)
  | action (et : EntityType)
    (h : et = env.reqty.action.ty) :
    Var.WellTyped env (.action) (.entity et)
  | context (rt : RecordType)
    (h : rt = env.reqty.context) :
    Var.WellTyped env (.context) (.record rt)

inductive UnaryApp.WellTyped (e : TypedExpr) (ty : CedarType) : UnaryOp → Prop
  | not
    (h₁ : e.typeOf.isBool)
    (h₂ : ty.isBool) :
    WellTyped e ty .not
  | neg
    (h₁ : e.typeOf.isInt)
    (h₂ : ty.isInt) :
    WellTyped e ty .neg
  | isEmpty
    (h₁ : e.typeOf.isSet)
    (h₂ : ty.isBool) :
    WellTyped e ty .isEmpty
  | like (p : Pattern)
    (h₁ : e.typeOf.isString)
    (h₂ : ty.isBool) :
    WellTyped e ty (.like p)

mutual

def ITEWellTyped (env : Environment) (c t e: TypedExpr) (ty : CedarType) : Prop :=
  TypedExpr.WellTyped env c ∧
  match c.typeOf with
  | .bool .tt => TypedExpr.WellTyped env t ∧ t.typeOf = ty
  | .bool .ff => TypedExpr.WellTyped env e ∧ e.typeOf = ty
  | .bool .anyBool =>
    TypedExpr.WellTyped env t ∧
    TypedExpr.WellTyped env e ∧
    IsSubtype t.typeOf ty ∧
    IsSubtype e.typeOf ty
  | _ => False
termination_by 1 + (sizeOf e) + (sizeOf c) + (sizeOf t)
decreasing_by
  all_goals
    omega

def AndWellTyped (env : Environment) (l r: TypedExpr) (ty : CedarType) : Prop :=
  TypedExpr.WellTyped env l ∧
  match l.typeOf, r.typeOf with
  | .bool .ff, _ => ty = .bool .ff
  | .bool bty₁, .bool .tt => TypedExpr.WellTyped env r ∧ ty = .bool bty₁
  | .bool bty₁, .bool bty₂ => TypedExpr.WellTyped env r ∧ ty = .bool bty₂
  | _, _ => False
termination_by 1 + (sizeOf l) + (sizeOf r)

def OrWellTyped (env : Environment) (l r: TypedExpr) (ty : CedarType) : Prop :=
  TypedExpr.WellTyped env l ∧
  match l.typeOf, r.typeOf with
  | .bool .tt, _ => True
  | .bool bty₁, .bool .ff => TypedExpr.WellTyped env r ∧ ty = .bool bty₁
  | .bool bty₁, .bool bty₂ => TypedExpr.WellTyped env r ∧ ty = .bool bty₂
  | _, _ => False
termination_by 1 + (sizeOf l) + (sizeOf r)

def EqWellTyped (ty₁ ty₂ : TypedExpr) (ty : CedarType) : Prop :=
  match ty₁.toExpr, ty₂.toExpr with
  | .lit p₁, .lit p₂ => if p₁ == p₂ then ty = .bool .tt else ty = .bool .ff
  | _, _ => (IsSubtype ty₁.typeOf ty ∧ IsSubtype ty₂.typeOf ty) ∨
    ((ty₁.typeOf.isEntity ∧ ty₂.typeOf.isEntity) → ty = .bool .ff)

def BinaryApp.WellTyped (env : Environment) (op : BinaryOp) (l r: TypedExpr) (ty : CedarType) : Prop :=
  TypedExpr.WellTyped env l ∧ TypedExpr.WellTyped env r ∧
  match op, l.typeOf, r.typeOf with
  | .eq, _, _ => EqWellTyped l r ty
  | _, _, _ => sorry

def TypedExpr.WellTyped (env : Environment) (e : TypedExpr) : Prop :=
  match e with
  | .lit p ty => InstanceOfType (.prim p) ty
  | .var v ty => Var.WellTyped env v ty
  | .ite c e t ty => ITEWellTyped env c e t ty
  | .and l r ty => AndWellTyped env l r ty
  | .or l r ty => OrWellTyped env l r ty
  | .unaryApp op e ty => TypedExpr.WellTyped env e ∧ UnaryApp.WellTyped e ty op
  | _ => False
termination_by sizeOf e
decreasing_by
  all_goals
    simp_wf
    have : sizeOf ty > 0 := by
      cases ty <;> simp <;> omega
    omega
end

theorem well_typed_expr_cannot_go_wrong {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  TypedExpr.WellTyped env ty →
  ∃ v, EvaluatesTo ty.toExpr request entities v ∧ InstanceOfType v ty.typeOf := sorry

theorem type_of_generate_well_typed_typed_expr {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty := by
  cases e <;> simp only [typeOf] <;> intro h₁
  case lit =>
    simp only [typeOfLit]
    split <;> simp [ok]
    case _ =>
      intro h₂ _
      rw [← h₂]
      simp only [TypedExpr.WellTyped]
      exact true_is_instance_of_tt
    case _ =>
      intro h₂ _
      rw [← h₂]
      simp only [TypedExpr.WellTyped]
      exact false_is_instance_of_ff
    case _ =>
      intro h₂ _
      rw [← h₂]
      simp only [TypedExpr.WellTyped]
      exact InstanceOfType.instance_of_int
    case _ =>
      intro h₂ _
      rw [← h₂]
      simp only [TypedExpr.WellTyped]
      exact InstanceOfType.instance_of_string
    case _ =>
      intro h₂
      rename_i uid
      split at h₂
      case _ =>
        simp at h₂
        have ⟨ h₂, _ ⟩ := h₂
        rw [← h₂]
        simp only [TypedExpr.WellTyped]
        have h₄ : InstanceOfEntityType uid uid.ty := by
          simp only [InstanceOfEntityType]
        exact InstanceOfType.instance_of_entity uid uid.ty h₄
      case _ =>
        cases h₂
  case _ => sorry
  case ite c t eₑ =>
    intro h₂
    simp only [typeOfIf] at h₂
    generalize h₃ : typeOf c c₁ env = cᵣ
    cases cᵣ
    case _ =>
      rw [h₃] at h₂
      simp only [Except.bind_err, reduceCtorEq] at h₂
    case _ tuple =>
      replace ⟨tc, _⟩ := tuple
      have h₄ := type_of_generate_well_typed_typed_expr h₁ h₃
      rw [h₃] at h₂
      simp only [Except.bind_ok] at h₂
      split at h₂
      case _ c₃ _ h₅ =>
        generalize h₆ : typeOf t (c₁ ∪ c₃) env = tᵣ
        cases tᵣ <;> rw [h₆] at h₂
        case _ =>
          simp only [Except.bind_err, reduceCtorEq] at h₂
        case _ tuple₁ =>
          replace ⟨ty₁, _⟩ := tuple₁
          simp only [ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at h₂
          replace ⟨h₂, _⟩ := h₂
          rw [h₂] at h₆
          exact type_of_generate_well_typed_typed_expr h₁ h₆
      case _ =>
        exact type_of_generate_well_typed_typed_expr h₁ h₂
      sorry
      sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

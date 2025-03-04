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
import Cedar.Thm.Validation.TypeChecker

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
    (t.typeOf ⊔ e.typeOf) = .some ty
  | _ => False
termination_by 1 + (sizeOf e) + (sizeOf c) + (sizeOf t)
decreasing_by
  all_goals
    omega


def AndWellTyped (env : Environment) (l r: TypedExpr) (ty : CedarType) : Prop :=
  TypedExpr.WellTyped env l ∧
  match l.typeOf, r.typeOf with
  | .bool .ff, _ => True
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
  | _, _ =>
    match ty₁.typeOf ⊔ ty₂.typeOf with
    | .some _ => ty = .bool .anyBool
    | .none   =>
    match ty₁.typeOf, ty₂.typeOf with
    | .entity _, .entity _ => ty = .bool .ff
    | _, _                 => False

def BinaryApp.WellTyped (env : Environment) (op : BinaryOp) (l r: TypedExpr) (ty : CedarType) : Prop :=
  TypedExpr.WellTyped env l ∧ TypedExpr.WellTyped env r ∧
  match op, l.typeOf, r.typeOf with
  | .eq, _, _ₜ => EqWellTyped l r ty
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
  ∃ v, EvaluatesTo ty.toExpr request entities v ∧ InstanceOfType v ty.typeOf := by
  intro h₀ h₁
  cases ty <;> simp [EvaluatesTo, TypedExpr.toExpr, TypedExpr.typeOf, evaluate]
  case lit ty =>
    simp only [TypedExpr.WellTyped] at h₁
    exact h₁
  case var v t =>
    simp only [TypedExpr.WellTyped] at h₁
    cases h₁ <;> simp [evaluate]
    · rename_i et heq
      replace ⟨ h₀, _⟩ := h₀
      simp only [InstanceOfRequestType] at h₀
      replace ⟨ h₀, _⟩ := h₀
      rw [heq]
      exact InstanceOfType.instance_of_entity request.principal env.reqty.principal h₀
    · rename_i et heq
      replace ⟨ h₀, _⟩ := h₀
      simp only [InstanceOfRequestType] at h₀
      replace ⟨ _, ⟨_, ⟨h₀, _⟩ ⟩ ⟩ := h₀
      rw [heq]
      exact InstanceOfType.instance_of_entity request.resource env.reqty.resource h₀
    · rename_i et heq
      replace ⟨ h₀, _⟩ := h₀
      replace ⟨ _, ⟨h₀, ⟨_, _⟩ ⟩ ⟩ := h₀
      rw [heq, h₀]
      exact InstanceOfType.instance_of_entity env.reqty.action env.reqty.action.ty rfl
    · rename_i rt heq
      replace ⟨ h₀, _⟩ := h₀
      replace ⟨ _, ⟨_, ⟨_, h₀⟩ ⟩ ⟩ := h₀
      rw [heq]
      exact h₀
  case ite cond te ee ty =>
    simp only [TypedExpr.WellTyped, ITEWellTyped] at h₁
    replace ⟨h₁, h₂⟩ := h₁
    replace h₁ := well_typed_expr_cannot_go_wrong h₀ h₁
    cases h₁
    rename_i vᵢ hᵢ
    replace ⟨hᵢ, hᵢₜ⟩ := hᵢ
    split at h₂
    case _ heq =>
      simp only [EvaluatesTo] at hᵢ
      rw [heq] at hᵢₜ
      cases hᵢₜ
      case _ b h₃ =>
        simp only [InstanceOfBoolType] at h₃
        sorry
    sorry
    sorry
    sorry
  case and a b t =>
    sorry
  case or a b t => sorry
  case unaryApp op expr t => sorry
  case binaryApp op a b t => sorry
  case getAttr expr attr t => sorry
  case hasAttr expr attr t => sorry
  case set ls t => sorry
  case record m t => sorry
  case call fn args t => sorry


theorem type_of_generate_well_typed_typed_expr {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty := by
  cases e <;> simp only [typeOf] <;> intro h₁ h₂
  case lit =>
    simp only [typeOfLit]
    split <;> simp [ok]
    case _ =>
      intro h₃ _
      rw [← h₃]
      simp only [TypedExpr.WellTyped]
      exact true_is_instance_of_tt
    case _ =>
      intro h₃ _
      rw [← h₃]
      simp only [TypedExpr.WellTyped]
      exact false_is_instance_of_ff
    case _ =>
      intro h₃ _
      rw [← h₃]
      simp only [TypedExpr.WellTyped]
      exact InstanceOfType.instance_of_int
    case _ =>
      intro h₃ _
      rw [← h₃]
      simp only [TypedExpr.WellTyped]
      exact InstanceOfType.instance_of_string
    case _ =>
      intro h₃
      rename_i uid
      split at h₃
      case _ =>
        simp at h₃
        have ⟨ h₃, _ ⟩ := h₃
        rw [← h₃]
        simp only [TypedExpr.WellTyped]
        have h₄ : InstanceOfEntityType uid uid.ty := by
          simp only [InstanceOfEntityType]
        exact InstanceOfType.instance_of_entity uid uid.ty h₄
      case _ =>
        cases h₃
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

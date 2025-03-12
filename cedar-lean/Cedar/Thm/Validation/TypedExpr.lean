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

inductive UnaryApp.WellTyped (x₁ : TypedExpr) (ty : CedarType) : UnaryOp → Prop
  | not
    (h₁ : x₁.typeOf.isBool)
    (h₂ : ty.isBool) :
    WellTyped x₁ ty .not
  | neg
    (h₁ : x₁.typeOf.isInt)
    (h₂ : ty.isInt) :
    WellTyped x₁ ty .neg
  | isEmpty
    (h₁ : x₁.typeOf.isSet)
    (h₂ : ty.isBool) :
    WellTyped x₁ ty .isEmpty
  | like (p : Pattern)
    (h₁ : x₁.typeOf.isString)
    (h₂ : ty.isBool) :
    WellTyped x₁ ty (.like p)

inductive BinaryApp.WellTyped (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType) (env : Environment) : BinaryOp → Prop
  | eq_lit (p₁ : Prim) (p₂ : Prim)
    (h₀ : x₁.toExpr = .lit p₁)
    (h₁ : x₂.toExpr = .lit p₂)
    (h₂ : if p₁ = p₂ then ty = .bool .tt else ty = .bool .ff) :
    WellTyped x₁ x₂ ty env .eq
  | eq
    (h₀ : (x₁.typeOf ⊔ x₂.typeOf).isSome)
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .eq
  | eq_entity (ety₁ : EntityType) (ety₂ : EntityType)
    (h₀ : ety₁ != ety₂)
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂)
    (h₃ : ty = .bool .ff) :
    WellTyped x₁ x₂ ty env .eq
  | memₑ_action (uid₁ : EntityUID) (uid₂ : EntityUID)
    (h₀ : x₁.toExpr = .lit (.entityUID uid₁))
    (h₁ : x₂.toExpr = .lit (.entityUID uid₂))
    (h₂ : env.acts.contains uid₁)
    (h₃ : if env.acts.descendentOf uid₁ uid₂ then ty = .bool .tt else ty = .bool .ff) :
    WellTyped x₁ x₂ ty env .mem
  | memₑ (ety₁ : EntityType) (ety₂ : EntityType)
    (h₀ : x₁.typeOf = .entity ety₁)
    (h₁ : x₂.typeOf = .entity ety₂)
    (h₃ : if env.ets.descendentOf ety₁ ety₂ then ty = .bool .anyBool else ty = .bool .ff) :
    WellTyped x₁ x₂ ty env .mem

inductive TypedExpr.WellTyped (env : Environment) : TypedExpr → Prop
| lit (p : Prim) (ty : CedarType)
  (h : InstanceOfType (.prim p) ty) :
  WellTyped env (.lit p ty)
| var (v : Var)
  (h : Var.WellTyped env var ty) :
  WellTyped env (.var v ty)
| ite (condExpr : TypedExpr) (thenExpr : TypedExpr) (elseExpr : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env condExpr)
  (h₁ : condExpr.typeOf.isBool)
  (h₂ : WellTyped env thenExpr)
  (h₃ : WellTyped env elseExpr)
  (h₄ : thenExpr.typeOf = elseExpr.typeOf ∧ thenExpr.typeOf = ty) :
  WellTyped env (.ite condExpr thenExpr elseExpr ty)
| and_left_ff (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf = .bool .ff) :
  WellTyped env (.and x₁ x₂ (.bool ff))
| and_left_tt (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf = .bool .tt)
  (h₂ : WellTyped env x₂)
  (h₃ : ∃ bty, x₂.typeOf = .bool bty) :
  WellTyped env (.and x₁ x₂ x₂.typeOf)
| and_left_anyBool (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf = .bool .anyBool)
  (h₂ : WellTyped env x₂)
  (h₃ : ∃ bty, x₂.typeOf = .bool bty) :
  WellTyped env (.and x₁ x₂ (.bool anyBool))
| or_left_tt (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf = .bool .tt) :
  WellTyped env (.and x₁ x₂ (.bool tt))
| or_left_ff (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf = .bool .ff)
  (h₂ : WellTyped env x₂)
  (h₃ : ∃ bty, x₂.typeOf = .bool bty) :
  WellTyped env (.and x₁ x₂ x₂.typeOf)
| or_left_anyBool (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf = .bool .anyBool)
  (h₂ : WellTyped env x₂)
  (h₃ : ∃ bty, x₂.typeOf = .bool bty) :
  WellTyped env (.and x₁ x₂ (.bool anyBool))
| unaryApp (x₁ : TypedExpr) (op₁ : UnaryOp) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : UnaryApp.WellTyped x₁ ty op₁) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp (x₁ : TypedExpr) (x₂ : TypedExpr) (op₂ : BinaryOp) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : WellTyped env x₂)
  (h₂ : BinaryApp.WellTyped x₁ x₂ ty env op₂) :
  WellTyped env (.binaryApp op₂ x₁ x₂ ty)
| getAttr_record (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : ∃ rty, x₁.typeOf = .record rty ∧ (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| getAttr_entity (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : ∃ ety, x₁.typeOf = .entity ety ∧ (∃ rty, env.ets.attrs? ety = .some rty ∧ (rty.find? attr).map Qualified.getType = .some ty)) :
  WellTyped env (.getAttr x₁ attr ty)
| hasAttr_record (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : ∃ rty, x₁.typeOf = .record rty ∧ if rty.contains attr then (ty = .bool .tt ∨ ty = .bool .anyBool) else ty = .bool .ff) :
  WellTyped env (.hasAttr x₁ attr ty)
| hasAttr_entity (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : ∃ ety, x₁.typeOf = .entity ety)
  (h₂ : ∃ bty, ty = .bool bty) :
  WellTyped env (.hasAttr x₁ attr ty)
| set (ls : List TypedExpr) (ty : CedarType)
  (h₀ : ∀ x, x ∈ ls → WellTyped env x)
  (h₁ : ∀ x, x ∈ ls → x.typeOf = ty):
  WellTyped env (.set ls ty)
| record (m : List (Attr × TypedExpr)) (ty : CedarType)
  (h₀ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  -- should we require well-formedness of `m` and then rewrite h₁ using quantifiers?
  (h₁ : ∃ rty, ty = .record rty ∧ rty = Map.make (m.map (λ (a, ty) => (a, .required ty.typeOf)))):
  WellTyped env (.record m ty)

theorem typechecked_is_well_typed {v : Value} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  TypedExpr.WellTyped env ty →
  evaluate ty.toExpr request entities = .ok v →
  InstanceOfType v ty.typeOf
:= by
  intro h₀ h₁ h₂
  cases h₁
  case ite condExpr thenExpr elseExpr ty h₃ h₄ h₅ h₆ h₇ =>
    simp [TypedExpr.toExpr, evaluate] at h₂
    simp [CedarType.isBool] at h₄
    split at h₄
    · rename_i heq
      generalize hᵢ₁ : evaluate condExpr.toExpr request entities = res₁
      cases res₁
      · simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
      · rename_i v₁
        have hᵢ₁' := typechecked_is_well_typed h₀ h₃ hᵢ₁
        simp only [heq] at hᵢ₁'
        have ⟨b, hᵢ₁'⟩ := instance_of_bool_is_bool hᵢ₁'
        simp only [hᵢ₁'] at hᵢ₁
        simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
        cases b <;> simp at h₂ <;> simp [TypedExpr.typeOf] <;> have ⟨h₇₁, h₇₂⟩ := h₇
        · have hᵢ₂ := typechecked_is_well_typed h₀ h₆ h₂
          simp only [← h₇₁, h₇₂] at hᵢ₂
          exact hᵢ₂
        · have hᵢ₃ := typechecked_is_well_typed h₀ h₅ h₂
          simp only [h₇₂] at hᵢ₃
          exact hᵢ₃
    · cases h₄
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
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

theorem type_of_generate_well_typed_typed_expr {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty
:= by
  sorry
end Cedar.Thm

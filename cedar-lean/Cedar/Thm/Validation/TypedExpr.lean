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
import Cedar.Thm

/-!
This file contains useful definitions and lemmas about well-typedness of `TypedExpr`
-/

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Data

inductive Var.WellTyped : Var → CedarType → Prop
  | principal (et : EntityType) :
    WellTyped .principal (.entity et)
  | resource (et : EntityType) :
    WellTyped .resource (.entity et)
  | action (et : EntityType) :
    WellTyped .action (.entity et)
  | context (rt : RecordType) :
    WellTyped .context (.record rt)

inductive UnaryApp.WellTyped (x₁ : TypedExpr) (ty : CedarType) : UnaryOp → Prop
  | not
    (h₁ : x₁.typeOf.isBool)
    (h₂ : ty = .bool anyBool) :
    WellTyped x₁ ty .not
  | neg
    (h₁ : x₁.typeOf.isInt)
    (h₂ : ty.isInt) :
    WellTyped x₁ ty .neg
  | isEmpty
    (h₁ : x₁.typeOf.isSet)
    (h₂ : ty = .bool anyBool) :
    WellTyped x₁ ty .isEmpty
  | like (p : Pattern)
    (h₁ : x₁.typeOf.isString)
    (h₂ : ty = .bool anyBool) :
    WellTyped x₁ ty (.like p)

inductive BinaryApp.WellTyped (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType) (env : Environment) : BinaryOp → Prop
  | eq (h₀ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .eq
  | memₑ
    (h₀ : x₁.typeOf.isEntity ∧ x₂.typeOf.isEntity)
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .mem
  | memₛ (ety : EntityType)
    (h₀ : x₁.typeOf.isEntity ∧ x₂.typeOf = .set (.entity ety))
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .mem
  | less
    (h₀ : x₁.typeOf = x₂.typeOf)
    (h₁ : x₁.typeOf.isInt ∨ x₁.typeOf = .ext .datetime ∨ x₁.typeOf = .ext .duration)
    (h₂ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .less
  | lessEq
    (h₀ : x₁.typeOf = x₂.typeOf)
    (h₁ : x₁.typeOf.isInt ∨ x₁.typeOf = .ext .datetime ∨ x₁.typeOf = .ext .duration)
    (h₂ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .lessEq
  | add
    (h₀ : x₁.typeOf.isInt ∧ x₂.typeOf.isInt)
    (h₁ : ty.isInt) :
    WellTyped x₁ x₂ ty env .add
  | sub
    (h₀ : x₁.typeOf.isInt ∧ x₂.typeOf.isInt)
    (h₁ : ty.isInt) :
    WellTyped x₁ x₂ ty env .sub
  | mul
    (h₀ : x₁.typeOf.isInt ∧ x₂.typeOf.isInt)
    (h₁ : ty.isInt) :
    WellTyped x₁ x₂ ty env .mul
  | contains (ety : CedarType)
    (h₀ : x₁.typeOf = ety ∧ x₂.typeOf = .set ety)
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .contains
  | containsAll (ety : CedarType)
    (h₀ : x₁.typeOf = x₁.typeOf ∧ x₁.typeOf = .set ety)
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .containsAll
  | containsAny (ety : CedarType)
    (h₀ : x₁.typeOf = x₁.typeOf ∧ x₁.typeOf = .set ety)
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .containsAny
  | hasTag (ety : EntityType)
    (h₀ : x₁.typeOf = .entity ety ∧ x₂.typeOf.isString)
    (h₁ : ty = .bool .anyBool) :
    WellTyped x₁ x₂ ty env .hasTag
  | getTag (ety : EntityType)
    (h₀ : x₁.typeOf = .entity ety ∧ x₂.typeOf.isString)
    (h₁ : env.ets.tags? ety = .some (.some ty)) :
    WellTyped x₁ x₂ ty env .getTag

inductive Call.WellTyped : CedarType → ExtFun → Prop
  | decimal : WellTyped (.ext .decimal) .decimal
  | lessThan : WellTyped (.bool .anyBool) .lessThan
  | lessThanOrEqual : WellTyped (.bool .anyBool) .lessThanOrEqual
  | greaterThan : WellTyped (.bool .anyBool) .greaterThan
  | greaterThanOrEqual : WellTyped (.bool .anyBool) .greaterThanOrEqual
  | ip : WellTyped (.ext .ipAddr) .ip
  | isIpv4 : WellTyped (.bool .anyBool) .isIpv4
  | isIpv6 : WellTyped (.bool .anyBool) .isIpv6
  | isLoopback : WellTyped (.bool .anyBool) .isLoopback
  | isMulticast : WellTyped (.bool .anyBool) .isMulticast
  | isInRange : WellTyped (.bool .anyBool) .isInRange
  | datetime : WellTyped (.ext .datetime) .datetime
  | duration : WellTyped (.ext .duration) .duration
  | offset : WellTyped (.ext .duration) .offset
  | durationSince : WellTyped (.ext .duration) .durationSince
  | toDate : WellTyped (.ext .datetime) .toDate
  | toTime : WellTyped (.ext .duration) .toTime

inductive TypedExpr.WellTyped (env : Environment) : TypedExpr → Prop
| lit (p : Prim) (ty : CedarType)
  (h : InstanceOfType (.prim p) ty) :
  WellTyped env (.lit p ty)
| var (v : Var)
  (h : Var.WellTyped var ty) :
  WellTyped env (.var v ty)
| ite (condExpr : TypedExpr) (thenExpr : TypedExpr) (elseExpr : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env condExpr)
  (h₁ : condExpr.typeOf.isBool)
  (h₂ : WellTyped env thenExpr)
  (h₃ : WellTyped env elseExpr)
  (h₄ : thenExpr.typeOf = elseExpr.typeOf ∧ thenExpr.typeOf = ty) :
  WellTyped env (.ite condExpr thenExpr elseExpr ty)
| and (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : WellTyped env x₂)
  (h₂ : x₁.typeOf.isBool ∧ x₂.typeOf.isBool)
  (h₃ : ty = .bool .anyBool) :
  WellTyped env (.and x₁ x₂ ty)
| or (x₁ : TypedExpr) (x₂ : TypedExpr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : WellTyped env x₂)
  (h₂ : x₁.typeOf.isBool ∧ x₂.typeOf.isBool)
  (h₃ : ty = .bool .anyBool) :
  WellTyped env (.or x₁ x₂ ty)
| unaryApp (x₁ : TypedExpr) (op₁ : UnaryOp) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : UnaryApp.WellTyped x₁ ty op₁) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp (x₁ : TypedExpr) (x₂ : TypedExpr) (op₂ : BinaryOp) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : WellTyped env x₂)
  (h₂ : BinaryApp.WellTyped x₁ x₂ ty env op₂) :
  WellTyped env (.binaryApp op₂ x₁ x₂ ty)
| hasAttr_entity (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf.isEntity)
  (h₂ : ty = .bool .anyBool) :
  WellTyped env (.hasAttr x₁ attr ty)
| hasAttr_record (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : x₁.typeOf.isRecord)
  (h₂ : ty = .bool .anyBool) :
  WellTyped env (.hasAttr x₁ attr ty)
| getAttr_entity (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : ∃ ety, x₁.typeOf = .entity ety ∧
    ∃ rty, env.ets.attrs? ety = .some rty ∧
      (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| getAttr_record (x₁ : TypedExpr) (attr : Attr) (ty : CedarType)
  (h₀ : WellTyped env x₁)
  (h₁ : ∃ rty, x₁.typeOf = .record rty ∧
    (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| set (ls : List TypedExpr) (ty : CedarType)
  (h₀ : ∀ x, x ∈ ls → WellTyped env x)
  (h₁ : ∀ x, x ∈ ls → x.typeOf = ty):
  WellTyped env (.set ls ty)
| record (m : List (Attr × TypedExpr)) (ty : CedarType)
  (h₀ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  -- should we require well-formedness of `m` and then rewrite h₁ using quantifiers?
  (h₁ : ∃ rty, ty = .record rty ∧ rty = Map.make (m.map (λ (a, ty) => (a, .required ty.typeOf)))):
  WellTyped env (.record m ty)
| call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType)
  (h₀ : ∀ x, x ∈ args → WellTyped env x)
  (h₁ : Call.WellTyped ty xfn) :
  WellTyped env (.call xfn args ty)

theorem typechecked_is_well_typed {v : Value} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  -- do we really need this hypothesis?
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
  case and x₁ x₂ ty h₃ h₄ h₅ h₆ =>
    simp [TypedExpr.toExpr, evaluate] at h₂
    rcases h₅ with ⟨h₅₁, h₅₂⟩
    /-
    rcases is_bool_implies_exists_bool h₅₁ with ⟨bty₁, h₅₁⟩
    rcases is_bool_implies_exists_bool h₅₂ with ⟨bty₂, h₅₂⟩
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁ <;> simp [hᵢ₁, Result.as, Coe.coe, Value.asBool] at h₂
    have hᵢ₁' := typechecked_is_well_typed h₀ h₃ hᵢ₁
    simp [h₅₁] at hᵢ₁'
    rcases instance_of_bool_is_bool hᵢ₁' with ⟨b₁, hᵢ₁'⟩
    simp [hᵢ₁'] at h₂
    cases b₁ <;> simp at h₂ <;> simp [TypedExpr.typeOf, h₆]
    · rw [← h₂] ; exact bool_is_instance_of_anyBool false
    · -- repeat on x₂
      sorry
    -/
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
  case _ => sorry
  case _ => sorry
  case _ => sorry

theorem well_typed_bool {v : Value} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  TypedExpr.WellTyped env ty →
  ty.typeOf.isBool →
  evaluate ty.toExpr request entities = .ok v →
  ∃ b : Bool, v = b
:= by
  intro h₀ h₁ h₂ h₃
  have h₄ := typechecked_is_well_typed h₀ h₁ h₃
  /-
  rcases is_bool_implies_exists_bool h₂ with ⟨bty, h₂⟩
  simp only [h₂] at h₄
  exact instance_of_bool_is_bool h₄
  -/
  sorry

theorem type_of_generate_well_typed_typed_expr {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty
:= by
  sorry
end Cedar.Thm

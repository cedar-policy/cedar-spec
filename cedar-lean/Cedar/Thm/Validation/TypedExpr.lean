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
    (h : et = env.reqty.principal ) :
    Var.WellTyped env (.principal) (.entity et)
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
    UnaryApp.WellTyped e ty .not
  | neg
    (h₁ : e.typeOf.isInt)
    (h₂ : ty.isInt) :
    UnaryApp.WellTyped e ty .neg
  | isEmpty
    (h₁ : e.typeOf.isSet)
    (h₂ : ty.isBool) :
    UnaryApp.WellTyped e ty .isEmpty
  | like (p : Pattern)
    (h₁ : e.typeOf.isString)
    (h₂ : ty.isBool) :
    UnaryApp.WellTyped e ty (.like p)

inductive TypedExpr.WellTyped (env : Environment) : TypedExpr → Prop
  | lit_wt (p : Prim) (ty : CedarType)
    (h : InstanceOfType (.prim p) ty) :
    WellTyped env (.lit p ty)
  | var_wt (v : Var) (ty : CedarType)
    (h : Var.WellTyped env v ty) :
    WellTyped env (.var v ty)
  | ite_wt (ce : TypedExpr) (te : TypedExpr) (ee : TypedExpr)
    (h₁ : WellTyped env ce)
    (h₂ : WellTyped env te)
    (h₃ : WellTyped env ee)
    (h₄ : ce.typeOf.isBool)
    (h₅ : te.typeOf = ee.typeOf) :
    WellTyped env (.ite ce te ee te.typeOf)
  | and_wt (l : TypedExpr) (r : TypedExpr)
    (h₁ : WellTyped env l)
    (h₂ : WellTyped env r)
    (h₃ : l.typeOf.isBool ∧ r.typeOf.isBool) :
    WellTyped env (.and l r l.typeOf)
  | or_wt (l : TypedExpr) (r : TypedExpr)
    (h₁ : WellTyped env l)
    (h₂ : WellTyped env r)
    (h₃ : l.typeOf.isBool ∧ r.typeOf.isBool) :
    WellTyped env (.or l r l.typeOf)
  | unaryApp_wt (op : UnaryOp) (e : TypedExpr) (ty : CedarType)
    (h₁ : WellTyped env e)
    (h₂ : UnaryApp.WellTyped e ty op) :
    WellTyped env (.unaryApp op e ty)
  | binaryApp_wt (op : BinaryOp) (l : TypedExpr) (r : TypedExpr) (ty : CedarType)
    (h₁ : WellTyped env l)
    (h₂ : WellTyped env r) :
    WellTyped env (.binaryApp op l r ty)
  | set_wt (s : List TypedExpr) (ety : CedarType)
    (h₁ : ∀ e, e ∈ s → WellTyped env e)
    (h₂ : ∀ e, e ∈ s → e.typeOf = ety) :
    WellTyped env (.set s (.set et))
  | record_wt (m : List (Attr × TypedExpr)) (rty : RecordType)
    (h₁ : ∀ a e, (a, e) ∈ m → WellTyped env e)
    (h₂ : ∀ a e, (a, e) ∈ m → (a, e.typeOf) ∈ rty.kvs.map λ (a, qt) ↦ (a, qt.getType)) :
    WellTyped env (.record m (.record rty))

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
      exact TypedExpr.WellTyped.lit_wt (.bool true) (.bool .tt) true_is_instance_of_tt
    case _ =>
      intro h₃ _
      rw [← h₃]
      exact TypedExpr.WellTyped.lit_wt (.bool false) (.bool .ff) false_is_instance_of_ff
    case _ =>
      intro h₃ _
      rw [← h₃]
      rename_i i _
      exact TypedExpr.WellTyped.lit_wt (.int i) (.int) InstanceOfType.instance_of_int
    case _ =>
      intro h₃ _
      rw [← h₃]
      rename_i s _
      exact TypedExpr.WellTyped.lit_wt (.string s) (.string) InstanceOfType.instance_of_string
    case _ =>
      intro h₃
      rename_i uid
      split at h₃
      case _ =>
        simp at h₃
        have ⟨ h₃, _ ⟩ := h₃
        rw [← h₃]
        have h₄ : InstanceOfEntityType uid uid.ty := by
          simp only [InstanceOfEntityType]
        exact TypedExpr.WellTyped.lit_wt (.entityUID uid) (.entity uid.ty) (InstanceOfType.instance_of_entity uid uid.ty h₄)
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

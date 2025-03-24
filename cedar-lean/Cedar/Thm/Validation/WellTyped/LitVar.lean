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
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation.WellTyped.TypeLifting
import Cedar.Thm.Validation
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem typechecked_is_well_typed_after_lifting_lit {p : Prim} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  --CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf (Expr.lit p) c₁ env = Except.ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  --intro h₁ h₂ h₃
  intro h₂ h₃
  simp only [typeOf, typeOfLit, List.empty_eq, Function.comp_apply, Bool.or_eq_true, ok] at h₃
  split at h₃ <;> try simp at h₃ ; rcases h₃ with ⟨h₃, _⟩
  · simp only [← h₃, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.bool true)
  · simp only [← h₃, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.bool false)
  · simp only [← h₃, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    rename_i i _
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.int i)
  · simp only [← h₃, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    rename_i s _
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.string s)
  · split at h₃
    · simp only [Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
      rcases h₃ with ⟨h₃, _⟩
      simp only [← h₃, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
      rename_i uid h₄ _
      exact TypedExpr.WellTyped.lit (Prim.WellTyped.entityUID uid h₄)
    · cases h₃

theorem typechecked_is_well_typed_after_lifting_var {v : Var} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  --CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf (Expr.var v) c₁ env = Except.ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  --intro h₁ h₂ h₃
  intro h₂ h₃
  simp only [typeOf, typeOfVar] at h₃
  split at h₃ <;>
  simp only [List.empty_eq, Function.comp_apply] at h₃ <;>
  rcases h₃ with ⟨h₃, _⟩
  · simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    exact TypedExpr.WellTyped.var (Var.WellTyped.principal)
  · simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    exact TypedExpr.WellTyped.var (Var.WellTyped.action)
  · simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    exact TypedExpr.WellTyped.var (Var.WellTyped.resource)
  · simp only [TypedExpr.liftBoolTypes]
    exact TypedExpr.WellTyped.var (Var.WellTyped.context)

theorem well_typed_is_sound_lit
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{p : Prim}
{ty : CedarType}
(h₁ : Prim.WellTyped env p ty)
(h₂ : evaluate (Expr.lit p) request entities = Except.ok v) :
InstanceOfType v (TypedExpr.lit p ty).typeOf
:= by
  simp only [evaluate] at h₂
  cases h₁ <;>
  simp only [TypedExpr.typeOf] <;>
  simp only [Except.ok.injEq] at h₂ <;>
  rw [←h₂]
  case bool => simp only [bool_is_instance_of_anyBool]
  case int => exact InstanceOfType.instance_of_int
  case string => exact InstanceOfType.instance_of_string
  case entityUID uid h =>
    have : InstanceOfEntityType uid uid.ty := by rfl
    exact InstanceOfType.instance_of_entity uid uid.ty this

theorem well_typed_is_sound_var
{v : Value}
{var : Var}
{env : Environment}
{request : Request}
{entities : Entities}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : Var.WellTyped env var ty)
(h₃ : evaluate (Expr.var var) request entities = Except.ok v) :
InstanceOfType v (TypedExpr.var var ty).typeOf
:= by
  cases h₂ <;>
  simp only [TypedExpr.typeOf] <;>
  simp only [TypedExpr.toExpr, evaluate, Except.ok.injEq] at h₃ <;>
  rw [←h₃] <;>
  simp only [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₁
  case principal =>
    rcases h₁ with ⟨⟨h₁, _, _, _⟩, _, _⟩
    exact InstanceOfType.instance_of_entity request.principal env.reqty.principal h₁
  case resource =>
    rcases h₁ with ⟨⟨_, _, h₁, _⟩, _, _⟩
    exact InstanceOfType.instance_of_entity request.resource env.reqty.resource h₁
  case action =>
    rcases h₁ with ⟨⟨_, h₁, _, _⟩, _, _⟩
    simp only [h₁]
    have : InstanceOfEntityType env.reqty.action env.reqty.action.ty := by rfl
    exact InstanceOfType.instance_of_entity env.reqty.action env.reqty.action.ty this
  case context =>
    rcases h₁ with ⟨⟨_, _, _, h₁⟩, _, _⟩
    exact type_lifting_preserves_instance_of_type h₁

end Cedar.Thm

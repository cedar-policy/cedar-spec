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

import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation.WellTyped.TypeLifting

/-!
This file contains well-typedness theorems of `TypedExpr`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec

theorem well_typed_is_sound {v : Value} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  TypedExpr.WellTyped env ty →
  evaluate ty.toExpr request entities = .ok v →
  InstanceOfType v ty.typeOf
:= by
  intro h₀ h₁ h₂
  cases h₁ <;> try simp only [TypedExpr.toExpr, evaluate] at h₂
  case lit p ty h₃ =>
    cases h₃ <;>
    simp only [TypedExpr.typeOf] <;>
    simp only [Except.ok.injEq] at h₂ <;>
    rw [←h₂]
    case bool => simp only [bool_is_instance_of_anyBool]
    case int => exact InstanceOfType.instance_of_int
    case string => exact InstanceOfType.instance_of_string
    case entityUID uid h =>
      have : InstanceOfEntityType uid uid.ty := by rfl
      exact InstanceOfType.instance_of_entity uid uid.ty this
  case var h₃ =>
    cases h₃ <;>
    simp only [TypedExpr.typeOf] <;>
    simp only [TypedExpr.toExpr, evaluate, Except.ok.injEq] at h₂ <;>
    rw [←h₂] <;>
    simp only [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₀
    case principal =>
      rcases h₀ with ⟨⟨h₀, _, _, _⟩, _, _⟩
      exact InstanceOfType.instance_of_entity request.principal env.reqty.principal h₀
    case resource =>
      rcases h₀ with ⟨⟨_, _, h₀, _⟩, _, _⟩
      exact InstanceOfType.instance_of_entity request.resource env.reqty.resource h₀
    case action =>
      rcases h₀ with ⟨⟨_, h₀, _, _⟩, _, _⟩
      simp only [h₀]
      have : InstanceOfEntityType env.reqty.action env.reqty.action.ty := by rfl
      exact InstanceOfType.instance_of_entity env.reqty.action env.reqty.action.ty this
    case context =>
      rcases h₀ with ⟨⟨_, _, _, h₀⟩, _, _⟩
      exact h₀
  case ite x₁ x₂ x₃ h₃ h₄ h₅ h₆ h₇ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok =>
      rename_i v₁
      have hᵢ₁' := well_typed_is_sound h₀ h₃ hᵢ₁
      simp only [h₆] at hᵢ₁'
      have ⟨b, hᵢ₁'⟩ := instance_of_anyBool_is_bool hᵢ₁'
      simp only [hᵢ₁'] at hᵢ₁
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
      have : (TypedExpr.ite x₁ x₂ x₃ x₂.typeOf).typeOf = x₂.typeOf := by
        simp only [TypedExpr.typeOf]
      simp only [this]
      cases b <;> simp at h₂
      case false =>
        have hᵢ₂ := well_typed_is_sound h₀ h₅ h₂
        rw [←h₇] at hᵢ₂
        exact hᵢ₂
      case true =>
        have hᵢ₃ := well_typed_is_sound h₀ h₄ h₂
        exact hᵢ₃
  case and x₁ x₂ h₃ h₄ h₅ h₆ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok =>
      have hᵢ₁' := well_typed_is_sound h₀ h₃ hᵢ₁
      simp only [h₅] at hᵢ₁'
      have ⟨b, hᵢ₁'⟩ := instance_of_anyBool_is_bool hᵢ₁'
      simp only [hᵢ₁'] at hᵢ₁
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
      simp only [TypedExpr.typeOf]
      cases b <;> simp at h₂
      case false =>
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      case true =>
        generalize hᵢ₂ : evaluate x₂.toExpr request entities = res₂
        cases res₂
        case error =>
          simp only [hᵢ₂, Except.map_error, reduceCtorEq] at h₂
        case ok =>
          simp only [hᵢ₂] at h₂
          have hᵢ₂' := well_typed_is_sound h₀ h₄ hᵢ₂
          simp only [h₆] at hᵢ₂'
          have ⟨_, hᵢ₂'⟩ := instance_of_anyBool_is_bool hᵢ₂'
          simp only [hᵢ₂', Except.map_ok, Except.ok.injEq] at h₂
          rw [←h₂]
          simp only [bool_is_instance_of_anyBool]
  case or x₁ x₂ h₃ h₄ h₅ h₆ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok =>
      have hᵢ₁' := well_typed_is_sound h₀ h₃ hᵢ₁
      simp only [h₅] at hᵢ₁'
      have ⟨b, hᵢ₁'⟩ := instance_of_anyBool_is_bool hᵢ₁'
      simp only [hᵢ₁'] at hᵢ₁
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
      simp only [TypedExpr.typeOf]
      cases b <;> simp at h₂
      case true =>
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      case false =>
        generalize hᵢ₂ : evaluate x₂.toExpr request entities = res₂
        cases res₂
        case error =>
          simp only [hᵢ₂, Except.map_error, reduceCtorEq] at h₂
        case ok =>
          simp only [hᵢ₂] at h₂
          have hᵢ₂' := well_typed_is_sound h₀ h₄ hᵢ₂
          simp only [h₆] at hᵢ₂'
          have ⟨_, hᵢ₂'⟩ := instance_of_anyBool_is_bool hᵢ₂'
          simp only [hᵢ₂', Except.map_ok, Except.ok.injEq] at h₂
          rw [←h₂]
          simp only [bool_is_instance_of_anyBool]
  case unaryApp op x₁ ty hᵢ h₃ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok v =>
      simp only [hᵢ₁, apply₁, Except.bind_ok] at h₂
      split at h₂ <;> cases h₃ <;> simp only [TypedExpr.typeOf]
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      · simp only [intOrErr] at h₂
        split at h₂
        · simp only [Except.ok.injEq] at h₂
          rw [←h₂]
          exact InstanceOfType.instance_of_int
        · cases h₂
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      · cases h₂
      · cases h₂
      · cases h₂
      · cases h₂
  case binaryApp op₂ x₁ x₂ ty hᵢ₁ hᵢ₂ h₃ =>
    generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
    generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
    cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₂
    -- case ok.ok
    rename_i v₁ v₂
    simp only [apply₂] at h₂
    simp only [TypedExpr.typeOf]
    split at h₂ <;>
    cases h₃ <;>
    try cases h₂ <;>
    try simp only [bool_is_instance_of_anyBool]
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  case hasAttr_entity ety x₁ attr hᵢ h₃ =>
    generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
    cases res₁ <;> simp [hᵢ'] at h₂
    simp only [hasAttr] at h₂
    sorry
  case hasAttr_record => sorry
  case getAttr_entity => sorry
  case getAttr_record => sorry
  case set => sorry
  case record => sorry
  case call xfn args ty h₃ h₄ => sorry
    /-
    generalize hᵢ : ((args.map₁ λ x => x.val.toExpr).mapM₁ λ x => evaluate x.val request entities) = res₁
    cases res₁ <;> simp [hᵢ] at h₂
    simp only [call, res, gt_iff_lt, ge_iff_le] at h₂
    simp only [TypedExpr.typeOf]
    split at h₂ <;>
    cases h₄
    case _ v _=>
      sorry
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ => sorry
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
  -/

theorem typechecked_is_well_typed_after_lifting {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by sorry

end Cedar.Thm

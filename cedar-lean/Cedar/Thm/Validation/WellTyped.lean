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
    · simp only [intOrErr] at h₂
      split at h₂
      · simp only [Except.ok.injEq] at h₂
        simp [←h₂]
        exact InstanceOfType.instance_of_int
      · cases h₂
    · simp only [intOrErr] at h₂
      split at h₂
      · simp only [Except.ok.injEq] at h₂
        simp [←h₂]
        exact InstanceOfType.instance_of_int
      · cases h₂
    · simp only [intOrErr] at h₂
      split at h₂
      · simp only [Except.ok.injEq] at h₂
        simp [←h₂]
        exact InstanceOfType.instance_of_int
      · cases h₂
    · have hᵢ₂' := well_typed_is_sound h₀ hᵢ₂ hᵢ₂'
      rename_i h₂
      simp only [h₂] at hᵢ₂'
      cases hᵢ₂'
    · simp only [inₛ, do_ok] at h₂
      rcases h₂ with ⟨_, _, h₂⟩
      simp only [← h₂, bool_is_instance_of_anyBool]
    · rename_i uid₁ tag _ _ _ h₃
      simp only [getTag, Data.Map.findOrErr] at h₂
      generalize hᵢ : entities.tags uid₁ = res₁
      cases res₁ <;> rw [hᵢ] at h₂
      case error => simp only [Except.bind_err, reduceCtorEq] at h₂
      case ok =>
        simp only [Except.bind_ok] at h₂
        split at h₂
        · rename_i ht₁ _ _ _ v₁ heq
          simp only [Except.ok.injEq] at h₂
          subst h₂
          have hᵢ₁' := well_typed_is_sound h₀ hᵢ₁ hᵢ₁'
          simp only [ht₁] at hᵢ₁'
          cases hᵢ₁'
          rename_i ht₁
          simp only [InstanceOfEntityType] at ht₁
          simp only [ht₁] at h₃
          simp only [RequestAndEntitiesMatchEnvironment] at h₀
          rcases h₀ with ⟨_, h₀, _⟩
          simp only [InstanceOfEntitySchema] at h₀
          simp only [Entities.tags, do_ok, Data.Map.findOrErr] at hᵢ
          split at hᵢ
          · simp only [Except.ok.injEq, exists_eq_left'] at hᵢ
            rename_i entry heq₁
            have ⟨entry₁, ⟨h₄, _, _, _, h₅⟩⟩ := h₀ uid₁ entry heq₁
            simp [InstanceOfEntityTags] at h₅
            simp [EntitySchema.tags?] at h₃
            rcases h₃ with ⟨_, h₃₁, h₃₂⟩
            simp only [h₄, Option.some.injEq] at h₃₁
            simp only [← h₃₁] at h₃₂
            simp only [h₃₂] at h₅
            simp only [←hᵢ] at heq
            exact h₅ v₁ (Data.Map.in_list_in_values (Data.Map.find?_mem_toList heq))
          · simp only [reduceCtorEq, false_and, exists_const] at hᵢ
        · cases h₂
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
:= by
  intro h₁ h₂ h₃
  cases e
  case lit p =>
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
        sorry
        --exact TypedExpr.WellTyped.lit (Prim.WellTyped.entityUID uid h₄)
      · cases h₃
  case var v =>
    simp only [typeOf, typeOfVar, List.empty_eq, Function.comp_apply, ok] at h₃
    split at h₃ <;>
    simp at h₃ <;>
    rcases h₃ with ⟨h₃, _⟩ <;>
    simp [← h₃, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    · exact TypedExpr.WellTyped.var (Var.WellTyped.principal)
    · exact TypedExpr.WellTyped.var (Var.WellTyped.action)
    · exact TypedExpr.WellTyped.var (Var.WellTyped.resource)
    · sorry
  case ite => sorry
  case and => sorry
  case or => sorry
  case unaryApp => sorry
  case binaryApp => sorry
  case getAttr => sorry
  case hasAttr => sorry
  case set => sorry
  case record => sorry
  case call => sorry

end Cedar.Thm

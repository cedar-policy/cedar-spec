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
import Cedar.Thm.Validation.WellTyped.GetAttr
import Cedar.Thm.Validation.WellTyped.Call
import Cedar.Thm.Validation.WellTyped.Record
import Cedar.Thm.Validation.WellTyped.LitVar
import Cedar.Thm.Validation.WellTyped.Set

/-!
This file contains well-typedness theorems of `TypedExpr`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec

theorem well_typed_is_sound {ty : TypedExpr} {v : Value} {env : Environment} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  TypedExpr.WellTyped env ty →
  evaluate ty.toExpr request entities = .ok v →
  InstanceOfType v ty.typeOf
:= by
  intro h₁ h₂ h₃
  induction h₂ generalizing v <;> simp only [TypedExpr.toExpr] at h₃
  case lit p ty h₄ =>
    exact well_typed_is_sound_lit h₄ h₃
  case var var ty h₄ =>
    exact well_typed_is_sound_var h₁ h₄ h₃
  case ite x₁ x₂ x₃ _ _ _ h₄ h₅ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp only [evaluate] at h₃
    generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
    case ok =>
      rename_i v₁
      specialize hᵢ₁ hᵢ₁'
      simp only [h₄] at hᵢ₁
      clear h₄
      replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
      simp only [hᵢ₁] at hᵢ₁'
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₃
      have h : (TypedExpr.ite x₁ x₂ x₃ x₂.typeOf).typeOf = x₂.typeOf := by
        simp only [TypedExpr.typeOf]
      rw [h]
      clear h
      cases b <;> simp [hᵢ₁'] at h₃
      case false =>
        rw [h₅]
        exact hᵢ₃ h₃
      case true =>
        exact hᵢ₂ h₃
  case and x₁ x₂ _ _ h₄ h₅ hᵢ₁ hᵢ₂ =>
    simp only [evaluate] at h₃
    generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
    case ok =>
      specialize hᵢ₁ hᵢ₁'
      simp only [h₄] at hᵢ₁
      clear h₄
      replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
      simp only [hᵢ₁] at hᵢ₁'
      simp only [Result.as, hᵢ₁', Coe.coe, Value.asBool, Except.bind_ok] at h₃
      simp only [TypedExpr.typeOf]
      cases b <;> simp at h₃
      case false =>
        rw [←h₃]
        simp only [bool_is_instance_of_anyBool]
      case true =>
        generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
        cases res₂
        case error =>
          simp only [hᵢ₂', Except.map_error, reduceCtorEq] at h₃
        case ok =>
          simp only [hᵢ₂'] at h₃
          specialize hᵢ₂ hᵢ₂'
          simp only [h₅] at hᵢ₂
          clear h₅
          replace ⟨_, hᵢ₂⟩ := instance_of_anyBool_is_bool hᵢ₂
          simp only [hᵢ₂, Except.map_ok, Except.ok.injEq] at h₃
          simp only [←h₃, bool_is_instance_of_anyBool]
  case or x₁ x₂ _ _ h₄ h₅ hᵢ₁ hᵢ₂ =>
    simp only [evaluate] at h₃
    generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
    case ok =>
      specialize hᵢ₁ hᵢ₁'
      simp only [h₄] at hᵢ₁
      clear h₄
      replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
      simp only [hᵢ₁] at hᵢ₁'
      simp only [Result.as, hᵢ₁', Coe.coe, Value.asBool, Except.bind_ok] at h₃
      simp only [TypedExpr.typeOf]
      cases b <;> simp at h₃
      case false =>
        generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
        cases res₂
        case error =>
          simp only [hᵢ₂', Except.map_error, reduceCtorEq] at h₃
        case ok =>
          simp only [hᵢ₂'] at h₃
          specialize hᵢ₂ hᵢ₂'
          simp only [h₅] at hᵢ₂
          clear h₅
          replace ⟨_, hᵢ₂⟩ := instance_of_anyBool_is_bool hᵢ₂
          simp only [hᵢ₂, Except.map_ok, Except.ok.injEq] at h₃
          simp only [←h₃, bool_is_instance_of_anyBool]
      case true =>
        rw [←h₃]
        simp only [bool_is_instance_of_anyBool]
  case unaryApp op₁ x₁ ty _ h₄ hᵢ =>
    simp only [evaluate] at h₃
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₃
    case ok v =>
      simp only [hᵢ₁, apply₁, Except.bind_ok] at h₃
      split at h₃ <;> cases h₄ <;> simp only [TypedExpr.typeOf]
      · simp only [Except.ok.injEq] at h₃
        simp only [←h₃, bool_is_instance_of_anyBool]
      · simp only [intOrErr] at h₃
        split at h₃
        · simp only [Except.ok.injEq] at h₃
          rw [←h₃]
          exact InstanceOfType.instance_of_int
        · cases h₃
      · simp only [Except.ok.injEq] at h₃
        simp only [←h₃, bool_is_instance_of_anyBool]
      · simp only [Except.ok.injEq] at h₃
        simp only [←h₃, bool_is_instance_of_anyBool]
      · simp at h₃
        subst h₃
        simp only [bool_is_instance_of_anyBool]
      · cases h₃
      · cases h₃
      · cases h₃
      · cases h₃
      · cases h₃
  case binaryApp op₂ x₁ x₂ ty _ _ h₄ hᵢ₁ hᵢ₂ =>
    simp only [evaluate] at h₃
    generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
    generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
    cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₃
    -- case ok.ok
    rename_i v₁ v₂
    simp only [apply₂] at h₃
    simp only [TypedExpr.typeOf]
    split at h₃ <;>
    cases h₄ <;>
    try cases h₃ <;>
    try simp only [bool_is_instance_of_anyBool]
    · simp only [intOrErr] at h₃
      split at h₃
      · simp only [Except.ok.injEq] at h₃
        simp [←h₃]
        exact InstanceOfType.instance_of_int
      · cases h₃
    · simp only [intOrErr] at h₃
      split at h₃
      · simp only [Except.ok.injEq] at h₃
        simp [←h₃]
        exact InstanceOfType.instance_of_int
      · cases h₃
    · simp only [intOrErr] at h₃
      split at h₃
      · simp only [Except.ok.injEq] at h₃
        simp [←h₃]
        exact InstanceOfType.instance_of_int
      · cases h₃
    · specialize hᵢ₂ hᵢ₂'
      rename_i h₂
      simp only [h₂] at hᵢ₂
      cases hᵢ₂
    · simp only [inₛ, do_ok] at h₃
      rcases h₃ with ⟨_, _, h₃⟩
      simp only [← h₃, bool_is_instance_of_anyBool]
    · rename_i uid₁ tag _ _ h₄ _ _
      simp only [getTag, Data.Map.findOrErr] at h₃
      generalize hᵢ : entities.tags uid₁ = res₁
      cases res₁ <;> rw [hᵢ] at h₃
      case error => simp only [Except.bind_err, reduceCtorEq] at h₃
      case ok =>
        simp only [Except.bind_ok] at h₃
        split at h₃
        · rename_i ht₁ _ _ _ v₁ heq
          simp only [Except.ok.injEq] at h₃
          subst h₃
          specialize hᵢ₁ hᵢ₁'
          simp only [ht₁] at hᵢ₁
          cases hᵢ₁
          rename_i ht₁
          simp only [InstanceOfEntityType] at ht₁
          simp only [ht₁] at h₄
          simp only [RequestAndEntitiesMatchEnvironment] at h₁
          rcases h₁ with ⟨_, h₁, _⟩
          simp only [InstanceOfEntitySchema] at h₁
          simp only [Entities.tags, do_ok, Data.Map.findOrErr] at hᵢ
          split at hᵢ
          · simp only [Except.ok.injEq, exists_eq_left'] at hᵢ
            rename_i entry heq₁
            specialize h₁ uid₁ entry heq₁
            replace ⟨entry₁, ⟨h₅, _, _, _, h₆⟩⟩ := h₁
            simp [InstanceOfEntityTags] at h₆
            simp [EntitySchema.tags?] at h₄
            rcases h₄ with ⟨_, h₃₁, h₃₂⟩
            simp only [h₅, Option.some.injEq] at h₃₁
            simp only [← h₃₁] at h₃₂
            simp only [h₃₂] at h₆
            simp only [←hᵢ] at heq
            have := h₆ v₁ (Data.Map.in_list_in_values (Data.Map.find?_mem_toList heq))
            -- subtype stuff
            sorry
          · simp only [reduceCtorEq, false_and, exists_const] at hᵢ
        · cases h₃
  case hasAttr_entity x₁ _ _ _ _ =>
    simp only [evaluate] at h₃
    generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
    cases res₁ <;> simp [hᵢ'] at h₃
    simp only [hasAttr, do_ok] at h₃
    rcases h₃ with ⟨_, _, h₃⟩
    simp only [← h₃, TypedExpr.typeOf, bool_is_instance_of_anyBool]
  case hasAttr_record x₁ _ _ _ _ =>
    simp only [evaluate] at h₃
    generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
    cases res₁ <;> simp [hᵢ'] at h₃
    simp only [hasAttr, do_ok] at h₃
    rcases h₃ with ⟨_, _, h₃⟩
    simp only [← h₃, TypedExpr.typeOf, bool_is_instance_of_anyBool]
  case getAttr_entity h₄ h₅ h₆ hᵢ =>
    exact well_typed_is_sound_get_attr_entity h₁ hᵢ h₄ h₅ h₆ h₃
  case getAttr_record h₄ h₅ hᵢ=>
    exact well_typed_is_sound_get_attr_record hᵢ h₄ h₅ h₃
  case set ls ty _ h₄ _ hᵢ =>
    exact well_typed_is_sound_set hᵢ h₄ h₃
  case record m rty _ h₄ hᵢ =>
    sorry
    --exact well_typed_is_sound_record hᵢ h₄ h₃
  case call xfn args ty _ h₄ _ =>
    exact well_typed_is_sound_call h₄ h₃

theorem typechecked_is_well_typed_after_lifting_lit
{p : Prim}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr} :
  typeOf (Expr.lit p) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₂
  simp only [typeOf, typeOfLit, List.empty_eq, Function.comp_apply, Bool.or_eq_true, ok] at h₂
  split at h₂ <;> try simp at h₂ ; rcases h₂ with ⟨h₂, _⟩
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.bool true)
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.bool false)
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    rename_i i _
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.int i)
  · simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    rename_i s _
    exact TypedExpr.WellTyped.lit (Prim.WellTyped.string s)
  · split at h₂
    · simp only [Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₂
      rcases h₂ with ⟨h₂, _⟩
      simp only [← h₂, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
      rename_i uid h₄ _
      exact TypedExpr.WellTyped.lit (Prim.WellTyped.entityUID uid h₄)
    · cases h₂

theorem typechecked_is_well_typed_after_lifting_var
{v : Var}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr} :
  typeOf (Expr.var v) c₁ env = Except.ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₂
  simp only [typeOf, typeOfVar] at h₂
  split at h₂ <;>
  {
    simp only [List.empty_eq, Function.comp_apply] at h₂
    rcases h₂ with ⟨h₂, _⟩
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
    constructor
    constructor
  }

theorem typechecked_is_well_typed_after_lifting_ite
{cond thenExpr elseExpr : Expr}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf cond c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ (c₁_1 : Capabilities) {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf thenExpr (c₁ ∪ c₁_1) env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₃ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf elseExpr c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
:
  typeOf (cond.ite thenExpr elseExpr) c₁ env = Except.ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₂
  simp only [typeOf] at h₂
  generalize heq : typeOf cond c₁ env = res₁
  cases res₁
  case error =>
    simp only [heq, Except.bind_err, reduceCtorEq] at h₂
  case ok =>
    simp only [heq, typeOfIf, Except.bind_ok] at h₂
    split at h₂
    case _ ty₁ _ heq₁ =>
      generalize heq₂ : typeOf thenExpr (c₁ ∪ ty₁.snd) env = res₂
      cases res₂
      case error =>
        simp only [heq₂, Except.bind_err, reduceCtorEq] at h₂
      case ok ty' =>
        simp only [heq₂, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at h₂
        rcases h₂ with ⟨h₂, _⟩
        subst h₂
        exact hᵢ₂ ty₁.snd h₁ heq₂
    case _ =>
      exact hᵢ₃ h₁ h₂
    case _ ty₁ _ heq₁ =>
      generalize heq₂ : typeOf thenExpr (c₁ ∪ ty₁.snd) env = res₂
      cases res₂
      case error => simp [heq₂] at h₂
      case ok =>
        simp only [heq₂, Except.bind_ok] at h₂
        generalize heq₃ : typeOf elseExpr c₁ env = res₃
        cases res₃
        case error => simp [heq₃] at h₂
        case ok =>
          simp only [heq₃, Except.bind_ok] at h₂
          split at h₂
          case _ ty₂ ty₃ _ ty' heq₄ =>
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₂
            rcases h₂ with ⟨h₂, _⟩
            subst h₂
            simp [TypedExpr.liftBoolTypes]
            have : ty'.liftBoolTypes = ty₂.fst.liftBoolTypes.typeOf := by
              simp [type_of_after_lifted_is_lifted]
              symm
              exact lifted_type_is_top (lub_left_subty heq₄)
            simp [this]
            clear this
            constructor
            · exact hᵢ₁ h₁ heq
            · exact hᵢ₂ ty₁.snd h₁ heq₂
            · exact hᵢ₃ h₁ heq₃
            · simp only [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes,
              BoolType.lift]
            · simp only [type_of_after_lifted_is_lifted, lifted_type_lub heq₄]
          case _ => simp only [err, reduceCtorEq] at h₂
    case _ => simp only [err, reduceCtorEq] at h₂

theorem typechecked_is_well_typed_after_lifting_and
{x₁ x₂ : Expr}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ (c : Capabilities) {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₂ (c₁ ∪ c) env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.and x₂) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp [typeOf] at h₃
  generalize hₓ₁ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error =>
    simp only [hₓ₁, Except.bind_err, reduceCtorEq] at h₃
  case ok ty₁ =>
    simp only [hₓ₁, Except.bind_ok] at h₃
    simp only [typeOfAnd, List.empty_eq] at h₃
    split at h₃
    case _ heq =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact hᵢ₁ h₁ hₓ₁
    case _ heq =>
      generalize hₓ₂ : typeOf x₂ (c₁ ∪ ty₁.snd) env = res₂
      cases res₂
      case error =>
        simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
      case ok ty₂ =>
        simp only [hₓ₂, Except.bind_ok] at h₃
        split at h₃ <;> try
        {
          rename_i heq₁
          simp [ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
          apply TypedExpr.WellTyped.and
          · exact hᵢ₁ h₁ hₓ₁
          · exact hᵢ₂ ty₁.snd h₁ hₓ₂
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
          · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        }
        case _ => simp only [err, reduceCtorEq] at h₃
    case _ => simp only [err, reduceCtorEq] at h₃

theorem typechecked_is_well_typed_after_lifting_or
{x₁ x₂ : Expr}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₂ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (x₁.or x₂) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp [typeOf] at h₃
  generalize hₓ₁ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error =>
    simp only [hₓ₁, Except.bind_err, reduceCtorEq] at h₃
  case ok ty₁ =>
    simp only [hₓ₁, Except.bind_ok, typeOfOr, List.empty_eq] at h₃
    split at h₃
    case _ heq =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact hᵢ₁ h₁ hₓ₁
    case _ heq =>
      generalize hₓ₂ : typeOf x₂ c₁ env = res₂
      cases res₂
      case error =>
        simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
      case ok ty₂ =>
        simp only [hₓ₂, Except.bind_ok] at h₃
        split at h₃
        case _ heq₁ =>
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp [TypedExpr.liftBoolTypes, heq₁, CedarType.liftBoolTypes, BoolType.lift]
          apply TypedExpr.WellTyped.or
          · exact hᵢ₁ h₁ hₓ₁
          · exact hᵢ₂ h₁ hₓ₂
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
          · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        case _ => simp [err] at h₃
    case _ heq =>
      generalize hₓ₂ : typeOf x₂ c₁ env = res₂
      cases res₂
      case error =>
        simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
      case ok =>
        simp only [hₓ₂, Except.bind_ok] at h₃
        split at h₃ <;> try {
          rename_i heq₁
          simp [ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp [TypedExpr.liftBoolTypes, heq₁, CedarType.liftBoolTypes, BoolType.lift]
          apply TypedExpr.WellTyped.or
          · exact hᵢ₁ h₁ hₓ₁
          · exact hᵢ₂ h₁ hₓ₂
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
          · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
        }
        case _ => simp only [err, reduceCtorEq] at h₃
    case _ => simp only [err, reduceCtorEq] at h₃

theorem typechecked_is_well_typed_after_lifting_unary_app
{x₁: Expr}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities}
{op₁ : UnaryOp}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.unaryApp op₁ x₁) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ : typeOf x₁ c₁ env = res₁
  cases res₁
  case error => simp [hᵢ] at h₃
  case ok ty₁ =>
    simp only [hᵢ, typeOfUnaryApp, ok, List.empty_eq, Function.comp_apply, Except.bind_ok] at h₃
    split at h₃ <;>
    simp [err] at h₃ <;>
    rcases h₃ with ⟨h₃₁, _⟩ <;>
    subst h₃₁ <;>
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift] <;>
    apply TypedExpr.WellTyped.unaryApp <;>
    try exact hᵢ₁ h₁ hᵢ
    case _ h₃ _ =>
      constructor
      simp only [type_of_after_lifted_is_lifted, h₃, CedarType.liftBoolTypes, BoolType.lift]
    case _ h₃ _ =>
      constructor
      simp only [type_of_after_lifted_is_lifted, h₃, CedarType.liftBoolTypes]
    case _ elmTy heq _ =>
      apply @UnaryOp.WellTyped.isEmpty _ elmTy.liftBoolTypes
      simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
    case _ heq _ =>
      constructor
      simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
    case _ ety₁ ety₂ heq _ =>
      apply @UnaryOp.WellTyped.is _ ety₁ ety₂
      simp only [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]

theorem typechecked_is_well_typed_after_lifting_binary_app
{x₁ x₂ : Expr}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities}
{op₂ : BinaryOp}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(hᵢ₁ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes)
(hᵢ₂ : ∀ {c₂ : Capabilities} {ty : TypedExpr},
  RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₂ c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes) :
  typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂) → TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₃
  simp only [typeOf] at h₃
  generalize hᵢ₁' : typeOf x₁ c₁ env = res₁
  generalize hᵢ₂' : typeOf x₂ c₁ env = res₂
  cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₃
  rename_i tc₁ tc₂
  simp only [typeOfBinaryApp] at h₃
  split at h₃
  case _ =>
    simp only [typeOfEq, beq_iff_eq, List.empty_eq, Function.comp_apply] at h₃
    split at h₃
    case _ p₁ p₂ =>
      split at h₃ <;>
      simp [ok] at h₃ <;>
      rcases h₃ with ⟨h₃, _⟩ <;>
      subst h₃ <;>
      simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift] <;>
      constructor
      · exact hᵢ₁ h₁ hᵢ₁'
      · exact hᵢ₂ h₁ hᵢ₂'
      · rcases type_of_lit_is_lit hᵢ₁' with ⟨ty₁, hᵢ₁'⟩
        rw [hᵢ₁']
        rcases type_of_lit_is_lit hᵢ₂' with ⟨ty₂, hᵢ₂'⟩
        rw [hᵢ₂']
        simp [TypedExpr.liftBoolTypes]
        exact BinaryOp.WellTyped.eq_lit
      · exact hᵢ₁ h₁ hᵢ₁'
      · exact hᵢ₂ h₁ hᵢ₂'
      · rcases type_of_lit_is_lit hᵢ₁' with ⟨ty₁, hᵢ₁'⟩
        rw [hᵢ₁']
        rcases type_of_lit_is_lit hᵢ₂' with ⟨ty₂, hᵢ₂'⟩
        rw [hᵢ₂']
        simp [TypedExpr.liftBoolTypes]
        exact BinaryOp.WellTyped.eq_lit
    case _ =>
      split at h₃
      case _ heq =>
        simp [ok] at h₃
        rcases h₃ with ⟨h₃, _⟩
        subst h₃
        simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
        constructor
        · exact hᵢ₁ h₁ hᵢ₁'
        · exact hᵢ₂ h₁ hᵢ₂'
        · apply BinaryOp.WellTyped.eq
          simp only [type_of_after_lifted_is_lifted, lifted_type_lub heq]
      case _ =>
        split at h₃
        case _ ety₁ ety₂ heq₁ heq₂ =>
          simp [ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
          constructor
          · exact hᵢ₁ h₁ hᵢ₁'
          · exact hᵢ₂ h₁ hᵢ₂'
          · apply @BinaryOp.WellTyped.eq_entity _ ety₁ ety₂ <;>
            simp [type_of_after_lifted_is_lifted]
            · simp [heq₁, CedarType.liftBoolTypes]
            · simp [heq₂, CedarType.liftBoolTypes]
        case _ => simp only [err, reduceCtorEq] at h₃
  case _ ety₁ ety₂ heq₁ heq₂ =>
    simp only [ok, List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · apply @BinaryOp.WellTyped.memₑ _ _ _ ety₁ ety₂ <;>
      simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ ety₁ ety₂ heq₁ heq₂ =>
    simp only [ok, List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · apply @BinaryOp.WellTyped.memₛ _ _ _ ety₁ ety₂ <;>
      simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ ety heq₁ heq₂ =>
    simp only [ok, do_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp only [TypedExpr.liftBoolTypes]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · simp only [typeOfHasTag, List.empty_eq] at h₃₁
      split at h₃₁
      case _ =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        subst h₃₁
        simp only [CedarType.liftBoolTypes, BoolType.lift]
        apply @BinaryOp.WellTyped.hasTag _ _ _ ety  <;>
        simp [type_of_after_lifted_is_lifted]
        · simp [heq₁, CedarType.liftBoolTypes]
        · simp [heq₂, CedarType.liftBoolTypes]
      case _ =>
        split at h₃₁ <;> {
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, BoolType.lift]
          apply @BinaryOp.WellTyped.hasTag _ _ _ ety  <;>
          simp [type_of_after_lifted_is_lifted]
          · simp [heq₁, CedarType.liftBoolTypes]
          · simp [heq₂, CedarType.liftBoolTypes]
        }
      case _ =>
        split at h₃₁
        case _ =>
          simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, BoolType.lift]
          apply @BinaryOp.WellTyped.hasTag _ _ _ ety  <;>
          simp [type_of_after_lifted_is_lifted]
          · simp [heq₁, CedarType.liftBoolTypes]
          · simp [heq₂, CedarType.liftBoolTypes]
        case _ => simp [err] at h₃₁
  case _ ety heq₁ heq₂ =>
    simp [ok, do_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [typeOfGetTag] at h₃₁
    split at h₃₁
    case _ => simp [err] at h₃₁
    case _ ty' heq₃ =>
      split at h₃₁
      case _ =>
        simp [ok] at h₃₁
        rcases h₃₁ with ⟨h₃₁, _⟩
        simp [TypedExpr.liftBoolTypes]
        subst h₃₁
        constructor
        · exact hᵢ₁ h₁ hᵢ₁'
        · exact hᵢ₂ h₁ hᵢ₂'
        · apply @BinaryOp.WellTyped.getTag _ _ _ ety ty' <;>
          try simp [type_of_after_lifted_is_lifted]
          · simp [heq₁, CedarType.liftBoolTypes]
          · simp [heq₂, CedarType.liftBoolTypes]
          · exact heq₃
      case _ => simp [err] at h₃₁
    case _ => simp [err] at h₃₁
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · apply BinaryOp.WellTyped.less_datetime <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · apply BinaryOp.WellTyped.less_duration <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
      simp [ok] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ h₁ hᵢ₁'
      · exact hᵢ₂ h₁ hᵢ₂'
      · constructor <;> simp [type_of_after_lifted_is_lifted]
        · simp [heq₁, CedarType.liftBoolTypes]
        · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · apply BinaryOp.WellTyped.lessEq_datetime <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · apply BinaryOp.WellTyped.lessEq_duration <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq₁ heq₂ =>
    simp [ok] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
    constructor
    · exact hᵢ₁ h₁ hᵢ₁'
    · exact hᵢ₂ h₁ hᵢ₂'
    · constructor <;> simp [type_of_after_lifted_is_lifted]
      · simp [heq₁, CedarType.liftBoolTypes]
      · simp [heq₂, CedarType.liftBoolTypes]
  case _ heq =>
    simp [ok, do_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [TypedExpr.liftBoolTypes]
    simp [ifLubThenBool] at h₃₁
    split at h₃₁
    case _ heq₁ =>
      simp [ok] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ h₁ hᵢ₁'
      · exact hᵢ₂ h₁ hᵢ₂'
      · constructor
        simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
        symm
        exact lifted_type_lub heq₁
    case _ => simp [err] at h₃₁
  case _ =>
    simp [ok, do_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [TypedExpr.liftBoolTypes]
    simp [ifLubThenBool] at h₃₁
    split at h₃₁
    case _ ty' heq₁ heq₂ _ _ heq₃ =>
      simp [ok] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ h₁ hᵢ₁'
      · exact hᵢ₂ h₁ hᵢ₂'
      · apply @BinaryOp.WellTyped.containsAll _ _ _ ty'.liftBoolTypes <;>
        simp [type_of_after_lifted_is_lifted, heq₁, heq₂, CedarType.liftBoolTypes]
        exact lifted_type_lub heq₃
    case _ => simp [err] at h₃₁
  case _ =>
    simp [ok, do_ok] at h₃
    rcases h₃ with ⟨a, h₃₁, h₃₂⟩
    subst h₃₂
    simp [TypedExpr.liftBoolTypes]
    simp [ifLubThenBool] at h₃₁
    split at h₃₁
    case _ ty' heq₁ heq₂ _ _ heq₃ =>
      simp [ok] at h₃₁
      rcases h₃₁ with ⟨h₃₁, _⟩
      subst h₃₁
      simp [CedarType.liftBoolTypes, BoolType.lift]
      constructor
      · exact hᵢ₁ h₁ hᵢ₁'
      · exact hᵢ₂ h₁ hᵢ₂'
      · apply @BinaryOp.WellTyped.containsAny _ _ _ ty'.liftBoolTypes <;>
        simp [type_of_after_lifted_is_lifted, heq₁, heq₂, CedarType.liftBoolTypes]
        exact lifted_type_lub heq₃
    case _ => simp [err] at h₃₁
  case _ => simp [err] at h₃

theorem typechecked_is_well_typed_after_lifting
{e : Expr}
{c₁ c₂ : Capabilities}
{env : Environment}
{ty : TypedExpr}
{request : Request}
{entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  intro h₁
  induction e, c₁, env using typeOf.induct generalizing ty c₂
  case _ =>
    exact typechecked_is_well_typed_after_lifting_lit
  case _ =>
    exact typechecked_is_well_typed_after_lifting_var
  case _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact typechecked_is_well_typed_after_lifting_ite h₁ hᵢ₁ hᵢ₂ hᵢ₃
  case _ hᵢ₁ hᵢ₂ =>
    exact typechecked_is_well_typed_after_lifting_and h₁ hᵢ₁ hᵢ₂
  case _ hᵢ₁ hᵢ₂ =>
    exact typechecked_is_well_typed_after_lifting_or h₁ hᵢ₁ hᵢ₂
  case _ hᵢ =>
    exact typechecked_is_well_typed_after_lifting_unary_app h₁ hᵢ
  case _ hᵢ₁ hᵢ₂ =>
    exact typechecked_is_well_typed_after_lifting_binary_app h₁ hᵢ₁ hᵢ₂
  case _ hᵢ => sorry
  case _ hᵢ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
end Cedar.Thm

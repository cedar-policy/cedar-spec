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
    · rename_i uid₁ tag _ _ _ h₄
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
            exact h₆ v₁ (Data.Map.in_list_in_values (Data.Map.find?_mem_toList heq))
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

theorem typechecked_is_well_typed_after_lifting {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  --CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty.liftBoolTypes
:= by
  --intro h₁ h₂ h₃
  intro h₂ h₃
  cases e
  case lit p =>
    exact typechecked_is_well_typed_after_lifting_lit h₂ h₃
  case var v =>
    exact typechecked_is_well_typed_after_lifting_var h₂ h₃
  case ite cond thenExpr elseExpr =>
    simp [typeOf] at h₃
    generalize heq : typeOf cond c₁ env = res₁
    cases res₁
    case error => simp [heq] at h₃
    case ok =>
      simp [heq] at h₃
      simp [typeOfIf] at h₃
      split at h₃
      case _ ty₁ _ heq₁ =>
        generalize heq₂ : typeOf thenExpr (c₁ ∪ ty₁.snd) env = res₂
        cases res₂
        case error =>
          simp [heq₂] at h₃
        case ok =>
          simp [heq₂, ok] at h₃
          rcases h₃ with ⟨h₃, _⟩
          subst h₃
          exact typechecked_is_well_typed_after_lifting h₂ heq₂
      case _ heq₁ =>
        exact typechecked_is_well_typed_after_lifting h₂ h₃
      case _ ty₁ _ heq₁ =>
        generalize heq₂ : typeOf thenExpr (c₁ ∪ ty₁.snd) env = res₂
        cases res₂
        case error => simp [heq₂] at h₃
        case ok =>
          simp [heq₂] at h₃
          generalize heq₃ : typeOf elseExpr c₁ env = res₃
          cases res₃
          case error => simp [heq₃] at h₃
          case ok =>
            simp [heq₃] at h₃
            split at h₃
            case _ ty₂ ty₃ _ ty' heq₄ =>
              simp [ok] at h₃
              rcases h₃ with ⟨h₃, _⟩
              symm at h₃
              subst h₃
              simp [TypedExpr.liftBoolTypes]
              have hᵢ : ty'.liftBoolTypes = ty₂.fst.liftBoolTypes.typeOf := by
                have hᵢ' := lub_left_subty heq₄
                replace hᵢ' := lifted_type_is_top hᵢ'
                simp [type_of_after_lifted_is_lifted]
                symm
                exact hᵢ'
              simp [hᵢ]
              have hᵢ₄ : ty₂.fst.liftBoolTypes.typeOf = ty₃.fst.liftBoolTypes.typeOf := by
                have hᵢ₄₁ := lub_left_subty heq₄
                simp [@lub_comm ty₂.fst.typeOf] at heq₄
                have hᵢ₄₂ := lub_left_subty heq₄
                replace hᵢ₄₁ := lifted_type_is_top hᵢ₄₁
                replace hᵢ₄₂ := lifted_type_is_top hᵢ₄₂
                simp [type_of_after_lifted_is_lifted, hᵢ₄₁, hᵢ₄₂]
              have hᵢ₅ : ty₁.fst.liftBoolTypes.typeOf = (.bool .anyBool) := by
                simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
              exact TypedExpr.WellTyped.ite
                (typechecked_is_well_typed_after_lifting h₂ heq)
                (typechecked_is_well_typed_after_lifting h₂ heq₂)
                (typechecked_is_well_typed_after_lifting h₂ heq₃) hᵢ₅ hᵢ₄
            case _ => simp [err] at h₃
      case _ => simp [err] at h₃
  case and x₁ x₂ =>
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
        simp [ok] at h₃
        rcases h₃ with ⟨h₃, _⟩
        subst h₃
        apply typechecked_is_well_typed_after_lifting h₂ hₓ₁
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
            · exact typechecked_is_well_typed_after_lifting h₂ hₓ₁
            · exact typechecked_is_well_typed_after_lifting h₂ hₓ₂
            · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
            · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
          }
          case _ => simp [err] at h₃
      case _ => simp [err] at h₃
  case or x₁ x₂ =>
    simp [typeOf] at h₃
    generalize hₓ₁ : typeOf x₁ c₁ env = res₁
    cases res₁
    case error =>
      simp only [hₓ₁, Except.bind_err, reduceCtorEq] at h₃
    case ok ty₁ =>
      simp only [hₓ₁, Except.bind_ok] at h₃
      simp only [typeOfOr, List.empty_eq] at h₃
      split at h₃
      case _ heq =>
        simp [ok] at h₃
        rcases h₃ with ⟨h₃, _⟩
        subst h₃
        apply typechecked_is_well_typed_after_lifting h₂ hₓ₁
      case _ heq =>
        generalize hₓ₂ : typeOf x₂ c₁ env = res₂
        cases res₂
        case error =>
          simp only [hₓ₂, Except.bind_err, reduceCtorEq] at h₃
        case ok ty₂ =>
          simp only [hₓ₂, Except.bind_ok] at h₃
          split at h₃
          case _ heq₁ =>
            simp [ok] at h₃
            rcases h₃ with ⟨h₃, _⟩
            subst h₃
            simp [TypedExpr.liftBoolTypes, heq₁, CedarType.liftBoolTypes, BoolType.lift]
            apply TypedExpr.WellTyped.or
            · exact typechecked_is_well_typed_after_lifting h₂ hₓ₁
            · exact typechecked_is_well_typed_after_lifting h₂ hₓ₂
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
            · exact typechecked_is_well_typed_after_lifting h₂ hₓ₁
            · exact typechecked_is_well_typed_after_lifting h₂ hₓ₂
            · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, BoolType.lift]
            · simp [type_of_after_lifted_is_lifted, heq₁, CedarType.liftBoolTypes, BoolType.lift]
          }
          case _ => simp [err] at h₃
      case _ => simp [err] at h₃
  case unaryApp => sorry
  case binaryApp => sorry
  case getAttr x₁ attr =>
    simp [typeOf] at h₃
    generalize hᵢ : typeOf x₁ c₁ env = res₁
    cases res₁
    case error => simp [hᵢ] at h₃
    case ok tc =>
      simp [hᵢ, typeOfGetAttr] at h₃
      split at h₃
      case _ rty heq =>
        simp [ok, do_ok] at h₃
        rcases h₃ with ⟨a, h₃₁, h₃₂⟩
        subst h₃₂
        simp [TypedExpr.liftBoolTypes]
        apply @TypedExpr.WellTyped.getAttr_record _ (.mk (CedarType.liftBoolTypesRecord rty.1))
        · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
        · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
        · simp
          simp [getAttrInRecord] at h₃₁
          split at h₃₁ <;> try
          {
            rename_i aty heq₁
            simp [ok] at h₃₁
            rcases h₃₁ with ⟨h₃₁, _⟩
            exists QualifiedType.liftBoolTypes (.required aty)
            apply And.intro
            · simp [lift_bool_types_record_eq_map_on_values,
                Data.Map.find?_mapOnValues_some QualifiedType.liftBoolTypes heq₁]
            · subst h₃₁
              simp [QualifiedType.liftBoolTypes, Qualified.getType]
          }
          case _ =>
            split at h₃₁
            case _ aty heq₁ _ =>
              simp [ok] at h₃₁
              rcases h₃₁ with ⟨h₃₁, _⟩
              exists QualifiedType.liftBoolTypes (.optional aty)
              apply And.intro
              · simp [lift_bool_types_record_eq_map_on_values,
                Data.Map.find?_mapOnValues_some QualifiedType.liftBoolTypes heq₁]
              · subst h₃₁
                simp [QualifiedType.liftBoolTypes, Qualified.getType]
            case _ => simp [err] at h₃₁
          case _ => simp [err] at h₃₁
      case _ ety heq =>
        split at h₃
        case _ rty heq₁ =>
          simp [ok, do_ok] at h₃
          rcases h₃ with ⟨a, h₃₁, h₃₂⟩
          subst h₃₂
          simp [TypedExpr.liftBoolTypes]
          apply @TypedExpr.WellTyped.getAttr_entity _ ety (.mk (CedarType.liftBoolTypesRecord rty.1))
          · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes]
          · simp [heq₁, RecordType.liftBoolTypes]
          · simp
            -- repeat the proofs on record get attr
            sorry
        case _ => simp [err] at h₃
      case _ => simp [err] at h₃
  case hasAttr x₁ attr =>
    simp [typeOf] at h₃
    generalize hᵢ : typeOf x₁ c₁ env = res₁
    cases res₁
    case error => simp [hᵢ] at h₃
    case ok ty =>
      simp [hᵢ] at h₃
      simp [typeOfHasAttr] at h₃
      split at h₃
      case _ rty heq =>
        simp [ok, do_ok] at h₃
        rcases h₃ with ⟨_, h₃₁, h₃₂⟩
        subst h₃₂
        simp [TypedExpr.liftBoolTypes]
        simp [hasAttrInRecord] at h₃₁
        split at h₃₁
        · split at h₃₁ <;>
          {
            simp [ok] at h₃₁
            rcases h₃₁ with ⟨h₃₁, _⟩
            subst h₃₁
            simp [CedarType.liftBoolTypes, BoolType.lift]
            apply @TypedExpr.WellTyped.hasAttr_record env (RecordType.liftBoolTypes rty)
            · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
            · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
          }
        · simp [ok] at h₃₁
          rcases h₃₁ with ⟨h₃₁, _⟩
          subst h₃₁
          simp [CedarType.liftBoolTypes, BoolType.lift]
          apply @TypedExpr.WellTyped.hasAttr_record env (RecordType.liftBoolTypes rty)
          · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
          · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
      case _ ety heq =>
        split at h₃
        case _ =>
          simp [ok, do_ok] at h₃
          rcases h₃ with ⟨_, h₃₁, h₃₂⟩
          subst h₃₂
          simp [TypedExpr.liftBoolTypes]
          simp [hasAttrInRecord] at h₃₁
          split at h₃₁
          · split at h₃₁ <;>
          {
            simp [ok] at h₃₁
            rcases h₃₁ with ⟨h₃₁, _⟩
            subst h₃₁
            simp [CedarType.liftBoolTypes, BoolType.lift]
            apply @TypedExpr.WellTyped.hasAttr_entity env ety
            · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
            · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
          }
          · simp [ok] at h₃₁
            rcases h₃₁ with ⟨h₃₁, _⟩
            subst h₃₁
            simp [CedarType.liftBoolTypes, BoolType.lift]
            apply @TypedExpr.WellTyped.hasAttr_entity env ety
            · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
            · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
        case _ =>
          split at h₃
          · simp [ok] at h₃
            rcases h₃ with ⟨h₃₁, h₃₂⟩
            subst h₃₁
            simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, BoolType.lift]
            apply @TypedExpr.WellTyped.hasAttr_entity env ety
            · exact typechecked_is_well_typed_after_lifting h₂ hᵢ
            · simp [type_of_after_lifted_is_lifted, heq, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
          · simp [err] at h₃
      case _ => simp [err] at h₃
  case set ls =>
    simp [typeOf] at h₃
    simp [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ env))] at h₃
    sorry
  case record m =>
    simp [typeOf] at h₃
    simp only [List.mapM₂, List.attach₂] at h₃
    simp only [List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c₁ env))] at h₃
    generalize hᵢ : List.mapM (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c₁ env)) m = res₁
    cases res₁
    case error => simp [hᵢ] at h₃
    case ok a =>
      simp [hᵢ, ok] at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp [TypedExpr.liftBoolTypes, CedarType.liftBoolTypes]
      apply TypedExpr.WellTyped.record
      · intro k v h
        simp only [List.map_attach₂ (fun (x : Attr × TypedExpr) => (x.fst, x.snd.liftBoolTypes))] at h
        simp [List.mapM_ok_iff_forall₂] at hᵢ
        replace hᵢ := List.forall₂_implies_all_right hᵢ
        replace h := List.map_mem (k, v) h
        rcases h with ⟨y, h₁, h₂⟩
        simp at h₂
        rcases h₂ with ⟨h₂₁, h₂₂⟩
        replace hᵢ := hᵢ y h₁
        subst h₂₂
        rcases hᵢ with ⟨_, ht, hᵢ⟩
        rename_i ty
        simp [Except.map] at hᵢ
        split at hᵢ
        case _ => cases hᵢ
        case _ heq =>
          simp at hᵢ
          have h₃ : y = (y.fst, y.snd) := by rfl
          rw [h₃] at hᵢ
          simp at hᵢ
          rcases hᵢ with ⟨_, hᵢ⟩
          rw [←hᵢ]
          -- termination proof...
          --exact typechecked_is_well_typed_after_lifting h₂ heq
          sorry
      · sorry
  case call xfn args =>
    exact typechecked_is_well_typed_after_lifting_call h₂ h₃
termination_by e

end Cedar.Thm

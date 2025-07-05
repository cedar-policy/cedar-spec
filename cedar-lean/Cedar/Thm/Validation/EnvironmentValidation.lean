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

import Cedar.Validation.EnvironmentValidator
import Cedar.Thm.Validation.Validator

/-!
This file proves that various `*.validateWellFormed` functions
correctly implement their spec versions.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem entity_type_validate_well_formed_is_sound
  {env : Environment} {ety : EntityType}
  (hok : EntityType.validateWellFormed env ety = .ok ()) :
  EntityType.WellFormed env ety
:= by
  simp only [
    EntityType.validateWellFormed,
    List.any_eq_true, beq_iff_eq, Prod.exists,
    exists_and_right, ite_eq_left_iff, Bool.not_eq_true,
    not_exists, not_and, forall_exists_index,
    reduceCtorEq, imp_false, Classical.not_forall,
    not_imp, Decidable.not_not,
  ] at hok
  simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType]
  cases h : env.ets.contains ety
  · have ⟨uid, entry, hacts, heq⟩ := hok h
    simp only [Bool.false_eq_true, false_or]
    exists uid
    simp only [heq, and_true]
    simp only [Map.toList] at hacts
    have : (List.find? (fun x => x.fst == uid) (Map.kvs env.acts)).isSome
    := by
      apply List.find?_isSome.mpr
      exists (uid, entry)
      simp [hacts]
    cases h : List.find? (fun x => x.fst == uid) (Map.kvs env.acts)
    · simp [h] at this
    · simp [ActionSchema.contains, Map.find?, h]
  · simp [h]

mutual

theorem validate_attrs_well_formed_is_sound
  {env : Environment} {rty} {attr : Attr} {qty : QualifiedType}
  (hwf : (Map.mk rty).WellFormed)
  (hok : validateAttrsWellFormed env rty = .ok ())
  (hfind : (Map.mk rty).find? attr = some qty) :
  QualifiedType.WellFormed env qty
:= by
  cases rty with
  | nil => simp [Map.find?, List.find?] at hfind
  | cons hd tl =>
    simp only [Map.toList, validateAttrsWellFormed] at hok
    cases h : hd.snd with
    | optional attr_ty =>
      simp only [h, bind, Except.bind] at hok
      split at hok
      · contradiction
      · rename_i hwf_hd
        have := (Map.in_list_iff_find?_some hwf).mpr hfind
        simp only [Map.kvs, List.mem_cons] at this
        cases this with
        | inl hhd =>
          have e : qty = hd.snd := by simp [← hhd]
          simp only [e, h]
          constructor
          exact type_validate_well_formed_is_sound hwf_hd
        | inr htl =>
          have hwf_tl : (Map.mk tl).WellFormed
          := Map.wf_implies_tail_wf hwf
          have := (Map.in_list_iff_find?_some hwf_tl).mp htl
          exact validate_attrs_well_formed_is_sound hwf_tl hok this
    | required attr_ty =>
      simp only [h, bind, Except.bind] at hok
      split at hok
      · contradiction
      · rename_i hwf_hd
        have := (Map.in_list_iff_find?_some hwf).mpr hfind
        simp only [Map.kvs, List.mem_cons] at this
        cases this with
        | inl hhd =>
          have e : qty = hd.snd := by simp [← hhd]
          simp only [e, h]
          constructor
          exact type_validate_well_formed_is_sound hwf_hd
        | inr htl =>
          have hwf_tl : (Map.mk tl).WellFormed
          := Map.wf_implies_tail_wf hwf
          have := (Map.in_list_iff_find?_some hwf_tl).mp htl
          exact validate_attrs_well_formed_is_sound hwf_tl hok this
termination_by sizeOf rty
decreasing_by
  any_goals
    have h : rty = hd :: tl := by assumption
    simp [h]
    omega
  -- optional attribute
  any_goals
    have h : rty = hd :: tl := by assumption
    try have hsnd : hd.snd = Qualified.optional attr_ty := by assumption
    try have hsnd : hd.snd = Qualified.required attr_ty := by assumption
    calc
      sizeOf attr_ty < sizeOf hd := by
        simp [←hhd]
        simp [e, hsnd]
        omega
      _ < sizeOf rty := by
        simp [h]
        omega

theorem type_validate_well_formed_is_sound
  {env : Environment} {ty : CedarType}
  (hok : ty.validateWellFormed env = .ok ()) :
  CedarType.WellFormed env ty
:= by
  cases ty with
  | bool _ | int | string | ext _ => constructor
  | entity ety =>
    simp only [CedarType.validateWellFormed] at hok
    constructor
    exact entity_type_validate_well_formed_is_sound hok
  | set ty =>
    simp only [CedarType.validateWellFormed] at hok
    constructor
    exact type_validate_well_formed_is_sound hok
  | record rty =>
    -- Some simplifications
    simp only [
      CedarType.validateWellFormed,
      Except.bind_ok,
      Except.bind_err,
    ] at hok
    cases hwf_rty : rty.wellFormed
    · simp only [hwf_rty, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hok
    simp only [hwf_rty, ↓reduceIte] at hok
    replace hwf_rty := Map.wellFormed_correct.mp hwf_rty
    constructor
    · exact hwf_rty
    -- Soundness of `CedarType.validateWellFormed.validateAttrsWellFormed`
    · intros _ _ hfind
      exact validate_attrs_well_formed_is_sound hwf_rty hok hfind
termination_by sizeOf ty
decreasing_by
  any_goals simp [*]
  · cases rty
    simp
    omega

end

end Cedar.Thm

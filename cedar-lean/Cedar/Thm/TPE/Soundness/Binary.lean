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


import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

import Cedar.Thm.TPE.Soundness.Basic
import Cedar.Thm.TPE.Attrs
import Cedar.Thm.TPE.State

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

/-- If the schema does not declare that an entity can have tags, then it does not have any tags. -/
theorem has_tag_false_of_entity_type_tagless
  {env : TypeEnv} {request : Request} {entities : Entities}
  {uid : EntityUID} {tag : Tag}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (htagless : EntitySchema.tags? env.ets uid.ty = some .none) :
  Spec.hasTag uid tag entities = .ok (.prim (.bool false))
:= by
  have hnone : (entities.tagsOrEmpty uid).find? tag = .none := by
    unfold Entities.tagsOrEmpty ; split
    case _ d hfind =>
      have ⟨_, _, hschema, _⟩ := hwf
      simp only [InstanceOfSchemaEntry] at hschema
      specialize hschema uid d hfind
      cases hschema with
      | inl hents =>
        have ⟨entry, hfind_entry, _, _, _, htags⟩ := hents
        simp only [EntitySchema.tags?, Option.map, hfind_entry,
          Option.some.injEq] at htagless
        simp only [InstanceOfEntityTags, htagless] at htags
        simp only [htags, Map.find?_empty]
      | inr hacts =>
        have ⟨_, htags, _⟩ := hacts
        simp only [htags, Map.find?_empty]
    case _ =>
      exact Map.find?_empty tag
  simp only [Spec.hasTag, Map.contains, hnone, Option.isSome_none]

/-- Two values of distinct entity types cannot be equal. -/
theorem eq_false_of_distinct_entity_types
  {env : TypeEnv} {v₁ v₂ : Value} {ety₁ ety₂ : EntityType}
  (hinst₁ : InstanceOfType env v₁ (.entity ety₁))
  (hinst₂ : InstanceOfType env v₂ (.entity ety₂))
  (hne : ety₁ ≠ ety₂) :
  (v₁ == v₂) = false
:= by
  have ⟨uid₁, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hinst₁
  have ⟨uid₂, hty₂, hv₂⟩ := instance_of_entity_type_is_entity hinst₂
  subst hv₁ hv₂
  simp only [beq_eq_false_iff_ne, ne_eq, Value.prim.injEq, Prim.entityUID.injEq]
  intro heq
  subst heq
  exact hne (hty₁ ▸ hty₂ ▸ rfl)

/-- An entity of type `ety₁` cannot be `in` an entity of type `ety₂` when the schema does not declare `ety₂` an ancestor type of `ety₁`. -/
theorem mem_false_of_cannot_be_inₑ
  {env : TypeEnv} {request : Request} {entities : Entities}
  {v₁ v₂ : Value} {ety₁ ety₂ : EntityType}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hinst₁ : InstanceOfType env v₁ (.entity ety₁))
  (hinst₂ : InstanceOfType env v₂ (.entity ety₂))
  (hdesc : env.descendentOf ety₁ ety₂ = false) :
  Spec.apply₂ .mem v₁ v₂ entities = .ok (Value.prim (Prim.bool false))
:= by
  have ⟨uid₁, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hinst₁
  have ⟨uid₂, hty₂, hv₂⟩ := instance_of_entity_type_is_entity hinst₂
  subst hv₁ hv₂ hty₁ hty₂
  simp only [Spec.apply₂, entity_type_in_false_implies_inₑ_false hwf hdesc]

/-- The set-valued counterpart of `mem_false_of_cannot_be_inₑ`. -/
theorem mem_false_of_cannot_be_inₛ
  {env : TypeEnv} {request : Request} {entities : Entities}
  {v₁ v₂ : Value} {ety₁ ety₂ : EntityType}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hinst₁ : InstanceOfType env v₁ (.entity ety₁))
  (hinst₂ : InstanceOfType env v₂ (.set (.entity ety₂)))
  (hdesc : env.descendentOf ety₁ ety₂ = false) :
  Spec.apply₂ .mem v₁ v₂ entities = .ok (Value.prim (Prim.bool false))
:= by
  have ⟨uid₁, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hinst₁
  have ⟨s, hv₂, _⟩ := instance_of_set_type_is_set hinst₂
  subst hv₁ hv₂ hty₁
  cases s
  rename_i vs
  have ⟨euids, hmap, htys⟩ := entity_set_type_implies_set_of_entities hinst₂
  simp only [Spec.apply₂, Spec.inₛ, Set.mapOrErr, Set.elts, hmap, Except.bind_ok,
    entity_type_in_false_implies_inₛ_false hwf hdesc htys]

/-- Whenever `TPE.inₑ` decides `in` for two concrete UIDs, concrete evaluation agrees. -/
theorem tpe_inₑ_agrees
{es : Entities}
{pes : PartialEntities}
{uid₁ uid₂ : EntityUID}
{b : Bool}
(href : EntitiesRefine es pes)
(hdec : TPE.inₑ uid₁ uid₂ pes = .some b) :
  Spec.inₑ uid₁ uid₂ es = b
:= by
  simp only [TPE.inₑ] at hdec
  split at hdec
  case isTrue heq =>
    simp only [Option.some.injEq] at hdec
    subst hdec heq
    simp [Spec.inₑ]
  case isFalse hneq =>
    simp only [beq_eq_false_iff_ne.mpr hneq, Bool.false_or, Spec.inₑ,
      Option.map_eq_some_iff, PartialEntities.ancestors, PartialEntities.get,
      Option.bind_eq_some_iff] at hdec ⊢
    obtain ⟨anc, ⟨ped, hfind, hanc⟩, hcontains⟩ := hdec
    have hpv := (href uid₁ ped hfind).2.1
    rw [hanc] at hpv
    have hpeq := PartialIsValid.some_inv.mp hpv
    rw [hpeq] at hcontains
    exact hcontains

/-- Whenever `TPE.hasTag` decides `hasTag`, concrete evaluation agrees. -/
theorem tpe_hasTag_agrees
{es : Entities} {pes : PartialEntities} {uid : EntityUID} {tag : Tag} {b : Bool}
(href : EntitiesRefine es pes)
(hdec : TPE.hasTag uid tag pes = .some b) :
  (es.tagsOrEmpty uid).contains tag = b
:= by
  simp only [TPE.hasTag] at hdec
  split at hdec
  case h_1 v hv | h_2 hv | h_3 hv =>
    simp only [Option.some.injEq] at hdec; subst hdec
    obtain ⟨v, hv⟩ := entity_tag_exists href (by rw [hv]; rfl)
    simp only [Map.contains, hv, Option.isSome_some]
  case h_4 ha =>
    simp only [Option.some.injEq] at hdec; subst hdec
    simp only [Map.contains, entity_tag_absent href ha, Option.isSome_none]
  case h_5 => simp at hdec

/-- `getTag` on an entity errors exactly when the (concrete) tag is missing. -/
theorem get_tag_entity_none {es : Entities} {uid : EntityUID} {tag : Tag}
  (h : (es.tagsOrEmpty uid).find? tag = .none) :
  Spec.getTag uid tag es = .error .entityDoesNotExist ∨
  Spec.getTag uid tag es = .error .tagDoesNotExist
:= by
  simp only [Spec.getTag, Entities.tags, Entities.tagsOrEmpty] at *
  cases hf : es.find? uid with
  | none => left; simp [hf, Data.Map.findOrErr, bind, Except.bind]
  | some d =>
    right
    simp only [hf] at h
    simp [hf, Data.Map.findOrErr, h, bind, Except.bind]

/--
If `tryDecideResidual₂` decides a binary operation from the operands' types,
then concrete evaluation agrees.
-/
theorem try_decide_residual₂_sound
{env : TypeEnv}
{op₂ : BinaryOp}
{r₁ r₂ : Residual}
{req : Request}
{es : Entities}
{v : Value}
(hwf : InstanceOfWellFormedEnvironment req es env)
(hwt₁ : Residual.WellTyped env r₁)
(hwt₂ : Residual.WellTyped env r₂)
(hdec : TPE.tryDecideResidual₂ env op₂ r₁ r₂ = .some v) :
  ∃ v₁ v₂, r₁.evaluate req es = .ok v₁ ∧ r₂.evaluate req es = .ok v₂ ∧
    Spec.apply₂ op₂ v₁ v₂ es = .ok v
:= by
  unfold TPE.tryDecideResidual₂ at hdec
  split at hdec
  case isFalse => simp at hdec
  case isTrue hef =>
  simp only [Bool.and_eq_true] at hef
  have hok₁ := error_free_evaluate_ok hwf hwt₁ ((Residual.error_free_spec _).mp hef.left)
  have hok₂ := error_free_evaluate_ok hwf hwt₂ ((Residual.error_free_spec _).mp hef.right)
  rw [Except.isOk_iff_exists] at hok₁ hok₂
  have ⟨v₁, hev₁⟩ := hok₁
  have ⟨v₂, hev₂⟩ := hok₂
  have hinst₁ := residual_well_typed_is_sound hwf hwt₁ hev₁
  have hinst₂ := residual_well_typed_is_sound hwf hwt₂ hev₂
  refine ⟨v₁, v₂, hev₁, hev₂, ?_⟩
  split at hdec
  case h_1 ety₁ ety₂ hty₁ hty₂ =>
    rw [hty₁] at hinst₁ ; rw [hty₂] at hinst₂
    split at hdec
    case isFalse => simp at hdec
    case isTrue hcond =>
    simp only [Option.some.injEq] at hdec
    subst hdec
    exact mem_false_of_cannot_be_inₑ hwf hinst₁ hinst₂ (by simpa using hcond)
  case h_2 ety₁ ety₂ hty₁ hty₂ =>
    rw [hty₁] at hinst₁ ; rw [hty₂] at hinst₂
    split at hdec
    case isFalse => simp at hdec
    case isTrue hcond =>
    simp only [Option.some.injEq] at hdec
    subst hdec
    exact mem_false_of_cannot_be_inₛ hwf hinst₁ hinst₂ (by simpa using hcond)
  case h_3 ety₁ ety₂ hty₁ hty₂ =>
    rw [hty₁] at hinst₁ ; rw [hty₂] at hinst₂
    split at hdec
    case isFalse => simp at hdec
    case isTrue hcond =>
    simp only [Option.some.injEq] at hdec
    subst hdec
    simp only [Spec.apply₂,
      eq_false_of_distinct_entity_types hinst₁ hinst₂ (by simpa using hcond)]
  case h_4 ety hty₁ hty₂ =>
    rw [hty₁] at hinst₁
    have ⟨uid, hety, hv₁⟩ := instance_of_entity_type_is_entity hinst₁
    have ⟨t, hv₂⟩ := instance_of_string_is_string (hty₂ ▸ hinst₂)
    subst hv₁ hv₂ hety
    split at hdec
    case isFalse => simp at hdec
    case isTrue hcond =>
    simp only [Option.some.injEq] at hdec
    subst hdec
    simp only [Spec.apply₂,
      has_tag_false_of_entity_type_tagless hwf (by simpa using hcond)]
  case h_5 => simp at hdec

theorem partial_evaluate_is_sound_binary_app
{op₂ : BinaryOp}
{ty : CedarType}
{x₁ x₂ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hwt₁ : Residual.WellTyped env x₁)
(hwt₂ : Residual.WellTyped env x₂)
(howt : BinaryResidualWellTyped env op₂ x₁ x₂ ty)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate env x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate env x₂ preq pes).evaluate req es)) :
  Except.toOption ((Residual.binaryApp op₂ x₁ x₂ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate env (Residual.binaryApp op₂ x₁ x₂ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₂]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  case _ heq _ =>
    simp [heq, Residual.evaluate] at hᵢ₂
    rcases to_option_right_err hᵢ₂ with ⟨_, hᵢ₂⟩
    simp only [Residual.evaluate, hᵢ₂, Except.bind_err, do_error_to_option]
    simp only [Except.toOption]
  split
  case h_1 hdec =>
    have hwt₁' := partial_eval_preserves_well_typed h₂ h₄ hwt₁
    have hwt₂' := partial_eval_preserves_well_typed h₂ h₄ hwt₂
    have ⟨v₁, v₂, hev₁, hev₂, hres⟩ := try_decide_residual₂_sound h₂ hwt₁' hwt₂' hdec
    have hev₁' : Except.toOption (x₁.evaluate req es) = some v₁ := by
      rw [hᵢ₁, hev₁]; rfl
    have hev₂' : Except.toOption (x₂.evaluate req es) = some v₂ := by
      rw [hᵢ₂, hev₂]; rfl
    rw [to_option_some] at hev₁' hev₂'
    simp [Residual.evaluate, hev₁', hev₂', hres, Except.toOption]
  case h_2 hdec =>
  split
  case _ heq₁ heq₂ =>
    rw [asValue_evaluate_val heq₁] at hᵢ₁
    rw [asValue_evaluate_val heq₂] at hᵢ₂
    replace hᵢ₁ := to_option_right_ok' hᵢ₁
    replace hᵢ₂ := to_option_right_ok' hᵢ₂
    simp [Residual.evaluate, hᵢ₁, hᵢ₂, Spec.apply₂]
    -- TODO: rewrite one of the two binary app evaluation function so that we don't need this amount of case splits.
    split <;> simp [Residual.evaluate]
    any_goals
      simp [intOrErr, someOrError]
      split <;> split
      case _ heq₃ _ _ _ _ heq₄ =>
        simp [Option.bind_eq_some_iff] at heq₄
        rcases heq₄ with ⟨_, heq₄₁, heq₄₂⟩
        subst heq₄₂
        simp [heq₃] at heq₄₁
        subst heq₄₁
        simp [Residual.evaluate]
      case _ heq₃ _ _ _ heq₄ =>
        simp only [heq₃, Option.bind_some, reduceCtorEq] at heq₄
      case _ heq₃ _ _ _ _ heq₄ =>
        simp only [heq₃, Option.bind_none, reduceCtorEq] at heq₄
      case _ =>
        simp only [Except.toOption, Residual.evaluate]
    case _ uid₁ uid₂ =>
      simp [apply₂.self, someOrSelf]
      split
      case _ heq₃ =>
        simp only [Option.bind_eq_some_iff] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp only [Residual.evaluate, tpe_inₑ_agrees h₄.right heq₃₁]
      case _ heq₃ =>
        rw [asValue_some] at heq₁ heq₂
        rw [heq₁.choose_spec, heq₂.choose_spec]
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ =>
      simp [apply₂.self, someOrSelf]
      split
      case _ uid vs _ _ _ _ _ heq₃ =>
        simp only [Option.bind_eq_some_iff] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp [Spec.inₛ]
        cases howt <;>
        (rename_i h₅; have h₆ := residual_well_typed_is_sound h₂ hwt₂ hᵢ₂; rw [h₅] at h₆; cases h₆)
        rename_i h₆
        simp [Data.Set.mapOrErr]
        generalize h₇ : List.mapM Value.asEntityUID vs.elts = res
        cases res
        case _ =>
          rcases List.mapM_error_implies_exists_error h₇ with ⟨v, h₇₁, h₇₂⟩
          specialize h₆ v h₇₁
          rcases instance_of_entity_type_is_entity h₆ with ⟨_, _, h₆⟩
          simp only [Value.asEntityUID, h₆, reduceCtorEq] at h₇₂
        case _ =>
          simp only [Except.bind_ok, Data.Set.any_make]
          simp [TPE.inₛ, Option.bind_eq_some_iff, Data.Set.toList] at heq₃₁
          rcases heq₃₁ with ⟨vs', heq₃₁, heq₃₂⟩
          rw [List.mapM_some_iff_forall₂] at heq₃₁
          have heq₄ : List.Forall₂ (fun x y => x.asEntityUID = .ok y) vs.elts vs' := by
            have : ∀ x y, (Except.toOption ∘ Value.asEntityUID) x = some y → x.asEntityUID = .ok y := by
              intro x y h
              simp [Except.toOption] at h
              split at h <;> cases h
              rename_i heq
              exact heq
            exact List.Forall₂.imp this heq₃₁
          rw [←List.mapM_ok_iff_forall₂] at heq₄
          simp [heq₄] at h₇
          subst h₇
          have : ∀ x b, (TPE.inₑ uid x pes) = .some b → (Spec.inₑ uid x es) = b :=
            λ _ _ h => tpe_inₑ_agrees h₄.right h
          replace heq₃₂ := List.ternary_any_some_implies_any (TPE.inₑ uid · pes) (Spec.inₑ uid · es) this heq₃₂
          subst heq₃₂
          simp only [Residual.evaluate]
      case _ =>
        rw [asValue_some] at heq₁ heq₂
        rw [heq₁.choose_spec, heq₂.choose_spec]
        simp only [Spec.inₛ, Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ uid _ =>
      simp [someOrSelf, apply₂.self]
      split
      case _ b heq =>
        -- `hasTag` decided a value
        rw [Option.bind_eq_some_iff] at heq
        rcases heq with ⟨b', heq₁, heq₂⟩
        simp only [Option.some.injEq] at heq₂
        subst heq₂
        simp only [Spec.hasTag, tpe_hasTag_agrees h₄.right heq₁, Residual.evaluate]
      case _ =>
        rw [asValue_some] at heq₁ heq₂
        rw [heq₁.choose_spec, heq₂.choose_spec]
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ uid tag =>
      have hself : Residual.WellTyped env
          (Residual.binaryApp BinaryOp.getTag (uid : Residual) (tag : Residual) ty) :=
        get_tag_self_well_typed (id₂ := tag)
          (partial_eval_preserves_well_typed h₂ h₄ hwt₁) heq₁ hwt₁ howt
      have hcons : AttrStateConsistent (entityTag pes uid tag)
          (((Residual.binaryApp BinaryOp.getTag (uid : Residual) (tag : Residual) ty).evaluate
            req es).toOption) := by
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok, getTag_toOption]
        exact entity_tag_consistent h₄.2
      simp only [TPE.getTag]
      rw [stateToResidual_sound (ty := ty) h₂ hcons hself rfl]
      simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ => simp [Except.toOption]
  case _ =>
    simp [Residual.evaluate, apply₂.self]
    exact to_option_eq_do₂
      (λ x y => Spec.apply₂ op₂ x y es) hᵢ₁ hᵢ₂


end Cedar.Thm

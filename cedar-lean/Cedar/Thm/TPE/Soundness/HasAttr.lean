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
import Cedar.Thm.TPE.PreservesTypeOf

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

/-- A record value whose type does not declare an attribute `a` does not have `a`. -/
theorem has_attr_false_of_absent_in_record_type
  {env : TypeEnv} {r : Map Attr Value} {rty : RecordType} {a : Attr} {es : Entities}
  (hinst : InstanceOfType env (.record r) (.record rty))
  (hnone : rty.find? a = .none) :
  Spec.hasAttr (.record r) a es = .ok (.prim (.bool false))
:= by
  have habsent := absent_attribute_is_absent hinst hnone
  simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, Map.contains, habsent,
    Option.isSome_none]

/-- If the schema does not declare an attribute `a` for an entity, then it does not have `a`. -/
theorem has_attr_false_of_absent_in_entity_type
  {env : TypeEnv} {request : Request} {entities : Entities}
  {uid : EntityUID} {rty : RecordType} {a : Attr}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hattrs : EntitySchema.attrs? env.ets uid.ty = some rty)
  (hnone : rty.find? a = .none) :
  Spec.hasAttr (.prim (.entityUID uid)) a entities = .ok (.prim (.bool false))
:= by
  have habsent : (entities.attrsOrEmpty uid).find? a = .none := by
    simp only [Entities.attrsOrEmpty]
    split
    case _ d hfind =>
      exact absent_attribute_is_absent (well_typed_entity_attributes hwf hfind hattrs) hnone
    case _ =>
      exact Map.find?_empty a
  simp only [Spec.hasAttr, Spec.attrsOf, Except.bind_ok, Map.contains, habsent, Option.isSome_none]

/--
If `tryDecideHasResidual` decides a `has` expression from the operand's type,
then concrete evaluation agrees.
-/
theorem try_decide_has_residual_sound
{env : TypeEnv}
{r₁ : Residual}
{req : Request}
{es : Entities}
{attr : Attr}
{v : Value}
(hwf : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env r₁)
(hdec : TPE.tryDecideHasResidual env r₁ attr = .some v) :
  ∃ v', r₁.evaluate req es = .ok v' ∧ Spec.hasAttr v' attr es = .ok v
:= by
  unfold TPE.tryDecideHasResidual at hdec
  split at hdec
  case isFalse => simp at hdec
  case isTrue hef =>
  have hok := error_free_evaluate_ok hwf hwt ((Residual.error_free_spec _).mp hef)
  rw [Except.isOk_iff_exists] at hok
  have ⟨v', hev⟩ := hok
  have hinst := residual_well_typed_is_sound hwf hwt hev
  refine ⟨v', hev, ?_⟩
  split at hdec
  case h_1 rty heqty =>
    rw [heqty] at hinst
    have ⟨r, hr⟩ := instance_of_record_type_is_record hinst
    subst hr
    split at hdec
    case isFalse => simp at hdec
    case isTrue hnone =>
    simp only [Option.some.injEq] at hdec
    subst hdec
    exact has_attr_false_of_absent_in_record_type hinst (Option.isNone_iff_eq_none.mp hnone)
  case h_2 ety heqty =>
    rw [heqty] at hinst
    cases hinst
    case instance_of_entity uid hient =>
      split at hdec
      case h_1 rty hattrs =>
        split at hdec
        case isFalse => simp at hdec
        case isTrue hnone =>
        simp only [Option.some.injEq] at hdec
        subst hdec
        have hty : uid.ty = ety := by
          simp only [InstanceOfEntityType] at hient
          exact hient.left.symm
        exact has_attr_false_of_absent_in_entity_type hwf (by rw [hty]; exact hattrs) (Option.isNone_iff_eq_none.mp hnone)
      case h_2 => simp at hdec
  case h_3 => simp at hdec

theorem partial_evaluate_is_sound_has_attr
{env : TypeEnv}
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env x₁)
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate env x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.hasAttr attr (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate env (x₁.hasAttr attr (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.hasAttr]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  split
  case h_1 hdec =>
    have hwt' := partial_eval_preserves_well_typed h₂ h₄ hwt
    have ⟨v, hev, hres⟩ := try_decide_has_residual_sound h₂ hwt' hdec
    have hev₁ : Except.toOption (x₁.evaluate req es) = some v := by
      rw [hᵢ₁, hev]; rfl
    rw [to_option_some] at hev₁
    simp [Residual.evaluate, hev₁, hres, Except.toOption]
  case h_2 =>
  split
  case _ heq =>
    simp [TPE.attrsOf] at heq
    split at heq
    case _ heq₁ =>
      simp only [Option.some.injEq] at heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.hasAttr, Spec.attrsOf, Except.toOption, heq]
    case _ uid _ heq₁ =>
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.hasAttr, Spec.attrsOf, Except.toOption]
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at heq
      rcases heq with ⟨data, heq₂, heq₃⟩
      simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
      rcases h₄ with ⟨_, h₄⟩
      specialize h₄ uid data heq₂
      rcases h₄ with ⟨_, h₄₁, h₄₂, _⟩
      simp only [heq₃, PartialIsValid.some_inv] at h₄₂
      subst h₄₂
      simp [Entities.attrsOrEmpty, h₄₁]
    case _ => cases heq
  case _ =>
    simp [Residual.evaluate]
    exact to_option_eq_do₁ (λ x => Spec.hasAttr x attr es) hᵢ₁

end Cedar.Thm

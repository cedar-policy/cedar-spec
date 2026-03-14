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

import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.WellTyped.Residual.Soundness
import Cedar.Thm.WellTyped.Expr.Typechecking
import Cedar.Thm.TPE.ResidualEval
import Cedar.TPE.Residual
import Cedar.Data.Map

/-!
This file contains well-typedness theorems of `Residual`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec
open Cedar.Spec.Ext
open Cedar.TPE
open Cedar.Data

/-- Successful evaluation of a well-typed residual should produce a value
of corresponding type. -/
theorem residual_well_typed_is_sound {r : Residual} {v : Value} {env : TypeEnv} {request : Request} {entities : Entities} :
  InstanceOfWellFormedEnvironment request entities env →
  Residual.WellTyped env r →
  r.evaluate request entities = .ok v →
  InstanceOfType env v r.typeOf
:= by
  intro h₁ h₂ h₃
  induction h₂ generalizing v <;> simp only [Residual.typeOf]
  case val rv ty h₄ =>
    simp only [Residual.evaluate] at h₃
    cases h₄ with
    | instance_of_bool b bty h =>
      simp only [ResidualValue.evaluate] at h₃; cases h₃; exact .instance_of_bool b bty h
    | instance_of_int =>
      simp only [ResidualValue.evaluate] at h₃; cases h₃; exact .instance_of_int
    | instance_of_string =>
      simp only [ResidualValue.evaluate] at h₃; cases h₃; exact .instance_of_string
    | instance_of_entity e ety h =>
      simp only [ResidualValue.evaluate] at h₃; cases h₃; exact .instance_of_entity e ety h
    | instance_of_set s ty h =>
      simp only [ResidualValue.evaluate] at h₃; cases h₃; exact .instance_of_set s ty h
    | instance_of_ext x xty h =>
      simp only [ResidualValue.evaluate] at h₃; cases h₃; exact .instance_of_ext x xty h
    | instance_of_record r rty h_keys h_present h_required =>
      -- h₃ : (.record r).evaluate request entities = .ok v
      -- Need: InstanceOfType env v (.record rty)
      -- The evaluate of .record r maps each attribute through evaluateAttr
      -- For .present rv entries, evaluateAttr returns rv.evaluate
      -- For .unknown expr ty entries, evaluateAttr returns (.getAttr expr _ ty).evaluate
      -- The result is a Value.record with the evaluated attributes
      -- We need to show this record satisfies InstanceOfType
      sorry
  case var var ty h₄ =>
    exact residual_well_typed_is_sound_var h₁ h₄ h₃
  case ite x₁ x₂ x₃ h₁ h₂ h₃ h₄ h₅ h₆ hᵢ₁ hᵢ₂ =>
    exact residual_well_typed_is_sound_ite h₄ h₅ h₆ hᵢ₁ hᵢ₂ h₃
  case and x₁ x₂ _ _ h₄ h₅ hᵢ₁ hᵢ₂ =>
    exact residual_well_typed_is_sound_and h₄ h₅ hᵢ₁ hᵢ₂ h₃
  case or x₁ x₂ _ _ h₄ h₅ hᵢ₁ hᵢ₂ =>
    exact residual_well_typed_is_sound_or h₄ h₅ hᵢ₁ hᵢ₂ h₃
  case unaryApp op₁ x₁ ty _ h₄ hᵢ₁ =>
    exact residual_well_typed_is_sound_unary_app h₄ hᵢ₁ h₃
  case binaryApp op₂ x₁ x₂ ty _ _ h₄ hᵢ₁ hᵢ₂ =>
    exact residual_well_typed_is_sound_binary_app h₁ h₄ hᵢ₁ hᵢ₂ h₃
  case hasAttr_entity ety x₁ attr h₁ h₂ h₃ =>
    exact residual_well_typed_is_sound_has_attr_entity h₃
  case hasAttr_record rty x₁ attr h₁ h₂ h₃ =>
    exact residual_well_typed_is_sound_has_attr_record h₃
  case getAttr_entity ety rty x₁ attr ty h₄ h₅ h₆ h₇ hᵢ =>
    exact residual_well_typed_is_sound_get_attr_entity h₁ hᵢ h₅ h₆ h₇ h₃
  case getAttr_record rty x₁ attr ty h₄ h₅ h₆ hᵢ =>
    exact residual_well_typed_is_sound_get_attr_record hᵢ h₅ h₆ h₃
  case set ls ty h₄ h₅ h₆ h₇ =>
    exact residual_well_typed_is_sound_set h₇ h₅ h₃
  case record rty m hᵢ₁ h₄ hᵢ =>
    exact residual_well_typed_is_sound_record hᵢ h₄ h₃
  case call xfn args ty _ h₄ _ =>
    exact residual_well_typed_is_sound_call h₄ h₃
  case error ty =>
    -- Error case should not produce a successful result
    simp only [Residual.evaluate] at h₃
    -- h₃ : Except.error Error.extensionError = Except.ok v
    -- This is a contradiction since error ≠ ok
    cases h₃

end Cedar.Thm

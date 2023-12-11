/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.lit` and `.var` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

theorem type_of_lit_is_sound {l : Prim} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₃ : typeOf (Expr.lit l) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.lit l) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.lit l) request entities v ∧ InstanceOfType v ty
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfLit] at h₃
  split at h₃ <;> simp [ok] at h₃
  case h_5;
  split at h₃ <;> try { simp [err] at h₃ }
  simp at h₃
  all_goals {
    rcases h₃ with ⟨h₃, h₄⟩; rw [←h₃, ←h₄]; constructor
    case left => exact empty_guarded_capabilities_invariant
    case right => first |
      exact true_is_instance_of_tt |
      exact false_is_instance_of_ff |
      apply InstanceOfType.instance_of_int |
      apply InstanceOfType.instance_of_string |
      apply InstanceOfType.instance_of_entity; simp [InstanceOfEntityType]
  }

theorem type_of_var_is_sound {var : Var} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.var var) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.var var) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.var var) request entities v ∧ InstanceOfType v ty
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfVar] at h₃
  rcases h₂ with ⟨h₂, _⟩
  simp [InstanceOfRequestType] at h₂
  split at h₃ <;> simp <;> simp [ok] at h₃ <;>
  rcases h₃ with ⟨h₃, h₄⟩ <;> rw [←h₃, ←h₄] <;> constructor <;>
  try { exact empty_guarded_capabilities_invariant }
  case intro.h_1.intro.right =>
    apply InstanceOfType.instance_of_entity; simp [h₂]
  case intro.h_2.intro.right =>
    apply InstanceOfType.instance_of_entity
    simp [h₂, InstanceOfEntityType]
  case intro.h_3.intro.right =>
    apply InstanceOfType.instance_of_entity; simp [h₂]
  case intro.h_4.intro.right =>
    simp [h₂]

end Cedar.Thm

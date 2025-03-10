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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.binaryApp .getTag` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_getTag_inversion {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .getTag x₁ x₂) c₁ env = .ok (ty, c₂)) :
  c₂ = [] ∧
  ∃ ety c₁' c₂',
    (typeOf x₁ c₁ env).typeOf = .ok (.entity ety, c₁') ∧
    (typeOf x₂ c₁ env).typeOf = .ok (.string, c₂') ∧
    env.ets.tags? ety = some (some ty.typeOf) ∧
    (x₁, .tag x₂) ∈ c₁
:= by
  simp only [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp only [h₂, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  cases h₃ : typeOf x₂ c₁ env <;> simp only [h₃, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  rename_i tyc₁ tyc₂
  cases tyc₁
  cases tyc₂
  rename_i ty₁ c₁' ty₂ c₂'
  simp only at h₁
  cases h₄ : ty₁.typeOf <;> simp [typeOfBinaryApp, err, reduceCtorEq, h₄] at h₁
  cases h₅ : ty₂.typeOf <;> simp [typeOfBinaryApp, err, reduceCtorEq, h₅] at h₁
  rename_i ety
  simp only [typeOfGetTag, List.empty_eq] at h₁
  split at h₁ <;> simp only [ok, err, Except.bind_err, reduceCtorEq] at h₁
  split at h₁ <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₁
  rename_i h₆ h₇
  replace ⟨h₁, h₁'⟩ := h₁
  subst h₁ h₁'
  simp only [true_and]
  exists ety
  simp only [ResultType.typeOf, Except.map, h₄, h₅, h₆, h₇]
  simp [TypedExpr.typeOf]

theorem type_of_getTag_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .getTag x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .getTag x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .getTag x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  replace ⟨hc, ety, c₁', c₂', h₃, h₄, h₅, h₆⟩ := type_of_getTag_inversion h₃
  subst hc
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  replace ⟨_, v₁, ih₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  replace ⟨_, v₂, ih₂, hty₂⟩ := ih₂ h₁ h₂ h₄
  simp only [EvaluatesTo] at *
  simp only [GuardedCapabilitiesInvariant, evaluate]
  rcases ih₁ with ih₁ | ih₁ | ih₁ | ih₁ <;>
  simp only [ih₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_is_inhabited)
  rcases ih₂ with ih₂ | ih₂ | ih₂ | ih₂ <;>
  simp only [ih₂, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_is_inhabited)
  rw [hl₃] at hty₁
  replace ⟨uid, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hty₁
  rw [hl₄] at hty₂
  replace ⟨s, hv₂⟩ := instance_of_string_is_string hty₂
  subst hv₁ hv₂ hty₁
  simp only [apply₂, hasTag, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or, exists_eq_left']
  simp only [getTag, Entities.tags]
  have hf₁ := Map.findOrErr_returns entities uid Error.entityDoesNotExist
  rcases hf₁ with ⟨d, hf₁⟩ | hf₁ <;>
  simp only [hf₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_self, or_false, true_and,
    type_is_inhabited, and_self, reduceCtorEq]
  rw [Map.findOrErr_ok_iff_find?_some] at hf₁
  replace ⟨entry, hf₂, _, _, _, h₂⟩  := h₂.right.left uid d hf₁
  simp only [InstanceOfEntityTags] at h₂
  simp only [EntitySchema.tags?, Option.map_eq_some'] at h₅
  replace ⟨_, h₅, h₇⟩ := h₅
  simp only [hf₂, Option.some.injEq] at h₅
  subst h₅
  simp only [EntitySchemaEntry.tags?] at h₂ h₇
  split at h₇
  simp only [h₇] at h₂
  have hf₃ := Map.findOrErr_returns d.tags s Error.tagDoesNotExist
  rcases hf₃ with ⟨v, hf₃⟩ | hf₃ <;>
  simp only [hf₃, false_implies, Except.error.injEq, or_self, false_and, exists_const, and_false,
    Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
  · simp only [← List.empty_eq, empty_capabilities_invariant request entities, implies_true, true_and, reduceCtorEq]
    apply h₂
    exact Map.findOrErr_ok_implies_in_values hf₃
  · replace h₁ := h₁.right x₁ x₂ h₆
    simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
      Value.prim.injEq, Prim.bool.injEq, false_or, reduceCtorEq] at h₁
    simp only [Entities.tagsOrEmpty, hf₁, Map.contains_iff_some_find?] at h₁
    replace ⟨_, h₁⟩ := h₁
    simp only [Map.findOrErr_err_iff_find?_none, h₁, reduceCtorEq] at hf₃
  · cases h₇

end Cedar.Thm

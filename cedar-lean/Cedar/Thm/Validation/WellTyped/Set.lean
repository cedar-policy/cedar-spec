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

import Cedar.Validation.TypedExpr
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem well_typed_is_sound_set
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{ls : List TypedExpr}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : ∀ (x : TypedExpr), x ∈ ls → WellTypedIsSound x)
(h₃ : ∀ (x : TypedExpr), x ∈ ls → TypedExpr.WellTyped env x)
(h₄ : ∀ (x : TypedExpr), x ∈ ls → x.typeOf = ty)
(h₅ : (do
  let vs ← (ls.map₁ λ x => x.val.toExpr).mapM₁ λ x => evaluate x.val request entities
  Except.ok (Value.set (Data.Set.make vs))) = Except.ok v)
: InstanceOfType v (TypedExpr.set ls ty.set).typeOf
:= by
  simp only [do_ok] at h₅
  rcases h₅ with ⟨v₁, h₅₁, h₅₂⟩
  subst h₅₂
  rw [List.map₁_eq_map, List.mapM₁_eq_mapM (λ x => evaluate x request entities)] at h₅₁
  simp only [List.mapM_map, List.mapM_ok_iff_forall₂] at h₅₁
  have h₆ := List.forall₂_implies_all_right h₅₁
  simp only [TypedExpr.typeOf]
  simp only [WellTypedIsSound] at h₂
  have hₛ : ∀ v, v ∈ (Data.Set.make v₁) → InstanceOfType v ty := by
    intro v h
    rw [←Data.Set.make_mem] at h
    obtain ⟨x, hₓ₁, hₓ₂⟩ := h₆ v h
    have h' := h₃ x hₓ₁
    have h₂' := h₂ x hₓ₁ h₁ (h₃ x hₓ₁) hₓ₂
    rw [h₄ x hₓ₁] at h₂'
    exact h₂'
  exact InstanceOfType.instance_of_set (Data.Set.make v₁) ty hₛ

end Cedar.Thm

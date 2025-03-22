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
{request : Request}
{entities : Entities}
{ls : List TypedExpr}
{ty : CedarType}
(h₁ : ∀ (x : TypedExpr), x ∈ ls → ∀ (v : Value), evaluate x.toExpr request entities = Except.ok v → InstanceOfType v x.typeOf)
(h₂ : ∀ (x : TypedExpr), x ∈ ls → x.typeOf = ty)
(h₃ : evaluate (Expr.set (ls.map₁ λ x => x.val.toExpr)) request entities = Except.ok v)
: InstanceOfType v (TypedExpr.set ls ty.set).typeOf
:= by
  simp only [evaluate, do_ok] at h₃
  obtain ⟨v₁, h₃₁, h₃₂⟩ := h₃
  subst h₃₂
  rw [List.map₁_eq_map, List.mapM₁_eq_mapM (λ x => evaluate x request entities)] at h₃₁
  simp only [List.mapM_map, List.mapM_ok_iff_forall₂] at h₃₁
  have h₄ := List.forall₂_implies_all_right h₃₁
  simp only [TypedExpr.typeOf]
  have hₛ : ∀ v, v ∈ (Data.Set.make v₁) → InstanceOfType v ty := by
    intro v h
    rw [←Data.Set.make_mem] at h
    obtain ⟨x, hₓ₁, hₓ₂⟩ := h₄ v h
    have h' := h₁ x hₓ₁ v hₓ₂
    rw [h₂ x hₓ₁] at h'
    exact h'
  exact InstanceOfType.instance_of_set (Data.Set.make v₁) ty hₛ

end Cedar.Thm

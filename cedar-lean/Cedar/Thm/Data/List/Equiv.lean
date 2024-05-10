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

import Cedar.Data.List

namespace List

open Cedar.Data

/-! ### Equiv -/

def Equiv {α} (a b : List α) : Prop :=
  a ⊆ b ∧ b ⊆ a

infix:50 " ≡ " => Equiv

theorem Equiv.refl {a : List α} :
  a ≡ a
:= by unfold List.Equiv; simp only [Subset.refl, and_self]

theorem Equiv.symm {a b : List α} :
  a ≡ b → b ≡ a
:= by unfold List.Equiv; simp only [and_imp]; intro h₁ h₂; simp [h₁, h₂]

theorem Equiv.trans {a b c : List α} :
  a ≡ b → b ≡ c → a ≡ c
:= by
  unfold List.Equiv
  simp only [and_imp]
  intro h₁ h₂ h₃ h₄
  apply And.intro
  exact List.Subset.trans h₁ h₃
  exact List.Subset.trans h₄ h₂

theorem cons_equiv_cons (x : α) (xs ys : List α) :
  xs ≡ ys → x :: xs ≡ x :: ys
:= by
  unfold List.Equiv
  intro h₁
  have ⟨h₁, h₂⟩ := h₁
  apply And.intro
  all_goals {
    apply List.cons_subset_cons; assumption
  }

theorem dup_head_equiv (x : α) (xs : List α) :
  x :: x :: xs ≡ x :: xs
:= by unfold List.Equiv; simp [List.subset_def]

theorem swap_cons_cons_equiv (x₁ x₂ : α) (xs : List α) :
  x₁ :: x₂ :: xs ≡ x₂ :: x₁ :: xs
:= by
  unfold List.Equiv
  simp only [subset_def, mem_cons, forall_eq_or_imp, true_or, or_true, true_and]
  apply And.intro
  all_goals { intro a h₁; simp [h₁] }

theorem filter_equiv (f : α → Bool) (xs ys : List α) :
  xs ≡ ys → xs.filter f ≡ ys.filter f
:= by
  simp only [Equiv, subset_def, and_imp]
  intros h₁ h₂
  apply And.intro <;>
  intro a h₃ <;>
  rw [mem_filter] <;> rw [mem_filter] at h₃
  exact And.intro (h₁ h₃.left) h₃.right
  exact And.intro (h₂ h₃.left) h₃.right

theorem map_equiv (f : α → β) (xs ys : List α) :
  xs ≡ ys → xs.map f ≡ ys.map f
:= by
  intro h
  have ⟨a, b⟩ := h
  apply And.intro <;>
  simp only [subset_def, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] <;>
  intro p h <;>
  exists p <;>
  rw [List.subset_def] at a b <;>
  simp only [and_true]
  · exact a h
  · exact b h

theorem filterMap_equiv (f : α → Option β) (xs ys : List α) :
  xs ≡ ys → xs.filterMap f ≡ ys.filterMap f
:= by
  simp only [Equiv, subset_def, mem_filterMap, forall_exists_index, and_imp]
  intros h₁ h₂
  apply And.intro <;>
  intro b a h₃ h₄ <;>
  exists a <;>
  simp only [h₄, and_true]
  · exact h₁ h₃
  · exact h₂ h₃

end List

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

/-! ### filterMap -/

/--
  our own variant of map_congr, for filterMap
-/
theorem filterMap_congr {f g : α → Option β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → filterMap f l = filterMap g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [filterMap, filterMap, h₁, filterMap_congr h₂]

theorem filterMap_empty_iff_all_none {f : α → Option β} {xs : List α} :
  xs.filterMap f = [] ↔ ∀ x ∈ xs, f x = none
:= by
  constructor
  case mp =>
    induction xs
    case nil =>
      simp only [filterMap_nil, not_mem_nil, false_implies, implies_true, imp_self]
    case cons hd tl ih =>
      intro h₁ a h₂
      simp only [List.filterMap_cons] at h₁
      split at h₁ <;> rename_i h₃
      · rcases (List.mem_cons.mp h₂) with h₄ | h₄
        · subst h₄ ; assumption
        · apply ih h₁ a ; assumption
      · simp only at h₁
  case mpr =>
    intro h₁
    induction xs
    case nil => simp only [filterMap_nil]
    case cons hd tl ih =>
      simp only [List.filterMap_cons]
      split
      case h_1 =>
        apply ih ; clear ih
        intro a h₂
        apply h₁ a
        exact List.mem_cons_of_mem hd h₂
      case h_2 b h₂ =>
        exfalso
        specialize h₁ hd
        simp only [mem_cons, true_or, forall_const] at h₁
        simp [h₁] at h₂

theorem filterMap_nonempty_iff_exists_some {f : α → Option β} {xs : List α} :
  xs.filterMap f ≠ [] ↔ ∃ x ∈ xs, (f x).isSome
:= by
  constructor
  case mp =>
    intro h₁
    replace ⟨b, h₁⟩ := List.exists_mem_of_ne_nil (xs.filterMap f) h₁
    replace ⟨x, h₁⟩ := (List.mem_filterMap f xs).mp h₁
    exists x
    simp [h₁, Option.isSome]
  case mpr =>
    intro h₁ h₂
    rw [filterMap_empty_iff_all_none] at h₂
    replace ⟨x, h₁, h₃⟩ := h₁
    specialize h₂ x h₁
    simp [h₂, Option.isSome] at h₃

theorem f_implies_g_then_subset {f g : α → Option β} {xs : List α} :
  (∀ a b, f a = some b → g a = some b) →
  xs.filterMap f ⊆ xs.filterMap g
:= by
  intro h₁
  simp only [subset_def, mem_filterMap, forall_exists_index, and_imp]
  intro b a h₂ h₃
  exists a
  apply And.intro h₂
  exact h₁ a b h₃

end List

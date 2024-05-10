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

/-! ### any -/

theorem any_of_mem {f : α → Bool} {x : α} {xs : List α}
  (h₁ : x ∈ xs)
  (h₂ : f x) :
  any xs f = true
:= by
  cases xs <;> simp only [mem_cons, not_mem_nil] at h₁
  case cons hd tl =>
    simp only [any_cons, Bool.or_eq_true, any_eq_true]
    rcases h₁ with h₁ | h₁
    subst h₁
    simp only [h₂, true_or]
    apply Or.inr
    exists x

/-! ### all -/

/--
  Copied from Mathlib. We can delete this if it gets added to Std.
-/
theorem all_pmap_subtype
  {p : α → Prop}
  (f : α → Bool)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.all (List.pmap Subtype.mk as h) (λ x : { a : α // p a } => f x.val)
    =
    List.all as f
:= by
  induction as <;> simp [*]

end List

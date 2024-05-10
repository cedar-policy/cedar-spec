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

/-! ### map and map₁ -/

/--
  Copied from Mathlib. We can delete this if it gets added to Std.
-/
theorem map_congr {f g : α → β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]

/--
  Copied from Mathlib. We can delete this if it gets added to Std.
-/
theorem map_pmap_subtype
  {p : α → Prop}
  (f : α → β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.map (λ x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.map f as
:= by
  induction as <;> simp [*]

/--
  Not actually a special case of `map_pmap_subtype` -- you can use this in
  places you can't use `map_pmap_subtype` because the LHS function (being
  mapped) doesn't fit the `map_pmap_subtype` form but does fit this form (where
  the application of `f` is not the outermost AST node of the function,
  basically)
-/
theorem map_pmap_subtype_snd
  {p : (α × β) → Prop}
  (f : β → γ)
  (xs : List (α × β))
  (h : ∀ pair ∈ xs, p pair)
  : List.map (λ x : { pair : (α × β) // p pair } => (x.val.fst, f x.val.snd)) (List.pmap Subtype.mk xs h)
    =
    xs.map λ pair => (pair.fst, f pair.snd)
:= by
  induction xs <;> simp [*]

theorem map₁_eq_map (f : α → β) (as : List α) :
  as.map₁ (λ x : {x // x ∈ as} => f x.val) =
  as.map f
:= by
  simp [map₁, attach, map_pmap_subtype]

theorem map_attach₂ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : (α × β) → γ) :
  xs.attach₂.map (λ x : { x : α × β // sizeOf x.snd < 1 + sizeOf xs } => f x.1) =
  xs.map f
:= by
  simp [attach₂, map_pmap_subtype]

/--
  Not actually a special case of `map_attach₂` -- you can use this in places you
  can't use `map_attach₂` because the LHS function (being mapped) doesn't fit
  the `map_attach₂` form but does fit this form (where the application of `f` is
  not the outermost AST node of the function, basically)
-/
theorem map_attach₂_snd {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : β → γ) :
  xs.attach₂.map (λ x : {x : α × β // sizeOf x.snd < 1 + sizeOf xs } => match x with | ⟨(a, b), _⟩ => (a, f b)) =
  xs.map λ (a, b) => (a, f b)
:= by
  simp [attach₂, map_pmap_subtype_snd]

end List


/-!
# List utilities

This file contains useful lemmas about Lists.
-/


namespace List

theorem first_of_two_mem {α} {x₁ x₂ : α} :
  x₁ ∈ [x₁, x₂]
:= by simp only [mem_cons, not_mem_nil, or_false, true_or]

theorem second_of_two_mem {α} {x₁ x₂ : α} :
  x₂ ∈ [x₁, x₂]
:= by simp only [mem_cons, not_mem_nil, or_false, or_true]

theorem sizeOf_attach₂ [SizeOf α] [SizeOf β] {a : α} {b : β} {l : List (α × β)} :
  (a, b) ∈ l → sizeOf (a, b).snd < 1 + sizeOf l
:= by
  intro hin
  simp only
  replace hin := List.sizeOf_lt_of_mem hin
  simp only [Prod.mk.sizeOf_spec] at hin
  omega

theorem sizeOf_attach₃ [SizeOf α] [SizeOf β] {a : α} {b : β} {l : List (α × β)} :
  (a, b) ∈ l → sizeOf (a, b).snd < 1 + (1 + sizeOf l)
:= by
  intro hin
  simp only
  replace hin := List.sizeOf_lt_of_mem hin
  simp only [Prod.mk.sizeOf_spec] at hin
  omega

end List

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

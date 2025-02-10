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

import Cedar.Data
import Cedar.Thm.Validation.Typechecker.Basic

namespace Cedar.Thm

/-!
This file contains lemma about data structures. These should move into
appropriate files in the `Data` directory, or be replaced by calls to existing
lemma where reasonable.
-/

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem set_mem_flatten_union_iff_mem_any {α : Type} [LT α] [DecidableLT α] {ll : List (Set α)} {e : α}
  : e ∈ flatten_union ll ↔ ∃ l ∈ ll, e ∈ l
:= by sorry

theorem map_find_then_value {α β : Type} [BEq α] {m : Map α β} {k : α} {v : β}
  (hf : m.find? k = some v)
  : v ∈ m.values
:= by sorry

theorem map_find_mapm_value {α β : Type} [LT α] [DecidableLT α] [BEq α] {ks : Set α} {k : α} {kvs : List (α × β)} {fn : α → Option β}
  (h₁ : some kvs = List.mapM (λ k => (fn k).bind λ v => (some (k, v))) ks.elts)
  (h₂ : k ∈ ks)
  : (Map.make kvs).find? k = fn k
:= by
  cases h₃ : ks.elts
  case nil =>
    have hcontra : List.Mem k [] := by
      simp only [Membership.mem, h₃] at h₂
      exact h₂
    contradiction
  case cons h t =>
    simp [h₃] at h₁
    cases h₄ : ((fn h).bind λ v => some (h, v)) <;> simp [h₄] at h₁
    cases h₅ : (List.mapM (λ k => (fn k).bind λ v => some (k, v)) t) <;> simp [h₅] at h₁
    subst h₁
    simp only [Membership.mem, h₃] at h₂
    cases h₂
    case head =>
      cases h₆ : (fn k) <;> simp [h₆] at h₄
      subst h₄
      sorry
    case tail h₂ =>
      symm at h₅
      sorry

theorem mapm_pair_lookup  {α γ : Type} [BEq α] [LawfulBEq α] {l : List α} {l' : List (α × γ)} {f : α → Option (α × γ)} {e: α}
  (h₁ : List.mapM f l = some l')
  (h₂ : e ∈ l)
  (hf : ∀ e, match f e with
    | some e' => e'.fst = e
    | none => True)
  : ∃ e', f e = some e' ∧  l'.lookup e'.fst = some e'.snd
:= by
  cases l
  case nil => contradiction
  case cons h t =>
    cases h₃ : f h <;>
    cases h₄ : List.mapM f t <;>
    simp only [h₃, h₄, List.mapM_cons, Option.pure_def, Option.bind_none_fun, Option.bind_some_fun, Option.some.injEq, reduceCtorEq] at h₁
    subst h₁
    simp only [List.mem_cons] at h₂
    cases h₂
    case _ h₂ =>
      simp [h₂, h₃, List.lookup]
    case _ h₂ =>
      have ⟨ e'', ih₁, ih₂ ⟩ := mapm_pair_lookup h₄ h₂ hf
      have fh₁ := hf h ; rw [h₃] at fh₁ ; subst fh₁
      have fh₂ := hf e ; rw [ih₁] at fh₂ ; subst fh₂
      simp only [ih₁,ih₂, Option.some.injEq, List.lookup, exists_eq_left']
      split
      · rename_i h₅
        simp only [beq_iff_eq] at h₅
        simp only [←h₅, ih₁, Option.some.injEq] at h₃
        rw [h₃]
      · simp

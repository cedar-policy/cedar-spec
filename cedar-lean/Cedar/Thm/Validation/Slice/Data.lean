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

theorem map_find_mapm_value {α β : Type} [BEq α] [LawfulBEq α] {kvs : List (α × β)} {ks : List α} {fn : α → Option β} {k: α}
  (h₁ : List.mapM (λ k => (fn k).bind λ v => (some (k, v))) ks = some kvs)
  (h₂ : k ∈ ks)
  : (Map.mk kvs).find? k = fn k
:= by
  simp only [Map.find?, Map.kvs]
  cases h₂
  case head l =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h₁
    cases hf : fn k <;> simp only [hf, Option.none_bind, Option.some_bind, reduceCtorEq] at h₁
    cases ht₁ : (List.mapM (λ k => (fn k).bind λ v => some (k, v)) l) <;> simp [ht₁ , Option.none_bind, Option.some_bind, reduceCtorEq, Option.some.injEq] at h₁
    subst h₁
    simp
  case tail h t h₂  =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h₁
    cases hf : fn h <;> simp only [hf, Option.none_bind, Option.some_bind, reduceCtorEq] at h₁
    cases ht₁ : (List.mapM (λ k => (fn k).bind λ v => some (k, v)) t) <;> simp only [ht₁, Option.none_bind, Option.some_bind, reduceCtorEq, Option.some.injEq] at h₁
    subst h₁
    simp only [List.find?]
    cases h₃ : (h == k)
    · simp only
      exact map_find_mapm_value ht₁ h₂
    · simp only [beq_iff_eq] at h₃
      simp [h₃, ←hf]

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

theorem mapm_none_lookup_none {α γ : Type} [BEq α] [LT α] [DecidableLT α] [DecidableEq α] {l : List α} {l' : List (α × γ)} {f : α → Option γ} {e: α}
  (h₂ : l.mapM (λ e => (f e).bind (λ e' => (e, e'))) = some l')
  (h₁ : f e = none) :
  l'.lookup e = none
:= by
  cases l
  case nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq, List.nil_eq] at h₂
    simp [h₂, List.lookup]
  case cons h t =>
    simp at h₂
    cases h₃ : (f h) <;> simp [h₃] at h₂
    cases h₄ : ((List.mapM (fun e => (f e).bind fun e' => some (e, e')) t)) <;> simp [h₄] at h₂
    subst h₂
    simp [List.lookup]
    split
    · rename_i heq
      have _ : e = h := by sorry
      subst e
      rw [h₃] at h₁
      contradiction
    · exact mapm_none_lookup_none h₄ h₁

theorem map_cons_find_none {α β : Type} [BEq α] [LT α] [DecidableLT α] {e₁ e₂ : α} {v : β} {t : List (α × β)}
  (h₁ : e₁ ≠ e₂)
  (h₂ : (Map.make t).find? e₁ = none) :
  (Map.make ((e₂, v) :: t)).find? e₁ = none
:= by sorry

theorem mapm_none_find_none {α γ : Type} [BEq α] [LT α] [DecidableLT α] {l : List α} {l' : List (α × γ)} {f : α → Option γ} {e: α}
  (h₂ : l.mapM (λ e => (f e).bind (λ e' => (e, e'))) = some l')
  (h₁ : f e = none) :
  (Map.make l').find? e = none
:= by
  cases l
  case nil =>
    simp at h₂
    subst h₂
    rw [Map.make_nil_is_empty]
    simp [Map.find?, Map.empty, Map.kvs]
  case cons h t =>
    simp at h₂
    cases h₃ : (f h) <;> simp [h₃] at h₂
    cases h₄ : ((List.mapM (fun e => (f e).bind fun e' => some (e, e')) t)) <;> simp [h₄] at h₂
    subst h₂
    have ih := mapm_none_find_none h₄ h₁
    have hne : e ≠ h := by
      intros heq
      subst heq
      rw [h₁] at h₃
      contradiction
    apply map_cons_find_none hne ih

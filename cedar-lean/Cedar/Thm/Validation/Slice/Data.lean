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

theorem mapm_key_id_sorted_by_key {α β : Type} [LT α] [BEq α] [LawfulBEq α] {kvs : List (α × β)} {ks : List α} {fn : α → Option β}
  (hm : List.mapM (λ k => (fn k).bind λ v => (some (k, v))) ks = some kvs)
  (hs : ks.SortedBy id)
  : kvs.SortedBy Prod.fst
:= by
  cases hs
  case nil =>
    have _ : kvs = [] := by simpa using hm
    subst kvs
    constructor
  case cons_nil head =>
    have ⟨_, _⟩ : ∃ kv, kvs = [kv] := by
      cases hm₁ : fn head <;>
      simp only [hm₁, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_none_fun, Option.bind_some_fun, Option.none_bind, Option.some_bind, Option.some.injEq, reduceCtorEq] at hm
      simp [←hm]
    subst kvs
    constructor
  case cons_cons head₀ head₁ tail hlt hs =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at hm
    cases hm₁ : (fn head₀) <;> simp only [hm₁, Option.none_bind, Option.some_bind, Option.some.injEq, reduceCtorEq] at hm
    cases hm₂ : (fn head₁) <;> simp only [hm₂, Option.none_bind, Option.some_bind, Option.some.injEq, reduceCtorEq] at hm
    cases hm₃ : (List.mapM (fun k => (fn k).bind fun v => some (k, v)) tail) <;> simp only [hm₃, Option.none_bind, Option.some_bind, Option.some.injEq, reduceCtorEq] at hm
    rename_i v₀ v₁ kvs'
    subst kvs

    replace hlt : (head₀, v₀).fst < (head₁, v₁).fst := by
      simpa using hlt

    replace hs : List.SortedBy Prod.fst ((head₁, v₁) :: kvs') := by
      have hm₄ : List.mapM (fun k => (fn k).bind fun v => some (k, v)) (head₁ :: tail) = some ((head₁, v₁) :: kvs') := by
        simp [hm₂, hm₃]
      exact mapm_key_id_sorted_by_key hm₄ hs

    exact List.SortedBy.cons_cons hlt hs

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

theorem mapm_none_find_none' {α γ : Type} [BEq α] [LT α] [DecidableLT α] {l : List α} {l' : List (α × γ)} {f : α → Option γ} {e: α}
  (hm : List.mapM (fun e => (f e).bind fun v => some (e, v)) l = some l')
  (hl : e ∉ l) :
  ∀ v, (e, v) ∉ l'
:= by
  intro v hl'
  cases l
  case nil =>
    have : l' = [] := by simpa using hm
    subst l'
    cases hl'
  case cons head tail =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at hm
    cases hm₁ : f head <;> simp only [hm₁, Option.none_bind, Option.some_bind, reduceCtorEq] at hm
    cases hm₂ : (List.mapM (fun e => (f e).bind fun v => some (e, v)) tail) <;> simp only [hm₂, Option.none_bind, Option.some_bind, Option.some.injEq, reduceCtorEq] at hm
    subst l'
    cases hl'
    case head =>
      exact hl (List.Mem.head _)
    case tail tail' ht' =>
      replace hl : e ∉ tail := (hl $ List.Mem.tail _ ·)
      exact mapm_none_find_none' hm₂ hl _ ht'

theorem map_not_in_list_then_not_in_map  [DecidableEq α] [LT α] [StrictLT α ] [DecidableLT α] {l : List (α × β)}
  (hl : ∀ v, (k, v) ∉ l) :
  (Map.make l).find? k = none
:= by
  rw [Map.find?_none_iff_all_absent]
  simp only [Map.kvs, Map.make]
  intro v hl'
  exact hl v (List.in_canonicalize_in_list hl')

theorem mapm_none_find_none {α γ : Type} [DecidableEq α] [LT α] [StrictLT α] [DecidableLT α] {l : List α} {l' : List (α × γ)} {f : α → Option γ} {e: α}
  (h₂ : l.mapM (λ e => (f e).bind (λ e' => (e, e'))) = some l')
  (h₁ : f e = none) :
  (Map.make l').find? e = none
:= by
  by_cases h₃ : e ∈ l
  case pos =>
    have ⟨ _, _, h₄ ⟩ := List.mapM_some_implies_all_some h₂ e h₃
    simp [h₁] at h₄
  case neg =>
    exact map_not_in_list_then_not_in_map (mapm_none_find_none' h₂ h₃)

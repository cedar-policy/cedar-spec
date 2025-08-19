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

import Cedar.Thm.SymCC.Data

/-! Some lemmas to simplify `UDF`s. -/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.SymCC
open Cedar.Data

/--
For simplifying `Factory.app` on a `UDF` with a table
of the form `make (m.toList.filterMap f)`.
-/
theorem map_make_filterMap_find?
  [BEq α] [LawfulBEq α]
  [DecidableEq γ] [LT γ] [DecidableLT γ] [StrictLT γ]
  {m : Map α β}
  {k : α} {v : β} {k' : γ} {v' : κ}
  {f : α × β → Option (γ × κ)}
  (hfind : m.find? k = .some v)
  (hkv : f (k, v) = .some (k', v'))
  (hf : ∀ kv, (∃ v'', f kv = .some (k', v'')) → kv.1 = k) :
  (Map.make (m.toList.filterMap f)).find? k' = .some v'
:= by
  apply Map.find?_implies_make_find?
  simp only [List.find?_filterMap]
  have :
    List.find? (fun a => Option.any (fun x => x.fst == k') (f a)) m.toList
    = .some (k, v)
  := by
    apply Map.map_find?_implies_find?_weaker_pred hfind
    · intros kv h
      simp only [Option.any] at h
      split at h
      · rename_i f_out heq
        simp at h
        apply hf kv
        exists f_out.snd
        simp only [heq, ←h]
      · contradiction
    · simp [
        Option.any,
        hkv,
      ]
  simp [this, hkv]

/-- Similar to above but for the `none` case -/
theorem map_make_filterMap_find?_none
  [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  [DecidableEq γ] [LT γ] [DecidableLT γ] [StrictLT γ]
  {m : Map α β}
  {k : α} {k' : γ}
  {f : α × β → Option (γ × κ)}
  (hfind : m.find? k = .none)
  (hf : ∀ kv, (∃ v'', f kv = .some (k', v'')) → kv.1 = k) :
  (Map.make (m.toList.filterMap f)).find? k' = .none
:= by
  apply Map.all_absent_find?_none
  intros v hmem_k'_v
  have := Map.make_mem_list_mem hmem_k'_v
  have ⟨(k'', v''), hmem_kv, hfkv⟩ := List.mem_filterMap.mp this
  have heq_k'' := hf (k'', v'')
  simp only [
    hfkv, Option.some.injEq,
    Prod.mk.injEq, true_and, exists_eq',
    forall_const,
  ] at heq_k''
  have := Map.in_list_implies_contains hmem_kv
  have := Map.contains_iff_some_find?.mp this
  have heq_m : Map.mk m.toList = m := by
    cases m
    rfl
  simp [heq_k'', heq_m, hfind] at this

/--
Simplifying `Factory.app` on a `UDF` with a table
of the form `make (m.toList.filterMap f)`.
-/
theorem app_table_make_filterMap
  [BEq α] [LawfulBEq α]
  {arg : TermType} {out : TermType} {default : Term}
  {m : Map α β} {k : α} {v : β}
  {t : Term} {r : Term}
  {f : α × β → Option (Term × Term)}
  (hfind : m.find? k = .some v)
  (hkv : f (k, v) = .some (t, r))
  (hf : ∀ kv, (∃ v'', f kv = .some (t, v'')) → kv.1 = k)
  (hlit : t.isLiteral) :
  Factory.app
    (.udf {
      arg := arg,
      out := out,
      table := Map.make (m.toList.filterMap f),
      default := default,
    }) t
  = r
:= by
  simp only [
    Factory.app,
    hlit,
    ↓reduceIte,
  ]
  have := map_make_filterMap_find? hfind hkv hf
  simp only [this]

/--
For simplifying `Factory.app` on a `UDF` with a table
of the form `make (m.toList.filterMap f).flatten`.
-/
theorem map_make_filterMap_flatten_find?
  [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
  [DecidableEq γ] [LT γ] [DecidableLT γ] [StrictLT γ]
  {m : Map α β}
  {k : α} {v : β} {k' : γ} {v' : κ}
  {f : α × β → Option (List (γ × κ))}
  (hfind : m.find? k = .some v)
  (hkv : ∃ l, f (k, v) = .some l ∧ l.find? (λ x => x.1 == k') = .some (k', v'))
  (hf : ∀ kv, (∃ l, f kv = .some l ∧ (l.find? (λ x => x.1 == k')).isSome) → kv.1 = k) :
  (Map.make (m.toList.filterMap f).flatten).find? k' = .some v'
:= by
  apply Map.find?_implies_make_find?
  simp only [List.find?_flatten]
  cases m with | mk l =>
  simp only [Map.toList, Map.kvs, Map.find?] at *
  split at hfind
  rotate_left; contradiction
  rename_i heq
  simp only [Option.some.injEq] at hfind
  simp only [hfind] at heq
  have := List.find?_some heq
  simp only [beq_iff_eq] at this
  simp only [this] at heq
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?] at heq
    split at heq
    · simp only [Option.some.injEq] at heq
      have ⟨fkv, hfkv, hfind_fkv⟩ := hkv
      simp only [List.filterMap, heq, hfkv]
      simp only [List.findSome?, hfind_fkv]
    · rename_i hne_hd_key
      simp only [List.filterMap]
      split
      · exact ih heq
      · rename_i l' hhd
        simp only [beq_eq_false_iff_ne, ne_eq] at hne_hd_key
        have := hf hd
        have :
          (∃ l, f hd = some l ∧ (List.find? (fun x => x.fst == k') l).isSome = true) → False
        := by
          intros h
          apply hne_hd_key
          apply this h
        simp only [
          imp_false, not_exists, not_and,
        ] at this
        have hfind_l' := this l' hhd
        simp only [List.findSome?]
        split
        · rename_i heq
          simp only [heq] at hfind_l'
          simp at hfind_l'
        · exact ih heq

end Cedar.Thm

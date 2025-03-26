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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Validator

import Cedar.Thm.Validation.Slice.Reachable

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem slice_at_level_inner_well_formed {entities : Entities} {work slice : Set EntityUID} {n : Nat}
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work n = some slice) :
  slice.WellFormed
:= by
  match n with
  | 0 =>
    simp only [Entities.sliceAtLevel.sliceAtLevel, Option.some.injEq] at hs
    subst slice
    exact Set.empty_wf
  | n + 1 =>
    simp only [Entities.sliceAtLevel.sliceAtLevel, Option.some.injEq] at hs
    cases hs₁ : List.mapM (Map.find? entities) work.elts <;>
      simp only [hs₁, Option.map_eq_map, Option.bind_eq_bind, Option.bind_none_fun, Option.bind_some_fun, reduceCtorEq] at hs
    rename_i eds
    cases hs₂ : List.mapM (fun ed : EntityData => Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs n) eds <;>
      simp only [hs₂, Option.map_none', Option.map_some', Option.none_bind, Option.some_bind, reduceCtorEq, Option.some.injEq] at hs
    subst slice
    simp [Union.union, Set.union, Set.make_wf]

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
  (h₁ : ks.mapM (λ k => do (k, ←fn k)) = some kvs)
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

theorem checked_eval_entity_in_slice  {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {slice entities : Entities} {ed : EntityData}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax [])
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hf : entities.find? euid = some ed)
  (hs : slice = Entities.sliceAtLevel entities request (n + 1)) :
  slice.find? euid = some ed
:= by
  simp only [Entities.sliceAtLevel] at hs
  cases hs₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs (n + 1)  <;>
    simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eids
  cases hs₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts) <;>
    simp only [hs₂, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
  subst hs
  have hf₁ : Map.contains entities euid := by simp [Map.contains, hf]
  have hw : ReachableIn entities request.sliceEUIDs euid (n + 1) :=
    checked_eval_entity_reachable hc hr ht hl he (.euid euid) hf₁
  have hi := slice_contains_reachable hw hs₁
  rw [←hf]
  rename_i eds
  replace hmake : Map.mk eds = Map.make eds := by
    have hsorted := eids.wf_iff_sorted.mp (slice_at_level_inner_well_formed hs₁)
    have hsbfst := mapm_key_id_sorted_by_key hs₂ hsorted
    have hwf : (Map.mk eds).WellFormed := by
      simpa [Map.wf_iff_sorted, Map.toList, Map.kvs] using hsbfst
    simpa [Map.WellFormed, Map.toList, Map.kvs] using hwf
  have hmk := map_find_mapm_value hs₂ hi
  simpa [hmake] using hmk

theorem not_in_list_not_in_mapm_list {α γ : Type} [BEq α] [LT α] [DecidableLT α] {l : List α} {l' : List (α × γ)} {f : α → Option γ} {e: α}
  (hm : l.mapM (λ e => do (e, ← f e)) = some l')
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
      exact not_in_list_not_in_mapm_list hm₂ hl _ ht'

theorem mapm_none_find_none {α γ : Type} [DecidableEq α] [LT α] [StrictLT α] [DecidableLT α] {l : List α} {l' : List (α × γ)} {f : α → Option γ} {e: α}
  (h₂ : l.mapM (λ e => do (e, ← f e)) = some l')
  (h₁ : f e = none) :
  (Map.make l').find? e = none
:= by
  by_cases h₃ : e ∈ l
  case pos =>
    have ⟨ _, _, h₄ ⟩ := List.mapM_some_implies_all_some h₂ e h₃
    simp [h₁] at h₄
  case neg =>
    simp only [Map.find?_none_iff_all_absent, Map.kvs, Map.make]
    intro v hl'
    have h₄ := List.in_canonicalize_in_list hl'
    exact not_in_list_not_in_mapm_list h₂ h₃ v h₄

theorem not_entities_then_not_slice {n: Nat} {request : Request} {uid : EntityUID} {entities slice : Entities}
  (hs : some slice = Entities.sliceAtLevel entities request n)
  (hse : entities.find? uid = none)
  : slice.find? uid = none
:= by
  simp only [Entities.sliceAtLevel] at hs
  cases hs₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs n <;>
    simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eids
  cases hs₂ : (List.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed)) eids.elts) <;>
    simp only [hs₂, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
  subst hs
  exact mapm_none_find_none hs₂ hse

/--
If an expression checks at level `n` and then evaluates to an entity, then the
data for that entity in the slice will be hte same as in the original entities.
-/
theorem checked_eval_entity_find_entities_eq_find_slice  {n nmax : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {slice entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax [])
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hs : slice = Entities.sliceAtLevel entities request (n + 1)) :
  entities.find? euid = slice.find? euid
:= by
  cases hfe : Map.find? entities euid
  case none =>
    simp [not_entities_then_not_slice hs hfe]
  case some =>
    have h₇ := checked_eval_entity_in_slice hc hr ht hl he hfe hs
    simp [h₇]

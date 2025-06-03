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
  unfold Entities.sliceAtLevel.sliceAtLevel at hs
  split at hs
  · injections hs
    subst hs
    exact Set.empty_wf
  · replace ⟨ _, _, hs⟩ : ∃ s₀ s₁, s₀ ∪ s₁ = slice := by
      cases hs₁ : work.elts.mapM (Map.find? entities) <;>
        simp only [hs₁, Option.map_eq_map, Option.bind_eq_bind, Option.bind_none_fun, Option.bind_some_fun, reduceCtorEq] at hs
      rename_i n eds
      cases hs₂ : eds.mapM (Entities.sliceAtLevel.sliceAtLevel entities ·.sliceEUIDs n) <;>
        simp only [hs₂, Option.map_none, Option.map_some, Option.none_bind, Option.some_bind, reduceCtorEq, Option.some.injEq] at hs
      rename_i slice'
      exists work, (slice'.mapUnion id)
    subst hs
    simp only [Set.union_wf]

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
  cases hs₂ : (eids.elts.mapM (λ e => (Map.find? entities e).bind λ ed => some (e, ed))) <;>
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
    have hsbfst := List.mapM_key_id_sortedBy_key hs₂ hsorted
    have hwf : (Map.mk eds).WellFormed := by
      simpa [Map.wf_iff_sorted] using hsbfst
    simpa [Map.WellFormed] using hwf
  have hmk := Map.find?_mapM_key_id hs₂ hi
  simpa [hmake] using hmk

theorem not_entities_then_not_slice {n: Nat} {request : Request} {uid : EntityUID} {entities slice : Entities}
  (hs : some slice = Entities.sliceAtLevel entities request n)
  (hse : entities.find? uid = none)
  : slice.find? uid = none
:= by
  simp only [Entities.sliceAtLevel] at hs
  cases hs₁ : Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs n <;>
    simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eids
  cases hs₂ : (eids.elts.mapM (λ e => (entities.find? e).bind λ ed => some (e, ed))) <;>
    simp only [hs₂, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
  subst hs
  exact Map.mapM_key_id_key_none_implies_find?_none hs₂ hse

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
  slice.find? euid = entities.find? euid
:= by
  cases hfe : Map.find? entities euid
  case none =>
    exact not_entities_then_not_slice hs hfe
  case some =>
    exact checked_eval_entity_in_slice hc hr ht hl he hfe hs

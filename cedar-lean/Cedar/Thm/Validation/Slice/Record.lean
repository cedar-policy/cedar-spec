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

import Cedar.Thm.Validation.Slice.Basic
import Cedar.Thm.Validation.Slice.Data

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem record_value_contains_evaluated_attrs {rxs : List (Attr × Expr)} {rvs : Map Attr Value} {a : Attr} {av : Value} {request : Request} {entities : Entities}
  (he : evaluate (.record rxs) request entities = .ok (.record rvs))
  (hfv : rvs.find? a = some av) :
  ∃ x, (Map.make rxs).find? a = some x ∧ evaluate x request entities = .ok av
:= by
  simp only [evaluate] at he
  cases he₁ : rxs.mapM₂ fun x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;>
    simp only [he₁, Except.bind_err, reduceCtorEq, Except.bind_ok, Except.ok.injEq, Value.record.injEq] at he
  rename_i rvs'
  replace he₁ : List.Forallᵥ (λ x y => evaluate x request entities = Except.ok y) rxs rvs' := by
    simp only [List.forallᵥ_def]
    rw [List.mapM₂, List.attach₂] at he₁
    rw [List.mapM_pmap_subtype λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)] at he₁
    rw [List.mapM_ok_iff_forall₂] at he₁
    apply List.Forall₂.imp _ he₁
    intro x y h
    simp only [bindAttr] at h
    cases hx : evaluate x.snd request entities <;> simp only [hx, Except.bind_err, Except.bind_ok, reduceCtorEq, Except.ok.injEq] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    simp only [←h, and_self]
  replace he₁ := List.canonicalize_preserves_forallᵥ _ _ _ he₁
  have hfv : List.find? (λ x => x.fst == a) (List.canonicalize Prod.fst rvs') = some (a, av) := by
    simp only [Map.find?] at hfv
    split at hfv <;> simp only [Option.some.injEq, reduceCtorEq] at hfv
    subst hfv
    rename_i a' _ hfv
    rw [←he, (by simpa using List.find?_some hfv : a' = a)] at hfv
    exact hfv
  have ⟨(_, x), he₂, he₃, he₄⟩ := List.forall₂_implies_all_right he₁ (a, av) (List.mem_of_find?_eq_some hfv)
  subst he₃
  exists x
  simp only [List.mem_of_sortedBy_implies_find? he₂ (List.canonicalize_sortedBy _ _), he₄, Map.make, Map.find?, and_self]

theorem checked_eval_entity_reachable_record {rxs : List (Attr × Expr)} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.record rxs) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (.record rxs) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hf : entities.contains euid)
  (ih : forall a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨ hc', rtxs, htx, hfat ⟩ := type_of_record_inversion ht
  subst hc' htx

  have ⟨ rvs, hv ⟩ : ∃ rvs, Value.record rvs = v := by
    simp only [evaluate] at he
    cases he₁ : rxs.mapM₂ fun x => bindAttr x.1.fst (evaluate x.1.snd request entities) <;>
      simp only [he₁, Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq] at he
    simp [←he]
  subst hv
  cases ha
  rename_i v a path' hfv hv
  have ⟨ x, hfx, hex ⟩ := record_value_contains_evaluated_attrs he hfv

  have ⟨atx, hfatx, het⟩ : ∃ atx, (Map.make rtxs).find? a = some atx ∧ AttrExprHasAttrType c env (a, x) (a, atx)  := by
    have he' := Map.make_mem_list_mem (Map.find?_mem_toList hfx)
    replace hfat' := List.forall₂_implies_all_left hfat
    have ⟨ atx, _, haty ⟩ := hfat' (a, x) he'
    have ⟨_, _, _, ht''⟩ := find_make_xs_find_make_txs hfat hfx
    rename_i tx _ _
    have ⟨ ha, htx ⟩ : a = atx.fst ∧ tx = atx.snd := by
      simpa [AttrExprHasAttrType, ht''] using haty
    subst ha htx
    exists atx.snd

  replace ⟨_, het⟩ : ∃ c', typeOf x c env = Except.ok (atx, c') := by
    simpa [AttrExprHasAttrType] using het

  have hl' : atx.EntityAccessAtLevel env n nmax path' := by
    cases hl
    rename_i hl _ _
    have := Map.find?_mem_toList hfatx
    have := Map.make_mem_list_mem this
    have := hl (a, atx) this
    simp at this
    rename_i h₁ _  _ _
    rw [h₁] at hfatx
    simp at hfatx
    subst atx
    assumption

  exact ih a x hfx hc hr het hl' hex hv hf

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

import Cedar.Thm.Authorization.Evaluator
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Slice.Reachable.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem checked_eval_entity_reachable_record {rxs : List (Attr × Expr)} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.record rxs) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (.record rxs) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hf : entities.contains euid)
  (ih : ∀ a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨ hc', rtxs, htx, hfat ⟩ := type_of_record_inversion ht
  subst hc' htx

  have ⟨ rvs, hv ⟩ := record_produces_record_value he
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

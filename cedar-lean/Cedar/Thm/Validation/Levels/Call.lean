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
import Cedar.Thm.Validation.Levels.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_call {xs : List Expr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hn : nmax ≥ n)
  (hs : slice = entities.sliceAtLevel request nmax)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.call xfn xs) c₀ env = Except.ok (tx, c₁))
  (hl : TypedExpr.AtLevel tx n nmax)
  (ih : ∀ x ∈ xs, TypedAtLevelIsSound x) :
  evaluate (.call xfn xs) request entities = evaluate (.call xfn xs) request slice
:= by
  replace ⟨ _, txs, ty, ht ⟩ := type_of_call_inversion ht
  subst tx
  cases hl ; rename_i hl

  have he : ∀ x ∈ xs, evaluate x request entities = evaluate x request slice := by
    intros x hx
    replace ⟨ tx, c', htxs, htx ⟩ := ht x hx
    specialize hl tx htxs
    exact ih x hx hn hs hc hr htx hl

  simp only [evaluate, List.mapM₁, List.attach, List.attachWith]
  simp only [List.mapM_pmap_subtype (λ x : Expr => evaluate x request entities) xs]
  simp only [List.mapM_pmap_subtype (λ x : Expr => evaluate x request slice) xs]
  rw [mapm_eval_congr_entities he]

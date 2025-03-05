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
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Basic

/-!
This file proves that level checking for `.record` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_record_attrs {rxs : List (Attr × Expr)} {n : Nat} {c : Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : List.Forall₂ (AttrExprHasAttrType c env) rxs atxs)
  (hl : ∀ atx ∈ atxs, TypedExpr.AtLevel atx.snd n)
  (ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd)
  :
  (rxs.mapM₂ λ x => do
    let v ← (evaluate x.1.snd request entities)
    Except.ok (x.1.fst, v)) =
  (rxs.mapM₂ λ x => do
    let v ← (evaluate x.1.snd request slice)
    Except.ok (x.1.fst, v))
:= by
  cases ht
  case nil =>
    simp [List.attach₂, List.mapM₂]
  case cons x tx rxs' txs' htx ht =>
    simp only [List.mem_cons, forall_eq_or_imp] at ih hl
    replace ⟨ ihx, ih ⟩ := ih
    replace ⟨ hlx, hl ⟩ := hl
    replace ⟨ _, _, htx ⟩ := htx
    specialize ihx hs hc hr htx hlx
    simp only [←ihx, List.mapM₂, List.attach₂, List.pmap_cons, List.mapM_cons]
    cases he₁ : evaluate x.snd request entities <;> simp only [Except.bind_err, Except.bind_ok]
    have ih' := level_based_slicing_is_sound_record_attrs hs hc hr ht hl ih
    simp only [List.mapM₂, List.attach₂] at ih'
    simp only [List.mapM_pmap_subtype (λ x : (Attr × Expr) => do let v ← evaluate x.snd request entities; .ok (x.fst, v)) rxs'] at ih' ⊢
    simp only [List.mapM_pmap_subtype (λ x : (Attr × Expr) => do let v ← evaluate x.snd request slice; .ok (x.fst, v)) rxs'] at ih' ⊢
    rw [ih']

theorem level_based_slicing_is_sound_record {rxs : List (Attr × Expr)} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.record rxs) c₀ env = Except.ok (tx, c₁))
  (hl : TypedExpr.AtLevel tx n)
  (ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd) :
  evaluate (.record rxs) request entities = evaluate (.record rxs) request slice
:= by
  replace ⟨ hc₁, atxs, htx, hatxs ⟩ := type_of_record_inversion ht
  subst htx
  cases hl
  rename_i hlatxs
  have h := level_based_slicing_is_sound_record_attrs hs hc hr hatxs hlatxs ih
  simp [h, evaluate, bindAttr]

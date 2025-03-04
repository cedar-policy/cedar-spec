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

import Cedar.Thm.Validation.Slice.Data
import Cedar.Thm.Validation.Slice.Basic
import Cedar.Thm.Validation.Slice.BinaryApp
import Cedar.Thm.Validation.Slice.GetAttr
import Cedar.Thm.Validation.Slice.IfThenElse
import Cedar.Thm.Validation.Slice.Record
import Cedar.Thm.Validation.Slice.Var

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem non_entity_lit_not_euid_via_path {p : Prim} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (ht : typeOf (.lit p) c env = .ok (tx, c'))
  (he : evaluate (.lit p) request entities = .ok v)
  (hel : ¬ TypedExpr.EntityLitViaPath tx path) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  cases p
  case entityUID =>
    replace ⟨ _, ht ⟩ := type_of_lit_inversion ht
    rw [←ht] at hel
    exact hel (by constructor)
  all_goals
    simp only [evaluate, Except.ok.injEq] at he
    subst he
    cases ha

theorem and_not_euid_via_path {e₁ e₂: Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.and e₁ e₂) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ :  Result.as Bool (evaluate e₁ request entities) <;>
    simp only [he₁, bind_pure_comp, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  split at he
  · injections he
    subst he ; cases ha
  · cases he₂ : Result.as Bool (evaluate e₂ request entities) <;>
      simp only [he₂, Except.map_error, reduceCtorEq, Except.map_ok, Except.ok.injEq] at he
    subst he ; cases ha

theorem or_not_euid_via_path {e₁ e₂: Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.or e₁ e₂) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : Result.as Bool (evaluate e₁ request entities) <;>
    simp only [he₁, bind_pure_comp, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  split at he
  · simp only [Except.ok.injEq] at he
    subst he ; cases ha
  · cases he₂ : Result.as Bool (evaluate e₂ request entities) <;>
      simp only [he₂, Except.map_error, reduceCtorEq, Except.map_ok, Except.ok.injEq] at he
    subst he ; cases ha

theorem unary_not_euid_via_path {op : UnaryOp} {e₁ : Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.unaryApp op e₁) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;>
    simp only [he₁, intOrErr, apply₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  (split at he <;> try split at he) <;>
  try simp only [reduceCtorEq] at he
  all_goals { injections he ; subst he ; cases ha }

theorem has_attr_not_euid_via_path {e₁ : Expr} {a : Attr} {entities : Entities} {path : List Attr}
  (he : evaluate (.hasAttr e₁ a) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;>
    simp only [he₁, Except.bind_err, reduceCtorEq, hasAttr, Except.bind_ok] at he
  rename_i v₁
  cases he₂ : attrsOf v₁ λ uid => Except.ok (entities.attrsOrEmpty uid) <;>
    simp only [he₂, Except.ok.injEq, Except.bind_ok, Except.bind_err, reduceCtorEq] at he
  subst he ; cases ha

theorem set_not_euid_via_path {xs : List Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.set xs) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : (xs.mapM₁ (λ x => evaluate x.val request entities)) <;>
    simp only [he₁, Except.bind_err, Except.bind_ok, Except.ok.injEq, reduceCtorEq] at he
  subst he ; cases ha

theorem call_not_euid_via_path {xfn : ExtFun} {xs : List Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.call xfn xs) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : xs.mapM₁ fun x => evaluate x.val request entities <;>
    simp only [he₁, Except.bind_err, reduceCtorEq] at he

  simp only [call, res, Except.bind_ok] at he
  (split at he <;> try split at he) <;>
  simp only [Except.ok.injEq, reduceCtorEq] at he

  all_goals { subst he ; cases ha }

/--
If an expression checks at level `n` and then evaluates an entity (or a record
containing an entity), then that entity must reachable in `n + 1` steps.
-/
theorem checked_eval_entity_reachable {e : Expr} {n nmax: Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {request : Request} {entities : Entities} {v : Value} {path : List Attr} {euid : EntityUID}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : TypedExpr.AtLevel tx n nmax)
  (hel : ¬ TypedExpr.EntityLitViaPath tx path)
  (he : evaluate e request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  cases e
  case lit =>
    exfalso
    exact non_entity_lit_not_euid_via_path ht he hel ha

  case var =>
    exact var_entity_reachable he ha hf

  case ite e₁ e₂ e₃ =>
    have ih₂ := @checked_eval_entity_reachable e₂
    have ih₃ := @checked_eval_entity_reachable e₃
    exact checked_eval_entity_reachable_ite hc hr ht hl hel he ha hf ih₂ ih₃

  case and =>
    exfalso
    exact and_not_euid_via_path he ha

  case or e=>
    exfalso
    exact or_not_euid_via_path he ha

  case unaryApp op e =>
    exfalso
    exact unary_not_euid_via_path he ha

  case binaryApp op e₁ e₂ =>
    have ih₁ := @checked_eval_entity_reachable e₁
    exact checked_eval_entity_reachable_binary hc hr ht hl he ha ih₁

  case getAttr e _ =>
    have ih := @checked_eval_entity_reachable e
    exact checked_eval_entity_reachable_get_attr hc hr ht hl hel he ha hf ih

  case hasAttr e a =>
    exfalso
    exact has_attr_not_euid_via_path he ha

  case set es =>
    exfalso
    exact set_not_euid_via_path he ha

  case record rxs =>
    have ih : forall a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x := by
      intros a x hfx
      have : sizeOf x < sizeOf (Expr.record rxs) := by
        replace he := Map.make_mem_list_mem (Map.find?_mem_toList hfx)
        have h₁ := List.sizeOf_lt_of_mem he
        rw [Prod.mk.sizeOf_spec a x] at h₁
        simp only [Expr.record.sizeOf_spec, gt_iff_lt]
        omega
      exact @checked_eval_entity_reachable x
    exact checked_eval_entity_reachable_record hc hr ht hl hel he ha hf ih

  case call xfn args =>
    exfalso
    exact call_not_euid_via_path he ha
termination_by e

theorem in_work_then_in_slice {entities : Entities} {work slice : Set EntityUID} {euid : EntityUID} {n : Nat}
  (hw : euid ∈ work)
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work (n + 1) = some slice)
  : euid ∈ slice
:= by
  unfold Entities.sliceAtLevel.sliceAtLevel at hs
  cases hs₁ :
    List.mapM (Map.find? entities) work.elts
  <;> simp only [hs₁, Option.map_eq_map, Option.bind_eq_bind, Option.bind_none_fun, reduceCtorEq] at hs
  rename_i eds
  cases hs₂ :
    List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds
  <;> simp only [hs₂, Option.map_none', Option.map_some', Option.none_bind, Option.some_bind, reduceCtorEq,Option.some.injEq] at hs
  rename_i slice'
  subst hs
  have ⟨ _, hc ⟩ := Set.mem_union_iff_mem_or work (slice'.mapUnion id) euid
  apply hc
  simp [hw]

/--
If an entity is reachable in `n` steps, then it must be included in slice at
`n`. This lemma talks about the inner slicing function, so it's possible that
the entity isn't in the original entities if it's in `work`.
-/
theorem slice_contains_reachable {n: Nat} {work : Set EntityUID} {euid : EntityUID} {entities : Entities} {slice : Set EntityUID}
  (hw : ReachableIn entities work euid (n + 1))
  (hs : Entities.sliceAtLevel.sliceAtLevel entities work (n + 1) = some slice) :
  euid ∈ slice
:= by
  cases hw
  case in_start hw =>
    exact in_work_then_in_slice hw hs
  case step ed euid' hf hi hw =>
    unfold Entities.sliceAtLevel.sliceAtLevel at hs
    cases hs₁ : (List.mapM (Map.find? entities) work.elts) <;>
      simp only [hs₁, Option.bind_none_fun, reduceCtorEq] at hs
    rename_i eds
    cases hs₂ : Option.map (List.mapUnion id) (List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds) <;>
      simp only [hs₂, Option.map_eq_map, Option.bind_eq_bind, Option.bind_some_fun, Option.none_bind, reduceCtorEq, Option.some_bind, Option.some.injEq] at hs
    subst hs
    rename_i slice'
    cases hs₃ : List.mapM (λ x => Entities.sliceAtLevel.sliceAtLevel entities x.sliceEUIDs n) eds <;>
      simp only [hs₃, Option.map_some', Option.some.injEq, Option.map_none', reduceCtorEq] at hs₂
    subst hs₂
    rw [Set.mem_union_iff_mem_or]
    right
    have ⟨ ed, hi₁, hf₁ ⟩ := List.mapM_some_implies_all_some hs₁ _ hi
    have ⟨ slice, _, hs ⟩ := List.mapM_some_implies_all_some hs₃ _ hi₁
    rw [hf₁] at hf ; injections hf ; subst hf
    cases hs₄ : Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs n <;>
      simp only [hs₄, reduceCtorEq, Option.some.injEq] at hs
    match n with
    | 0 => cases hw
    | n + 1 =>
      have ih := slice_contains_reachable hw hs₄
      rw [Set.mem_mapUnion_iff_mem_exists]
      subst hs
      rename_i ed_slice _
      exists ed_slice

/--
If an expression checks at level `n` and then evaluates to an entity, then that
entity must be in a slice at `n + 1`.
-/
theorem checked_eval_entity_in_slice  {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {slice entities : Entities} {ed : EntityData}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : TypedExpr.AtLevel tx n nmax)
  (hrt : ¬ TypedExpr.EntityLitViaPath tx [])
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
    checked_eval_entity_reachable hc hr ht hl hrt he (.euid euid) hf₁
  have hi := slice_contains_reachable hw hs₁
  rw [←hf]
  have hmk := map_find_mapm_value hs₂ hi
  rename_i eds
  have hsb : eds.SortedBy Prod.fst := by
    -- TODO: is sorted by `fst` because `fst` came from set elements
    sorry
  have hwf : (Map.mk eds).WellFormed := by
    rw [Map.wf_iff_sorted]
    simp [Map.toList, Map.kvs]
    exact hsb
  replace hwf : Map.mk eds = Map.make eds := by
    simpa [Map.WellFormed, Map.toList, Map.kvs] using hwf
  rw [hwf] at hmk
  simp [hmk]

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

theorem checked_eval_entity_find_entities_eq_find_slice  {n nmax : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {slice entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : TypedExpr.AtLevel tx n nmax)
  (hrt : ¬ TypedExpr.EntityLitViaPath tx [])
  (he : evaluate e request entities = .ok (Value.prim (Prim.entityUID euid)))
  (hs : slice = Entities.sliceAtLevel entities request (n + 1)) :
  entities.find? euid = slice.find? euid
:= by
  cases hfe : Map.find? entities euid
  case none =>
    simp [not_entities_then_not_slice hs hfe]
  case some =>
    have h₇ := checked_eval_entity_in_slice hc hr ht hl hrt he hfe hs
    simp [h₇]

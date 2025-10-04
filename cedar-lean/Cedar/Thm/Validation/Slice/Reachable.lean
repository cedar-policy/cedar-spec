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

import Cedar.Thm.Validation.Slice.Reachable.Basic
import Cedar.Thm.Validation.Slice.Reachable.BinaryApp
import Cedar.Thm.Validation.Slice.Reachable.GetAttr
import Cedar.Thm.Validation.Slice.Reachable.IfThenElse
import Cedar.Thm.Validation.Slice.Reachable.Record
import Cedar.Thm.Validation.Slice.Reachable.Var

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


theorem checked_eval_entity_lit_is_action {p : Prim} {n nmax : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {entities : Entities} {path : List Attr}
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.lit p) c env = .ok (tx, c'))
  (he : evaluate (.lit p) request entities = .ok v)
  (hel : tx.EntityAccessAtLevel env n nmax path)
  (ha : Value.EuidViaPath v path euid) :
  request.action = euid
:= by
  cases p
  case entityUID =>
    replace he : euid = env.sig.action := by
      replace ⟨ _, ht ⟩ := type_of_lit_inversion ht
      rw [ht] at hel
      cases hel
      simp only [evaluate, Except.ok.injEq] at he
      rw [←he] at ha
      cases ha
      rfl
    simp only [action_matches_env hr, he]
  all_goals
    simp only [evaluate, Except.ok.injEq] at he
    rw [←he] at ha
    cases ha

theorem and_not_euid_via_path {e₁ e₂: Expr} {entities : Entities} {path : List Attr}
  (he : evaluate (.and e₁ e₂) request entities = .ok v) :
  ¬ Value.EuidViaPath v path euid
:= by
  have he' := and_produces_bool_or_error e₁ e₂ request entities
  split at he' <;>
    first
    | contradiction
    | rename_i he''
      simp only [he'', Except.ok.injEq, reduceCtorEq] at he
  subst v
  intro ha
  cases ha

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
  all_goals
    simp only [Except.ok.injEq] at he
    rw [←he] at ha
    cases ha

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

  all_goals
    rw [←he] at ha
    cases ha

/--
If an expression checks at level `n` and then evaluates an entity (or a record
containing an entity), then that entity must reachable in `n + 1` steps.
-/
theorem checked_eval_entity_reachable {e : Expr} {n nmax: Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {request : Request} {entities : Entities} {v : Value} {path : List Attr} {euid : EntityUID}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate e request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  cases e
  case lit =>
    have hi : euid ∈ request.sliceEUIDs := by
      have hact := checked_eval_entity_lit_is_action hr ht he hl ha
      simp [hact, Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
    exact ReachableIn.in_start hi

  case var =>
    exact var_entity_reachable he ha hf

  case ite e₁ e₂ e₃ =>
    have ih₂ := @checked_eval_entity_reachable e₂
    have ih₃ := @checked_eval_entity_reachable e₃
    exact checked_eval_entity_reachable_ite hc hr ht hl he ha hf ih₂ ih₃

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
    exact checked_eval_entity_reachable_get_attr hc hr ht hl he ha hf ih

  case hasAttr e a =>
    exfalso
    exact has_attr_not_euid_via_path he ha

  case set es =>
    exfalso
    exact set_not_euid_via_path he ha

  case record rxs =>
    have ih : ∀ a x, (Map.make rxs).find? a = some x → CheckedEvalEntityReachable x := by
      intros a x hfx
      have : sizeOf x < sizeOf (Expr.record rxs) := by
        replace he := Map.make_mem_list_mem (Map.find?_mem_toList hfx)
        have h₁ := List.sizeOf_lt_of_mem he
        rw [Prod.mk.sizeOf_spec a x] at h₁
        simp only [Expr.record.sizeOf_spec, gt_iff_lt]
        omega
      exact @checked_eval_entity_reachable x
    exact checked_eval_entity_reachable_record hc hr ht hl he ha hf ih

  case call xfn args =>
    exfalso
    exact call_not_euid_via_path he ha
termination_by e

theorem in_work_then_in_slice {entities : Entities} {work : Set EntityUID} {euid : EntityUID} {n : Nat}
  (hw : euid ∈ work)
  : euid ∈ Entities.sliceAtLevel.sliceAtLevel entities work (n + 1)
:= by
  simp only [Entities.sliceAtLevel.sliceAtLevel]
  let slice' := ((List.filterMap (Map.find? entities) work.elts).map λ ed => Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs n).mapUnion id
  have ⟨ _, hc ⟩ := Set.mem_union_iff_mem_or work slice' euid
  apply hc
  simp [hw]

/--
If an entity is reachable in `n` steps, then it must be included in slice at
`n`. This lemma talks about the inner slicing function, so it's possible that
the entity isn't in the original entities if it's in `work`.
-/
theorem slice_contains_reachable {n: Nat} {work : Set EntityUID} {euid : EntityUID} {entities : Entities}
  (hw : ReachableIn entities work euid (n + 1)) :
  euid ∈ Entities.sliceAtLevel.sliceAtLevel entities work (n + 1)
:= by
  cases hw
  case in_start hw =>
    exact in_work_then_in_slice hw
  case step ed euid' hf hi hw =>
    simp only [Entities.sliceAtLevel.sliceAtLevel]
    let slice' := ((List.filterMap (Map.find? entities) work.elts).map λ ed => Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs n).mapUnion id
    rw [Set.mem_union_iff_mem_or]
    right
    cases n
    case _ => cases hw
    case _ n' =>
      simp only [Set.mem_mapUnion_iff_mem_exists, List.mem_map, List.mem_filterMap]
      exists Entities.sliceAtLevel.sliceAtLevel entities ed.sliceEUIDs (n' + 1)
      and_intros
      · exists ed
        and_intros
        · exists euid'
        · rfl
      · exact slice_contains_reachable hw

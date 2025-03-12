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

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem reachable_tag_step {n : Nat} {euid euid' : EntityUID} {start : Set EntityUID} {entities : Entities} {ed : EntityData} {tag : Tag} {path : List Attr}
  (hr : ReachableIn entities start euid n)
  (he₁ : entities.find? euid = some ed)
  (he₂ : ed.tags.find? tag = some tv)
  (he₃ : Value.EuidViaPath tv path euid') :
  ReachableIn entities start euid' (n + 1)
:= by
  cases hr
  case in_start n' hi =>
    have he₄ : euid' ∈ ed.sliceEUIDs := by
      simp only [EntityData.sliceEUIDs]
      rw [Set.mem_union_iff_mem_or]
      right
      rw [Set.mem_mapUnion_iff_mem_exists]
      exists tv
      constructor
      · exact Map.find?_some_implies_in_values he₂
      · exact in_val_then_val_slice he₃
    have hr' : ReachableIn entities ed.sliceEUIDs euid' (n' + 1) :=
      ReachableIn.in_start he₄
    exact ReachableIn.step euid hi he₁ hr'
  case step n' ed' euid'' he₁' hi hr' =>
    have ih := reachable_tag_step hr' he₁ he₂ he₃
    exact ReachableIn.step euid'' hi he₁' ih

theorem checked_eval_entity_reachable_get_tag {e₁ e₂: Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.binaryApp .getTag e₁ e₂) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (.binaryApp .getTag e₁ e₂) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (ih₁ : CheckedEvalEntityReachable e₁) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;> simp only [he₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  cases he₂ : evaluate e₂ request entities <;> simp only [he₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  simp only [apply₂] at he
  split at he <;> try contradiction
  rename_i euid' _ _

  have ⟨hc', ety, ty, tx₁, tx₂, c₁', c₂', htx₁, hty₁, htx₂, hty₂, ht, htx, hc₁⟩ := type_of_getTag_inversion ht
  subst htx hc'
  cases hl
  rename_i hl₁ hl₂
  simp only [getTag] at he
  cases he₃ : entities.tags euid' <;> simp only [he₃, Except.bind_ok, Except.bind_err, reduceCtorEq] at he
  simp only [Map.findOrErr] at he
  split at he <;> simp only [reduceCtorEq, Except.ok.injEq] at he
  subst he
  rename_i hv

  have ⟨ ed, hed, hed' ⟩ := entities_tags_then_find? he₃
  subst hed'
  have hf' : entities.contains euid' := by simp [Map.contains, Option.isSome, hed]

  have ih := ih₁ hc hr htx₁ hl₁ he₁ (.euid euid') hf'
  exact reachable_tag_step ih hed hv ha

theorem binary_op_not_euid_via_path {op : BinaryOp} {e₁ e₂: Expr} {entities : Entities} {path : List Attr}
  (hop : op ≠ .getTag)
  (he : evaluate (.binaryApp op e₁ e₂) request entities = .ok v) :
  ¬Value.EuidViaPath v path euid
:= by
  intro ha
  simp only [evaluate] at he
  cases he₁ : evaluate e₁ request entities <;> simp only [he₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  cases he₂ : evaluate e₂ request entities <;> simp only [he₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  simp only [apply₂, intOrErr, inₛ, hasTag] at he
  split at he <;> try split at he
  all_goals first
  | contradiction
  | simp only [Except.ok.injEq] at he
    rw [←he] at ha
    cases ha
  | rename_i vs
    cases he₃ : Set.mapOrErr Value.asEntityUID vs Error.typeError <;> simp only [he₃, Except.bind_err, Except.bind_ok, reduceCtorEq, Except.ok.injEq] at he
    subst he ; cases ha

theorem checked_eval_entity_reachable_binary {op : BinaryOp} {e₁ e₂: Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.binaryApp op e₁ e₂) c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate (.binaryApp op e₁ e₂) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (ih₁ : CheckedEvalEntityReachable e₁) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  cases hop : op == .getTag <;> simp only [beq_eq_false_iff_ne, beq_iff_eq] at hop
  · exfalso
    exact binary_op_not_euid_via_path hop he ha
  · subst op
    exact checked_eval_entity_reachable_get_tag hc hr ht hl he ha ih₁

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

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem checked_eval_entity_reachable_ite {e₁ e₂ e₃: Expr} {n : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : Environment} {entities : Entities} {path : List Attr}
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.ite e₁ e₂ e₃) c env = .ok (tx, c'))
  (hl : TypedExpr.EntityAccessAtLevel tx n nmax)
  (hel : ¬ TypedExpr.EntityLitViaPath tx path)
  (he : evaluate (.ite e₁ e₂ e₃) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hf : entities.contains euid)
  (ih₂ : CheckedEvalEntityReachable e₂)
  (ih₃ : CheckedEvalEntityReachable e₃) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have ⟨tx₁, bty₁, c₁, tx₂, c₂, tx₃, c₃, htx, htx₁, hty₁, hif ⟩ := type_of_ite_inversion ht
  have ⟨ hgc, v, he₁, hi₁⟩ := type_of_is_sound hc hr htx₁

  rw [htx] at hl
  cases hl
  rename_i hl₁ hl₂ hl₃

  rw [htx] at hel
  have hel₂ : ¬ TypedExpr.EntityLitViaPath tx₂ path := by
    intros hel₂
    exact hel (.ite_true hel₂)
  have hel₃ : ¬ TypedExpr.EntityLitViaPath tx₃ path := by
    intros hel₃
    exact hel (.ite_false hel₃)

  simp only [evaluate] at he
  cases he₁ : Result.as Bool (evaluate e₁ request entities) <;> simp only [he₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at he
  simp only [Result.as, Coe.coe, Value.asBool] at he₁
  split at he₁ <;> try contradiction
  split at he₁ <;> try contradiction
  injections he₁
  subst he₁
  rename_i _ b he₁'
  replace he₁ : Value.prim (Prim.bool b) = v := by
    unfold EvaluatesTo at he₁
    simp only [he₁', reduceCtorEq, Except.ok.injEq, false_or] at he₁
    exact he₁
  subst he₁

  split at he
  case isTrue hb =>
    subst hb
    have htx₂ : typeOf e₂ (c ∪ c₁) env = .ok (tx₂, c₂) := by
      split at hif <;> try simp only [hif]
      rw [hty₁] at hi₁
      have := instance_of_ff_is_false hi₁
      contradiction
    replace hgc : CapabilitiesInvariant c₁ request entities := by
      simp only [he₁', GuardedCapabilitiesInvariant, forall_const] at hgc
      exact hgc
    exact ih₂ (capability_union_invariant hc hgc) hr htx₂ hl₂ hel₂ he ha hf
  case isFalse hb =>
    replace hb : b = false := by
      cases b <;> simp only [Bool.true_eq_false] <;> contradiction
    subst hb
    have htx₃ : typeOf e₃ c env = .ok (tx₃, c₃) := by
      split at hif <;> try simp only [hif]
      rw [hty₁] at hi₁
      have := instance_of_tt_is_true hi₁
      contradiction
    exact ih₃ hc hr htx₃ hl₃ hel₃ he ha hf

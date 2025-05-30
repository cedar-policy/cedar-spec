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

import Cedar.Thm.SymCC.Compiler.Basic

/-!
This file proves the reduction lemmas for `.lit` and `.var` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem int64?_some {i : Int64} :
  BitVec.int64? i.toBitVec = some i
:= by
  simp only [BitVec.int64?, ↓reduceIte, Int64.toBitVec, Option.some.injEq]
  cases i ; rename_i i
  simp only [Int64.ofInt, UInt64.toInt64]
  cases i ; rename_i i
  simp only
  congr
  simp only [BitVec.ofInt_toInt]

theorem compile_evaluate_lit {p : Prim} {env : Env} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.lit p) εnv = .ok t) :
  evaluate (.lit p) env.request env.entities ∼ t
:= by
  cases p <;>
  simp only [compile, compilePrim, someOf, Except.ok.injEq] at h₁
  case bool | string =>
    subst h₁
    simp only [Same.same, SameResults, evaluate, SameValues, ne_eq, Term.value?,
      TermPrim.value?]
  case int i =>
    subst h₁
    simp only [Same.same, SameResults, evaluate, SameValues, ne_eq, Term.value?,
      TermPrim.value?]
    simp only [Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe,
      Coe.coe, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq,
      Value.prim.injEq, Prim.int.injEq, exists_eq_right]
    exact int64?_some
  case entityUID =>
    split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
    subst h₁
    simp only [Same.same, SameResults, evaluate, SameValues, ne_eq, Term.value?,
      TermPrim.value?]

theorem compile_evaluate_var {v : Var} {env : Env} {εnv : SymEnv} {t : Term}
  (h₁ : env ∼ εnv)
  (h₂ : compile (.var v) εnv = .ok t) :
  evaluate (.var v) env.request env.entities ∼ t
:= by
  simp only [Same.same, SameEnvs, SameRequests, SameValues] at h₁
  replace h₁ := h₁.left
  cases v <;>
  simp only [evaluate, Same.same, SameResults, ne_eq] <;>
  simp only [compile, compileVar] at h₂ <;>
  split at h₂ <;>
  simp only [Except.ok.injEq, someOf, reduceCtorEq] at h₂ <;>
  subst h₂ <;>
  simp only [SameValues] <;>
  simp only [h₁, Term.value?, TermPrim.value?]

theorem compile_interpret_lit {p : Prim} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (h₁ : compile (.lit p) εnv = .ok t) :
  compile (.lit p) (εnv.interpret I) = .ok (t.interpret I)
:= by
  cases p <;>
  simp only [compile, compilePrim, someOf, Except.ok.injEq] at *
  case bool | int | string =>
    subst h₁
    simp only [Term.interpret, someOf]
  case entityUID uid =>
    split at h₁ <;> simp at h₁
    subst h₁
    rename_i h₂
    have h₃ := interpret_entities_isValidEntityUID (εnv.entities) I uid
    simp only [h₂] at h₃
    simp only [SymEnv.interpret, h₃, ite_true, Term.interpret, someOf]

theorem compile_interpret_var {v : Var} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (h₁ : I.WellFormed εnv.entities)
  (h₂ : εnv.WellFormedFor (.var v))
  (h₃ : compile (.var v) εnv = .ok t) :
  compile (.var v) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace h₂ := wf_εnv_implies_wf_ρeq h₂.left
  simp only [SymRequest.WellFormed] at h₂
  cases v <;>
  simp only [compile, compileVar] at * <;>
  split at h₃ <;>
  simp only [Except.ok.injEq, reduceCtorEq] at h₃  <;>
  subst h₃ <;>
  rename_i h₄ <;>
  simp only [SymEnv.interpret, SymRequest.interpret, someOf]
  case' principal.isTrue =>
    replace h₂ : Term.WellFormed εnv.entities εnv.request.principal := by simp only [h₂]
    have h₅ := interpret_term_isEntityType h₁ h₂
  case' action.isTrue =>
    replace h₂ : Term.WellFormed εnv.entities εnv.request.action := by simp only [h₂]
    have h₅ := interpret_term_isEntityType h₁ h₂
  case' resource.isTrue =>
    replace h₂ : Term.WellFormed εnv.entities εnv.request.resource := by simp only [h₂]
    have h₅ := interpret_term_isEntityType h₁ h₂
  case' context.isTrue =>
    replace h₂ : Term.WellFormed εnv.entities εnv.request.context := by simp only [h₂]
    have h₅ := interpret_term_isRecordType h₁ h₂
  all_goals {
    simp only [←h₅, h₄, ite_true, Term.interpret, someOf]
  }

end Cedar.Thm

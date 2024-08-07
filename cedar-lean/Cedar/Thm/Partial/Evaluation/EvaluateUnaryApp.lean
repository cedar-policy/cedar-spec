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

import Cedar.Partial.Evaluator
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

/-! Theorems about `Partial.evaluateUnaryApp` -/

namespace Cedar.Thm.Partial.Evaluation.EvaluateUnaryApp

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Expr Prim UnaryOp)

/--
  `Partial.evaluateUnaryApp` on concrete arguments gives the same output as
  `Spec.apply₁` on the same arguments
-/
theorem on_concrete_eqv_concrete (op : UnaryOp) (v : Spec.Value) :
  Partial.evaluateUnaryApp op v = (Spec.apply₁ op v).map Partial.Value.value
:= by
  rfl

/--
  if `Spec.apply₁` returns `ok` with some value, that is a well-formed value as
  well

  This theorem does not actually require that the input value is WellFormed
-/
theorem specApply₁_wf {v : Spec.Value} {op : UnaryOp} :
  Spec.apply₁ op v = .ok v' → v'.WellFormed
:= by
  unfold Spec.apply₁
  intro h
  split at h <;> try simp at h <;> subst h
  · simp [Spec.Value.WellFormed, Prim.WellFormed]
  · unfold Spec.intOrErr at h
    split at h <;> simp at h
    subst h ; simp [Spec.Value.WellFormed, Prim.WellFormed]
  · simp [Spec.Value.WellFormed, Prim.WellFormed]
  · simp [Spec.Value.WellFormed, Prim.WellFormed]

/--
  if `Partial.evaluateUnaryApp` on a well-formed value returns `ok` with some
  value, that is a well-formed value as well
-/
theorem evaluateUnaryApp_wf {pval : Partial.Value} {op : UnaryOp}
  (wf : pval.WellFormed) :
  Partial.evaluateUnaryApp op pval = .ok pval' → pval'.WellFormed
:= by
  unfold Partial.evaluateUnaryApp
  cases pval <;> simp only [Except.ok.injEq]
  case residual r =>
    intro h₁ ; subst h₁
    simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed] at *
    exact wf
  case value v =>
    cases h₁ : Spec.apply₁ op v
    case error e => simp only [Except.bind_err, false_implies]
    case ok v' =>
      simp only [Except.bind_ok, Except.ok.injEq]
      intro h ; subst h ; simp only [Partial.Value.WellFormed]
      exact specApply₁_wf h₁

/--
  If `Partial.evaluateUnaryApp` produces `ok` with a concrete value, then so
  would partial-evaluating its operand
-/
theorem returns_concrete_then_operand_evals_to_concrete {pval₁ : Partial.Value} {op : UnaryOp} :
  Partial.evaluateUnaryApp op pval₁ = .ok (.value v) →
  ∃ v₁, pval₁ = .value v₁
:= by
  unfold Partial.evaluateUnaryApp
  cases pval₁
  case value v₁ => intro _ ; exists v₁
  case residual r₁ => simp only [Except.ok.injEq, exists_const, imp_self]

/--
  If `Partial.evaluateUnaryApp` returns a concrete value, then it returns the
  same value after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {op : UnaryOp} {subsmap : Subsmap} :
  Partial.evaluateUnaryApp op pval₁ = .ok (.value v) →
  Partial.evaluateUnaryApp op (pval₁.subst subsmap) = .ok (.value v)
:= by
  cases pval₁ <;> simp [Partial.evaluateUnaryApp]
  case value v₁ => simp [Subst.subst_concrete_value]

/--
  If `Partial.evaluateUnaryApp` returns an error, then it returns the same error
  after any substitution of unknowns
-/
theorem subst_preserves_errors {pval₁ : Partial.Value} {op : UnaryOp} {subsmap : Subsmap} :
  Partial.evaluateUnaryApp op pval₁ = .error e →
  Partial.evaluateUnaryApp op (pval₁.subst subsmap) = .error e
:= by
  cases pval₁ <;> simp [Partial.evaluateUnaryApp]
  case value v₁ => simp [Subst.subst_concrete_value, do_error]

/--
  If `Partial.evaluateUnaryApp` returns an error, but reducing its arg succeeds,
  then it returns the same error on the reduced arg
-/
theorem reducing_arg_preserves_errors {pval₁ : Partial.Value} {op : UnaryOp} {entities : Partial.Entities} :
  Partial.evaluateUnaryApp op pval₁ = .error e →
  Partial.evaluateValue pval₁ entities = .ok pval' →
  Partial.evaluateUnaryApp op pval' = .error e
:= by
  cases pval₁ <;> simp [Partial.evaluateUnaryApp]
  case value v₁ =>
    simp [Partial.evaluateValue]
    intro h₁ _ ; subst pval'
    simp [h₁]

/--
  If reducing the arg then `Partial.evaluateUnaryApp` returns a concrete value,
  then any subst before that process shouldn't make a difference.

  This is like `subst_preserves_evaluation_to_value` but with a reduce operation
  in front of the `Partial.evaluateUnaryApp` in both cases

  Takes an inductive hypothesis `ih` which says that
  `subst_preserves_evaluation_to_value` holds for `pv₁`
-/
theorem subst_preserves_reduce_evaluation_to_value {pv₁ pv₂ : Partial.Value} {op : UnaryOp} {entities : Partial.Entities} (subsmap : Subsmap)
  (ih : ∀ v, Partial.evaluateValue pv₁ entities = .ok (.value v) → Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap) = .ok (.value v)) :
  Partial.evaluateValue pv₁ entities = .ok pv₂ →
  Partial.evaluateUnaryApp op pv₂ = .ok (.value v) →
  ∃ pv₃,
    Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap) = .ok pv₃ ∧
    Partial.evaluateUnaryApp op pv₃ = .ok (.value v)
:= by
  cases pv₁ <;> simp [Partial.evaluateUnaryApp]
  case value v₁ =>
    simp [Subst.subst_concrete_value, Partial.evaluateValue]
    intro _ ; subst pv₂ ; simp only [imp_self]
  case residual r₁ =>
    cases pv₂ <;> simp only [Except.ok.injEq, false_implies, implies_true]
    case value v₂ =>
      intro h₁ h₂
      specialize ih v₂ h₁
      exists (.value v₂)

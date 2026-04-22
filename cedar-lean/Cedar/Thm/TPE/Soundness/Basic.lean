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


import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

/-!
This file contains basic utility theorems used in the TPE soundness proof.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem asValue_some {r : Residual} {v : Value} :
  r.asValue = .some v ↔ (∃ ty, r = .val v ty)
:= by
  simp only [Residual.asValue]
  split
  · simp
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact not_exists.mpr (h v)

theorem isError_true {r : Residual} :
  r.isError ↔ (∃ e ty, r = .error e ty)
:= by
  simp only [Residual.isError]
  split
  · simp
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_exists]
    exact h

theorem asValue_evaluate_val {r : Residual} {v : Value} :
  r.asValue = .some v → ∀ req es, r.evaluate req es = Except.ok v
:= by
  simp only [asValue_some, forall_exists_index]
  intro _ hv
  simp [hv, Residual.evaluate]

theorem isError_evaluate_err {r : Spec.Residual} :
  r.isError → ∀ req es, ∃ e, r.evaluate req es = .error e
:= by
  simp only [isError_true, forall_exists_index]
  intro _ he hr
  simp [Spec.Residual.evaluate, hr]

@[simp]
theorem asError_some {r : Residual} {e : Spec.Error} {ty : CedarType} :
  r.asError = some (e, ty) ↔ r = .error e ty
:= by
  simp only [Residual.asError]
  split
  · simp
  · simp only [reduceCtorEq, false_iff]
    rename_i h
    exact h e ty

@[simp]
theorem evaluate_error {e : Spec.Error} {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.error e ty).evaluate req es = .error e
:= by simp [Residual.evaluate]

@[simp]
theorem evaluate_val {v : Value} {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.val v ty).evaluate req es = .ok v
:= by simp [Residual.evaluate]

@[simp]
theorem okOrResidualError_ok {v : Value} {ty : CedarType} :
  okOrResidualError (.ok v) ty = .val v ty
:= by simp [okOrResidualError]

@[simp]
theorem okOrResidualError_error {e : Spec.Error} {ty : CedarType} :
  okOrResidualError (.error e) ty = .error e ty
:= by simp [okOrResidualError]

theorem okOrResidualError_eq_val_iff {r : Spec.Result Value} {ty : CedarType} {v : Value} {ty' : CedarType} :
  okOrResidualError r ty = .val v ty' ↔ r = .ok v ∧ ty = ty'
:= by cases r <;> simp

theorem okOrResidualError_eq_error_iff {r : Spec.Result Value} {ty : CedarType} {e : Spec.Error} {ty' : CedarType} :
  okOrResidualError r ty = .error e ty' ↔ r = .error e ∧ ty = ty'
:= by cases r <;> simp

@[simp]
theorem toOption_ok {v : α} :
  Except.toOption (.ok v : Except ε α) = .some v
:= by simp [Except.toOption]

@[simp]
theorem toOption_error {e : ε} :
  Except.toOption (.error e : Except ε α) = .none
:= by simp [Except.toOption]

@[simp]
theorem toOption_eq_some_iff {r : Except ε α} {v : α} :
  Except.toOption r = .some v ↔ r = .ok v
:= by cases r <;> simp

@[simp]
theorem toOption_eq_none_iff {r : Except ε α} :
  Except.toOption r = .none ↔ ∃ e, r = .error e
:= by cases r <;> simp

@[simp]
theorem someOrError_some {v : Value} {e : Spec.Error} {ty : CedarType} :
  someOrError (.some v) e ty = .val v ty
:= by simp [someOrError]

@[simp]
theorem someOrError_none {e : Spec.Error} {ty : CedarType} :
  someOrError .none e ty = .error e ty
:= by simp [someOrError]

@[simp]
theorem someOrError_eq_val_iff {o : Option Value} {e : Spec.Error} {ty : CedarType} {v : Value} {ty' : CedarType} :
  someOrError o e ty = .val v ty' ↔ o = .some v ∧ ty = ty'
:= by cases o <;> simp

@[simp]
theorem someOrError_eq_error_iff {o : Option Value} {e : Spec.Error} {ty : CedarType} {e' : Spec.Error} {ty' : CedarType} :
  someOrError o e ty = .error e' ty' ↔ o = .none ∧ e = e' ∧ ty = ty'
:= by cases o <;> simp

end Cedar.Thm

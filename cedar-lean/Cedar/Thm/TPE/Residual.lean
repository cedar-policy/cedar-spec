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
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map

/-!
This file contains basic utility theorems used in the TPE soundness proof.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

@[simp]
theorem residual_value_prim_evaluates  :
  (ResidualValue.prim p).evaluate req es = Except.ok p
:= by simp [ResidualValue.evaluate]

@[simp]
theorem residual_val_prim_evaluates  :
  (Residual.val (ResidualValue.prim p) ty).evaluate req es = Except.ok p
:= by simp [Residual.evaluate]

@[simp]
theorem residual_value_set_evaluates  :
  (ResidualValue.set elems).evaluate req es = Except.ok elems
:= by simp [ResidualValue.evaluate]

@[simp]
theorem residual_val_set_evaluates  :
  (Residual.val (ResidualValue.set elems) ty).evaluate req es = Except.ok elems
:= by simp [Residual.evaluate]

@[simp]
theorem residual_value_ext_evaluates  :
  (ResidualValue.ext e).evaluate req es = Except.ok e
:= by simp [ResidualValue.evaluate]

@[simp]
theorem residual_val_ext_evaluates  :
  (Residual.val (ResidualValue.ext e) ty).evaluate req es = Except.ok e
:= by simp [Residual.evaluate]

@[simp]
theorem asValue_inverse_asResidualValue (v : Value) :
  v.asResidualValue.asValue = some v
:= by
  match v with
  | .prim p => simp only [Value.asResidualValue, ResidualValue.asValue]
  | .set s => simp only [Value.asResidualValue, ResidualValue.asValue]
  | .ext x => simp only [Value.asResidualValue, ResidualValue.asValue]
  | .record as =>
    simp only [Value.asResidualValue]
    simp only [Map.mapOnValues₂_eq_mapOnValues as (fun x => ResidualAttribute.present x.asResidualValue)]
    simp only [ResidualValue.asValue, Option.pure_def, Option.bind_eq_bind]
    simp only [Map.mapMOnValues₂_eq_mapMOnValues (Map.mapOnValues (fun x => ResidualAttribute.present x.asResidualValue) as) (fun x => x.asValue)]
    simp only [Map.mapMOnValues_mapOnValues]
    rw [Map.mapMOnValues_some_of_id]
    · simp
    · intro v' hv'
      simp only [Function.comp_apply, ResidualAttribute.asValue]
      exact asValue_inverse_asResidualValue v'
termination_by sizeOf v
decreasing_by
  simp_wf
  have h1 := Map.sizeOf_lt_of_values hv'
  simp [Value.record.sizeOf_spec]
  omega


@[simp]
theorem residual_val_as_residual_val  :
  (Residual.val v ty).asResidualValue = some v
:= by simp [Residual.asResidualValue]

-- Helper: asValue is a left inverse of asResidualValue
theorem ResidualValue.asValue_eq_some_val {rv : ResidualValue} {v : Value} :
  rv.asValue = some v → rv = v.asResidualValue
:= by
  intro h
  cases rv with
  | prim p =>
    simp only [ResidualValue.asValue, Option.some.injEq] at h
    subst v; simp [Value.asResidualValue]
  | set s =>
    simp only [ResidualValue.asValue, Option.some.injEq] at h
    subst v; simp [Value.asResidualValue]
  | ext e =>
    simp only [ResidualValue.asValue, Option.some.injEq] at h
    subst v; simp [Value.asResidualValue]
  | record m =>
    sorry -- record case needs induction on map structure

@[simp]
theorem asValue_some {r : Residual} {v : Value} :
  r.asValue = .some v ↔ (∃ ty, r = .val v ty)
:= by
  constructor
  · intro h
    unfold Residual.asValue at h
    unfold Bind.kleisliRight at h
    simp only [Bind.bind] at h
    cases r
    case val rv ty =>
      simp only [Residual.asResidualValue, Option.bind_some] at h
      exact ⟨ty, by congr 1; exact ResidualValue.asValue_eq_some_val h⟩
    all_goals (simp [Residual.asResidualValue] at h)
  · intro ⟨ty, h⟩
    subst h
    unfold Residual.asValue Bind.kleisliRight
    simp only [Bind.bind, Residual.asResidualValue, Option.bind_some]
    exact asValue_inverse_asResidualValue _

@[simp]
theorem isError_true {r : Residual} :
  r.isError ↔ (∃ ty, r = .error ty)
:= by
  simp only [Residual.isError]
  split
  · simp
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact not_exists.mpr h

@[simp]
theorem evaluate_asResidualValue (v : Value) (req : Request) (es : Entities) :
  (v.asResidualValue).evaluate req es = .ok v
:= by
  match v with
  | .prim p => simp [Value.asResidualValue, ResidualValue.evaluate]
  | .set s => simp [Value.asResidualValue, ResidualValue.evaluate]
  | .ext x => simp [Value.asResidualValue, ResidualValue.evaluate]
  | .record as =>
    simp only [Value.asResidualValue, Map.mapOnValues₂_eq_mapOnValues as (fun x => ResidualAttribute.present x.asResidualValue)]
    rw [ResidualValue.evaluate.eq_def]; dsimp only []
    rw [Map.mapMKVsIntoValues₂_eq_mapMKVsIntoValues _ (fun kv => ResidualValue.evaluateAttr kv req es)]
    rw [Map.mapMKVsIntoValues_mapOnValues_roundtrip
      (fun x => ResidualAttribute.present x.asResidualValue)
      (fun kv => ResidualValue.evaluateAttr kv req es)
      as
      (fun ⟨k, v⟩ hkv => by
        simp only [ResidualValue.evaluateAttr]
        exact evaluate_asResidualValue v req es)]
    rfl
termination_by sizeOf v
decreasing_by
  simp_wf
  have h1 := Map.sizeOf_lt_of_values (Map.in_list_in_values hkv)
  simp [Value.record.sizeOf_spec]; omega

theorem asValue_evaluate_val {r : Residual} {v : Value} :
  r.asValue = .some v → ∀ req es, r.evaluate req es = Except.ok v
:= by
  intro h req es
  rw [asValue_some] at h
  rcases h with ⟨ty, h⟩
  subst h
  simp only [Residual.evaluate]
  exact evaluate_asResidualValue v req es

@[simp]
theorem err_evaluate_err  :
 ((Residual.error ty).evaluate req es).toOption = none
:= by simp [Residual.evaluate, Except.toOption]

theorem isError_evaluate_err {r : Spec.Residual} :
  r.isError → ∃ e, ∀ req es, r.evaluate req es = .error e
:= by
  simp [isError_true]
  intro _ he
  simp [he, Spec.Residual.evaluate]

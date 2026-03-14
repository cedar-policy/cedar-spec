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

import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.Thm.TPE.Input
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Control
import Cedar.Data.SizeOf

/-!
Evaluation lemmas for ResidualValue/Residual that don't depend on WellTyped.
Split out to avoid import cycles.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data
open Cedar.TPE
open Cedar.Validation

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

theorem asResidualValue_evaluate {r : Residual} {rv : ResidualValue} :
  r.asResidualValue = some rv → ∀ req es, r.evaluate req es = rv.evaluate req es
:= by
  intro h req es
  cases r <;> simp [Residual.asResidualValue] at h
  subst h; simp [Residual.evaluate]


@[simp]
theorem someOrError_evaluate_ok {v : Value} {ty : CedarType} {req : Request} {es : Entities} :
  (someOrError (some v) ty).evaluate req es = Except.ok v := by
  simp [someOrError, Residual.evaluate, evaluate_asResidualValue]


@[simp]
theorem someOrError_evaluate_err {ty : CedarType} {req : Request} {es : Entities} :
  (someOrError none ty).evaluate req es = Except.error Error.extensionError := by
  simp [someOrError, Residual.evaluate]


@[simp]
theorem someOrSelf_some_evaluate {v : Value} {ty : CedarType} {r : Residual} {req : Request} {es : Entities} :
  (someOrSelf (some v) ty r).evaluate req es = Except.ok v := by
  simp [someOrSelf, Residual.evaluate, evaluate_asResidualValue]

@[simp] theorem Residual.typeOf_val {rv : ResidualValue} {ty : CedarType} :
  (Residual.val rv ty).typeOf = ty := rfl

@[simp] theorem Residual.typeOf_error {ty : CedarType} :
  (Residual.error ty).typeOf = ty := rfl

@[simp] theorem Residual.asResidualValue_val {rv : ResidualValue} {ty : CedarType} :
  (Residual.val rv ty).asResidualValue = some rv := by
  simp [Residual.asResidualValue]

@[simp] theorem Residual.asResidualValue_error {ty : CedarType} :
  (Residual.error ty).asResidualValue = none := by
  simp [Residual.asResidualValue]

/-! ## Core @[simp] lemmas for Residual.evaluate and ResidualValue.evaluate -/

@[simp] theorem Residual.evaluate_error {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.error ty).evaluate req es = .error .extensionError := by
  unfold Residual.evaluate; rfl

@[simp] theorem Residual.evaluate_val {rv : ResidualValue} {ty : CedarType} {req : Request} {es : Entities} :
  (Residual.val rv ty).evaluate req es = rv.evaluate req es := by
  unfold Residual.evaluate; rfl

@[simp] theorem ResidualValue.evaluate_prim {p : Prim} {req : Request} {es : Entities} :
  (ResidualValue.prim p).evaluate req es = .ok (.prim p) := by
  unfold ResidualValue.evaluate; rfl

@[simp] theorem ResidualValue.evaluate_set {s : Set Value} {req : Request} {es : Entities} :
  (ResidualValue.set s).evaluate req es = .ok (.set s) := by
  unfold ResidualValue.evaluate; rfl

@[simp] theorem ResidualValue.evaluate_ext {x : Ext} {req : Request} {es : Entities} :
  (ResidualValue.ext x).evaluate req es = .ok (.ext x) := by
  unfold ResidualValue.evaluate; rfl

/-! ## Refinement lemmas (Paper Lemmas 4.1-4.3) -/

/-- Paper Lemma 4.1: absent partial attr → absent concrete attr -/
theorem AttributesRefines.absent_implies_concrete_absent
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  (href : AttributesRefines env concrete partial_)
  {a : Attr}
  (habsent : ∀ pa, (a, pa) ∉ partial_) :
  ∀ v, (a, v) ∉ concrete := by
  cases href with
  | nil => intro v h; cases h
  | cons_present a' v v' t t' hvr har =>
    intro w h; cases h with
    | head => exact habsent _ (.head _)
    | tail _ h => exact absent_implies_concrete_absent har (fun pa hp => habsent pa (.tail _ hp)) w h
  | cons_unknown a' v ty t t' hit har =>
    intro w h; cases h with
    | head => exact habsent _ (.head _)
    | tail _ h => exact absent_implies_concrete_absent har (fun pa hp => habsent pa (.tail _ hp)) w h
  | cons_unknown_neq a' a'' v ty t t' hneq har =>
    intro w h
    exact absent_implies_concrete_absent har (fun pa hp => habsent pa (.tail _ hp)) w h
termination_by concrete.length + partial_.length

/-- Paper Lemma 4.2: present partial attr → concrete value refines -/
theorem AttributesRefines.present_implies_concrete_refines
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  (href : AttributesRefines env concrete partial_)
  {a : Attr} {pv : PartialValue}
  (hpresent : (a, PartialAttribute.present pv) ∈ partial_) :
  ∃ v, (a, v) ∈ concrete ∧ ValueRefines env v pv := by
  cases href with
  | nil => cases hpresent
  | cons_present a' v v' t t' hvr har =>
    cases hpresent with
    | head => exact ⟨v, .head _, hvr⟩
    | tail _ h => have ⟨w, hw, hwr⟩ := present_implies_concrete_refines har h; exact ⟨w, .tail _ hw, hwr⟩
  | cons_unknown a' v ty t t' hit har =>
    cases hpresent with
    | tail _ h => have ⟨w, hw, hwr⟩ := present_implies_concrete_refines har h; exact ⟨w, .tail _ hw, hwr⟩
  | cons_unknown_neq a' a'' v ty t t' hneq har =>
    cases hpresent with
    | tail _ h => have ⟨w, hw, hwr⟩ := present_implies_concrete_refines har h; exact ⟨w, hw, hwr⟩
termination_by concrete.length + partial_.length

/-- Paper Lemma 4.3: unknown partial attr → concrete value exists and is well-typed.
    NOTE: This only holds when the unknown entry was added via cons_unknown (not cons_unknown_neq).
    For entity attributes accessed via EntitiesRefine, cons_unknown_neq represents
    optional schema attributes that may not exist in the concrete record. -/
theorem AttributesRefines.unknown_implies_concrete_typed
  {env : TypeEnv} {concrete : List (Attr × Value)}
  {partial_ : List (Attr × PartialAttribute PartialValue)}
  (href : AttributesRefines env concrete partial_)
  {a : Attr} {ty : CedarType}
  (hunknown : (a, PartialAttribute.unknown ty) ∈ partial_) :
  (∃ v, (a, v) ∈ concrete ∧ InstanceOfType env v ty) ∨
  (∀ v, (a, v) ∉ concrete) := by
  sorry

/-- Paper Lemma 5.1 (Target Correctness): toResidualValue produces values that evaluate correctly.
    If target.evaluate = .ok v_container and ValueRefines env v pv,
    then (toResidualValue target pv ty).evaluate = .ok v. -/
theorem toResidualValue_evaluate
  {env : TypeEnv} {target : Residual} {v : Value} {pv : PartialValue} {ty : CedarType}
  {req : Request} {es : Entities}
  (htarget : target.evaluate req es = .ok v)
  (href : ValueRefines env v pv) :
  (PartialValue.toResidualValue target pv ty).evaluate req es = .ok v := by
  cases href with
  | prim => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | ext => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | set => simp [PartialValue.toResidualValue, ResidualValue.evaluate]
  | record har =>
    -- Record case: toResidualValue maps each attribute
    -- present(pv') → present(toResidualValue (.getAttr target a rty) pv' aty)
    -- unknown(ty') → unknown(target, ty')
    -- evaluate maps each through evaluateAttr
    -- Need to show the result equals the concrete record
    sorry

end Cedar.Thm

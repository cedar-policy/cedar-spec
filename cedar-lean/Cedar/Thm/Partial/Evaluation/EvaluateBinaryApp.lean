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
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.WellFormed
import Cedar.Thm.Partial.Subst

/-! Theorems about `Partial.evaluateBinaryApp` -/

namespace Cedar.Thm.Partial.Evaluation.EvaluateBinaryApp

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (BinaryOp EntityUID Expr intOrErr Prim Result)

/--
  `Partial.Entities.ancestorsOrEmpty` on concrete entities is the same as
  `Spec.Entities.ancestorsOrEmpty` on those entities
-/
theorem ancestorsOrEmpty_on_concrete_eqv_concrete {entities : Spec.Entities} {uid : EntityUID} :
  Partial.Entities.ancestorsOrEmpty entities uid = Spec.Entities.ancestorsOrEmpty entities uid
:= by
  unfold Partial.Entities.ancestorsOrEmpty Spec.Entities.ancestorsOrEmpty
  unfold Spec.Entities.asPartialEntities Spec.EntityData.asPartialEntityData
  rw [← Map.find?_mapOnValues]
  cases entities.find? uid <;> simp

/--
  `Partial.inₑ` on concrete arguments is the same as `Spec.inₑ` on those arguments
-/
theorem partialInₑ_on_concrete_eqv_concrete {uid₁ uid₂ : EntityUID} {entities : Spec.Entities} :
  Partial.inₑ uid₁ uid₂ entities = Spec.inₑ uid₁ uid₂ entities
:= by
  unfold Partial.inₑ Spec.inₑ
  cases uid₁ == uid₂ <;> simp only [Bool.true_or, Bool.false_or]
  case false => simp only [ancestorsOrEmpty_on_concrete_eqv_concrete]

/--
  `Partial.inₛ` on concrete arguments is the same as `Spec.inₛ` on those arguments
-/
theorem partialInₛ_on_concrete_eqv_concrete {uid : EntityUID} {vs : Set Spec.Value} {entities : Spec.Entities} :
  Partial.inₛ uid vs entities = Spec.inₛ uid vs entities
:= by
  unfold Partial.inₛ Spec.inₛ
  simp only [partialInₑ_on_concrete_eqv_concrete]

/--
  `Partial.apply₂` on concrete arguments is the same as `Spec.apply₂` on those
  arguments
-/
theorem partialApply₂_on_concrete_eqv_concrete {op : BinaryOp} {v₁ v₂ : Spec.Value} {entities : Spec.Entities} :
  Partial.apply₂ op v₁ v₂ entities = (Spec.apply₂ op v₁ v₂ entities).map Partial.Value.value
:= by
  unfold Partial.apply₂ Spec.apply₂ Except.map
  cases op <;> split <;> rename_i h
  <;> simp only [false_implies, forall_const] at h
  <;> try simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
  case add | sub | mul => split <;> rename_i h <;> simp [h]
  case mem.h_10 uid₁ uid₂ => simp only [partialInₑ_on_concrete_eqv_concrete]
  case mem.h_11 uid vs =>
    simp only [partialInₛ_on_concrete_eqv_concrete]
    cases Spec.inₛ uid vs entities <;> simp only [Except.bind_ok, Except.bind_err]
  case mem.h_12 =>
    split <;> rename_i h₂ <;> split at h₂
    <;> simp only [imp_self, false_implies, implies_true, forall_const, forall_eq',
      Except.error.injEq, Spec.Value.prim.injEq, Spec.Value.set.injEq, Spec.Prim.entityUID.injEq,
      forall_apply_eq_imp_iff] at *
    exact h₂

/--
  `Partial.evaluateBinaryApp` on concrete arguments is the same as `Spec.apply₂` on
  those arguments
-/
theorem on_concrete_eqv_concrete {op : BinaryOp} {v₁ v₂ : Spec.Value} {entities : Spec.Entities} :
  Partial.evaluateBinaryApp op v₁ v₂ entities = (Spec.apply₂ op v₁ v₂ entities).map Partial.Value.value
:= by
  simp only [Partial.evaluateBinaryApp, partialApply₂_on_concrete_eqv_concrete]

/--
  if `Partial.inₛ` returns `ok` with some value, that is a well-formed value
-/
theorem partialInₛ_wf {uid : EntityUID} {vs : Set Spec.Value} :
  ∀ pval, Partial.inₛ uid vs entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.inₛ
  intro pval
  cases vs.mapOrErr Spec.Value.asEntityUID Spec.Error.typeError <;> simp
  case ok uids =>
    intro h ; subst h ; simp [Spec.Value.WellFormed, Prim.WellFormed]

/--
  if `Partial.apply₂` on two well-formed values and well-formed entities
  returns `ok` with some value, that is a well-formed value as well
-/
theorem partialApply₂_wf {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities}
  (wf₁ : v₁.WellFormed)
  (wf₂ : v₂.WellFormed) :
  ∀ pval, Partial.apply₂ op v₁ v₂ entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.apply₂
  intro pval
  split <;> intro h₁ <;> try simp at h₁ <;> subst h₁
  all_goals try {
    simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  }
  · rename_i i j
    cases h₂ : intOrErr (i.add? j) <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      unfold intOrErr at h₂
      split at h₂ <;> simp at h₂
      subst h₂
      simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  · rename_i i j
    cases h₂ : intOrErr (i.sub? j) <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      unfold intOrErr at h₂
      split at h₂ <;> simp at h₂
      subst h₂
      simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  · rename_i i j
    cases h₂ : intOrErr (i.mul? j) <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      unfold intOrErr at h₂
      split at h₂ <;> simp at h₂
      subst h₂
      simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  · rename_i uid vs
    cases h₂ : Partial.inₛ uid vs entities <;> simp [h₂] at h₁
    case ok v =>
      subst h₁
      simp [Partial.Value.WellFormed]
      exact partialInₛ_wf v h₂

/--
  if `Partial.evaluateBinaryApp` on two well-formed values and well-formed
  entities returns `ok` with some value, that is a well-formed value as well
-/
theorem evaluateBinaryApp_wf {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities}
  (wf₁ : pval₁.WellFormed)
  (wf₂ : pval₂.WellFormed) :
  ∀ pval, Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateBinaryApp
  split
  · rename_i v₁ v₂ h₁
    simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
    simp only [Partial.Value.WellFormed] at wf₁ wf₂
    exact partialApply₂_wf wf₁ wf₂
  · intro pval h₁ ; simp only [Except.ok.injEq] at h₁ ; subst h₁
    simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]

/--
  If `Partial.evaluateBinaryApp` produces `ok` with a concrete value, then so
  would partial-evaluating either of the operands
-/
theorem returns_concrete_then_operands_eval_to_concrete {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok (.value v) →
  (∃ v₁, pval₁ = .value v₁) ∧ (∃ v₂, pval₂ = .value v₂)
:= by
  unfold Partial.evaluateBinaryApp
  intro h₁
  cases pval₁ <;> cases pval₂
  case value.value v₁ v₂ =>
    exact And.intro (by exists v₁) (by exists v₂)
  all_goals simp only [Except.ok.injEq] at h₁

/--
  The return value of `Partial.inₑ` is not affected by substitution of unknowns
  in `entities`
-/
theorem partialInₑ_subst_const {uid₁ uid₂ : EntityUID} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.inₑ uid₁ uid₂ entities = Partial.inₑ uid₁ uid₂ (entities.subst subsmap)
:= by
  unfold Partial.inₑ
  cases uid₁ == uid₂ <;> simp only [Bool.false_or, Bool.true_or]
  case false =>
    rw [← Subst.entities_subst_preserves_ancestorsOrEmpty entities uid₁ subsmap]

/--
  The return value of `Partial.inₛ` is not affected by substitution of unknowns
  in `entities`
-/
theorem partialInₛ_subst_const {uid₁ : EntityUID} {s₂ : Set Spec.Value} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.inₛ uid₁ s₂ entities = Partial.inₛ uid₁ s₂ (entities.subst subsmap)
:= by
  unfold Partial.inₛ
  cases s₂.mapOrErr Spec.Value.asEntityUID .typeError
  case error e => simp only [Except.bind_err]
  case ok uids => simp only [← partialInₑ_subst_const, Except.bind_ok]

/--
  If `Partial.apply₂` returns a concrete value, then it returns the same value
  after any substitution of unknowns in `entities`
-/
theorem partialApply₂_subst_preserves_evaluation_to_value {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.apply₂ op v₁ v₂ entities = .ok (.value v) →
  Partial.apply₂ op v₁ v₂ (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.apply₂
  cases op
  case eq => simp only [Except.ok.injEq, Partial.Value.value.injEq, imp_self]
  case mem =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, imp_self]
      case entityUID.entityUID uid₁ uid₂ =>
        rw [← partialInₑ_subst_const]
        simp only [imp_self]
    case prim.set p₁ s₂ =>
      cases p₁ <;> simp only [imp_self]
      case entityUID uid₁ =>
        rw [← partialInₛ_subst_const]
        simp only [imp_self]
    all_goals simp only [Partial.apply₂.match_1.eq_12, imp_self]
  all_goals {
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, imp_self]
    all_goals simp only [Partial.apply₂.match_1.eq_12, imp_self]
  }

/--
  If `Partial.evaluateBinaryApp` returns a concrete value, then it returns
  the same value after any substitution of unknowns in `entities`
-/
theorem subst_preserves_evaluation_to_value {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .ok (.value v) →
  Partial.evaluateBinaryApp op pval₁ pval₂ (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateBinaryApp
  cases pval₁ <;> cases pval₂ <;> simp only [Except.ok.injEq, imp_self]
  case value.value v₁ v₂ => exact partialApply₂_subst_preserves_evaluation_to_value

/--
  If `Partial.apply₂` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns in `entities`
-/
theorem partialApply₂_subst_preserves_errors {v₁ v₂ : Spec.Value} {op : BinaryOp} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.apply₂ op v₁ v₂ entities = .error e →
  ∃ e', Partial.apply₂ op v₁ v₂ (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.apply₂]
  cases op
  case eq => simp only [exists_false, imp_self]
  case mem =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
    case prim.set p₁ s₂ =>
      cases p₁ <;> simp only [Except.error.injEq, exists_eq', implies_true]
      case entityUID uid₁ =>
        rw [← partialInₛ_subst_const]
        intro _ ; exists e
    all_goals simp only [Partial.apply₂.match_1.eq_12, Except.error.injEq, exists_eq', implies_true]
  case add | sub | mul =>
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
      case int.int i₁ i₂ => intro _ ; exists e
    all_goals simp only [Partial.apply₂.match_1.eq_12, Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
  all_goals {
    cases v₁ <;> cases v₂
    case prim.prim p₁ p₂ =>
      cases p₁ <;> cases p₂
      <;> simp only [Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
    all_goals simp only [Partial.apply₂.match_1.eq_12, Except.error.injEq, exists_eq', implies_true, exists_false, imp_self]
  }

/--
  If `Partial.evaluateBinaryApp` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns in
  `entities`
-/
theorem subst_preserves_errors {pval₁ pval₂ : Partial.Value} {op : BinaryOp} {entities : Partial.Entities} (subsmap : Subsmap) :
  Partial.evaluateBinaryApp op pval₁ pval₂ entities = .error e →
  ∃ e', Partial.evaluateBinaryApp op pval₁ pval₂ (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.evaluateBinaryApp]
  cases pval₁ <;> cases pval₂ <;> simp only [exists_false, imp_self]
  case value.value v₁ v₂ => exact partialApply₂_subst_preserves_errors

/--
  `Partial.apply₂` followed by a substitution and then `Partial.evaluateValue`,
  is equivalent to substituting first and then `Partial.apply₂`
-/
theorem reeval_eqv_substituting_first_partialApply₂ {op : BinaryOp} {v₁ v₂ : Spec.Value} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.apply₂ op v₁ v₂ entities = .ok pv →
  Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap) = Partial.apply₂ op v₁ v₂ (entities.subst subsmap)
:= by
  cases pv
  case value v =>
    simp only [Subst.subst_concrete_value, Partial.evaluateValue]
    intro h
    exact (EvaluateBinaryApp.partialApply₂_subst_preserves_evaluation_to_value h).symm
  case residual r =>
    cases op <;> simp only [Partial.apply₂, Except.ok.injEq, false_implies]
    case mem =>
      cases v₁
      case prim p₁ =>
        cases p₁
        case entityUID uid₁ =>
          cases v₂
          case prim p₂ =>
            cases p₂ <;> simp only [Except.ok.injEq, false_implies]
          case set s₂ => simp only [do_ok, and_false, exists_const, false_implies]
          all_goals simp only [false_implies]
        all_goals simp only [false_implies]
      all_goals simp only [false_implies]
    case less | lessEq | add | sub | mul =>
      cases v₁
      case prim p₁ =>
        cases p₁
        case int i₁ =>
          cases v₂
          case prim p₂ =>
            cases p₂
            case int i₂ =>
              simp only [do_ok, Except.ok.injEq, false_implies, and_false, exists_const]
            all_goals simp only [false_implies]
          all_goals simp only [false_implies]
        all_goals simp only [false_implies]
      all_goals simp only [false_implies]
    case contains =>
      cases v₁
      case set s₁ => simp only [Except.ok.injEq, false_implies]
      all_goals simp only [false_implies]
    case containsAll | containsAny =>
      cases v₁
      case set s₁ =>
        cases v₂
        case set s₂ => simp only [Except.ok.injEq, false_implies]
        all_goals simp only [false_implies]
      all_goals simp only [false_implies]

/--
  If `Partial.evaluateBinaryApp` returns a residual, re-evaluating that residual with a
  substitution is equivalent to substituting first, evaluating the args, and calling
  `Partial.evaluateBinaryApp` on the substituted/evaluated arg
-/
theorem reeval_eqv_substituting_first (op : BinaryOp) (pval₁ pval₂ : Partial.Value) (entities : Partial.Entities) (subsmap : Subsmap)
  (wf₁ : pval₁.WellFormed)
  (wf₂ : pval₂.WellFormed) :
  let re_evaluated := Partial.evaluateBinaryApp op pval₁ pval₂ entities >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)
  let subst_first := do
    let pval₁' ← Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap)
    let pval₂' ← Partial.evaluateValue (pval₂.subst subsmap) (entities.subst subsmap)
    Partial.evaluateBinaryApp op pval₁' pval₂' (entities.subst subsmap)
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  unfold Partial.evaluateBinaryApp
  split <;> rename_i h₁ <;> simp only [Prod.mk.injEq] at h₁ <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
  · -- both `pval₁` and `pval₂` are concrete
    rename_i v₁ v₂
    simp only [Partial.Value.subst, Partial.evaluateValue, Except.bind_ok]
    cases h₁ : Partial.apply₂ op v₁ v₂ entities <;> simp only [Except.bind_ok, Except.bind_err]
    case error e =>
      have ⟨e', h⟩ := EvaluateBinaryApp.partialApply₂_subst_preserves_errors h₁ (subsmap := subsmap)
      simp only [h, implies_true]
    case ok pv =>
      rw [← reeval_eqv_substituting_first_partialApply₂ h₁]
      split <;> simp only
  · -- `pval₁` and `pval₂` aren't both concrete
    simp only [Except.bind_ok]
    split
    · trivial
    · rename_i hₑ h₁ ; simp only [Prod.mk.injEq] at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
      cases hv₁ : Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap)
      <;> cases hv₂ : Partial.evaluateValue (pval₂.subst subsmap) (entities.subst subsmap)
      <;> simp only [hv₁, hv₂, Except.bind_ok, Except.bind_err, Except.error.injEq, imp_false,
        forall_apply_eq_imp_iff] at hₑ
      <;> simp only [Except.bind_ok, Except.bind_err]
      case error.error e₁ e₂ | error.ok e₁ pv₂ | ok.error pv₁ e₂ =>
        simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue,
          Partial.evaluateResidual, hv₁, hv₂, Except.bind_err, Except.bind_ok, Except.error.injEq,
          forall_eq'] at hₑ
      case ok.ok pv₁ pv₂ =>
        simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue,
          Partial.evaluateResidual, hv₁, hv₂, Except.bind_ok]
        split
        <;> rename_i h <;> simp only [Prod.mk.injEq] at h <;> replace ⟨h, h'⟩ := h <;> subst h h'
        <;> simp only [Partial.evaluateBinaryApp]

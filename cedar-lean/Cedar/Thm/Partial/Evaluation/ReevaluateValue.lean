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
import Cedar.Partial.Value
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.EvaluateBinaryApp
import Cedar.Thm.Partial.Evaluation.EvaluateHasAttr
import Cedar.Thm.Partial.Evaluation.EvaluateValue
import Cedar.Thm.Partial.Evaluation.ReevaluateGetAttr
import Cedar.Thm.Partial.Subst

/-! This file contains theorems about reevaluation of `Partial.evaluateValue` (and `Partial.evaluateResidual`). -/

namespace Cedar.Thm.Partial.Evaluation.ReevaluateValue

open Cedar.Data
open Cedar.Partial (Subsmap)
open Cedar.Spec (Error Prim)

private theorem mapM_ok_some {xs : List α} {ys : List β} {f : α → Except ε β} {g : β → Option ζ} :
  List.mapM f xs = .ok ys →
  List.mapM g ys = some zs →
  ∀ x ∈ xs, ∃ y ∈ ys, ∃ z ∈ zs, f x = .ok y ∧ g y = some z
:= by
  intro h₁ h₂ x hx
  replace ⟨y, hy, h₁⟩ := List.mapM_ok_implies_all_ok h₁ x hx
  replace ⟨z, hz, h₂⟩ := List.mapM_some_implies_all_some h₂ y hy
  exists y
  apply And.intro hy
  exists z

private theorem mapM_ok_none {xs : List α} {ys : List β} {f : α → Except ε β} {g : β → Option ζ} :
  List.mapM f xs = .ok ys →
  List.mapM g ys = none →
  ∃ x ∈ xs, ∃ y ∈ ys, f x = .ok y ∧ g y = none
:= by
  intro h₁ h₂
  replace ⟨y, hy, h₂⟩ := List.mapM_none_iff_exists_none.mp h₂
  replace ⟨x, hx, h₁⟩ := List.mapM_ok_implies_all_from_ok h₁ y hy
  exists x
  apply And.intro hx
  exists y

private theorem mapM_from_ok_some {xs : List α} {ys : List β} {f : α → Except ε β} {g : β → Option ζ} :
  List.mapM g ys = some zs →
  List.mapM f xs = .ok ys →
  ∀ z ∈ zs, ∃ y ∈ ys, ∃ x ∈ xs, f x = .ok y ∧ g y = some z
:= by
  intro h₁ h₂ z hz
  replace ⟨y, hy, h₁⟩ := List.mapM_some_implies_all_from_some h₁ z hz
  replace ⟨x, hx, h₂⟩ := List.mapM_ok_implies_all_from_ok h₂ y hy
  exists y
  apply And.intro hy
  exists x

private theorem mapM_ok_some_from_ok_some {xs : List α} {ys ys' : List β} {f f' : α → Except ε β} {g g' : β → Option ζ} :
  List.mapM f xs = .ok ys →
  List.mapM g ys = some zs →
  List.mapM f' xs = .ok ys' →
  List.mapM g' ys' = some zs' →
  ∀ z' ∈ zs', ∃ y' ∈ ys', ∃ x ∈ xs, ∃ y ∈ ys, ∃ z ∈ zs, f x = .ok y ∧ g y = some z ∧ f' x = .ok y' ∧ g' y' = some z'
:= by
  intro h₁ h₂ h₃ h₄ z' hz'
  replace ⟨y', hy', x, hx, h₃, h₄⟩ := mapM_from_ok_some h₄ h₃ z' hz'
  replace ⟨y, hy, z, hz, h₁, h₂⟩ := mapM_ok_some h₁ h₂ x hx
  exists y'
  apply And.intro hy'
  exists x
  apply And.intro hx
  exists y
  apply And.intro hy
  exists z

/--
  `mapM_ok_some_from_ok_some` specialized to a particular `g` and `g'`, which allows
  us to give a stronger conclusion
-/
private theorem mapM_ok_some_from_ok_some' {xs : List α} {ys ys' : List Partial.Value} {f f' : α → Except ε Partial.Value} :
  List.mapM f xs = .ok ys →
  List.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) ys = some zs →
  List.mapM f' xs = .ok ys' →
  List.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) ys' = some zs' →
  ∀ v' ∈ zs', Partial.Value.value v' ∈ ys' ∧ ∃ x ∈ xs, ∃ v, Partial.Value.value v ∈ ys ∧ f x = .ok (.value v) ∧ f' x = .ok (.value v') ∧ v ∈ zs
:= by
  intro h₁ h₂ h₃ h₄ z' hz'
  replace ⟨y', hy', x, hx, y, hy, z, hz, h₁, h₂, h₃, h₄⟩ := mapM_ok_some_from_ok_some h₁ h₂ h₃ h₄ z' hz'
  split at h₂ <;> simp at h₂ ; subst z ; rename_i v
  split at h₄ <;> simp at h₄ ; subst z' ; rename_i v'
  apply And.intro hy'
  exists x
  apply And.intro hx
  exists v

private theorem mapM_ok_some_from_ok_none {xs : List α} {ys ys' : List β} {f f' : α → Except ε β} {g g' : β → Option ζ} :
  List.mapM f xs = .ok ys →
  List.mapM g ys = some zs →
  List.mapM f' xs = .ok ys' →
  List.mapM g' ys' = none →
  ∃ y' ∈ ys', ∃ x ∈ xs, ∃ y ∈ ys, ∃ z ∈ zs, f x = .ok y ∧ g y = some z ∧ f' x = .ok y' ∧ g' y' = none
:= by
  intro h₁ h₂ h₃ h₄
  replace ⟨x, hx, y', hy', h₃, h₄⟩ := mapM_ok_none h₃ h₄
  replace ⟨y, hy, z, hz, h₁, h₂⟩ := mapM_ok_some h₁ h₂ x hx
  exists y'
  apply And.intro hy'
  exists x
  apply And.intro hx
  exists y
  apply And.intro hy
  exists z

/--
  `mapM_ok_some_from_ok_none` specialized to a particular `g` and `g'`, which allows
  us to give a stronger conclusion
-/
private theorem mapM_ok_some_from_ok_none' {xs : List α} {ys ys' : List Partial.Value} {f f' : α → Except ε Partial.Value} :
  List.mapM f xs = .ok ys →
  List.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) ys = some zs →
  List.mapM f' xs = .ok ys' →
  List.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) ys' = none →
  ∃ r, Partial.Value.residual r ∈ ys' ∧ ∃ x ∈ xs, ∃ v, Partial.Value.value v ∈ ys ∧ f x = .ok (.value v) ∧ f' x = .ok (.residual r)
:= by
  intro h₁ h₂ h₃ h₄
  replace ⟨y', hy', x, hx, y, hy, z, hz, h₁, h₂, h₃, h₄⟩ := mapM_ok_some_from_ok_none h₁ h₂ h₃ h₄
  split at h₂ <;> simp at h₂ ; subst z ; rename_i v
  split at h₄ <;> simp at h₄ ; rename_i r
  exists r
  apply And.intro hy'
  exists x
  apply And.intro hx
  exists v

private theorem mapM_ok_none_from_ok_none {xs : List α} {ys ys' : List β} {f f' : α → Except ε β} {g g' : β → Option ζ} :
  List.mapM f xs = .ok ys →
  List.mapM g ys = none →
  List.mapM f' xs = .ok ys' →
  List.mapM g' ys' = none →
  -- tracing backward from ys
  ∃ y₁ ∈ ys, ∃ y'₁ ∈ ys', ∃ x₁ ∈ xs, f x₁ = .ok y₁ ∧ g y₁ = none ∧ f' x₁ = .ok y'₁ ∧
  -- tracing backward from ys'
  ∃ y₂ ∈ ys, ∃ y'₂ ∈ ys', ∃ x₂ ∈ xs, f' x₂ = .ok y'₂ ∧ g' y'₂ = none ∧ f x₂ = .ok y₂
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨x₁, hx₁, y₁, hy₁, h₅, h₆⟩ := mapM_ok_none h₁ h₂
  have ⟨x₂, hx₂, y'₂, hy'₂, h₇, h₈⟩ := mapM_ok_none h₃ h₄
  replace ⟨y'₁, hy'₁, h₃⟩ := List.mapM_ok_implies_all_ok h₃ x₁ hx₁
  replace ⟨y₂, hy₂, h₁⟩ := List.mapM_ok_implies_all_ok h₁ x₂ hx₂
  exists y₁
  apply And.intro hy₁
  exists y'₁
  apply And.intro hy'₁
  exists x₁
  apply And.intro hx₁
  apply And.intro h₅
  apply And.intro h₆
  apply And.intro h₃
  exists y₂
  apply And.intro hy₂
  exists y'₂
  apply And.intro hy'₂
  exists x₂

/--
  `mapM_ok_none_from_ok_none` specialized to a particular `g` and `g'`, which allows
  us to give a stronger conclusion
-/
private theorem mapM_ok_none_from_ok_none' {xs : List α} {ys ys' : List Partial.Value} {f f' : α → Except ε Partial.Value} :
  List.mapM f xs = .ok ys →
  List.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) ys = none →
  List.mapM f' xs = .ok ys' →
  List.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) ys' = none →
  -- tracing backward from ys
  ∃ r, Partial.Value.residual r ∈ ys ∧ ∃ x ∈ xs, f x = .ok (.residual r) ∧ ∃ pv' ∈ ys', f' x = .ok pv' ∧
  -- tracing backward from ys'
  ∃ r', Partial.Value.residual r' ∈ ys' ∧ ∃ x' ∈ xs, f' x' = .ok (.residual r') ∧ ∃ pv ∈ ys, f x' = .ok pv
:= by
  intro h₁ h₂ h₃ h₄
  replace ⟨y₁, hy₁, y'₁, hy'₁, x₁, hx₁, h₁, h₂, h₃, y₂, hy₂, y'₂, hy'₂, x₂, hx₂, h₄, h₅, h₆⟩ := mapM_ok_none_from_ok_none h₁ h₂ h₃ h₄
  split at h₂ <;> simp at h₂ ; rename_i r
  split at h₅ <;> simp at h₅ ; rename_i r'
  exists r
  apply And.intro hy₁
  exists x₁
  apply And.intro hx₁
  apply And.intro h₁
  exists y'₁
  apply And.intro hy'₁
  apply And.intro h₃
  exists r'
  apply And.intro hy'₂
  exists x₂
  apply And.intro hx₂
  apply And.intro h₄
  exists y₂

mutual

/--
  Evaluating a `Partial.ResidualExpr` with `Partial.evaluateResidual`, then substituting, then re-evaluating,
  produces the same end-result as just substituting and then evaluating
-/
theorem evalResidual_reeval_eqv_substituting_first {r : Partial.ResidualExpr} {pv' : Partial.Value} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_r : r.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateResidual r entities = .ok pv' →
  Partial.evaluateValue (pv'.subst subsmap) (entities.subst subsmap) =
  Partial.evaluateValue (r.subst subsmap) (entities.subst subsmap)
:= by
  cases r <;> simp only [Partial.evaluateResidual, Partial.evaluateValue, Partial.ResidualExpr.subst,
    Partial.Value.subst, Except.ok.injEq, Bool.not_eq_true']
    <;> simp only [Partial.ResidualExpr.WellFormed] at wf_r
  case unknown u =>
    intro _ ; subst pv'
    simp only [Partial.Value.subst, Partial.ResidualExpr.subst]
  case and pv₁ pv₂ | or pv₁ pv₂ =>
    have := EvaluateValue.sizeOf_lt_and pv₁ pv₂
    have := EvaluateValue.sizeOf_lt_or pv₁ pv₂
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have ih₁ := reeval_eqv_substituting_first wf_r.left wf_e wf_s hpv₁
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err]
      case error e₁ =>
        cases pv₁' <;> simp
        case value v₁' =>
          simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.left hpv₁] at hpv₁'
        case residual r₁' =>
          intro _ ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst]
          simp [Partial.Value.subst] at ih₁
          simp [Partial.evaluateValue, Partial.evaluateResidual]
          simp [ih₁, hpv₁']
      case ok pv₁'' =>
        cases pv₁' <;> simp
        case residual r₁' =>
          intro _ ; subst pv'
          simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue,
            Partial.evaluateResidual, Bool.not_eq_true'] at *
          simp only [hpv₁'] at ih₁
          simp only [ih₁, Except.bind_ok]
        case value v₁' =>
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.left hpv₁] at hpv₁'
          subst pv₁''
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at *
          cases hv₁' : v₁'.asBool <;> simp
          case ok b₁' =>
            cases b₁' <;> simp
            all_goals try {
              -- this dispatches the `false` case for and, and the `true` case for or
              intro _ ; subst pv'
              simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
            }
            -- what follows is an extremely similar tactic sequence to what we did for pv₁,
            -- just for pv₂ this time. In the future we could reduce duplication (lemma? tactic?)
            cases hpv₂ : Partial.evaluateValue pv₂ entities
            <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
            case ok pv₂' =>
              have ih₂ := reeval_eqv_substituting_first wf_r.right wf_e wf_s hpv₂
              cases hpv₂' : Partial.evaluateValue (pv₂.subst subsmap) (entities.subst subsmap)
              <;> simp only [Except.bind_ok, Except.bind_err]
              case error e₂ =>
                cases pv₂' <;> simp
                case value v₂' =>
                  simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.right hpv₂] at hpv₂'
                case residual r₂' =>
                  intro _ ; subst pv'
                  simp [Partial.Value.subst, Partial.ResidualExpr.subst]
                  simp [Partial.Value.subst] at ih₂
                  simp [Partial.evaluateValue, Partial.evaluateResidual]
                  simp [ih₂, hpv₂', Spec.Value.asBool]
              case ok pv₂'' =>
                cases pv₂' <;> simp
                case residual r₂' =>
                  intro _ ; subst pv'
                  simp only [Spec.Value.asBool, Partial.Value.subst, Partial.ResidualExpr.subst,
                    Partial.evaluateValue, Partial.evaluateResidual, Bool.not_eq_true',
                    Except.bind_ok, Bool.true_eq_false, reduceIte] at *
                  simp only [hpv₂'] at ih₂
                  simp only [ih₂, Except.bind_ok]
                case value v₂' =>
                  simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.right hpv₂] at hpv₂'
                  subst pv₂''
                  simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at *
                  cases hv₂' : v₂'.asBool <;> simp
                  intro _ ; subst pv'
                  simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
  case binaryApp op pv₁ pv₂ =>
    have := EvaluateValue.sizeOf_lt_binaryApp op pv₁ pv₂
    -- this also shares a lot of commonality with the and/or proof.
    -- could potentially reuse the same lemma/tactic.
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> cases hpv₂ : Partial.evaluateValue pv₂ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok.ok pv₁' pv₂' =>
      have ih₁ := reeval_eqv_substituting_first wf_r.left wf_e wf_s hpv₁
      have ih₂ := reeval_eqv_substituting_first wf_r.right wf_e wf_s hpv₂
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> cases hpv₂' : Partial.evaluateValue (pv₂.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Partial.evaluateBinaryApp]
      case error.error e₁ _ | error.ok e₁ _ =>
        split <;> rename_i h₁
        <;> simp only [Prod.mk.injEq] at h₁ <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
        · simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.left hpv₁] at hpv₁'
        · rename_i hv
          intro h ; simp at h ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual, ih₁, ih₂, hpv₁', hpv₂']
      case ok.error _ e₂ =>
        split <;> rename_i h₁
        <;> simp only [Prod.mk.injEq] at h₁ <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
        · simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.right hpv₂] at hpv₂'
        · rename_i hv
          intro h ; simp at h ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual, ih₁, ih₂, hpv₁', hpv₂']
      case ok.ok pv₁'' pv₂'' =>
        simp [hpv₁'] at ih₁
        simp [hpv₂'] at ih₂
        split <;> rename_i h₁
        <;> simp only [Prod.mk.injEq] at h₁ <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
        · rename_i v₁ v₂
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at *
          subst pv₁'' pv₂''
          cases op <;> simp [Partial.apply₂]
          case eq =>
            intro _ ; subst pv'
            simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
          case less | lessEq | add | sub | mul =>
            cases v₁ <;> cases v₂
            case prim.prim p₁ p₂ =>
              cases p₁ <;> cases p₂ <;> simp
              case int.int i₁ i₂ =>
                cases Spec.intOrErr (i₁.add? i₂)
                <;> cases Spec.intOrErr (i₁.sub? i₂)
                <;> cases Spec.intOrErr (i₁.mul? i₂)
                <;> try simp
                all_goals {
                  intro _ ; subst pv'
                  simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
                }
            all_goals simp
          case mem =>
            cases v₁ <;> cases v₂
            case prim.prim p₁ p₂ =>
              cases p₁ <;> cases p₂ <;> simp
              case entityUID.entityUID uid₁ uid₂ =>
                intro _ ; subst pv'
                simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
                exact EvaluateBinaryApp.partialInₑ_subst_const
            case prim.set p₁ s₂ =>
              cases p₁ <;> simp
              case entityUID uid₁ =>
                rw [← EvaluateBinaryApp.partialInₛ_subst_const]
                intro h₁ ; replace ⟨v, h₁, h₂⟩ := do_ok.mp h₁
                subst pv'
                simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value, h₁]
            all_goals simp
          case contains =>
            cases v₁ <;> simp
            case set s₁ =>
              intro _ ; subst pv'
              simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
          case containsAll | containsAny =>
            cases v₁ <;> cases v₂ <;> simp
            case set.set s₁ s₂ =>
              intro _ ; subst pv'
              simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
        · rename_i hv
          simp only [Except.ok.injEq]
          intro _ ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual, ih₁, ih₂, hpv₁', hpv₂']
          split <;> rename_i h₁
          <;> simp only [Prod.mk.injEq] at h₁ <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
          · simp [Partial.evaluateBinaryApp]
          · rename_i hv'
            cases pv₁'' <;> cases pv₂'' <;> simp [Partial.evaluateBinaryApp]
            case value.value v₁' v₂' => exfalso ; exact hv' v₁' v₂' rfl rfl
  case ite pv₁ pv₂ pv₃ =>
    have := EvaluateValue.sizeOf_lt_ite pv₁ pv₂ pv₃
    -- the first many lines of this are identical to those in the and/or proof.
    -- in the future we could reduce duplication. (lemma? tactic?)
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have ih₁ := reeval_eqv_substituting_first wf_r.left wf_e wf_s hpv₁
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err]
      case error e₁ =>
        cases pv₁' <;> simp
        case value v₁' =>
          simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.left hpv₁] at hpv₁'
        case residual r₁' =>
          intro _ ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst]
          simp [Partial.Value.subst] at ih₁
          simp [Partial.evaluateValue, Partial.evaluateResidual]
          simp [ih₁, hpv₁']
      case ok pv₁'' =>
        cases pv₁' <;> simp
        case residual r₁' =>
          intro _ ; subst pv'
          simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue,
            Partial.evaluateResidual, Bool.not_eq_true'] at *
          simp only [hpv₁'] at ih₁
          simp only [ih₁, Except.bind_ok]
        case value v₁' =>
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r.left hpv₁] at hpv₁'
          subst pv₁''
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at *
          cases hv₁' : v₁'.asBool <;> simp
          case ok b₁' =>
            cases hpv₂ : Partial.evaluateValue pv₂ entities
            <;> cases hpv₃ : Partial.evaluateValue pv₃ entities
            <;> cases b₁' <;> simp
            case ok.error.true pv₂' e₃ | ok.ok.true pv₂' pv₃' =>
              intro _ ; subst pv'
              simp [reeval_eqv_substituting_first wf_r.right.left wf_e wf_s hpv₂]
            case error.ok.false e₂ pv₃' | ok.ok.false pv₂' pv₃' =>
              intro _ ; subst pv'
              simp [reeval_eqv_substituting_first wf_r.right.right wf_e wf_s hpv₃]
  case unaryApp op pv₁ =>
    have := EvaluateValue.sizeOf_lt_unaryApp op pv₁
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have ih₁ := reeval_eqv_substituting_first wf_r wf_e wf_s hpv₁
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err]
      case error e₁ =>
        cases pv₁'
        case value v₁' =>
          simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r hpv₁] at hpv₁'
        case residual r₁' =>
          simp [Partial.evaluateUnaryApp]
          intro _ ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst]
          simp [Partial.Value.subst] at ih₁
          simp [Partial.evaluateValue, Partial.evaluateResidual]
          simp [ih₁, hpv₁']
      case ok pv₁'' =>
        cases pv₁'
        case residual r₁' =>
          simp [Partial.evaluateUnaryApp]
          intro _ ; subst pv'
          simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue,
            Partial.evaluateResidual] at *
          simp only [hpv₁'] at ih₁
          simp only [ih₁, Except.bind_ok, Partial.evaluateUnaryApp]
        case value v₁' =>
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r hpv₁] at hpv₁'
          subst pv₁''
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at *
          intro h₁ ; simp [h₁]
          simp [Partial.evaluateUnaryApp] at h₁
          replace ⟨v₁, h₁, h₂⟩ := do_ok.mp h₁
          subst pv'
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
  case hasAttr pv₁ attr =>
    have := EvaluateValue.sizeOf_lt_hasAttr pv₁ attr
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have ih₁ := reeval_eqv_substituting_first wf_r wf_e wf_s hpv₁
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err]
      case error e₁ =>
        cases pv₁'
        case value v₁' =>
          simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r hpv₁] at hpv₁'
        case residual r₁' =>
          simp [Partial.evaluateHasAttr]
          intro _ ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst]
          simp [Partial.Value.subst] at ih₁
          simp [Partial.evaluateValue, Partial.evaluateResidual]
          simp [ih₁, hpv₁']
      case ok pv₁'' =>
        cases pv₁'
        case residual r₁' =>
          simp [Partial.evaluateHasAttr]
          intro _ ; subst pv'
          simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue,
            Partial.evaluateResidual] at *
          simp only [hpv₁'] at ih₁
          simp only [ih₁, Except.bind_ok, Partial.evaluateHasAttr]
        case value v₁' =>
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r hpv₁] at hpv₁'
          subst pv₁''
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at *
          simp [Partial.evaluateHasAttr]
          rw [← EvaluateHasAttr.hasAttr_subst_const wf_e]
          intro h₁ ; simp [h₁]
          replace ⟨v₁, h₁, h₂⟩ := do_ok.mp h₁
          subst pv'
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
  case getAttr pv₁ attr =>
    have := EvaluateValue.sizeOf_lt_getAttr pv₁ attr
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have wf₁ : pv₁'.WellFormed := EvaluateValue.evalValue_wf wf_r wf_e hpv₁
      have ih₁ := reeval_eqv_substituting_first wf_r wf_e wf_s hpv₁
      cases pv₁'
      case value v₁ =>
        simp only [Partial.Value.WellFormed] at wf₁
        cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
        <;> simp only [Except.bind_ok, Except.bind_err]
        case error e₁ =>
          simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r hpv₁] at hpv₁'
        case ok pv₁'' =>
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_r hpv₁] at hpv₁'
          subst pv₁''
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at ih₁
          simp [Partial.evaluateGetAttr]
          cases h₁ : Partial.getAttr v₁ attr entities <;> simp
          case ok pv₂ =>
            have wf₂ : pv₂.WellFormed := EvaluateGetAttr.getAttr_wf wf₁ wf_e _ h₁
            simp [EvaluateGetAttr.getAttr_subst_preserves_attrs wf₁ wf_e wf_s h₁]
            intro h₂
            simp [EvaluateValue.reduce_commutes_subst subsmap wf₂ h₂]
      case residual r₁ =>
        simp only [Partial.evaluateGetAttr, Except.ok.injEq]
        intro _ ; subst pv'
        simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
        simp only [Partial.Value.subst] at ih₁
        simp [ih₁]
  case set pvs =>
    have := EvaluateValue.sizeOf_lt_set pvs
    rw [List.mapM₁_eq_mapM (Partial.evaluateValue · entities)]
    rw [List.map₁_eq_map]
    rw [List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap))]
    rw [List.mapM_map]
    cases h₁ : pvs.mapM (Partial.evaluateValue · entities) <;> simp
    case ok pvs₂ =>
      cases h₂ : pvs.mapM (λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)) <;> simp
      case ok pvs₃ =>
        split <;> rename_i h₃ <;> simp
        · rename_i vs₂
          intro _ ; subst pv'
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
          split <;> rename_i h₄ <;> simp
          · rename_i vs₃
            simp [Set.make_make_eqv, List.Equiv, List.subset_def]
            and_intros <;> intro v hv
            · replace ⟨hv', pv₂, hpv₂, v', hv'', h₁, h₂, h₃⟩ := mapM_ok_some_from_ok_some' h₂ h₄ h₁ h₃ v hv ; clear h₄
              have wf₂ : pv₂.WellFormed := wf_r pv₂ hpv₂
              simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf₂ h₂] at h₁
              subst v'
              exact h₃
            · replace ⟨hv', pv, hpv, v', hv'', h₁, h₂, h₃⟩ := mapM_ok_some_from_ok_some' h₁ h₃ h₂ h₄ v hv ; clear h₄
              have wf : pv.WellFormed := wf_r pv hpv
              simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf h₁] at h₂
              subst v'
              exact h₃
          · replace ⟨r, hr, pv, hpv, v', hv', h₁, h₂⟩ := mapM_ok_some_from_ok_none' h₁ h₃ h₂ h₄ ; clear h₃ h₄
            have wf₁ : pv.WellFormed := wf_r pv hpv
            simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf₁ h₁] at h₂
        · intro _ ; subst pv'
          simp [Partial.Value.subst, Partial.ResidualExpr.subst, List.map₁_eq_map]
          simp [Partial.evaluateValue, Partial.evaluateResidual, List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap)), List.mapM_map]
          split <;> rename_i h₄
          · rename_i vs₃
            have ⟨r, hr, pv, hpv, v', hv', h₅, h₆⟩ := mapM_ok_some_from_ok_none' h₂ h₄ h₁ h₃
            cases h₇ : pvs₂.mapM (λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)) <;> simp
            case error e =>
              replace ⟨pv₂, hpv₂, h₇⟩ := List.mapM_error_implies_exists_error h₇
              replace ⟨pv₃, hpv₃, h₁⟩ := List.mapM_ok_implies_all_from_ok h₁ pv₂ hpv₂
              have wf₃ : pv₃.WellFormed := wf_r pv₃ hpv₃
              have : sizeOf pv₃ < sizeOf pvs := List.sizeOf_lt_of_mem hpv₃
              simp [reeval_eqv_substituting_first wf₃ wf_e wf_s h₁] at h₇
              replace h₂ := List.mapM_ok_implies_all_ok h₂ pv₃ hpv₃
              simp [h₇] at h₂
            case ok pvs₄ =>
              split <;> rename_i h₈
              · rename_i vs₄
                simp [Set.make_make_eqv, List.Equiv, List.subset_def]
                and_intros <;> intro v'' hv''
                · sorry
                · sorry
              · exfalso
                sorry
          · have ⟨r, hr, pv, hpv, h₅, pv₃, hpv₃, h₆, r', hr', pv', hpv', h₇, pv₂, hpv₂, h₈⟩ := mapM_ok_none_from_ok_none' h₁ h₃ h₂ h₄
            cases h₉ : pvs₂.mapM λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
            <;> simp
            case error e =>
              replace ⟨pv₂', hpv₂', h₉⟩ := List.mapM_error_implies_exists_error h₉
              replace ⟨pv'', hpv'', h₁⟩ := List.mapM_ok_implies_all_from_ok h₁ pv₂' hpv₂'
              have wf'' : pv''.WellFormed := wf_r pv'' hpv''
              have : sizeOf pv'' < sizeOf pvs := List.sizeOf_lt_of_mem hpv''
              have : sizeOf pvs < sizeOf (Partial.ResidualExpr.set pvs) := EvaluateValue.sizeOf_lt_set pvs
              simp [reeval_eqv_substituting_first wf'' wf_e wf_s h₁] at h₉
              cases pv₂'
              case value v₂ => simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf'' h₁] at h₉
              case residual r₂ =>
                sorry
            case ok pvs₄ =>
              split <;> rename_i h₁₀
              · exfalso
                rename_i vs₄
                sorry
              · simp only [Except.ok.injEq, Partial.Value.residual.injEq,
                  Partial.ResidualExpr.set.injEq]
                sorry
      case error e =>
        replace ⟨pv, hpv, h₂⟩ := List.mapM_error_implies_exists_error h₂
        have wf_pv : pv.WellFormed := wf_r pv hpv
        split <;> rename_i h₃ <;> simp only [Except.ok.injEq]
        <;> intro _ <;> subst pv'
        · exfalso
          rename_i vs₂
          replace ⟨pv₂, hpv₂, v₂, hv₂, h₁⟩ := mapM_ok_some h₁ h₃ pv hpv
          split at h₁ <;> simp at h₁
          replace ⟨h₁, h₁'⟩ := h₁ ; subst v₂ ; rename_i v₂
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_pv h₁] at h₂
        · replace ⟨pv', hpv', pv₂, hpv₂, h₁, h₃⟩ := mapM_ok_none h₁ h₃
          split at h₃ <;> simp at h₃ ; rename_i r₂
          simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
          rw [List.map₁_eq_map]
          rw [List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap))]
          rw [List.mapM_map]
          cases h₄ : pvs₂.mapM λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
          <;> simp
          case error e' =>
            sorry
          case ok pvs₃ =>
            split <;> rename_i h₅
            · exfalso
              rename_i vs₃
              replace ⟨pv₃, hpv₃, v₃, hv₃, h₄, h₅⟩ := mapM_ok_some h₄ h₅ (.residual r₂) hpv₂
              split at h₅ <;> simp at h₅ ; subst v₃ ; rename_i v₃
              sorry
            · replace ⟨pv₂, hpv₂, pv₃, hpv₃, h₄, h₅⟩ := mapM_ok_none h₄ h₅
              split at h₅ <;> simp at h₅ ; rename_i r₃
              exfalso
              sorry
  case record attrs =>
    have := EvaluateValue.sizeOf_lt_record attrs
    sorry
  case call xfn pvs =>
    have := EvaluateValue.sizeOf_lt_call xfn pvs
    sorry
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals try subst r
  all_goals try omega
  case _ | _ =>
    rename _ = Partial.ResidualExpr.set _ => h ; subst h
    omega

/--
  Evaluating a `Partial.Value` with `Partial.evaluateValue`, then substituting, then re-evaluating,
  produces the same end-result as just substituting and then evaluating
-/
theorem reeval_eqv_substituting_first {pv pv' : Partial.Value} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_pv : pv.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateValue pv entities = .ok pv' →
  Partial.evaluateValue (pv'.subst subsmap) (entities.subst subsmap) =
  Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
:= by
  cases pv <;> simp only [Partial.evaluateValue, Except.ok.injEq]
  case value v => intro _ ; subst pv' ; rfl
  case residual r =>
    simp only [Partial.Value.subst]
    simp only [Partial.Value.WellFormed] at wf_pv
    exact evalResidual_reeval_eqv_substituting_first subsmap wf_pv wf_e wf_s
termination_by sizeOf pv

end

end Cedar.Thm.Partial.Evaluation.ReevaluateValue

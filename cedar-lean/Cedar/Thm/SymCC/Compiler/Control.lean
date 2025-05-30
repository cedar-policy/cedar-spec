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

import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

/-!
This file proves the reduction lemmas for `.ite`, `.and`, and `.or` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

private theorem compile_evaluate_ite_none {x₂ x₃ : Expr} {εnv : SymEnv} {t : Term} {e : Spec.Error} {ty : TermType}
  (hwφ₂ : SymEnv.WellFormedFor εnv x₂)
  (hwφ₃ : SymEnv.WellFormedFor εnv x₃)
  (h₁   : ReduceIfSym t (Term.none ty) (compile x₂ εnv) (compile x₃ εnv))
  (h₂   : ¬e = Error.entityDoesNotExist) :
  (Except.error e : Spec.Result Value) ∼ t
:= by
  simp only [ReduceIfSym, Term.typeOf, TermType.option.injEq] at h₁
  replace ⟨h₁, t₂, t₃, h₃, h₄, h₅, h₆⟩ := h₁
  subst h₁
  replace ⟨hwφ₂, ty, hty⟩ := compile_wf hwφ₂ h₃
  replace hwφ₃ := (compile_wf hwφ₃ h₄).left
  have h₇ :
    (option.get (Term.none TermType.bool)).WellFormed εnv.entities ∧
    (option.get (Term.none TermType.bool)).typeOf = .bool := by
    exact wf_option_get (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (typeOf_term_none .bool)
  replace h₇ := (wf_ite h₇.left hwφ₂ hwφ₃ h₇.right h₅).right
  simp only [hty] at h₇
  simp only [pe_ifSome_none h₇] at h₆
  subst h₆
  exact same_error_implied_by h₂

theorem compile_evaluate_ite {x₁ x₂ x₃ : Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (h₁  : env ∼ εnv)
  (h₂  : env.WellFormedFor (.ite x₁ x₂ x₃))
  (h₃  : εnv.WellFormedFor (.ite x₁ x₂ x₃))
  (h₄  : compile (.ite x₁ x₂ x₃) εnv = .ok t)
  (ih₁ : ReduceEvaluate x₁)
  (ih₂ : ReduceEvaluate x₂)
  (ih₃ : ReduceEvaluate x₃) :
  evaluate (.ite x₁ x₂ x₃) env.request env.entities ∼ t
:= by
  replace ⟨t₁, hr₁, h₄⟩ := compile_ite_ok_implies h₄
  have ⟨hwf₁, hwf₂, hwf₃⟩ := wf_env_for_ite_implies h₂
  have ⟨hwφ₁, hwφ₂, hwφ₃⟩ := wf_εnv_for_ite_implies h₃
  replace ih₁ := ih₁ h₁ hwf₁ hwφ₁ hr₁
  simp only [evaluate, Result.as, Coe.coe, Value.asBool]
  simp_do_let (evaluate x₁ env.request env.entities) <;>
  rename_i h₅ <;>
  simp only [h₅] at ih₁
  case error e =>
    replace ⟨ih₁, tty, ih₁'⟩ := same_error_implies ih₁
    subst ih₁'
    simp only at h₄
    exact compile_evaluate_ite_none hwφ₂ hwφ₃ h₄ ih₁
  case ok v =>
    split <;> simp
    case h_1 b =>
      replace ih₁ := same_ok_bool_implies ih₁
      subst ih₁
      cases b <;>
      simp only [ReduceIfSym] at h₄ <;>
      rw [eq_comm] at h₄
      case false => simp only [ite_false, ih₃ h₁ hwf₃ hwφ₃ h₄, reduceCtorEq]
      case true  => simp only [ite_true, ih₂ h₁ hwf₂ hwφ₂ h₄]
    case h_2 v' hneq =>
      split at h₄
      case h_1 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        specialize hneq true ih₁
        contradiction
      case h_2 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        specialize hneq false ih₁
        contradiction
      case h_3 =>
        replace ih₁ := same_ok_value_implies_lit ih₁
        replace ⟨hwφ₁, ty, hty⟩ := compile_wf hwφ₁ hr₁
        replace hr₁ := wfl_of_type_option_is_option (And.intro hwφ₁ ih₁) hty
        rcases hr₁ with hr₁ | hr₁
        case inl =>
          subst hr₁
          exact compile_evaluate_ite_none hwφ₂ hwφ₃ h₄ (by simp only [not_false_eq_true, reduceCtorEq])
        case inr h₅ h₆ =>
          replace ⟨t', hr₁, hr₁'⟩ := hr₁ ; subst hr₁ hr₁'
          simp only [ReduceIfSym, Term.typeOf, TermType.option.injEq] at h₄
          replace hwφ₁ := wf_term_some_implies hwφ₁
          replace ih₁ := lit_term_some_implies_lit ih₁
          replace ih₁ := wfl_of_type_bool_is_true_or_false (And.intro hwφ₁ ih₁) h₄.left
          rcases ih₁ with ih₁ | ih₁ <;>
          simp [ih₁] at h₅ h₆

theorem compile_interpret_ite {x₁ x₂ x₃ : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (h₁  : I.WellFormed εnv.entities)
  (h₂  : εnv.WellFormedFor (.ite x₁ x₂ x₃))
  (h₃  : compile (.ite x₁ x₂ x₃) εnv = .ok t)
  (ih₁ : ReduceInterpret x₁)
  (ih₂ : ReduceInterpret x₂)
  (ih₃ : ReduceInterpret x₃) :
  compile (.ite x₁ x₂ x₃) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨_, hr₁, h₃⟩ := compile_ite_ok_implies h₃
  have ⟨hwf₁, hwf₂, hwf₃⟩ := wf_εnv_for_ite_implies h₂
  simp only [compile, ih₁ h₁ hwf₁ hr₁, Except.bind_ok]
  clear ih₁ h₂
  split at h₃
  case h_1 =>
    simp only [Term.interpret, someOf, compileIf]
    rw [eq_comm] at h₃
    exact ih₂ h₁ hwf₂ h₃
  case h_2 =>
    simp only [Term.interpret, someOf, compileIf]
    rw [eq_comm] at h₃
    exact ih₃ h₁ hwf₃ h₃
  case h_3 t₁ _ h₄ h₅ =>
    replace ⟨hopt, t₂, t₃, hr₂, hr₃, hty, h₃⟩ := h₃
    simp only [compileIf, ih₂ h₁ hwf₂ hr₂, ih₃ h₁ hwf₃ hr₃, Except.bind_ok]
    clear ih₂ ih₃
    replace hwf₁ := compile_wf hwf₁ hr₁
    replace hwf₂ := compile_wf hwf₂ hr₂
    replace hwf₃ := compile_wf hwf₃ hr₃
    have ⟨h₆, h₇⟩ := wf_option_get hwf₁.left hopt
    have h₈ := wf_ite h₆ hwf₂.left hwf₃.left h₇ hty
    clear hr₁ hr₂ hr₃
    split
    case h_3 hopt' _ _ =>
      have hwf₁' := wf_option_get (interpret_term_wf h₁ hwf₁.left).left hopt'
      have hwf₂' := interpret_term_wf h₁ hwf₂.left
      have hwf₃' := interpret_term_wf h₁ hwf₃.left
      simp only [hwf₂'.right, hty, hwf₃'.right, ite_true, Except.ok.injEq]
      simp only [h₃,
        interpret_ifSome h₁ hwf₁.left h₈.left,
        interpret_ite h₁ h₆ hwf₂.left hwf₃.left h₇ hty,
        interpret_option_get I hwf₁.left hopt]

      have h₉ := (wf_ite hwf₁'.left hwf₂'.left hwf₃'.left hwf₁'.right
        (by simp [hwf₂'.right, hwf₃'.right, hty])).right

      have h₇' := wf_option_get' h₁ hwf₁.left hopt
      have h₈' := wf_ite h₇'.left hwf₂.left hwf₃.left h₇'.right hty
      have h₉' := (interpret_term_wf h₁ h₈'.left).right
      simp only [h₈'.right,
        interpret_ite h₁ h₇'.left hwf₂.left hwf₃.left h₇'.right hty,
        interpret_option_get' h₁ hwf₁.left hopt] at h₉'

      replace ⟨_, hwf₂⟩ := hwf₂.right
      simp only [hwf₂, hwf₂'.right] at h₉ h₉'
      simp [pe_ifSome_get_eq_get' I
          (Factory.ite · (Term.interpret I t₂) (Term.interpret I t₃))
          (interpret_term_wfl h₁ hwf₁.left).left hopt' h₉ h₉']
    case h_4 h =>
      simp only [← (interpret_term_wf h₁ hwf₁.left).right] at hopt
      simp only [hopt, forall_const] at h
    case' h_1 =>
      have ⟨_, hty'⟩ := hwf₂.right
      simp only [← (interpret_term_wf h₁ hwf₂.left).right] at hty'
    case' h_2 =>
      have ⟨_, hty'⟩ := hwf₃.right
      simp only [← (interpret_term_wf h₁ hwf₃.left).right] at hty'
    case h_1 heq _ | h_2 heq _ =>
      subst h₃
      simp only [
        Except.ok.injEq,
        heq,
        interpret_ifSome h₁ hwf₁.left h₈.left,
        interpret_ite h₁ h₆ hwf₂.left hwf₃.left h₇ hty,
        interpret_option_get I hwf₁.left hopt,
        pe_option_get_some,
        pe_ite_true,
        pe_ite_false,
        pe_ifSome_some hty',
        option.get']

private theorem compile_evaluate_and_none {x₂ : Expr} {εnv : SymEnv} {t : Term} {e : Spec.Error} {ty : TermType}
  (hwφ₂ : SymEnv.WellFormedFor εnv x₂)
  (h₁   : ReduceAndSym t (Term.none ty) (compile x₂ εnv))
  (h₂   : ¬e = Error.entityDoesNotExist) :
  (Except.error e : Spec.Result Value) ∼ t
:= by
  simp only [ReduceAndSym, Term.typeOf, TermType.option.injEq] at h₁
  replace ⟨h₁, t₂, h₃, h₄, h₅⟩ := h₁
  subst h₁
  replace ⟨hwφ₂, _, _⟩ := compile_wf hwφ₂ h₃
  subst h₅
  have hopt := @wf_option_get εnv.entities (Term.none TermType.bool) .bool
    (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (typeOf_term_none .bool)
  have hite := @wf_ite
    εnv.entities (option.get (Term.none TermType.bool)) t₂ (Term.some (Term.prim (TermPrim.bool false)))
    hopt.left hwφ₂ (Term.WellFormed.some_wf wf_bool) hopt.right
    (by simp only [typeOf_term_some, typeOf_bool, h₄])
  rw [h₄] at hite
  simp [pe_ifSome_none hite.right]
  exact same_error_implied_by h₂

private theorem compile_bool_same_implies_bool {x : Expr} {εnv : SymEnv} {t : Term} {v : Value}
  (hwφ : Term.WellFormed εnv.entities t)
  (hr  : compile x εnv = Except.ok t)
  (hs  : (Except.ok v : Spec.Result Value) ∼ t)
  (hty : Term.typeOf t = TermType.option TermType.bool) :
  ∃ b, t = .some (.prim (.bool b)) ∧ v = .prim (.bool b)
:= by
  have hlit := wfl_of_type_option_is_option (And.intro hwφ (same_ok_value_implies_lit hs)) hty
  rcases hlit with hlit | ⟨t', hlit, hty'⟩ <;> subst hlit
  case inl => simp only [Same.same, SameResults] at hs
  case inr =>
    cases hwφ ; rename_i hwφ
    have hlit := lit_term_some_implies_lit (same_ok_value_implies_lit hs)
    replace ⟨b, hlit⟩ := wfl_of_type_bool_is_bool (And.intro hwφ hlit) hty'
    subst hlit
    exists b
    simp only [true_and]
    exact same_ok_bool_term_implies hs

theorem compile_evaluate_and {x₁ x₂ : Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (h₁  : env ∼ εnv)
  (h₂  : env.WellFormedFor (.and x₁ x₂))
  (h₃  : εnv.WellFormedFor (.and x₁ x₂))
  (h₄  : compile (.and x₁ x₂) εnv = .ok t)
  (ih₁ : ReduceEvaluate x₁)
  (ih₂ : ReduceEvaluate x₂) :
  evaluate (.and x₁ x₂) env.request env.entities ∼ t
:= by
  replace ⟨_, hr₁, h₄⟩ := compile_and_ok_implies h₄
  have ⟨hwf₁, hwf₂⟩ := wf_env_for_and_implies h₂
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_and_implies h₃
  replace ih₁ := ih₁ h₁ hwf₁ hwφ₁ hr₁
  simp only [evaluate, Result.as, Coe.coe, Value.asBool]
  simp_do_let (evaluate x₁ env.request env.entities) <;>
  rename_i h₅ <;>
  simp only [h₅] at ih₁
  case error =>
    replace ⟨ih₁, tty, ih₁'⟩ := same_error_implies ih₁
    subst ih₁'
    simp only at h₄
    exact compile_evaluate_and_none hwφ₂ h₄ ih₁
  case ok =>
    split <;>
    simp only [Bool.not_eq_true', Except.bind_ok, Except.bind_err]
    case h_1 t₁ v b =>
      replace ih₁ := same_ok_bool_implies ih₁
      subst ih₁
      cases b <;> simp only [ite_true, ite_false] at *
      case false =>
        subst h₄
        exact same_ok_bool
      case true =>
        replace ⟨t₂, h₄, hty, ht⟩ := h₄.right
        simp only [pe_option_get_some, pe_ite_true, pe_ifSome_some hty] at ht
        subst ht
        replace ih₂ := ih₂ h₁ hwf₂ hwφ₂ h₄
        simp_do_let (evaluate x₂ env.request env.entities)
        case error hx₂ =>
          simp only [hx₂] at ih₂
          exact ih₂
        case ok hx₂ =>
          simp only [hx₂] at ih₂
          have ⟨_, _, hvt⟩ := compile_bool_same_implies_bool ((compile_wf hwφ₂ h₄).left) h₄ ih₂ hty
          subst hvt
          simp only [↓reduceIte, pure, Except.pure, Except.bind_ok, ih₂]
    case h_2 t₁ v₁ _ hneq =>
      split at h₄
      case h_1 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        subst ih₁
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq
      case h_2 =>
        have ⟨_, _, hvt⟩ := compile_bool_same_implies_bool ((compile_wf hwφ₁ hr₁).left) hr₁ ih₁ h₄.left
        subst hvt
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq

theorem compile_interpret_and {x₁ x₂ : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (h₁  : I.WellFormed εnv.entities)
  (h₂  : εnv.WellFormedFor (.and x₁ x₂))
  (h₃  : compile (.and x₁ x₂) εnv = .ok t)
  (ih₁ : ReduceInterpret x₁)
  (ih₂ : ReduceInterpret x₂) :
  compile (.and x₁ x₂) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨_, hr₁, h₃⟩ := compile_and_ok_implies h₃
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_and_implies h₂
  simp only [compile, ih₁ h₁ hwφ₁ hr₁, Except.bind_ok]
  clear ih₁ h₂
  split at h₃
  case h_1 =>
    simp only [interpret_term_some, interpret_term_prim, someOf, compileAnd]
    subst h₃
    simp only [interpret_term_some, interpret_term_prim]
  case h_2 t₁ _ hneq =>
    replace ⟨ht₁, t₂, hr₂, ht₂, h₃⟩ := h₃
    simp only [compileAnd, ih₂ h₁ hwφ₂ hr₂, Except.bind_ok]
    replace hwφ₁ := compile_wf hwφ₁ hr₁
    replace hwφ₂ := compile_wf hwφ₂ hr₂
    have hopt := wf_option_get hwφ₁.left ht₁
    have hite := @wf_ite
      εnv.entities (option.get t₁) t₂ (Term.some (Term.prim (TermPrim.bool false)))
      hopt.left hwφ₂.left (Term.WellFormed.some_wf wf_bool)
      hopt.right (by simp only [Term.typeOf, TermPrim.typeOf, ht₂])
    split
    case h_1 heq =>
      simp only [heq, h₃, Except.ok.injEq]
      simp only [
        interpret_ifSome h₁ hwφ₁.left hite.left,
        interpret_ite h₁ hopt.left hwφ₂.left (wf_term_some wf_bool rfl).left
          hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
        interpret_term_some, interpret_term_prim, heq]
      simp only [interpret_option_get I hwφ₁.left ht₁, heq]
      simp only [pe_option_get'_some, pe_ite_false]
      simp only [pe_ifSome_some typeOf_term_some]
    case h_2  =>
      split
      case isTrue ht₁' _ ht₂' =>
        subst h₃

        simp only [Except.ok.injEq,
          interpret_ifSome h₁ hwφ₁.left hite.left, someOf,
          interpret_ite h₁ hopt.left hwφ₂.left (wf_term_some wf_bool rfl).left
            hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
          interpret_option_get I hwφ₁.left ht₁,
          interpret_term_some, interpret_term_prim]

        have hoptI := wf_option_get (interpret_term_wf h₁ hwφ₁.left).left ht₁'

        have hoptI' := interpret_term_wf h₁ hwφ₁.left
        simp only [ht₁] at hoptI'
        replace hoptI' := wf_option_get' h₁ hoptI'.left hoptI'.right

        replace hwφ₂ := (interpret_term_wf h₁ hwφ₂.left).left

        have ht' : Term.typeOf (Term.interpret I t₂) = Term.typeOf (Term.some (Term.prim (TermPrim.bool false))) := by
          simp only [Term.typeOf, TermPrim.typeOf, ht₂']

        have hto := wf_ite hoptI.left hwφ₂ (Term.WellFormed.some_wf wf_bool) hoptI.right ht'
        have hto' := wf_ite hoptI'.left hwφ₂ (Term.WellFormed.some_wf wf_bool) hoptI'.right ht'
        rw [ht₂'] at hto hto'

        exact @pe_ifSome_get_eq_get'
          εnv.entities I (Term.interpret I t₁) .bool .bool
          (Factory.ite · (Term.interpret I t₂) (Term.some (Term.prim (TermPrim.bool false))))
          (interpret_term_wfl h₁ hwφ₁.left).left
          (by assumption) (by simp only [hto]) (by simp only [hto'])

      case isFalse ht₂' =>
        have hwφ₂' := (interpret_term_wf h₁ hwφ₂.left).right
        simp only [hwφ₂', ht₂, not_true_eq_false] at ht₂'
    case h_3 ht₁' =>
      have hwφ₁' := (interpret_term_wf h₁ hwφ₁.left).right
      simp only [hwφ₁', ht₁, forall_const] at ht₁'

private theorem compile_evaluate_or_none {x₂ : Expr} {εnv : SymEnv} {t : Term} {e : Spec.Error} {ty : TermType}
  (hwφ₂ : SymEnv.WellFormedFor εnv x₂)
  (h₁   : ReduceOrSym t (Term.none ty) (compile x₂ εnv))
  (h₂   : ¬e = Error.entityDoesNotExist) :
  (Except.error e : Spec.Result Value) ∼ t
:= by
  simp only [ReduceOrSym, Term.typeOf, TermType.option.injEq] at h₁
  replace ⟨h₁, t₂, h₃, h₄, h₅⟩ := h₁
  subst h₁
  replace ⟨hwφ₂, _, _⟩ := compile_wf hwφ₂ h₃
  subst h₅
  have hopt := @wf_option_get εnv.entities (Term.none TermType.bool) .bool
    (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (typeOf_term_none .bool)
  have hite := @wf_ite
    εnv.entities (option.get (Term.none TermType.bool)) (Term.some (Term.prim (TermPrim.bool true))) t₂
    hopt.left (Term.WellFormed.some_wf wf_bool) hwφ₂ hopt.right
    (by simp only [typeOf_term_some, typeOf_bool, h₄])
  simp only [typeOf_term_some, typeOf_bool] at hite
  simp [pe_ifSome_none hite.right]
  exact same_error_implied_by h₂

theorem compile_evaluate_or {x₁ x₂ : Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (h₁  : env ∼ εnv)
  (h₂  : env.WellFormedFor (.or x₁ x₂))
  (h₃  : εnv.WellFormedFor (.or x₁ x₂))
  (h₄  : compile (.or x₁ x₂) εnv = .ok t)
  (ih₁ : ReduceEvaluate x₁)
  (ih₂ : ReduceEvaluate x₂) :
  evaluate (.or x₁ x₂) env.request env.entities ∼ t
:= by
  replace ⟨_, hr₁, h₄⟩ := compile_or_ok_implies h₄
  have ⟨hwf₁, hwf₂⟩ := wf_env_for_or_implies h₂
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_or_implies h₃
  replace ih₁ := ih₁ h₁ hwf₁ hwφ₁ hr₁
  simp only [evaluate, Result.as, Coe.coe, Value.asBool]
  simp_do_let (evaluate x₁ env.request env.entities) <;>
  rename_i h₅ <;>
  simp only [h₅] at ih₁
  case error =>
    replace ⟨ih₁, tty, ih₁'⟩ := same_error_implies ih₁
    subst ih₁'
    simp only at h₄
    exact compile_evaluate_or_none hwφ₂ h₄ ih₁
  case ok =>
    split <;>
    simp only [Bool.not_eq_true', Except.bind_ok, Except.bind_err]
    case h_1 t₁ v b =>
      replace ih₁ := same_ok_bool_implies ih₁
      subst ih₁
      cases b <;> simp only [ite_true, ite_false] at *
      case true =>
        subst h₄
        exact same_ok_bool
      case false =>
        replace ⟨t₂, h₄, hty, ht⟩ := h₄.right
        simp only [pe_option_get_some, pe_ite_false, pe_ifSome_some hty] at ht
        subst ht
        replace ih₂ := ih₂ h₁ hwf₂ hwφ₂ h₄
        simp_do_let (evaluate x₂ env.request env.entities)
        case error hx₂ =>
          simp only [hx₂] at ih₂
          exact ih₂
        case ok hx₂ =>
          simp only [hx₂] at ih₂
          have ⟨_, _, hvt⟩ := compile_bool_same_implies_bool ((compile_wf hwφ₂ h₄).left) h₄ ih₂ hty
          subst hvt
          simp only [↓reduceIte, pure, Except.pure, Except.bind_ok, ih₂]
    case h_2 t₁ v₁ _ hneq =>
      split at h₄
      case h_1 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        subst ih₁
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq
      case h_2 =>
        have ⟨_, _, hvt⟩ := compile_bool_same_implies_bool ((compile_wf hwφ₁ hr₁).left) hr₁ ih₁ h₄.left
        subst hvt
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq

theorem compile_interpret_or {x₁ x₂ : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (h₁  : I.WellFormed εnv.entities)
  (h₂  : εnv.WellFormedFor (.or x₁ x₂))
  (h₃  : compile (.or x₁ x₂) εnv = .ok t)
  (ih₁ : ReduceInterpret x₁)
  (ih₂ : ReduceInterpret x₂) :
  compile (.or x₁ x₂) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨_, hr₁, h₃⟩ := compile_or_ok_implies h₃
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_or_implies h₂
  simp only [compile, ih₁ h₁ hwφ₁ hr₁, Except.bind_ok]
  clear ih₁ h₂
  split at h₃
  case h_1 =>
    simp only [interpret_term_some, interpret_term_prim, someOf, compileOr]
    subst h₃
    simp only [interpret_term_some, interpret_term_prim]
  case h_2 t₁ _ hneq =>
    replace ⟨ht₁, t₂, hr₂, ht₂, h₃⟩ := h₃
    simp only [compileOr, ih₂ h₁ hwφ₂ hr₂, Except.bind_ok]
    replace hwφ₁ := compile_wf hwφ₁ hr₁
    replace hwφ₂ := compile_wf hwφ₂ hr₂
    have hopt := wf_option_get hwφ₁.left ht₁
    have hite := @wf_ite
      εnv.entities (option.get t₁) (Term.some (Term.prim (TermPrim.bool true))) t₂
      hopt.left (Term.WellFormed.some_wf wf_bool) hwφ₂.left
      hopt.right (by simp only [Term.typeOf, TermPrim.typeOf, ht₂])
    split
    case h_1 heq =>
      simp only [heq, h₃, Except.ok.injEq]
      simp only [
        interpret_ifSome h₁ hwφ₁.left hite.left,
        interpret_ite h₁ hopt.left (wf_term_some wf_bool rfl).left hwφ₂.left
          hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
        interpret_term_some, interpret_term_prim, heq]
      simp only [interpret_option_get I hwφ₁.left ht₁, heq]
      simp only [pe_option_get'_some, pe_ite_true]
      simp only [pe_ifSome_some typeOf_term_some]
    case h_2  =>
      split
      case isTrue ht₁' _ ht₂' =>
        subst h₃

        simp only [Except.ok.injEq,
          interpret_ifSome h₁ hwφ₁.left hite.left, someOf,
          interpret_ite h₁ hopt.left (wf_term_some wf_bool rfl).left hwφ₂.left
            hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
          interpret_option_get I hwφ₁.left ht₁,
          interpret_term_some, interpret_term_prim]

        have hoptI := wf_option_get (interpret_term_wf h₁ hwφ₁.left).left ht₁'

        have hoptI' := interpret_term_wf h₁ hwφ₁.left
        simp only [ht₁] at hoptI'
        replace hoptI' := wf_option_get' h₁ hoptI'.left hoptI'.right

        replace hwφ₂ := (interpret_term_wf h₁ hwφ₂.left).left

        have ht' : Term.typeOf (Term.some (Term.prim (TermPrim.bool true))) = Term.typeOf (Term.interpret I t₂) := by
          simp only [Term.typeOf, TermPrim.typeOf, ht₂']

        have hto := wf_ite hoptI.left (Term.WellFormed.some_wf wf_bool) hwφ₂ hoptI.right ht'
        have hto' := wf_ite hoptI'.left (Term.WellFormed.some_wf wf_bool) hwφ₂ hoptI'.right ht'
        simp only [typeOf_term_some, typeOf_bool] at hto hto'

        exact @pe_ifSome_get_eq_get'
          εnv.entities I (Term.interpret I t₁) .bool .bool
          (Factory.ite · (Term.some (Term.prim (TermPrim.bool true))) (Term.interpret I t₂))
          (interpret_term_wfl h₁ hwφ₁.left).left
          (by assumption) (by simp only [hto]) (by simp only [hto'])
      case isFalse ht₂' =>
        have hwφ₂' := (interpret_term_wf h₁ hwφ₂.left).right
        simp only [hwφ₂', ht₂, not_true_eq_false] at ht₂'
    case h_3 ht₁' =>
      have hwφ₁' := (interpret_term_wf h₁ hwφ₁.left).right
      simp only [hwφ₁', ht₁, forall_const] at ht₁'

end Cedar.Thm

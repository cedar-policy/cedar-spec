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

import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Authorizer
import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.SymCC.Compiler
import Cedar.Thm.SymCC.Compiler.WellTyped
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.Validation.Typechecker.WF

/-!
This file defines the top-level correctness properties for the symbolic
compiler. We show the encoding is sound and complete with respect to the
concrete semantics of Cedar. That is, the symbolic semantics both
overapproximates (soundness) and underapproximates (completeness) the concrete
semantics.
--/

namespace Cedar.Thm

open Spec SymCC Validation

/--
Let `x` be a Cedar expression, `env` a concrete evaluation environment (request
and entities), `εnv` a symbolic environment, and `t` the outcome of
compiling `x` to a Term with respect to `εnv`.

Let `x` and `env` be a well-formed input to the concrete evaluator, i.e.,
`env.WellFormedFor x`.  This means that the entity store `env.entities` has
no dangling entity references, and all entity references that occur in `x` and
`env.request` are included in `env.entities`.

Let `x` and `εnv` be a well-formed input to the symbolic compiler, i.e.,
`εnv.WellFormedFor x`.  This means that the symbolic entity store `εnv.entities`
has no dangling (undefined) entity types or references; all term types contained
in `εnv.entities` represent valid Cedar types; and all entity references that
occur in `x` and `εnv.request` are valid according to
`εnv.entities.isValidEntityUID`.

Let `εnv` represent a set of concrete environments that includes `env`, i.e.,
`env ∈ᵢ εnv`.  We relate concrete structures to their symbolic counterparts via
interpretations, which map from term variables and uninterpreted functions to
literals.  For example, `env ∈ᵢ εnv` if there exists a well-formed interpretation
`I` such that `env ∼ εnv.interpret I` are equivalent according to the sameness
relation `∼`.  Note that we can't use equality here, because interpreting a
symbolic structure with respect to an `Interpretation` produces a literal
symbolic structure (without any unknowns), which is then compared to the
corresponding concrete structure using a suitable sameness relation.

Given the above, the soundness theorem says that the output of the concrete
evaluator on `x` and `env` is contained in the set of concrete outcomes
represented by the output of the symbolic compiler on `x` and `εnv`. We state
soundness in terms of `Outcome`s rather than `Result`s because the symbolic
compiler does not distinguish between different kinds of errors---only between
normal and erroring executions.
-/
theorem compile_is_sound {x : Expr} {env : Env} {εnv : SymEnv} {t : Term.Outcome εnv} :
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  env ∈ᵢ εnv →
  compile x εnv = .ok t →
  ∃ (o : Outcome Value),
    o ∈ₒ t ∧
    evaluate x env.request env.entities ∼ o
:= by
  intros h₁ h₂ h₃ h₄
  replace ⟨I, h₃, h₅⟩ := h₃
  have ⟨o, h₆, h₇⟩ := same_results_implies_exists_outcome (compile_bisimulation h₁ h₂ h₃ h₅ h₄)
  exists o
  simp only [h₆, and_true]
  exists I

/--
Let `x` be a Cedar expression and `εnv` a symbolic environment, where
`x` and `εnv` are a well-formed input to the symbolic compiler, i.e.,
`εnv.WellFormedFor x`.

Let `t` the outcome of compiling `x` to a Term with respect to `εnv`, and `o` a
concrete outcome represented by `t`.

Then, the completeness theorem says that there exists a concrete environment
`env` represented by `εnv` such that `x` and `env` are well-formed inputs to the
concrete evaluator and evaluating `x` against `env` produces the outcome `o`.
-/
theorem compile_is_complete {x : Expr} {εnv : SymEnv} {t : Term.Outcome εnv} {o : Outcome Value} :
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  o ∈ₒ t →
  ∃ (env : Env),
    env.WellFormedFor x ∧
    env ∈ᵢ εnv ∧
    evaluate x env.request env.entities ∼ o
:= by
  intros h₁ h₂ h₃
  replace ⟨I, h₃, h₅⟩ := h₃
  have ⟨env, h₆, h₇⟩ := exists_wf_env h₁ h₃
  exists env
  simp only [h₇, true_and]
  constructor
  · exists I
  · have ⟨o', h₈, h₉⟩ := same_results_implies_exists_outcome (compile_bisimulation h₁ h₇ h₃ h₆ h₂)
    have h₁₀ := same_outcomes_implies_eq h₅ h₉
    subst h₁₀
    exact h₈

/--
Let `ps` be Cedar policies, `env` a concrete evaluation environment (request and
entities), `εnv` a symbolic environment, and `t` the term resulting
from symbolically authorizing `ps` with respect to `εnv`, i.e.,
`SymCC.isAuthorized ps εnv = .ok t`.

Let `ps` and `env` be a well-formed input to the concrete authorizer, i.e.,
`env.WellFormedForPolicies ps`.  This means that the entity store `env.entities`
has no dangling entity references, and all entity references that occur in `ps`
and `env.request` are included in `env.entities`.

Let `ps` and `εnv` be a well-formed input to the symbolic authorizer, i.e.,
`εnv.WellFormedForPolices ps`.  This means that the symbolic entity store
`εnv.entities` has no dangling (undefined) entity types or references; all term
types contained in `εnv.entities` represent valid Cedar types; and all entity
references that occur in `ps` and `εnv.request` are valid according to
`εnv.entities.isValidEntityUID`.

Let `εnv` represent a set of concrete environments that includes `env`, i.e.,
`env ∈ᵢ εnv`.  We relate concrete structures to their symbolic counterparts via
interpretations, which map from term variables and uninterpreted functions to
literals.  For example, `env ∈ᵢ εnv` if there exists a well-formed interpretation
`I` such that `env ∼ εnv.interpret I` are equivalent according to the sameness
relation `∼`.  Note that we can't use equality here, because interpreting a
symbolic structure with respect to an `Interpretation` produces a literal
symbolic structure (without any unknowns), which is then compared to the
corresponding concrete structure using a suitable sameness relation.

Given the above, the soundness theorem says that the decision of the concrete
authorizer on `ps` and `env` is contained in the set of concrete decisions
represented by the output of the symbolic authorizer on `ps` and `εnv`. We state
soundness in terms of `Decision`s rather than `Response`s because the symbolic
authorizer computes only decision (and not the extra diagnostics contained in a
concrete `Response`).
-/
theorem isAuthorized_is_sound  {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term.Outcome εnv} :
  εnv.WellFormedForPolicies ps →
  env.WellFormedForPolicies ps →
  env ∈ᵢ εnv →
  SymCC.isAuthorized ps εnv = .ok t →
  ∃ (decision : Spec.Decision),
    decision ∈ₒ t ∧
    Spec.isAuthorized env.request env.entities ps ∼ decision
:= by
  intro hεnv henv hinᵢ hok
  replace ⟨I, hI, hinᵢ⟩ := hinᵢ
  have heq := isAuthorized_bisimulation hεnv henv hI hinᵢ hok
  exists (Spec.isAuthorized env.request env.entities ps).decision
  simp only [same_responses_self_decision, and_true]
  exists I

/--
Let `ps` be Cedar policies and `εnv` a symbolic environment, where
`ps` and `εnv` are a well-formed input to the symbolic authorizer, i.e.,
`εnv.WellFormedForPolicies ps`.

Let `t` the outcome of symbolically authorizing `ps` with respect to `εnv`, and `d` a
concrete authorization decision represented by `t`.

Then, the completeness theorem says that there exists a concrete environment
`env` represented by `εnv` such that `ps` and `env` are well-formed inputs to the
concrete authorizer and authorizing `os` against `env` produces the decision `d`.
-/
theorem isAuthorized_is_complete {ps : Policies} {εnv : SymEnv} {t : Term.Outcome εnv} {decision : Spec.Decision} :
  εnv.WellFormedForPolicies ps →
  SymCC.isAuthorized ps εnv = .ok t →
  decision ∈ₒ t →
  ∃ (env : Env),
    env.WellFormedForPolicies ps ∧
    env ∈ᵢ εnv ∧
    Spec.isAuthorized env.request env.entities ps ∼ decision
:= by
  intro hεnv hok hinₒ
  replace ⟨I, hI, hinₒ⟩ := hinₒ
  have ⟨env, heq, henv⟩ := exists_wf_env_for_policies hεnv hI
  exists env
  simp only [henv, true_and]
  constructor
  · exists I
  · replace heq := isAuthorized_bisimulation hεnv henv hI heq hok
    exact same_decision_and_response_implies_same_decision hinₒ heq

/--
For any well-typed expression `tx` in a well-formed environment `Γ`
(which can be produced by Cedar's type checker), the symbolic compiler
should never fail and produce a term `t` that is well-formed and has
the type `TermType.ofType tx.typeOf`.
-/
theorem compile_well_typed {tx : TypedExpr} {Γ : TypeEnv} :
  Γ.WellFormed →
  TypedExpr.WellTyped Γ tx →
  ∃ t : Term,
    compile tx.toExpr (SymEnv.ofEnv Γ) = .ok t ∧
    t.WellFormed (SymEnv.ofEnv Γ).entities ∧
    t.typeOf = .option (TermType.ofType tx.typeOf)
:= by
  intros hwf hwt
  have hwf_tx := ofEnv_wf_for_expr hwf hwt
  have ⟨t, hok, hty⟩ := compile_well_typed_on_wf_expr (And.intro rfl (And.intro hwt hwf_tx))
  have hwf_t := compile_wf hwf_tx hok
  exists t
  simp [hok, hwf_t, hty]

def IsOption (tty : TermType) := ∃ tty', tty = TermType.option tty'
def OptionTyped (t : Term) := IsOption t.typeOf

/--
Lemma
-/
private theorem typeOf_noneOf (tty : TermType) :
  OptionTyped (Factory.noneOf tty)
:= by
  simp [OptionTyped, IsOption, Factory.noneOf, Term.typeOf]

/--
Lemma
-/
private theorem typeOf_someOf (t : Term) :
  OptionTyped (⊙t)
:= by
  simp [OptionTyped, IsOption, Factory.someOf, Term.typeOf]

/--
Lemma
-/
private theorem typeOf_ite.simplify {c t f : Term} :
  OptionTyped t → OptionTyped f → OptionTyped (Factory.ite.simplify c t f)
:= by
  simp only [OptionTyped, IsOption, Factory.ite.simplify, Bool.or_eq_true, decide_eq_true_eq,
    forall_exists_index]
  intro tty ht fty hf
  split <;> rename_i h
  · exists tty
  · split
    · exists fty
    · split
      · simp [Term.typeOf, TermPrim.typeOf] at ht
      · simp [Term.typeOf, TermPrim.typeOf] at ht
      · simp [Term.typeOf, TermPrim.typeOf] at hf
      · simp [Term.typeOf, TermPrim.typeOf] at ht
      · simp [Term.typeOf] ; exists tty

/--
Lemma
-/
private theorem typeOf_ite {c t f : Term} :
  OptionTyped t → OptionTyped f → OptionTyped (Factory.ite c t f)
:= by
  intro ht hf
  simp only [OptionTyped, IsOption, Factory.ite]
  split
  · simp [Term.typeOf]
  · apply typeOf_ite.simplify ht hf

/--
Lemma
-/
private theorem typeOf_ifFalse {g t : Term} :
  OptionTyped (Factory.ifFalse g t)
:= by
  simp only [Factory.ifFalse]
  apply typeOf_ite
  · apply typeOf_noneOf
  · apply typeOf_someOf

/--
Lemma
-/
private theorem typeOf_ifTrue {g t : Term} :
  OptionTyped (Factory.ifTrue g t)
:= by
  simp only [Factory.ifTrue]
  apply typeOf_ite
  · apply typeOf_someOf
  · apply typeOf_noneOf

/--
Lemma
-/
private theorem typeOf_ifSome {g t : Term} :
  OptionTyped t → OptionTyped (Factory.ifSome g t)
:= by
  intro ht
  simp only [OptionTyped, IsOption, Factory.ifSome]
  split
  · apply typeOf_ite _ ht
    apply typeOf_noneOf
  · apply typeOf_ifFalse

/--
Lemma
-/
private theorem typeOf_ifAllSome {gs : List Term} {t : Term} :
  OptionTyped t → OptionTyped (Factory.ifAllSome gs t)
:= by
  simp only [Factory.ifAllSome]
  split
  · apply typeOf_ite
    apply typeOf_noneOf
  · intro h ; apply typeOf_ifFalse

/--
Weaker result than `compile_well_typed`, but requiring weaker hypotheses:

If `compile` on any expression (not necessarily well-typed) produces `.ok t`,
then `t` must have option type
-/
theorem compile_ok_implies_option {x : Expr} {εnv : SymEnv} {t : Term} :
  compile x εnv = .ok t →
  ∃ tty, t.typeOf = .option tty
:= by
  cases x <;> simp [compile]
  case lit p =>
    cases p <;> simp [compilePrim]
    case bool | int | string =>
      intro h ; subst t
      apply typeOf_someOf
    case entityUID =>
      split <;> simp
      intro h ; subst t
      apply typeOf_someOf
  case var v =>
    cases v <;> simp [compileVar]
    all_goals {
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_someOf
    }
  case and x₁ x₂ | or x₁ x₂ =>
    cases hx₁ : compile x₁ εnv <;> simp [compileAnd, compileOr]
    case ok t₁ =>
      replace ⟨tty₁, hx₁⟩ := compile_ok_implies_option hx₁
      split <;> simp [Term.typeOf] at *
      · subst tty₁ ; intro h ; subst t ; simp [Term.typeOf]
      · cases hx₂ : compile x₂ εnv <;> simp
        case ok t₂ =>
          replace ⟨tty₂, hx₂⟩ := compile_ok_implies_option hx₂
          split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
          · intro h ; subst t
            apply typeOf_ifSome
            apply typeOf_ite
            repeat first
            | { simp [OptionTyped, IsOption, hx₂] }
            | { apply typeOf_someOf }
  case ite x₁ x₂ x₃ =>
    cases hx₁ : compile x₁ εnv <;> simp [compileIf]
    case ok t₁ =>
      replace ⟨tty₁, hx₁⟩ := compile_ok_implies_option hx₁
      split <;> simp [Term.typeOf] at *
      · subst tty₁
        intro hx₂ ; simp [compile_ok_implies_option hx₂]
      · subst tty₁
        intro hx₃ ; simp [compile_ok_implies_option hx₃]
      · cases hx₂ : compile x₂ εnv <;> simp
        case ok t₂ =>
          replace ⟨tty₂, hx₂⟩ := compile_ok_implies_option hx₂
          cases hx₃ : compile x₃ εnv <;> simp
          case ok t₃ =>
            replace ⟨tty₃, hx₃⟩ := compile_ok_implies_option hx₃
            split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
            · intro h ; subst h
              apply typeOf_ifSome
              apply typeOf_ite
              all_goals simp [OptionTyped, IsOption, *]
  case unaryApp op x =>
    cases hx : compile x εnv <;> simp [compileApp₁]
    case ok t =>
      replace ⟨tty, hx⟩ := compile_ok_implies_option hx
      split <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
      <;> intro h <;> subst h <;> rename_i h
      <;> apply typeOf_ifSome
      · apply typeOf_someOf
      · apply typeOf_ifFalse
      · apply typeOf_someOf
      · apply typeOf_someOf
      · apply typeOf_someOf
  case binaryApp op x₁ x₂ =>
    cases hx₁ : compile x₁ εnv <;> simp [compileApp₂]
    case ok t₁ =>
      replace ⟨tty₁, hx₁⟩ := compile_ok_implies_option hx₁
      cases hx₂ : compile x₂ εnv <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq, false_implies]
      case ok t₂ =>
        replace ⟨tty₂, hx₂⟩ := compile_ok_implies_option hx₂
        split
        case _ =>
          cases reducibleEq (Factory.option.get t₁).typeOf (Factory.option.get t₂).typeOf <;> simp
          case ok b =>
          split <;> simp only [Except.bind_ok, Except.ok.injEq]
          <;> intro h <;> subst t <;> apply typeOf_ifSome
          <;> simp only [OptionTyped, IsOption]
          <;> apply typeOf_ifSome
          <;> apply typeOf_someOf
        case _ | _ | _ | _ | _ | _ =>
          simp only [Except.bind_ok, Except.ok.injEq]
          intro h ; subst t
          apply typeOf_ifSome
          apply typeOf_ifSome
          apply typeOf_someOf
        case _ | _ | _ =>
          simp only [Except.bind_ok, Except.ok.injEq]
          intro h ; subst t
          apply typeOf_ifSome
          apply typeOf_ifSome
          apply typeOf_ifFalse
        case _ =>
          cases (Factory.option.get t₂).typeOf
          case prim | option | set | record =>
            split <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
            intro h ; subst t
            apply typeOf_ifSome
            apply typeOf_ifSome
            apply typeOf_someOf
        case _ | _ =>
          split <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
          intro h ; subst t
          apply typeOf_ifSome
          apply typeOf_ifSome
          apply typeOf_someOf
        case _ | _ =>
          simp only [Except.bind_ok, Except.ok.injEq]
          intro h ; subst t
          apply typeOf_ifSome
          apply typeOf_ifSome
          apply typeOf_someOf
        case _ =>
          rename_i ety _ _
          cases htag : compileHasTag (Factory.option.get t₁) (Factory.option.get t₂) (εnv.entities.tags ety)
          <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
          case ok t' =>
          intro h ; subst t
          apply typeOf_ifSome
          apply typeOf_ifSome
          simp only [compileHasTag] at htag
          split at htag <;> simp only [Except.ok.injEq, reduceCtorEq] at htag
          <;> subst htag
          <;> apply typeOf_someOf
        case _ =>
          rename_i ety _ _
          cases htag : compileGetTag (Factory.option.get t₁) (Factory.option.get t₂) (εnv.entities.tags ety)
          <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
          case ok t' =>
          intro h ; subst t
          apply typeOf_ifSome
          apply typeOf_ifSome
          simp only [compileGetTag] at htag
          split at htag <;> simp only [Except.ok.injEq, reduceCtorEq] at htag
          subst htag
          simp only [SymTags.getTag]
          apply typeOf_ifTrue
        case _ => simp
  case hasAttr x attr =>
    cases hx : compile x εnv <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq, false_implies]
    case ok t' =>
    replace ⟨tty, hx⟩ := compile_ok_implies_option hx
    cases hattr : compileHasAttr (Factory.option.get t') attr εnv.entities
    <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
    case ok t'' =>
    intro h ; subst t
    apply typeOf_ifSome
    simp only [compileHasAttr] at hattr
    cases hattrs : compileAttrsOf (Factory.option.get t') εnv.entities
    <;> simp only [hattrs, Except.bind_ok, Except.bind_err, reduceCtorEq] at hattr
    split at hattr
    · split at hattr <;> simp only [Except.ok.injEq] at hattr
      <;> subst hattr
      <;> apply typeOf_someOf
    · simp at hattr
  case getAttr x attr =>
    cases hx : compile x εnv <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq, false_implies]
    case ok t' =>
    replace ⟨tty, hx⟩ := compile_ok_implies_option hx
    cases hattr : compileGetAttr (Factory.option.get t') attr εnv.entities
    <;> simp only [Except.bind_ok, Except.ok.injEq, Except.bind_err, reduceCtorEq, false_implies]
    case ok t'' =>
    intro h ; subst t
    apply typeOf_ifSome
    simp only [compileGetAttr] at hattr
    cases hattrs : compileAttrsOf (Factory.option.get t') εnv.entities
    <;> simp only [hattrs, Except.bind_ok, Except.bind_err, reduceCtorEq] at hattr
    split at hattr <;> rename_i h₁
    · split at hattr <;> simp only [Except.ok.injEq, reduceCtorEq] at hattr
      <;> subst hattr
      · rename_i attrTy hattrTy
        exists attrTy
        simp only [Factory.record.get]
        split
        · split <;> rename_i h₂
          · have h₃ := typeOf_term_record_attr_value_typeOf h₁ h₂
            simp [hattrTy] at h₃ ; simp [← h₃]
          · exfalso
            have ⟨t'', h₃⟩ := typeOf_term_record_attr_value h₁ hattrTy
            apply h₂ t'' h₃.left
        · split <;> rename_i h₂
          · split
            · simp only [Term.typeOf]
              simp only [compileAttrsOf] at hattrs
              split at hattrs
              · split at hattrs <;> simp only [Except.ok.injEq, reduceCtorEq] at hattrs
                subst hattrs
                simp [h₁] at h₂ ; subst h₂
                rename_i h₂
                simp [hattrTy] at h₂ ; simp [h₂]
              · simp only [Except.ok.injEq] at hattrs ; subst hattrs
                rename_i h _ ; simp [h₁] at h ; subst h
                simp [h₁] at h₂ ; subst h₂
                rename_i h₂
                simp [hattrTy] at h₂ ; simp [h₂]
              · simp at hattrs
            · exfalso
              simp [h₁] at h₂ ; subst h₂
              rename_i h₂ ; apply h₂ attrTy.option hattrTy
          · exfalso
            apply h₂ _ h₁
      · apply typeOf_someOf
    · simp at hattr
  case set xs =>
    cases hxs : xs.mapM₁ λ x => compile x.val εnv
    <;> rw [List.mapM₁_eq_mapM (compile · εnv)] at hxs
    <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq, false_implies]
    simp only [compileSet, List.all_eq_true, decide_eq_true_eq]
    split <;> simp only [reduceCtorEq, false_implies, List.mem_cons, forall_eq_or_imp, List.map_cons]
    split <;> simp only [*, true_and, reduceCtorEq, false_implies]
    split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
    intro h ; subst t
    apply typeOf_ifAllSome
    apply typeOf_someOf
  case call xfn xs =>
    cases hxs : xs.mapM₁ λ x => compile x.val εnv
    <;> rw [List.mapM₁_eq_mapM (compile · εnv)] at hxs
    <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq, false_implies]
    simp only [compileCall]
    split
    case _ =>
      simp only [compileCall₀]
      split
      · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
        intro h ; subst t
        apply typeOf_someOf
      · simp only [reduceCtorEq, false_implies]
    case _ | _ | _ | _ =>
      simp only [compileCall₂, compileCallWithError₂]
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_ifSome
      apply typeOf_ifSome
      apply typeOf_someOf
    case _ =>
      simp only [compileCall₀]
      split
      · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
        intro h ; subst t
        apply typeOf_someOf
      · simp only [reduceCtorEq, false_implies]
    case _ | _ | _ | _ =>
      simp only [compileCall₁, compileCallWithError₁]
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_ifSome
      apply typeOf_someOf
    case _ =>
      simp only [compileCall₂, compileCallWithError₂]
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_ifSome
      apply typeOf_ifSome
      apply typeOf_someOf
    case _ | _ =>
      simp only [compileCall₀]
      split
      · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
        intro h ; subst t
        apply typeOf_someOf
      · simp only [reduceCtorEq, false_implies]
    case _ | _ =>
      simp only [compileCallWithError₂, Bool.and_eq_true, decide_eq_true_eq]
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_ifSome
      apply typeOf_ifSome
      simp only [Datetime.offset, Datetime.durationSince]
      apply typeOf_ifFalse
    case _ =>
      simp only [compileCallWithError₁]
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_ifSome
      simp only [Datetime.toDate]
      apply typeOf_ite
      · apply typeOf_someOf
      · apply typeOf_ite
        · apply typeOf_someOf
        · apply typeOf_ifFalse
    case _ | _ | _ | _ | _ | _ =>
      simp only [compileCall₁, compileCallWithError₁]
      split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst t
      apply typeOf_ifSome
      apply typeOf_someOf
    case _ => simp
  case record m =>
    simp [do_eq_ok] ; intro m' hm h ; subst t
    simp_do_let (m.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do .ok (a₁, ← compile x₁ εnv))) at hm
    simp only [Except.ok.injEq] at hm ; subst hm
    rename_i m' hm
    simp only [compileRecord]
    apply typeOf_ifAllSome
    apply typeOf_someOf

end Cedar.Thm

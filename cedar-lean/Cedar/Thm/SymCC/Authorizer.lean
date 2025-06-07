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

import Cedar.SymCC.Authorizer
import Cedar.Thm.SymCC.Compiler
import Cedar.Thm.Authorization.Authorizer

/-!
This file proves a key lemma used to show the soundness and completeness of
analyses built on top of Cedar's symbolic authorizer.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

theorem compileWithEffect_error_implies {effect : Effect} {p : Policy} {εnv : SymEnv} {err : SymCC.Error }:
  compileWithEffect effect p εnv = .error err →
  p.effect = effect ∧ compile p.toExpr εnv = .error err
:= by
  intro h₁
  simp only [compileWithEffect, beq_iff_eq, bind_pure_comp] at h₁
  split at h₁ <;> try simp only [reduceCtorEq] at h₁
  rename_i h₂
  simp only [h₂, true_and]
  simp only [Functor.map, Except.map] at h₁
  split at h₁ <;> rename_i h₃
  · simp only [Except.error.injEq] at h₁
    subst h₁
    exact h₃
  · simp only [reduceCtorEq] at h₁

theorem compileWithEffect_none_implies {effect : Effect} {p : Policy} {εnv : SymEnv} :
  compileWithEffect effect p εnv = .ok .none →
  p.effect ≠ effect
:= by
  intro h₁
  simp only [compileWithEffect, beq_iff_eq, bind_pure_comp, ite_eq_right_iff] at h₁
  by_contra hc
  simp only [hc, Functor.map, Except.map, forall_const] at h₁
  split at h₁ <;> simp at h₁

theorem compileWithEffect_some_implies {effect : Effect} {p : Policy} {εnv : SymEnv} {t : Term} :
  compileWithEffect effect p εnv = Except.ok (some t) →
  p.effect = effect ∧ compile p.toExpr εnv = .ok t
:= by
  intro h₁
  simp [compileWithEffect] at h₁
  split at h₁ <;> try simp only [Except.ok.injEq, reduceCtorEq] at h₁
  rename_i h₂
  simp only [h₂, true_and]
  simp only [Functor.map, Except.map] at h₁
  split at h₁ <;> simp only [reduceCtorEq, Except.ok.injEq, Option.some.injEq] at h₁
  subst h₁
  assumption

theorem satisfiedPolicies_filterMapM_eq {effect : Effect} {ps : Policies} {εnv : SymEnv} :
  List.filterMapM (compileWithEffect effect · εnv) ps =
  (ps.filter (λ p => p.effect == effect)).mapM (λ p => compile p.toExpr εnv)
 := by
  induction ps
  case nil => simp
  case cons p ps ih =>
    simp only [List.filterMapM_cons, bind_pure_comp]
    simp_do_let (compileWithEffect effect p εnv)
    case error h₁ =>
      replace ⟨h₁, h₂⟩ := compileWithEffect_error_implies h₁
      rw [List.filter_cons_of_pos (by simp only [h₁, beq_self_eq_true])]
      simp only [List.mapM_cons, bind_pure_comp]
      simp_do_let (compile p.toExpr εnv)
      case error h₃ =>
        simp only [h₃, Except.map_error, Except.error.injEq] at *
        simp only [h₂]
      case ok h₃ =>
        simp only [h₃, Except.map_ok, reduceCtorEq] at h₂
    case ok opt h₁ =>
      cases opt <;> simp only
      case none =>
        replace h₁ := compileWithEffect_none_implies h₁
        rw [List.filter_cons_of_neg (by simp only [beq_iff_eq, h₁, not_false_eq_true])]
        exact ih
      case some t =>
        replace ⟨h₁, h₃⟩ := compileWithEffect_some_implies h₁
        rw [List.filter_cons_of_pos (by simp only [h₁, beq_self_eq_true])]
        simp only [h₃, ih, List.mapM_cons, bind_pure_comp, Except.bind_ok]

private theorem compile_and_wf_option_bool {x₁ x₂ : Expr} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedFor (Expr.and x₁ x₂) →
  compile (Expr.and x₁ x₂) εnv = .ok t →
  (t.WellFormed εnv.entities ∧ t.typeOf = .option .bool)
:= by
  intro hwε hok
  simp only [compile_wf hwε hok, true_and]
  replace ⟨t₁, hok₁, hok⟩ := compile_and_ok_implies hok
  split at hok <;> try simp only [hok, typeOf_term_some, typeOf_bool]
  simp only [CompileAndSym] at hok
  replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
  subst hok
  have ⟨hw₁, hw₂⟩ := wf_εnv_for_and_implies hwε
  replace hw₁ := (compile_wf hw₁ hok₁).left
  replace hw₂ := (compile_wf hw₂ hok₂).left
  have h₁ := wf_option_get hw₁ hty₁
  have h₂ : (Term.prim (TermPrim.bool false)).some.WellFormed εnv.entities ∧ (Term.prim (TermPrim.bool false)).some.typeOf = .option .bool := by
    simp only [Term.WellFormed.some_wf wf_bool, typeOf_term_some, typeOf_bool, and_self]
  have h₃ := wf_ite h₁.left hw₂ h₂.left h₁.right (by simp only [hty₂, typeOf_term_some, typeOf_bool])
  rw [hty₂] at h₃
  simp only [wf_ifSome_option hw₁ h₃.left h₃.right]

theorem compile_policy_wf {p : Policy} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedFor p.toExpr →
  compile p.toExpr εnv = .ok t →
  (t.WellFormed εnv.entities ∧ t.typeOf = .option .bool)
:= by
  intro hwε hok
  simp only [Policy.toExpr] at hwε hok
  exact compile_and_wf_option_bool hwε hok

theorem satisfiedPolicies_ok_implies {effect : Effect} {ps : Policies} {εnv : SymEnv} {t : Term} :
  satisfiedPolicies effect ps εnv = .ok t →
  ∃ ts,
    t = anyTrue (eq · (Term.some (Term.bool true))) ts ∧
    List.mapM (λ p => compile p.toExpr εnv) (List.filter (λ p => p.effect == effect) ps) = Except.ok ts
:= by
  intro hok
  simp only [SymCC.satisfiedPolicies] at hok
  simp_do_let (List.filterMapM (compileWithEffect effect · εnv) ps) at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  rename_i ts hok
  rw [satisfiedPolicies_filterMapM_eq] at hok
  exists ts

private theorem mapM_compile_ok_implies_wf {ps : Policies} {εnv : SymEnv} {ts : List Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hok : List.mapM (fun p => compile p.toExpr εnv) ps = Except.ok ts) :
  ∀ t ∈ ts, t.WellFormed εnv.entities ∧ t.typeOf = .option .bool
 := by
  intro t hin
  replace ⟨p, hf, hok⟩ := List.mapM_ok_implies_all_from_ok hok t hin
  exact compile_policy_wf (wf_εnv_all_policies_implies_wf_all hwε p hf) hok

abbrev eqSomeTrue := (eq · (Term.some (Term.bool true)))

private theorem mapM_compile_ok_implies_wf_eqSomeTrue {ps : Policies} {εnv : SymEnv} {ts : List Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hok : List.mapM (fun p => compile p.toExpr εnv) ps = Except.ok ts) :
  ∀ t ∈ ts, (eqSomeTrue t).WellFormed εnv.entities ∧ (eqSomeTrue t).typeOf = .bool
 := by
  intro t hin
  have hwf := mapM_compile_ok_implies_wf hwε hok t hin
  apply wf_eq hwf.left (Term.WellFormed.some_wf wf_bool)
  simp only [hwf.right, typeOf_term_some, typeOf_bool]

theorem satisfiedPolicies_wf {effect : Effect} {ps : Policies} {εnv : SymEnv} {t : Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hok : Cedar.SymCC.satisfiedPolicies effect ps εnv = .ok t) :
  t.WellFormed εnv.entities ∧ t.typeOf = .bool
 := by
  replace ⟨ts, ht, hok⟩ := satisfiedPolicies_ok_implies hok
  subst ht
  replace hwε := wf_εnv_for_policies_implies_wf_for_filter (fun p => p.effect == effect) hwε
  have hwf := mapM_compile_ok_implies_wf hwε hok
  have hfun_wf := mapM_compile_ok_implies_wf_eqSomeTrue hwε hok
  simp only [wf_anyTrue hfun_wf, and_self]

private theorem mapM_compile_ok_implies_interpret_eqSomeTrue {ps : Policies} {εnv : SymEnv} {I : Interpretation} {ts : List Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwI : I.WellFormed εnv.entities)
  (hok : List.mapM (fun p => compile p.toExpr εnv) ps = Except.ok ts) :
   ∀ t ∈ ts, (eqSomeTrue t).interpret I = eqSomeTrue (t.interpret I)
:= by
  intro t hin
  have hwf := mapM_compile_ok_implies_wf hwε hok t hin
  simp only [eqSomeTrue, Term.bool]
  rw (config := {occs := .pos [2]}) [← @interpret_term_prim I]
  rw [← @interpret_term_some I]
  exact interpret_eq hwI hwf.left (Term.WellFormed.some_wf wf_bool)

private theorem mapM_compile_ok_implies_map_interpret {ps : Policies} {εnv : SymEnv} {ts : List Term} {I : Interpretation}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwI : I.WellFormed εnv.entities)
  (hok : List.mapM (fun p => compile p.toExpr εnv) ps = Except.ok ts) :
  List.mapM (fun p => compile p.toExpr (εnv.interpret I)) ps = Except.ok (ts.map (Term.interpret I))
 := by
  rw [List.mapM_ok_iff_forall₂] at *
  induction hok
  case nil =>
    simp only [List.map_nil, List.Forall₂.nil]
  case cons hd t tl ts h₁ h₂ ih =>
    replace hwε := wf_εnv_for_policies_cons hwε
    simp only [List.map_cons, List.forall₂_cons]
    simp only [compile_interpret hwI hwε.left h₁, ih hwε.right, and_self]

theorem satisfiedPolicies_interpret {effect : Effect} {ps : Policies} {εnv : SymEnv} {t : Term} {I : Interpretation}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwI : I.WellFormed εnv.entities)
  (hok : Cedar.SymCC.satisfiedPolicies effect ps εnv = .ok t) :
  Cedar.SymCC.satisfiedPolicies effect ps (εnv.interpret I) = t.interpret I
 := by
  replace ⟨ts, ht, hok⟩ := satisfiedPolicies_ok_implies hok
  subst ht
  replace hwε := wf_εnv_for_policies_implies_wf_for_filter (fun p => p.effect == effect) hwε
  have hfun_wf := mapM_compile_ok_implies_wf_eqSomeTrue hwε hok
  have hfun_I := mapM_compile_ok_implies_interpret_eqSomeTrue hwε hwI hok
  replace hok := mapM_compile_ok_implies_map_interpret hwε hwI hok
  simp only [SymCC.satisfiedPolicies, satisfiedPolicies_filterMapM_eq, hok, someOf,
    interpret_anyTrue hwI hfun_wf hfun_I, Except.bind_ok, Except.ok.injEq]

theorem satisfiedPolicies_eq {effect : Effect} {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwe : env.WellFormedForPolicies ps)
  (heq : env ∼ εnv)
  (hok : Cedar.SymCC.satisfiedPolicies effect ps εnv = .ok t) :
  t = .bool (!(Cedar.Spec.satisfiedPolicies effect ps env.request env.entities).isEmpty)
 := by
  replace ⟨ts, ht, hok⟩ := satisfiedPolicies_ok_implies hok
  subst ht
  cases hb : (Spec.satisfiedPolicies effect ps env.request env.entities).isEmpty <;>
  simp only [Bool.not_true, Bool.not_false]
  case false =>
    replace ⟨p, hpin, heff, hb⟩ := if_satisfiedPolicies_non_empty_then_satisfied hb
    replace ⟨t, htin, hok⟩ := List.mapM_ok_implies_all_ok hok p (by simp only [List.mem_filter, hpin, heff,
      beq_self_eq_true, and_self])
    simp only [satisfied, decide_eq_true_eq] at hb
    have hr := compile_evaluate heq (wf_env_all_policies_implies_wf_all hwe p hpin) (wf_εnv_all_policies_implies_wf_all hwε p hpin) hok
    rw [hb] at hr
    replace hr := same_ok_bool_implies hr
    apply pe_anyTrue_true htin
    subst hr
    simp only [pe_eq_same]
  case true =>
    apply pe_anyTrue_false
    intro t hin
    replace hwε := wf_εnv_for_policies_implies_wf_for_filter (fun p => p.effect == effect) hwε
    have hwf := mapM_compile_ok_implies_wf hwε hok t hin
    replace ⟨p, hpin, hok⟩ := List.mapM_ok_implies_all_from_ok hok t hin
    simp only [List.mem_filter, beq_iff_eq] at hpin
    have hr := compile_evaluate heq
      (wf_env_all_policies_implies_wf_all hwe p hpin.left)
      (wf_εnv_all_policies_implies_wf_all hwε p (by simp only [hpin, List.mem_filter, beq_self_eq_true, and_self]))
      hok
    cases hv : evaluate p.toExpr env.request env.entities <;> simp only [hv] at hr
    · replace ⟨_, hr⟩ := (same_error_implies hr).right
      subst hr
      simp only [pe_eq_none_some]
    · replace ⟨t', ht, hr⟩ := same_ok_implies hr
      subst ht
      simp only [typeOf_term_some, TermType.option.injEq] at hwf
      have ⟨b, hlit⟩ := wfl_of_type_bool_is_bool (And.intro (wf_term_some_implies hwf.left) (same_value_implies_lit hr)) hwf.right
      subst hlit
      cases b
      · simp only [eq, eq.simplify, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true, ↓reduceIte, Term.isLiteral, Bool.and_self]
      · replace hr := same_bool_term_implies hr
        subst hr
        have hb' : (Spec.satisfiedPolicies effect ps env.request env.entities).isEmpty = false := by
          apply if_satisfied_then_satisfiedPolicies_non_empty
          exists p
          simp only [hpin, satisfied, hv, decide_true, and_self]
        simp only [hb, Bool.true_eq_false] at hb'

theorem satisfiedPolicies_bisimulation {effect : Effect} {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term} {I : Interpretation}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwe : env.WellFormedForPolicies ps)
  (hwI : I.WellFormed εnv.entities)
  (heq : env ∼ εnv.interpret I)
  (hok : Cedar.SymCC.satisfiedPolicies effect ps εnv = .ok t) :
  t.interpret I = .bool (!(Cedar.Spec.satisfiedPolicies effect ps env.request env.entities).isEmpty)
 := by
  replace hok := satisfiedPolicies_interpret hwε hwI hok
  replace hwε := interpret_εnv_wf_for_policies hwε hwI
  exact satisfiedPolicies_eq hwε hwe heq hok

private theorem satisfiedPolicies_interpret_eq_when_interpret_eq {effect : Effect} {ps : Policies} {εnv : SymEnv} {I I' : Interpretation} {t : Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwI : I.WellFormed εnv.entities)
  (hwI' : I'.WellFormed εnv.entities)
  (heq : ∀ (p : Policy) (t : Term), p ∈ ps → compile p.toExpr εnv = Except.ok t → Term.interpret I t = Term.interpret I' t)
  (hok : SymCC.satisfiedPolicies effect ps εnv = .ok t) :
  Term.interpret I t = Term.interpret I' t
:= by
  replace ⟨ts₁, ht₁, hok₁⟩ := satisfiedPolicies_ok_implies (satisfiedPolicies_interpret hwε hwI hok)
  replace ⟨ts₂, ht₂, hok₂⟩ := satisfiedPolicies_ok_implies (satisfiedPolicies_interpret hwε hwI' hok)
  simp only [ht₁, ht₂]
  clear ht₁ ht₂
  apply congr
  · rfl
  · replace ⟨_, _, hok⟩ := satisfiedPolicies_ok_implies hok
    replace heq :
      List.mapM (fun p => compile p.toExpr (SymEnv.interpret I εnv)) (List.filter (fun p => p.effect == effect) ps) =
      List.mapM (fun p => compile p.toExpr (SymEnv.interpret I' εnv)) (List.filter (fun p => p.effect == effect) ps) := by
      apply List.mapM_congr
      intro p hin
      replace ⟨t, _, hok⟩ := List.mapM_ok_implies_all_ok hok p hin
      simp only [List.mem_filter, beq_iff_eq] at hin
      specialize heq p t hin.left hok
      replace hwε := wf_εnv_all_policies_implies_wf_all hwε p hin.left
      simp only [compile_interpret hwI hwε hok, heq, compile_interpret hwI' hwε hok]
    simp only [heq, hok₂, Except.ok.injEq] at hok₁
    simp only [hok₁]

theorem same_decisions_def {d : Spec.Decision} {t : Term} :
  d ∼ t ↔ SymCC.SameDecisions d t
:= by
  simp only [Same.same]

theorem same_decisions_iff_allow_true_or_deny_false {d : Spec.Decision} {t : Term} :
  d ∼ t ↔ (d = .allow ∧ t = .bool true ∨ d = .deny ∧ t = .bool false)
:= by
  simp only [Same.same, SymCC.SameDecisions]
  split
  · simp only [and_self, reduceCtorEq, Term.prim.injEq, TermPrim.bool.injEq, Bool.true_eq_false,
    or_false]
  · simp only [reduceCtorEq, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true, and_self,
    or_true]
  · simp only [false_iff, not_or, not_and]
    cases d
    all_goals {
      simp only [forall_const, reduceCtorEq, false_implies, and_true, true_and]
      simp only [imp_false, forall_const, reduceCtorEq, false_implies] at *
      assumption
    }

theorem same_responses_iff_same_decisions {r : Response} {t : Term} :
  r ∼ t ↔ r.decision ∼ t
:= by
  simp only [Same.same, SameResponses]

theorem same_responses_self_decision {resp : Response} :
  resp ∼ resp.decision
:= by
  simp only [Same.same, Spec.SameDecisions]

theorem same_decision_and_response_implies_same_decision
  {decision : Spec.Decision} {resp : Response} {t : Term} :
  decision ∼ t → resp ∼ t → resp ∼ decision
:= by
  intro h₁ h₂
  rw [same_responses_iff_same_decisions] at h₂
  rw [same_decisions_iff_allow_true_or_deny_false] at h₁
  rcases h₁ with ⟨h₁, h₃⟩ | ⟨h₁, h₃⟩
  all_goals {
    subst h₁ h₃
    simp only [Same.same, SymCC.SameDecisions, Term.prim.injEq, TermPrim.bool.injEq,
      Bool.false_eq_true, imp_self, implies_true, Spec.SameDecisions] at *
    split at h₂ <;> first | contradiction | assumption
  }

theorem isAuthorized_ok_implies {ps : Policies} {εnv : SymEnv} {t : Term} :
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  ∃ tp tf,
    satisfiedPolicies .permit ps εnv = .ok tp ∧
    satisfiedPolicies .forbid ps εnv = .ok tf ∧
    t = and tp (not tf)
:= by
  intro hok
  simp only [SymCC.isAuthorized] at hok
  simp_do_let (SymCC.satisfiedPolicies Effect.forbid ps εnv) at hok
  simp_do_let (SymCC.satisfiedPolicies Effect.permit ps εnv) at hok
  simp only [Except.ok.injEq, exists_and_left, exists_eq_left'] at *
  simp only [hok]

theorem isAuthorized_wf {ps : Policies} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedForPolicies ps →
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  t.WellFormed εnv.entities ∧ t.typeOf = .bool
:= by
  intro hwε hok
  replace ⟨tp, tf, hokp, hokf, hok⟩ := isAuthorized_ok_implies hok
  subst hok
  replace hokp := satisfiedPolicies_wf hwε hokp
  replace hokf := satisfiedPolicies_wf hwε hokf
  replace hokf := wf_not hokf.left hokf.right
  exact wf_and hokp.left hokf.left hokp.right hokf.right

theorem isAuthorized_interpret_eq_when_interpret_eq {ps : Policies} {εnv : SymEnv} {I I' : Interpretation} {t : Term}
  (hwε : εnv.WellFormedForPolicies ps)
  (hwI : I.WellFormed εnv.entities)
  (hwI' : I'.WellFormed εnv.entities)
  (heq : ∀ (p : Policy) (t : Term), p ∈ ps → compile p.toExpr εnv = Except.ok t → Term.interpret I t = Term.interpret I' t)
  (hok : SymCC.isAuthorized ps εnv = .ok t) :
  Term.interpret I t = Term.interpret I' t
:= by
  replace ⟨tp, tf, hokp, hokf, hok⟩ := isAuthorized_ok_implies hok
  subst hok
  have ⟨hwp, htyp⟩ := satisfiedPolicies_wf hwε hokp
  have ⟨hwf, htyf⟩ := satisfiedPolicies_wf hwε hokf
  have hwfn := wf_not hwf htyf
  rw [interpret_and hwI hwp hwfn.left htyp hwfn.right, interpret_not hwI hwf,
    interpret_and hwI' hwp hwfn.left htyp hwfn.right, interpret_not hwI' hwf,
    satisfiedPolicies_interpret_eq_when_interpret_eq hwε hwI hwI' heq hokp,
    satisfiedPolicies_interpret_eq_when_interpret_eq hwε hwI hwI' heq hokf]

theorem isAuthorized_interpret {ps : Policies} {εnv : SymEnv} {t : Term} {I : Interpretation} :
  εnv.WellFormedForPolicies ps →
  I.WellFormed εnv.entities →
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  Cedar.SymCC.isAuthorized ps (εnv.interpret I) = .ok (t.interpret I)
:= by
  intro hwε hwI hok
  replace ⟨tp, tf, hokp, hokf, hok⟩ := isAuthorized_ok_implies hok
  subst hok
  simp only [SymCC.isAuthorized, satisfiedPolicies_interpret hwε hwI hokf,
    satisfiedPolicies_interpret hwε hwI hokp, Except.bind_ok, Except.ok.injEq]
  have ⟨hwp, htyp⟩ := satisfiedPolicies_wf hwε hokp
  have ⟨hwf, htyf⟩ := satisfiedPolicies_wf hwε hokf
  have hwfn := wf_not hwf htyf
  rw [interpret_and hwI hwp hwfn.left htyp hwfn.right]
  rw [interpret_not hwI hwf]

theorem isAuthorized_same {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedForPolicies ps →
  env.WellFormedForPolicies ps →
  env ∼ εnv →
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  Cedar.Spec.isAuthorized env.request env.entities ps ∼ t
:= by
  intro hwε hwe heq hok
  rw [same_responses_iff_same_decisions, same_decisions_iff_allow_true_or_deny_false]
  replace ⟨tp, tf, hokp, hokf, hok⟩ := isAuthorized_ok_implies hok
  subst hok
  have ⟨hwp, htyp⟩ := satisfiedPolicies_wf hwε hokp
  replace hokp := satisfiedPolicies_eq hwε hwe heq hokp
  have ⟨hwf, htyf⟩ := satisfiedPolicies_wf hwε hokf
  replace hokf := satisfiedPolicies_eq hwε hwe heq hokf
  clear hwp htyp hwf htyf
  subst hokp hokf
  cases hbp : (Spec.satisfiedPolicies Effect.permit ps env.request env.entities).isEmpty
  · simp only [Bool.not_false, pe_and_true_left]
    cases hbf : (Spec.satisfiedPolicies Effect.forbid ps env.request env.entities).isEmpty
    · simp only [Spec.isAuthorized, hbf, pe_not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq, Bool.not_false, Term.prim.injEq, TermPrim.bool.injEq, and_self, or_true]
    · simp only [Spec.isAuthorized, hbf, hbp, pe_not_false, Bool.not_false, Bool.and_self, ↓reduceIte,
      Bool.not_true, and_self, reduceCtorEq, Term.prim.injEq, TermPrim.bool.injEq, Bool.true_eq_false, or_false]
  · simp only [Spec.isAuthorized, hbp, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, reduceCtorEq, pe_and_false_left, Term.prim.injEq, TermPrim.bool.injEq, and_self, or_true]

theorem isAuthorized_bisimulation {ps : Policies} {env : Env} {εnv : SymEnv} {t : Term} {I : Interpretation} :
  εnv.WellFormedForPolicies ps →
  env.WellFormedForPolicies ps →
  I.WellFormed εnv.entities →
  env ∼ εnv.interpret I →
  Cedar.SymCC.isAuthorized ps εnv = .ok t →
  Cedar.Spec.isAuthorized env.request env.entities ps ∼ t.interpret I
:= by
  intro hwε hwe hwI heq hok
  replace hok := isAuthorized_interpret hwε hwI hok
  replace hwε := interpret_εnv_wf_for_policies hwε hwI
  exact isAuthorized_same hwε hwe heq hok

end Cedar.Thm

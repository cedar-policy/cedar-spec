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

import Cedar.SymCC.Verifier
import Cedar.Thm.SymCC.Enforcer
import Cedar.Thm.SymCC.Authorizer
import Cedar.Thm.SymCC.Verifier.Same

/-!
This file proves the soundness and completeness of
`Cedar.SymCC.verifyEvaluate` for well-behaved verification queries.  This
enables proving soundness and completeness of analyses built on `verifyEvaluate`
by proving that their queries are well-behaved.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

def WellBehavedEvaluateQuery (φ : Term → Term) (f : Spec.Result Value → Bool) : Prop :=
  WellFormedOutput ∧ Interpretable ∧ Same
where
  WellFormedInput (t : Term) (εs : SymEntities) :=
    t.WellFormed εs ∧ t.typeOf = .option .bool
  WellFormedOutput :=
    ∀ (t : Term) (εs : SymEntities),
      WellFormedInput t εs →
      (φ t).WellFormed εs ∧ (φ t).typeOf = .bool
  Interpretable :=
    ∀ (t : Term) (εs : SymEntities) (I : Interpretation),
      WellFormedInput t εs →
      I.WellFormed εs →
      (φ t).interpret I = φ (t.interpret I)
  Same :=
    ∀ (t : Term) (εs : SymEntities) (r : Spec.Result Value),
      WellFormedInput t εs →
      r ∼ t →
      (f r) ∼ (φ t)

private theorem wbeq_bisimulation {φ : Term → Term} {f : Spec.Result Value → Bool} {εs : SymEntities} {t : Term} {r : Spec.Result Value} {I : Interpretation} :
  WellBehavedEvaluateQuery.WellFormedInput t εs →
  WellBehavedEvaluateQuery.Same φ f →
  I.WellFormed εs →
  r ∼ (t.interpret I) →
  (f r) ∼ (φ (t.interpret I))
:= by
  intro hwt hφf hwI heq
  have hwt' := interpret_term_wf hwI hwt.left
  rw [hwt.right] at hwt'
  exact hφf _ _ r hwt' heq

private theorem interpret_not_wbeq {φ : Term → Term} {t : Term} {I : Interpretation} {εs : SymEntities} :
  I.WellFormed εs →
  WellBehavedEvaluateQuery.WellFormedInput t εs →
  WellBehavedEvaluateQuery.WellFormedOutput φ →
  WellBehavedEvaluateQuery.Interpretable φ →
  Term.interpret I (not (φ t)) = not (φ (t.interpret I))
:= by
  intro hwI hwt hwφ hiφ
  rw [interpret_not hwI]
  · rw [hiφ t εs I hwt hwI]
  · exact (hwφ t εs hwt).left

private theorem verifyEvaluate_ok_implies {φ : Term → Term} {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  verifyEvaluate φ p εnv = .ok asserts →
  ∃ t ts,
    compile p.toExpr εnv = .ok t ∧
    enforce [p.toExpr] εnv = Set.mk ts ∧
    asserts = ts ++ [not (φ t)]
:= by
  intro hok
  simp only [verifyEvaluate] at hok
  simp_do_let (compile p.toExpr εnv) at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  rename_i t hr
  exists t, (enforce [p.toExpr] εnv).elts

theorem verifyEvaluate_is_sound {φ : Term → Term} {f : Spec.Result Value → Bool} {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedEvaluateQuery φ f →
  εnv.StronglyWellFormedForPolicy p →
  verifyEvaluate φ p εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p →
    f (evaluate p.toExpr env.request env.entities) = true
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε hok hsat env ⟨I, hwI, heq⟩ hwe
  rw [asserts_unsatisfiable_def] at hsat
  replace ⟨t, hsat⟩ := hsat I hwI
  replace ⟨t₁, ts, hok, ha, hvc⟩ := verifyEvaluate_ok_implies hok
  subst hvc
  replace ha := swf_implies_enforce_satisfiedBy heq hwI
    (swf_εnv_for_policy_iff_swf_for_polices.mp hwε)
    (swf_env_for_policy_iff_swf_for_polices.mp hwe) ha
  replace ha := asserts_last_not_true ha hsat.left hsat.right
  subst ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, ne_eq, true_and] at hsat
  replace hwε := swf_εnv_for_implies_wf_for hwε
  replace hwe := swf_env_for_implies_wf_for hwe
  have hrb := compile_bisimulation hwε hwe hwI heq hok
  have hwt₁ := compile_policy_wf hwε hok
  rw [interpret_not_wbeq hwI hwt₁ hwφ hiφ] at hsat
  replace hrb := wbeq_bisimulation hwt₁ hφf hwI hrb
  exact same_bool_not_not_true_implies_true hrb hsat

theorem verifyEvaluate_is_complete {φ : Term → Term} {f : Spec.Result Value → Bool} {p : Policy} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedEvaluateQuery φ f →
  εnv.StronglyWellFormedForPolicy p →
  verifyEvaluate φ p εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p ∧
    Env.EnumCompleteFor env εnv ∧
    f (evaluate p.toExpr env.request env.entities) = false
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε hok hsat
  rw [asserts_satisfiable_def] at hsat
  replace ⟨I, hwI, hsat⟩ := hsat
  replace ⟨t₁, ts, hok, ha, hvc⟩ := verifyEvaluate_ok_implies hok
  subst hvc
  replace ⟨hsat, hvc⟩ := asserts_all_true hsat
  replace ⟨I', env, hwI', heq, hwe, henum_comp, hsat⟩ := enforce_satisfiedBy_implies_exists_swf
    (swf_εnv_for_policy_iff_swf_for_polices.mp hwε) hwI ha hsat
  exists env
  rw [← swf_env_for_policy_iff_swf_for_polices] at hwe
  simp only [memOfSymEnv, hwe, true_and]
  constructor
  · exists I'
  · replace hwε := swf_εnv_for_implies_wf_for hwε
    replace hwe := swf_env_for_implies_wf_for hwe
    have hrb := compile_bisimulation hwε hwe hwI' heq hok
    have hwt₁ := compile_policy_wf hwε hok
    specialize hsat p t₁ (by simp only [List.mem_cons, List.not_mem_nil, or_false]) hok
    rw [interpret_not_wbeq hwI hwt₁ hwφ hiφ, hsat] at hvc
    replace hrb := wbeq_bisimulation hwt₁ hφf hwI' hrb
    simp only [henum_comp, true_and]
    exact same_bool_not_true_implies_false hrb hvc

end Cedar.Thm

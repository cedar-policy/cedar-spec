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
`Cedar.SymCC.verifyEvaluatePair` for well-behaved verification queries.  This
enables proving soundness and completeness of analyses built on `verifyEvaluatePair`
by proving that their queries are well-behaved.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

def WellBehavedEvaluatePairQuery (φ : Term → Term → Term) (f : Spec.Result Value → Spec.Result Value → Bool) : Prop :=
  WellFormedOutput ∧ Interpretable ∧ Same
where
  WellFormedInput (t₁ t₂ : Term) (εs : SymEntities) :=
    t₁.WellFormed εs ∧ t₁.typeOf = .option .bool ∧
    t₂.WellFormed εs ∧ t₂.typeOf = .option .bool
  WellFormedOutput :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities),
      WellFormedInput t₁ t₂ εs →
      (φ t₁ t₂).WellFormed εs ∧ (φ t₁ t₂).typeOf = .bool
  Interpretable :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities) (I : Interpretation),
      WellFormedInput t₁ t₂ εs →
      I.WellFormed εs →
      (φ t₁ t₂).interpret I = φ (t₁.interpret I) (t₂.interpret I)
  Same :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities) (r₁ r₂ : Spec.Result Value),
      WellFormedInput t₁ t₂ εs →
      r₁ ∼ t₁ →
      r₂ ∼ t₂ →
      (f r₁ r₂) ∼ (φ t₁ t₂)

private theorem wbepq_bisimulation {φ : Term → Term → Term} {f : Spec.Result Value → Spec.Result Value → Bool} {εs : SymEntities} {t₁ t₂ : Term} {r₁ r₂ : Spec.Result Value} {I : Interpretation} :
  WellBehavedEvaluatePairQuery.WellFormedInput t₁ t₂ εs →
  WellBehavedEvaluatePairQuery.Same φ f →
  I.WellFormed εs →
  r₁ ∼ (t₁.interpret I) →
  r₂ ∼ (t₂.interpret I) →
  (f r₁ r₂) ∼ (φ (t₁.interpret I) (t₂.interpret I))
:= by
  intro hwt hφf hwI heq₁ heq₂
  have hwt₁' := interpret_term_wf hwI hwt.left
  have hwt₂' := interpret_term_wf hwI hwt.2.2.left
  have hwt₁_wf := hwt₁'.left
  have hwt₁_ty := hwt₁'.right
  have hwt₂_wf := hwt₂'.left
  have hwt₂_ty := hwt₂'.right
  rw [hwt.2.left] at hwt₁_ty
  rw [hwt.2.2.2] at hwt₂_ty
  exact hφf (t₁.interpret I) (t₂.interpret I) εs r₁ r₂ ⟨hwt₁_wf, hwt₁_ty, hwt₂_wf, hwt₂_ty⟩ heq₁ heq₂

private theorem interpret_not_wbepq {φ : Term → Term → Term} {t₁ t₂ : Term} {I : Interpretation} {εs : SymEntities} :
  I.WellFormed εs →
  WellBehavedEvaluatePairQuery.WellFormedInput t₁ t₂ εs →
  WellBehavedEvaluatePairQuery.WellFormedOutput φ →
  WellBehavedEvaluatePairQuery.Interpretable φ →
  Term.interpret I (not (φ t₁ t₂)) = not (φ (t₁.interpret I) (t₂.interpret I))
:= by
  intro hwI hwt hwφ hiφ
  rw [interpret_not hwI]
  · rw [hiφ t₁ t₂ εs I hwt hwI]
  · exact (hwφ t₁ t₂ εs hwt).left

private theorem verifyEvaluatePair_ok_implies {φ : Term → Term → Term} {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  verifyEvaluatePair φ p₁ p₂ εnv = .ok asserts →
  ∃ t₁ t₂ ts,
    compile p₁.toExpr εnv = .ok t₁ ∧
    compile p₂.toExpr εnv = .ok t₂ ∧
    enforce [p₁.toExpr, p₂.toExpr] εnv = Set.mk ts ∧
    asserts = ts ++ [not (φ t₁ t₂)]
:= by
  intro hok
  simp only [verifyEvaluatePair] at hok
  simp_do_let (compile p₁.toExpr εnv) at hok
  simp_do_let (compile p₂.toExpr εnv) at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  rename_i t₁ hr₁ t₂ hr₂
  exists t₁, t₂, (enforce [p₁.toExpr, p₂.toExpr] εnv).elts

theorem verifyEvaluatePair_is_sound {φ : Term → Term → Term} {f : Spec.Result Value → Spec.Result Value → Bool} {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedEvaluatePairQuery φ f →
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyEvaluatePair φ p₁ p₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicy p₁ →
    env.StronglyWellFormedForPolicy p₂ →
    f (evaluate p₁.toExpr env.request env.entities) (evaluate p₂.toExpr env.request env.entities) = true
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε₁ hwε₂ hok hsat env ⟨I, hwI, heq⟩ hwe₁ hwe₂
  rw [asserts_unsatisfiable_def] at hsat
  replace ⟨t, hsat⟩ := hsat I hwI
  replace ⟨t₁, t₂, ts, hok₁, hok₂, ha, hvc⟩ := verifyEvaluatePair_ok_implies hok
  subst hvc
  replace ha := swf_implies_enforce_satisfiedBy heq hwI
    (swf_εnv_for_policies_iff_swf_for_append.mp (And.intro
      (swf_εnv_for_policy_iff_swf_for_polices.mp hwε₁)
      (swf_εnv_for_policy_iff_swf_for_polices.mp hwε₂)))
    (swf_env_for_policies_iff_swf_for_append.mp (And.intro
      (swf_env_for_policy_iff_swf_for_polices.mp hwe₁)
      (swf_env_for_policy_iff_swf_for_polices.mp hwe₂))) ha
  replace ha := asserts_last_not_true ha hsat.left hsat.right
  subst ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, ne_eq, true_and] at hsat
  replace hwε₁ := swf_εnv_for_implies_wf_for hwε₁
  replace hwε₂ := swf_εnv_for_implies_wf_for hwε₂
  replace hwe₁ := swf_env_for_implies_wf_for hwe₁
  replace hwe₂ := swf_env_for_implies_wf_for hwe₂
  have hrb₁ := compile_bisimulation hwε₁ hwe₁ hwI heq hok₁
  have hrb₂ := compile_bisimulation hwε₂ hwe₂ hwI heq hok₂
  have hwt₁ := compile_policy_wf hwε₁ hok₁
  have hwt₂ := compile_policy_wf hwε₂ hok₂
  rw [interpret_not_wbepq hwI ⟨hwt₁.left, hwt₁.right, hwt₂.left, hwt₂.right⟩ hwφ hiφ] at hsat
  replace hrb := wbepq_bisimulation ⟨hwt₁.left, hwt₁.right, hwt₂.left, hwt₂.right⟩ hφf hwI hrb₁ hrb₂
  exact same_bool_not_not_true_implies_true hrb hsat

theorem verifyEvaluatePair_is_complete {φ : Term → Term → Term} {f : Spec.Result Value → Spec.Result Value → Bool} {p₁ p₂ : Policy} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedEvaluatePairQuery φ f →
  εnv.StronglyWellFormedForPolicy p₁ →
  εnv.StronglyWellFormedForPolicy p₂ →
  verifyEvaluatePair φ p₁ p₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicy p₁ ∧
    env.StronglyWellFormedForPolicy p₂ ∧
    Env.EnumCompleteFor env εnv ∧
    f (evaluate p₁.toExpr env.request env.entities) (evaluate p₂.toExpr env.request env.entities) = false
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε₁ hwε₂ hok hsat
  rw [asserts_satisfiable_def] at hsat
  replace ⟨I, hwI, hsat⟩ := hsat
  replace ⟨t₁, t₂, ts, hok₁, hok₂, ha, hvc⟩ := verifyEvaluatePair_ok_implies hok
  subst hvc
  replace ⟨hsat, hvc⟩ := asserts_all_true hsat
  replace ⟨I', env, hwI', heq, hwe, henum_comp, hsat⟩ := enforce_satisfiedBy_implies_exists_swf
    (swf_εnv_for_policies_iff_swf_for_append.mp (And.intro
      (swf_εnv_for_policy_iff_swf_for_polices.mp hwε₁)
      (swf_εnv_for_policy_iff_swf_for_polices.mp hwε₂))) hwI ha hsat
  exists env
  rw [← swf_env_for_policies_iff_swf_for_append] at hwe
  have hwe₁ : env.StronglyWellFormedForPolicy p₁ := by
    have := hwe.left
    rwa [← swf_env_for_policy_iff_swf_for_polices] at this
  have hwe₂ : env.StronglyWellFormedForPolicy p₂ := by
    have := hwe.right
    rwa [← swf_env_for_policy_iff_swf_for_polices] at this
  simp only [memOfSymEnv, hwe₁, hwe₂, true_and]
  constructor
  · exists I'
  · replace hwε₁ := swf_εnv_for_implies_wf_for hwε₁
    replace hwε₂ := swf_εnv_for_implies_wf_for hwε₂
    replace hwe₁ := swf_env_for_implies_wf_for hwe₁
    replace hwe₂ := swf_env_for_implies_wf_for hwe₂
    have hrb₁ := compile_bisimulation hwε₁ hwe₁ hwI' heq hok₁
    have hrb₂ := compile_bisimulation hwε₂ hwe₂ hwI' heq hok₂
    have hwt₁ := compile_policy_wf hwε₁ hok₁
    have hwt₂ := compile_policy_wf hwε₂ hok₂
    have hsat₁ := hsat p₁ t₁ (by simp) hok₁
    have hsat₂ := hsat p₂ t₂ (by simp) hok₂
    rw [interpret_not_wbepq hwI ⟨hwt₁.left, hwt₁.right, hwt₂.left, hwt₂.right⟩ hwφ hiφ] at hvc
    rw [hsat₁, hsat₂] at hvc
    replace hrb := wbepq_bisimulation ⟨hwt₁.left, hwt₁.right, hwt₂.left, hwt₂.right⟩ hφf hwI' hrb₁ hrb₂
    simp only [henum_comp, true_and]
    exact same_bool_not_true_implies_false hrb hvc

end Cedar.Thm

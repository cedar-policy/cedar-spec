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
`Cedar.SymCC.verifyIsAuthorized` for well-behaved verification queries.  This
enables proving soundness and completenss of analyses built on
`verifyIsAuthorized` by proving that their queries are well-behaved.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

def WellBehavedIsAuthorizedQuery (φ : Term → Term → Term) (f : Response → Response → Bool) : Prop :=
  WellFormedOutput ∧ Interpretable ∧ Same
where
  WellFormedInput (t : Term) (εs : SymEntities) :=
    t.WellFormed εs ∧ t.typeOf = .bool
  WellFormedInputs (t₁ t₂ : Term) (εs : SymEntities) :=
    WellFormedInput t₁ εs ∧ WellFormedInput t₂ εs
  WellFormedOutput :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities),
      WellFormedInputs t₁ t₂ εs →
      (φ t₁ t₂).WellFormed εs ∧ (φ t₁ t₂).typeOf = .bool
  Interpretable :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities) (I : Interpretation),
      WellFormedInputs t₁ t₂ εs →
      I.WellFormed εs →
      (φ t₁ t₂).interpret I = φ (t₁.interpret I) (t₂.interpret I)
  Same :=
    ∀ (t₁ t₂ : Term) (εs : SymEntities) (r₁ r₂ : Response),
      WellFormedInputs t₁ t₂ εs →
      r₁ ∼ t₁ → r₂ ∼ t₂ →
      (f r₁ r₂) ∼ (φ t₁ t₂)

private theorem wbaq_bisimulation {φ : Term → Term → Term} {f : Response → Response → Bool} {εs : SymEntities} {t₁ t₂ : Term} {r₁ r₂ : Response} {I : Interpretation} :
  WellBehavedIsAuthorizedQuery.WellFormedInputs t₁ t₂ εs →
  WellBehavedIsAuthorizedQuery.Same φ f →
  I.WellFormed εs →
  r₁ ∼ (t₁.interpret I) → r₂ ∼ (t₂.interpret I) →
  (f r₁ r₂) ∼ (φ (t₁.interpret I) (t₂.interpret I))
:= by
  intro ⟨hwt₁, hwt₂⟩ hφf hwI heq₁ heq₂
  have hwt₁' := interpret_term_wf hwI hwt₁.left
  rw [hwt₁.right] at hwt₁'
  have hwt₂' := interpret_term_wf hwI hwt₂.left
  rw [hwt₂.right] at hwt₂'
  exact hφf _ _ _ _ _ (And.intro hwt₁' hwt₂') heq₁ heq₂

private theorem interpret_not_wbaq {φ : Term → Term → Term} {t₁ t₂ : Term} {I : Interpretation} {εs : SymEntities} :
  I.WellFormed εs →
  WellBehavedIsAuthorizedQuery.WellFormedInputs t₁ t₂ εs →
  WellBehavedIsAuthorizedQuery.WellFormedOutput φ →
  WellBehavedIsAuthorizedQuery.Interpretable φ →
  Term.interpret I (not (φ t₁ t₂)) = not (φ (t₁.interpret I) (t₂.interpret I))
:= by
  intro hwI hwt hwφ hiφ
  rw [interpret_not hwI]
  · rw [hiφ t₁ t₂ εs I hwt hwI]
  · exact (hwφ t₁ t₂ εs hwt).left

private theorem verifyIsAuthorized_ok_implies {φ : Term → Term → Term} {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  verifyIsAuthorized φ ps₁ ps₂ εnv = .ok asserts →
  ∃ t₁ t₂ ts,
    isAuthorized ps₁ εnv = .ok t₁ ∧
    isAuthorized ps₂ εnv = .ok t₂ ∧
    enforce ((ps₁ ++ ps₂).map Policy.toExpr) εnv = Set.mk ts ∧
    asserts = ts ++ [not (φ t₁ t₂)]
:= by
  intro hok
  simp only [verifyIsAuthorized, List.map_append] at hok
  simp_do_let (isAuthorized ps₁ εnv) at hok
  simp_do_let (isAuthorized ps₂ εnv) at hok
  rename_i t₁ hok₁ t₂ hok₂
  simp only [Except.ok.injEq] at hok
  subst hok
  exists t₁, t₂, (enforce (List.map Policy.toExpr ps₁ ++ List.map Policy.toExpr ps₂) εnv).elts
  simp only [List.map_append, and_self]

theorem verifyIsAuthorized_is_sound {φ : Term → Term → Term} {f : Response → Response → Bool} {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedIsAuthorizedQuery φ f →
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyIsAuthorized φ ps₁ ps₂ εnv = .ok asserts →
  εnv ⊭ asserts →
  ∀ env,
    env ∈ᵢ εnv →
    env.StronglyWellFormedForPolicies ps₁ →
    env.StronglyWellFormedForPolicies ps₂ →
    f (Spec.isAuthorized env.request env.entities ps₁) (Spec.isAuthorized env.request env.entities ps₂) = true
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε₁ hwε₂ hok hsat env ⟨I, hwI, heq⟩ hwe₁ hwe₂
  rw [asserts_unsatisfiable_def] at hsat
  replace ⟨t, hsat⟩ := hsat I hwI
  replace ⟨t₁, t₂, ts, hok₁, hok₂, ha, hok⟩ := verifyIsAuthorized_ok_implies hok
  subst hok
  replace ha := swf_implies_enforce_satisfiedBy heq hwI
    (swf_εnv_for_policies_iff_swf_for_append.mp (And.intro hwε₁ hwε₂))
    (swf_env_for_policies_iff_swf_for_append.mp (And.intro hwe₁ hwe₂)) ha
  replace ha := asserts_last_not_true ha hsat.left hsat.right
  subst ha
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, ne_eq, true_and] at hsat
  replace hwε₁ := swf_εnv_for_policies_implies_wf_for_policies hwε₁
  replace hwe₁ := swf_env_for_policies_implies_wf_for_policies hwe₁
  have hrb₁ := isAuthorized_bisimulation hwε₁ hwe₁ hwI heq hok₁
  replace hwε₂ := swf_εnv_for_policies_implies_wf_for_policies hwε₂
  replace hwe₂ := swf_env_for_policies_implies_wf_for_policies hwe₂
  have hrb₂ := isAuthorized_bisimulation hwε₂ hwe₂ hwI heq hok₂
  have hwt₁ := isAuthorized_wf hwε₁ hok₁
  have hwt₂ := isAuthorized_wf hwε₂ hok₂
  rw [interpret_not_wbaq hwI (And.intro hwt₁ hwt₂) hwφ hiφ] at hsat
  have hrb := wbaq_bisimulation (And.intro hwt₁ hwt₂) hφf hwI hrb₁ hrb₂
  exact same_bool_not_not_true_implies_true hrb hsat

theorem verifyIsAuthorized_is_complete {φ : Term → Term → Term} {f : Response → Response → Bool} {ps₁ ps₂ : Policies} {εnv : SymEnv} {asserts : Asserts} :
  WellBehavedIsAuthorizedQuery φ f →
  εnv.StronglyWellFormedForPolicies ps₁ →
  εnv.StronglyWellFormedForPolicies ps₂ →
  verifyIsAuthorized φ ps₁ ps₂ εnv = .ok asserts →
  εnv ⊧ asserts →
  ∃ env,
    env ∈ᵢ εnv ∧
    env.StronglyWellFormedForPolicies ps₁ ∧
    env.StronglyWellFormedForPolicies ps₂ ∧
    f (Spec.isAuthorized env.request env.entities ps₁) (Spec.isAuthorized env.request env.entities ps₂) = false
:= by
  intro ⟨hwφ, hiφ, hφf⟩ hwε₁ hwε₂ hok hsat
  rw [asserts_satisfiable_def] at hsat
  replace ⟨I, hwI, hsat⟩ := hsat
  replace ⟨t₁, t₂, ts, hok₁, hok₂, ha, hok⟩ := verifyIsAuthorized_ok_implies hok
  subst hok
  replace ⟨hsat, hvc⟩ := asserts_all_true hsat
  replace ⟨I', env, hwI', heq, hwe, hsat⟩ := enforce_satisfiedBy_implies_exists_swf
    (swf_εnv_for_policies_iff_swf_for_append.mp (And.intro hwε₁ hwε₂)) hwI ha hsat
  exists env
  rw [← swf_env_for_policies_iff_swf_for_append] at hwe
  simp only [memOfSymEnv, hwe, true_and]
  constructor
  · exists I'
  · replace hwε₁ := swf_εnv_for_policies_implies_wf_for_policies hwε₁
    replace hwe₁ := swf_env_for_policies_implies_wf_for_policies hwe.left
    have hrb₁ := isAuthorized_bisimulation hwε₁ hwe₁ hwI' heq hok₁
    replace hwε₂ := swf_εnv_for_policies_implies_wf_for_policies hwε₂
    replace hwe₂ := swf_env_for_policies_implies_wf_for_policies hwe.right
    have hrb₂ := isAuthorized_bisimulation hwε₂ hwe₂ hwI' heq hok₂
    have hwt₁ := isAuthorized_wf hwε₁ hok₁
    have hwt₂ := isAuthorized_wf hwε₂ hok₂
    have hsat₁ : ∀ (p : Policy) (t : Term), p ∈ ps₁ → compile p.toExpr εnv = Except.ok t → Term.interpret I t = Term.interpret I' t := by
      intro p t hin hok
      exact hsat p t (by simp only [hin, List.mem_append, true_or]) hok
    have hsat₂ : ∀ (p : Policy) (t : Term), p ∈ ps₂ → compile p.toExpr εnv = Except.ok t → Term.interpret I t = Term.interpret I' t := by
      intro p t hin hok
      exact hsat p t (by simp only [hin, List.mem_append, or_true]) hok
    replace hok₁ := isAuthorized_interpret_eq_when_interpret_eq hwε₁ hwI hwI' hsat₁ hok₁
    replace hok₂ := isAuthorized_interpret_eq_when_interpret_eq hwε₂ hwI hwI' hsat₂ hok₂
    rw [interpret_not_wbaq hwI (And.intro hwt₁ hwt₂) hwφ hiφ, hok₁, hok₂] at hvc
    have hrb := wbaq_bisimulation (And.intro hwt₁ hwt₂) hφf hwI' hrb₁ hrb₂
    exact same_bool_not_true_implies_false hrb hvc

end Cedar.Thm

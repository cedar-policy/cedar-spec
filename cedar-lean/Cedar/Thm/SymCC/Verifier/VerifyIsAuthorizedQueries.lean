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

import Cedar.Thm.SymCC.Verifier.VerifyIsAuthorized

/-!
This file proves that `verifyIsAuthorized` queries are well-behaved.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

def bothAllowOrBothDeny (r₁ r₂ : Response) : Bool :=
  r₁.decision = r₂.decision

theorem verifyEquivalent_wbaq :
  WellBehavedIsAuthorizedQuery eq bothAllowOrBothDeny
:= by
  have hw : WellBehavedIsAuthorizedQuery.WellFormedOutput eq := by
    intro t₁ t₂ εs ⟨hwt₁, hwt₂⟩
    exact wf_eq hwt₁.left hwt₂.left (by simp only [hwt₁.right, hwt₂.right])
  have hi : WellBehavedIsAuthorizedQuery.Interpretable eq := by
    intro t₁ t₂ εs I ⟨hwt₁, hwt₂⟩ hwI
    exact interpret_eq hwI hwt₁.left hwt₂.left
  have hs : WellBehavedIsAuthorizedQuery.Same eq bothAllowOrBothDeny := by
    intro t₁ t₂ εs r₁ r₂ ⟨hwt₁, hwt₂⟩ heq₁ heq₂
    rw [same_responses_iff_same_decisions, same_decisions_iff_allow_true_or_deny_false] at heq₁ heq₂
    simp only [bothAllowOrBothDeny, same_bool_def]
    rcases heq₁ with ⟨heq₁, ht₁⟩ | ⟨heq₁, ht₁⟩ <;>
    rcases heq₂ with ⟨heq₂, ht₂⟩ | ⟨heq₂, ht₂⟩
    all_goals {
      subst ht₁ ht₂
      simp [heq₁, heq₂, pe_eq_prim]
    }
  simp [WellBehavedIsAuthorizedQuery, hw, hi, hs]

def atLeastOneDenies (r₁ r₂ : Response) : Bool :=
  ! (r₁.decision = .allow && r₂.decision = .allow)

theorem verifyDisjoint_wbaq :
  WellBehavedIsAuthorizedQuery verifyDisjoint.disjoint atLeastOneDenies
:= by
  have hw : WellBehavedIsAuthorizedQuery.WellFormedOutput verifyDisjoint.disjoint := by
    intro t₁ t₂ εs ⟨hwt₁, hwt₂⟩
    have h := wf_and hwt₁.left hwt₂.left hwt₁.right hwt₂.right
    simp [verifyDisjoint.disjoint, wf_not h.left h.right]
  have hi : WellBehavedIsAuthorizedQuery.Interpretable verifyDisjoint.disjoint := by
    intro t₁ t₂ εs I ⟨hwt₁, hwt₂⟩ hwI
    have h := wf_and hwt₁.left hwt₂.left hwt₁.right hwt₂.right
    simp [verifyDisjoint.disjoint, interpret_not hwI h.left, interpret_and hwI hwt₁.left hwt₂.left hwt₁.right hwt₂.right]
  have hs : WellBehavedIsAuthorizedQuery.Same verifyDisjoint.disjoint atLeastOneDenies := by
    intro t₁ t₂ εs r₁ r₂ ⟨hwt₁, hwt₂⟩ heq₁ heq₂
    rw [same_responses_iff_same_decisions, same_decisions_iff_allow_true_or_deny_false] at heq₁ heq₂
    simp only [verifyDisjoint.disjoint, atLeastOneDenies, same_bool_def]
    rcases heq₁ with ⟨heq₁, ht₁⟩ | ⟨heq₁, ht₁⟩ <;>
    rcases heq₂ with ⟨heq₂, ht₂⟩ | ⟨heq₂, ht₂⟩
    all_goals {
      subst ht₁ ht₂
      simp [heq₁, heq₂, pe_and_true_left, pe_and_false_left, pe_not_true, pe_not_false]
    }
  simp only [WellBehavedIsAuthorizedQuery, hw, hi, hs, and_self]

def ifFirstAllowsSoDoesSecond (r₁ r₂ : Response) : Bool :=
  r₁.decision != .allow || r₂.decision = .allow

theorem verifyImplies_wbaq :
  WellBehavedIsAuthorizedQuery implies ifFirstAllowsSoDoesSecond
:= by
  have hw : WellBehavedIsAuthorizedQuery.WellFormedOutput implies := by
    intro t₁ t₂ εs ⟨hwt₁, hwt₂⟩
    simp only [implies]
    have h := wf_not hwt₁.left hwt₁.right
    apply wf_or h.left hwt₂.left h.right hwt₂.right
  have hi : WellBehavedIsAuthorizedQuery.Interpretable implies := by
    intro t₁ t₂ εs I ⟨hwt₁, hwt₂⟩ hwI
    have h := wf_not hwt₁.left hwt₁.right
    simp [implies, interpret_or hwI h.left hwt₂.left h.right hwt₂.right, interpret_not hwI hwt₁.left]
  have hs : WellBehavedIsAuthorizedQuery.Same implies ifFirstAllowsSoDoesSecond := by
    intro t₁ t₂ εs r₁ r₂ ⟨hwt₁, hwt₂⟩ heq₁ heq₂
    rw [same_responses_iff_same_decisions, same_decisions_iff_allow_true_or_deny_false] at heq₁ heq₂
    simp only [implies, ifFirstAllowsSoDoesSecond, same_bool_def]
    rcases heq₁ with ⟨heq₁, ht₁⟩ | ⟨heq₁, ht₁⟩ <;>
    rcases heq₂ with ⟨heq₂, ht₂⟩ | ⟨heq₂, ht₂⟩
    all_goals {
      subst ht₁ ht₂
      simp [heq₁, heq₂, pe_not_true, pe_not_false, pe_or_true_left, pe_or_false_left]
    }

  simp only [WellBehavedIsAuthorizedQuery, hw, hi, hs, and_self]

def denies (r₁ : Response) : Bool :=
  r₁.decision = .deny

theorem isAuthorized_empty_denies (env : Env) :
  (Spec.isAuthorized env.request env.entities []).decision = .deny
:= by
  simp [Spec.isAuthorized, Spec.satisfiedPolicies, denies]

theorem denies_eq_implies_false (r₁ : Response) (env : Env) :
  denies r₁ = ifFirstAllowsSoDoesSecond r₁ (Spec.isAuthorized env.request env.entities [])
:= by
  simp only [denies, ifFirstAllowsSoDoesSecond, isAuthorized_empty_denies env, reduceCtorEq, decide_false, Bool.or_false]
  cases r₁.decision <;> simp

theorem swf_εnv_for_empty_policies {εnv : SymEnv} :
  εnv.StronglyWellFormed → εnv.StronglyWellFormedForPolicies []
:= by
  simp [SymEnv.StronglyWellFormedForPolicies, SymEnv.StronglyWellFormedForAll]

theorem swf_env_for_empty_policies {env : Env} :
  env.StronglyWellFormed → env.StronglyWellFormedForPolicies []
:= by
  simp [Env.StronglyWellFormedForPolicies, Env.StronglyWellFormedForAll]

def allows (r₁ : Response) : Bool :=
  r₁.decision = .allow

private theorem satisfiedWithEffect_allowAll_permit (env : Env) :
  satisfiedWithEffect .permit verifyAlwaysAllows.allowAll env.request env.entities =
  .some verifyAlwaysAllows.allowAll.id
:= by
  simp [satisfiedWithEffect, verifyAlwaysAllows.allowAll,
    satisfied, Policy.toExpr, PrincipalScope.toExpr,
    ActionScope.toExpr, ResourceScope.toExpr, Scope.toExpr,
    Conditions.toExpr, evaluate, Result.as, Coe.coe, Value.asBool]

private theorem satisfiedWithEffect_allowAll_forbid (env : Env) :
  satisfiedWithEffect .forbid verifyAlwaysAllows.allowAll env.request env.entities =
  .none
:= by
  simp [satisfiedWithEffect, verifyAlwaysAllows.allowAll]

private theorem satisfiedPolicies_allowAll_permit_nonempty {env : Env} :
  (satisfiedPolicies .permit [verifyAlwaysAllows.allowAll] env.request env.entities).isEmpty = false
:= by
  unfold Spec.satisfiedPolicies
  rw [List.filterMap_cons_some (by exact satisfiedWithEffect_allowAll_permit env)]
  simp only [List.filterMap_nil]
  by_contra hc
  simp only [Bool.not_eq_false, ← Set.make_empty, List.cons_ne_self] at hc

private theorem satisfiedPolicies_allowAll_forbid_empty {env : Env} :
  (satisfiedPolicies .forbid [verifyAlwaysAllows.allowAll] env.request env.entities).isEmpty = true
:= by
  unfold Spec.satisfiedPolicies
  rw [List.filterMap_cons_none (by exact satisfiedWithEffect_allowAll_forbid env)]
  simp only [List.filterMap_nil, ← Set.make_empty]

theorem isAuthorized_allowAll_allows (env : Env) :
  (Spec.isAuthorized env.request env.entities [verifyAlwaysAllows.allowAll]).decision = .allow
:= by
  simp [Spec.isAuthorized,
    satisfiedPolicies_allowAll_permit_nonempty,
    satisfiedPolicies_allowAll_forbid_empty]

theorem allows_eq_allowAll_implies (r₁ : Response) (env : Env) :
  allows r₁ = ifFirstAllowsSoDoesSecond (Spec.isAuthorized env.request env.entities [verifyAlwaysAllows.allowAll]) r₁
:= by
  simp [allows, ifFirstAllowsSoDoesSecond, isAuthorized_allowAll_allows env]

private theorem allowAll_validRefs (f : EntityUID → Prop) :
  Expr.ValidRefs f verifyAlwaysAllows.allowAll.toExpr
:= by
  simp only [Policy.toExpr, PrincipalScope.toExpr, Scope.toExpr, verifyAlwaysAllows.allowAll,
    ActionScope.toExpr, ResourceScope.toExpr, Conditions.toExpr, List.foldr_nil]
  have ht : Prim.ValidRef f (Prim.bool true) := by simp only [Prim.ValidRef]
  apply Expr.ValidRefs.and_valid
  exact Expr.ValidRefs.lit_valid ht
  apply Expr.ValidRefs.and_valid
  exact Expr.ValidRefs.lit_valid ht
  apply Expr.ValidRefs.and_valid <;>
  exact Expr.ValidRefs.lit_valid ht

theorem swf_εnv_for_allowAll_policies {εnv : SymEnv} :
  εnv.StronglyWellFormed → εnv.StronglyWellFormedForPolicies [verifyAlwaysAllows.allowAll]
:= by
  simp only [SymEnv.StronglyWellFormedForPolicies, SymEnv.StronglyWellFormedForAll, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  intro h
  simp [h, SymEntities.ValidRefsFor, allowAll_validRefs]

theorem swf_env_for_allowAll_policies {env : Env} :
  env.StronglyWellFormed → env.StronglyWellFormedForPolicies [verifyAlwaysAllows.allowAll]
:= by
  simp only [Env.StronglyWellFormedForPolicies, Env.StronglyWellFormedForAll, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  intro h
  simp [h, SymEntities.ValidRefsFor, allowAll_validRefs]

end Cedar.Thm

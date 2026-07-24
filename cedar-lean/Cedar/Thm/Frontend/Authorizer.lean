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

import Cedar.Spec
import Cedar.Frontend.Cst
import Cedar.Frontend.Cst.Semantics
import Cedar.Thm.Data.Set

namespace Cedar.Thm.Cst

open Cedar.Data
open Cedar.Spec
open Cedar.Frontend
open Cedar.Frontend.Cst hiding Expr ExprImpl ExprData OrExpr AndExpr AddExpr MultExpr Name Policy PolicyImpl Policies Ident Literal Primary Member MemAccess Unary Relation RelOp Cond VariableDef Ref RecInit Str


def HasSatisfiedEffect (effect : Effect) (request : Request) (entities : Entities) (policies : Cst.Policies) : Prop :=
  ∃ policy ∈ policies.ps,
  Cst.satisfiedWithEffect effect policy request entities = true

theorem satisfied_iff_satisfiedPolicies_non_empty {effect : Effect} {request : Request} {entities : Entities} {policies : Cst.Policies} :
  HasSatisfiedEffect effect request entities policies ↔ (Cst.satisfiedPolicies effect policies request entities).isEmpty = false := by
  simp only [HasSatisfiedEffect, Cst.satisfiedPolicies, Set.isEmpty_make_eq_false]
  constructor
  · rintro ⟨p, hp, hsat⟩
    apply List.ne_nil_of_mem (a := p.id)
    rw [List.mem_filterMap]
    exact ⟨p, hp, by simp [hsat]⟩
  · intro hne
    obtain ⟨id, hid⟩ := List.exists_mem_of_ne_nil _ hne
    rw [List.mem_filterMap] at hid
    obtain ⟨pol, hpair, hf⟩ := hid
    refine ⟨pol, hpair, ?_⟩
    by_cases h : Cst.satisfiedWithEffect effect pol request entities = true
    · exact h
    · simp [h] at hf

def IsExplicitlyForbidden := HasSatisfiedEffect .forbid

theorem explicitly_forbidden_iff_satisfying_forbid
  (req : Request) (entities : Entities) (policies : Cst.Policies) :
  IsExplicitlyForbidden req entities policies ↔ (Cst.satisfiedPolicies .forbid policies req entities).isEmpty = false := by
  unfold IsExplicitlyForbidden
  simp [satisfied_iff_satisfiedPolicies_non_empty]

def IsExplicitlyPermitted := HasSatisfiedEffect .permit

theorem explicitly_permitted_iff_satisfying_permit
  (req : Request) (entities : Entities) (policies : Cst.Policies) :
  IsExplicitlyPermitted req entities policies ↔ (Cst.satisfiedPolicies .permit policies req entities).isEmpty = false := by
  unfold IsExplicitlyPermitted
  simp [satisfied_iff_satisfiedPolicies_non_empty]

theorem forbid_trumps_permit
  (request : Request) (entities : Entities) (policies : Cst.Policies) :
  (IsExplicitlyForbidden request entities policies) →
  (Cst.isAuthorized request entities policies).decision = .deny := by
  intro h
  unfold Cst.isAuthorized
  rw [explicitly_forbidden_iff_satisfying_forbid] at h
  simp [h]

theorem allowed_only_if_explicitly_permitted (request : Request) (entities : Entities) (policies : Cst.Policies) :
  (Cst.isAuthorized request entities policies).decision = .allow →
  IsExplicitlyPermitted request entities policies := by
  unfold Cst.isAuthorized
  generalize hf: (Cst.satisfiedPolicies .forbid policies request entities) = forbids
  generalize hp: (Cst.satisfiedPolicies .permit policies request entities) = permits
  simp [Bool.and_eq_true]
  cases forbids.isEmpty <;> simp
  cases hpemp : permits.isEmpty with
  | true => simp
  | false =>
    simp
    rw [←hp] at hpemp
    have h := explicitly_permitted_iff_satisfying_permit request entities policies
    simp [h]; exact hpemp

theorem default_deny
  (request : Request) (entities : Entities) (policies : Cst.Policies) :
  ¬ IsExplicitlyPermitted request entities policies →
  (Cst.isAuthorized request entities policies).decision = .deny := by
  intro h
  generalize hdec : (Cst.isAuthorized request entities policies).decision = dec
  by_contra hcontra
  cases dec with
  | allow =>
    have hperm := allowed_only_if_explicitly_permitted request entities policies hdec
    contradiction
  | deny => contradiction

theorem explicit_allow
  (request : Request) (entities : Entities) (policies : Cst.Policies) :
  (Cst.isAuthorized request entities policies).decision = .allow →
  IsExplicitlyPermitted request entities policies :=
  allowed_only_if_explicitly_permitted request entities policies


end Cedar.Thm.Cst

import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Thm.Data.Set

namespace Cedar.Thm.Cst

open Cedar.Data
open Cedar.Spec

def HasSatisfiedEffect (effect : Effect) (request : Request) (entities : Entities) (policies : Cst.Policies) : Prop :=
  ∃ policy ∈ policies.ps,
  Cst.satisfiedWithEffect effect policy request entities = true

/-- The second components of `withIDs` are exactly the original policies. -/
private theorem withIDs_map_snd (policies : Cst.Policies) :
    (Cst.Policies.withIDs policies).map Prod.snd = policies.ps := by
  unfold Cst.Policies.withIDs
  apply List.map_snd_zip
  simp [List.length_range]

theorem satisfied_iff_satisfiedPolicies_non_empty {effect : Effect} {request : Request} {entities : Entities} {policies : Cst.Policies} :
  HasSatisfiedEffect effect request entities policies ↔ (Cst.satisfiedPolicies effect policies request entities).isEmpty = false := by
  simp only [HasSatisfiedEffect, Cst.satisfiedPolicies, Set.isEmpty_make_eq_false]
  rw [← withIDs_map_snd policies]
  constructor
  · rintro ⟨p, hp, hsat⟩
    rw [List.mem_map] at hp
    obtain ⟨⟨pid, pol⟩, hpair, hpeq⟩ := hp
    simp only at hpeq
    subst hpeq
    apply List.ne_nil_of_mem (a := pid)
    rw [List.mem_filterMap]
    exact ⟨(pid, pol), hpair, by simp [hsat]⟩
  · intro hne
    obtain ⟨id, hid⟩ := List.exists_mem_of_ne_nil _ hne
    rw [List.mem_filterMap] at hid
    obtain ⟨⟨pid, pol⟩, hpair, hf⟩ := hid
    refine ⟨pol, ?_, ?_⟩
    · rw [List.mem_map]; exact ⟨(pid, pol), hpair, rfl⟩
    · by_cases h : Cst.satisfiedWithEffect effect pol request entities = true
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

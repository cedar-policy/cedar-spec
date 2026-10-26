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

import CedarRustModel.Evaluator
import CedarRustModel.Authorizer
import CedarRustModel.Policy
import Cedar.Thm.Authorization
import Cedar.Thm.PolicySlice

/-!
# Authorization theorems about the Rust model

The theorems of `Cedar/Thm/Authorization.lean` and `Cedar/Thm/PolicySlice.lean`,
restated for `authorizer.is_authorized` via `is_authorized_ok`. They are
transcribed literally as Verus axioms in
`cedar-policy-core/src/verification/authorizer_lean_theorems.rs`.

They assume `Linked ps`: an arbitrary model policy need not correspond to a
Lean policy, but `policy.to_policy` of a linked policy does.
-/

namespace CedarRustModel.Thm

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data
open CedarRustModel

/-! ## Definitions (transcribed to Verus) -/

/-- `p` is the authorizer's policy of a linked policy. -/
def IsLinked (p : authorizer.Policy) : Prop :=
  ∃ lp, policy.to_policy lp = ok p

/-- Every policy of `ps` is the authorizer's policy of a linked policy. -/
def Linked (ps : value.List authorizer.Policy) : Prop :=
  ∀ p ∈ List.toList ps, IsLinked p

/-- Some policy of `ps` with effect `eff` is satisfied. -/
def HasSatisfiedEffect (eff : authorizer.Effect) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) : Prop :=
  ∃ p ∈ List.toList ps, p.effect = eff ∧ authorizer.satisfied p req es = ok true

def IsExplicitlyForbidden := HasSatisfiedEffect .Forbid
def IsExplicitlyPermitted := HasSatisfiedEffect .Permit

/-- The effect of the policies that determine a decision -/
def decisionEffect : authorizer.Decision → authorizer.Effect
  | .Allow => .Permit
  | .Deny => .Forbid

/-- `slice` is a sound slice of `ps`: a subset that only leaves out policies
that are neither satisfied nor erroring. -/
def IsSoundPolicySlice (req : request.Request) (es : value.List (value.EntityUID × entities.EntityData))
    (slice ps : value.List authorizer.Policy) : Prop :=
  (∀ p ∈ List.toList slice, p ∈ List.toList ps) ∧
  ∀ p ∈ List.toList ps, p ∉ List.toList slice →
    authorizer.satisfied p req es = ok false ∧ authorizer.has_error p req es = ok false

/-! ## From model policies to Lean policies -/

/-- The Lean policy of a model policy (a fixed choice of a linked policy). -/
noncomputable def specOf (p : authorizer.Policy) : Cedar.Spec.Policy :=
  open Classical in
  if h : IsLinked p then LinkedPolicy.toSpec (Classical.choose h)
  else { id := Str.toSpec p.id, effect := Effect.toSpec p.effect,
         principalScope := .principalScope .any, actionScope := .actionScope .any,
         resourceScope := .resourceScope .any, condition := [] }

noncomputable def specsOf (ps : value.List authorizer.Policy) : List Cedar.Spec.Policy :=
  (List.toList ps).map specOf

theorem specOf_corresponds {p : authorizer.Policy} (h : IsLinked p) : Policy.Corresponds p (specOf p) := by
  simp only [specOf, h, _root_.dite_true]
  obtain ⟨q, h₁, h₂⟩ := to_policy_correct (Classical.choose h)
  rw [Classical.choose_spec h, Result.ok.injEq] at h₁
  subst h₁
  exact h₂

theorem specsOf_corresponds {ps : value.List authorizer.Policy} (h : Linked ps) :
    List.Forall₂ Policy.Corresponds (List.toList ps) (specsOf ps) := by
  unfold specsOf
  rw [List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun p hp => specOf_corresponds (h p hp)

theorem str_toSpec_inj {a b : value.List Char} (h : Str.toSpec a = Str.toSpec b) : a = b := by
  have h' : List.toList a = List.toList b := by
    simpa [Str.toSpec] using congrArg String.toList h
  clear h
  induction a generalizing b with
  | Nil => cases b <;> simp_all [List.toList]
  | Cons x xs ih =>
    cases b with
    | Nil => simp_all [List.toList]
    | Cons y ys =>
      simp only [List.toList, List.cons.injEq] at h'
      rw [h'.1, ih h'.2]

theorem effect_toSpec_inj {a b : authorizer.Effect} (h : Effect.toSpec a = Effect.toSpec b) : a = b := by
  cases a <;> cases b <;> simp_all [Effect.toSpec]

theorem strs_toSpec_inj {a b : value.List (value.List Char)}
    (h : (List.toList a).map Str.toSpec = (List.toList b).map Str.toSpec) : a = b := by
  induction a generalizing b with
  | Nil => cases b <;> simp_all [List.toList]
  | Cons x xs ih =>
    cases b with
    | Nil => simp_all [List.toList]
    | Cons y ys =>
      simp only [List.toList, List.map_cons, List.cons.injEq] at h
      rw [str_toSpec_inj h.1, ih h.2]

theorem decision_toSpec_inj {a b : authorizer.Decision} (h : Decision.toSpec a = Decision.toSpec b) : a = b := by
  cases a <;> cases b <;> simp_all [Decision.toSpec]

theorem response_toSpec_inj {r₁ r₂ : authorizer.Response} (h : Response.toSpec r₁ = Response.toSpec r₂) :
    r₁ = r₂ := by
  obtain ⟨d₁, p₁, e₁⟩ := r₁
  obtain ⟨d₂, p₂, e₂⟩ := r₂
  simp only [Response.toSpec, Cedar.Spec.Response.mk.injEq, Set.mk.injEq] at h
  rw [decision_toSpec_inj h.1, strs_toSpec_inj h.2.1, strs_toSpec_inj h.2.2]

theorem satisfied_spec {p : authorizer.Policy} (h : IsLinked p) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    authorizer.satisfied p req es = ok (Cedar.Spec.satisfied (specOf p) (Request.toSpec req) (Entities.toSpec es)) :=
  satisfied_ok p _ (specOf_corresponds h) req es

theorem has_error_spec {p : authorizer.Policy} (h : IsLinked p) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    authorizer.has_error p req es = ok (Cedar.Spec.hasError (specOf p) (Request.toSpec req) (Entities.toSpec es)) :=
  has_error_ok p _ (specOf_corresponds h) req es

theorem has_satisfied_effect_iff {eff : authorizer.Effect} {req : request.Request}
    {es : value.List (value.EntityUID × entities.EntityData)} {ps : value.List authorizer.Policy} (h : Linked ps) :
    HasSatisfiedEffect eff req es ps ↔
      Cedar.Thm.HasSatisfiedEffect (Effect.toSpec eff) (Request.toSpec req) (Entities.toSpec es) (specsOf ps) := by
  unfold HasSatisfiedEffect Cedar.Thm.HasSatisfiedEffect specsOf
  constructor
  · rintro ⟨p, hp, he, hs⟩
    refine ⟨specOf p, List.mem_map_of_mem hp, ?_, ?_⟩
    · rw [(specOf_corresponds (h p hp)).2.1, he]
    · rw [satisfied_spec (h p hp), Result.ok.injEq] at hs; exact hs
  · rintro ⟨lp, hlp, he, hs⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hlp
    refine ⟨p, hp, ?_, ?_⟩
    · rw [(specOf_corresponds (h p hp)).2.1] at he; exact effect_toSpec_inj he
    · rw [satisfied_spec (h p hp)]; simp [hs]

/-- The model's authorizer is `isAuthorized` on the Lean policies. -/
theorem is_authorized_spec (req : request.Request) (es : value.List (value.EntityUID × entities.EntityData))
    {ps : value.List authorizer.Policy} (h : Linked ps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      Response.toSpec r = isAuthorized (Request.toSpec req) (Entities.toSpec es) (specsOf ps) :=
  is_authorized_ok req es ps _ (specsOf_corresponds h)

theorem decision_deny {r : authorizer.Response} :
    r.decision = .Deny ↔ (Response.toSpec r).decision = .deny := by
  cases h : r.decision <;> simp [Response.toSpec, Decision.toSpec, h]

theorem decision_allow {r : authorizer.Response} :
    r.decision = .Allow ↔ (Response.toSpec r).decision = .allow := by
  cases h : r.decision <;> simp [Response.toSpec, Decision.toSpec, h]

/-! ## Theorems -/

/-- `Cedar.Thm.forbid_trumps_permit` -/
theorem forbid_trumps_permit (req : request.Request) (es : value.List (value.EntityUID × entities.EntityData))
    (ps : value.List authorizer.Policy) (hl : Linked ps) :
    IsExplicitlyForbidden req es ps →
    ∃ r, authorizer.is_authorized req es ps = ok r ∧ r.decision = .Deny := by
  intro hf
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, decision_deny.mpr ?_⟩
  rw [h₂]
  exact Cedar.Thm.forbid_trumps_permit _ _ _ ((has_satisfied_effect_iff hl).mp hf)

/-- `Cedar.Thm.allowed_only_if_explicitly_permitted` -/
theorem allowed_only_if_explicitly_permitted (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) (hl : Linked ps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      (r.decision = .Allow → IsExplicitlyPermitted req es ps) := by
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, fun ha => ?_⟩
  rw [decision_allow, h₂] at ha
  exact (has_satisfied_effect_iff hl).mpr (Cedar.Thm.allowed_only_if_explicitly_permitted _ _ _ ha)

/-- `Cedar.Thm.default_deny` -/
theorem default_deny (req : request.Request) (es : value.List (value.EntityUID × entities.EntityData))
    (ps : value.List authorizer.Policy) (hl : Linked ps) :
    ¬ IsExplicitlyPermitted req es ps →
    ∃ r, authorizer.is_authorized req es ps = ok r ∧ r.decision = .Deny := by
  intro hp
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, decision_deny.mpr ?_⟩
  rw [h₂]
  exact Cedar.Thm.default_deny _ _ _ (fun h => hp ((has_satisfied_effect_iff hl).mpr h))

/-- `Cedar.Thm.allowed_iff_explicitly_permitted_and_not_denied` -/
theorem allowed_iff_explicitly_permitted_and_not_denied (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) (hl : Linked ps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      ((IsExplicitlyPermitted req es ps ∧ ¬ IsExplicitlyForbidden req es ps) ↔ r.decision = .Allow) := by
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, ?_⟩
  rw [decision_allow, h₂, ← Cedar.Thm.allowed_iff_explicitly_permitted_and_not_denied]
  unfold IsExplicitlyPermitted IsExplicitlyForbidden Cedar.Thm.IsExplicitlyPermitted
    Cedar.Thm.IsExplicitlyForbidden
  rw [has_satisfied_effect_iff hl, has_satisfied_effect_iff hl]
  rfl

/-- `Cedar.Thm.denied_iff_explicitly_denied_or_not_permitted` -/
theorem denied_iff_explicitly_denied_or_not_permitted (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) (hl : Linked ps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      ((IsExplicitlyForbidden req es ps ∨ ¬ IsExplicitlyPermitted req es ps) ↔ r.decision = .Deny) := by
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, ?_⟩
  rw [decision_deny, h₂, ← Cedar.Thm.denied_iff_explicitly_denied_or_not_permitted]
  unfold IsExplicitlyPermitted IsExplicitlyForbidden Cedar.Thm.IsExplicitlyPermitted
    Cedar.Thm.IsExplicitlyForbidden
  rw [has_satisfied_effect_iff hl, has_satisfied_effect_iff hl]
  rfl

/-- `Cedar.Thm.order_and_dup_independent`: the response only depends on the
set of policies. -/
theorem order_and_dup_independent (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps₁ ps₂ : value.List authorizer.Policy)
    (hl₁ : Linked ps₁) (hl₂ : Linked ps₂) :
    (∀ p, p ∈ List.toList ps₁ ↔ p ∈ List.toList ps₂) →
    ∃ r, authorizer.is_authorized req es ps₁ = ok r ∧ authorizer.is_authorized req es ps₂ = ok r := by
  intro h
  obtain ⟨r₁, h₁, h₂⟩ := is_authorized_spec req es hl₁
  obtain ⟨r₂, h₃, h₄⟩ := is_authorized_spec req es hl₂
  have heq : specsOf ps₁ ≡ specsOf ps₂ := by
    unfold specsOf
    constructor <;> intro x hx <;> obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx <;>
      exact List.mem_map_of_mem (by simp_all)
  have := Cedar.Thm.order_and_dup_independent (Request.toSpec req) (Entities.toSpec es) _ _ heq
  rw [← h₂, ← h₄] at this
  rw [response_toSpec_inj this] at h₁
  exact ⟨r₂, h₁, h₃⟩

/-- `Cedar.Thm.unchanged_allow_when_add_permit` -/
theorem unchanged_allow_when_add_permit (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy)
    (p : authorizer.Policy) (hl : Linked ps) (hp : IsLinked p) :
    p.effect = .Permit →
    ∃ r r', authorizer.is_authorized req es ps = ok r ∧
      authorizer.is_authorized req es (.Cons p ps) = ok r' ∧
      (r.decision = .Allow → r'.decision = .Allow) := by
  intro he
  have hl' : Linked (.Cons p ps) := by
    intro q hq; simp only [List.toList, List.mem_cons] at hq; rcases hq with rfl | hq
    exacts [hp, hl q hq]
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  obtain ⟨r', h₃, h₄⟩ := is_authorized_spec req es hl'
  refine ⟨r, r', h₁, h₃, fun ha => ?_⟩
  rw [decision_allow, h₄]
  rw [decision_allow, h₂] at ha
  have hpe : (specOf p).effect = .permit := by rw [(specOf_corresponds hp).2.1, he]; rfl
  exact Cedar.Thm.unchanged_allow_when_add_permit _ _ _ _ hpe ha

/-- `Cedar.Thm.unchanged_deny_when_add_forbid` -/
theorem unchanged_deny_when_add_forbid (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy)
    (p : authorizer.Policy) (hl : Linked ps) (hp : IsLinked p) :
    p.effect = .Forbid →
    ∃ r r', authorizer.is_authorized req es ps = ok r ∧
      authorizer.is_authorized req es (.Cons p ps) = ok r' ∧
      (r.decision = .Deny → r'.decision = .Deny) := by
  intro he
  have hl' : Linked (.Cons p ps) := by
    intro q hq; simp only [List.toList, List.mem_cons] at hq; rcases hq with rfl | hq
    exacts [hp, hl q hq]
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  obtain ⟨r', h₃, h₄⟩ := is_authorized_spec req es hl'
  refine ⟨r, r', h₁, h₃, fun ha => ?_⟩
  rw [decision_deny, h₄]
  rw [decision_deny, h₂] at ha
  have hpe : (specOf p).effect = .forbid := by rw [(specOf_corresponds hp).2.1, he]; rfl
  exact Cedar.Thm.unchanged_deny_when_add_forbid _ _ _ _ hpe ha

/-- `Cedar.Thm.isAuthorized_eq_for_sound_policy_slice` -/
theorem is_authorized_eq_for_sound_policy_slice (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (slice ps : value.List authorizer.Policy)
    (hl : Linked ps) :
    IsSoundPolicySlice req es slice ps →
    ∃ r, authorizer.is_authorized req es slice = ok r ∧ authorizer.is_authorized req es ps = ok r := by
  intro ⟨hsub, hsound⟩
  have hls : Linked slice := fun p hp => hl p (hsub p hp)
  obtain ⟨r₁, h₁, h₂⟩ := is_authorized_spec req es hls
  obtain ⟨r₂, h₃, h₄⟩ := is_authorized_spec req es hl
  have hs : Cedar.Thm.IsSoundPolicySlice (Request.toSpec req) (Entities.toSpec es)
      (specsOf slice) (specsOf ps) := by
    constructor
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map_of_mem (hsub p hp)
    · intro x hx hnx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hnp : p ∉ List.toList slice := fun h => hnx (List.mem_map_of_mem h)
      obtain ⟨hs₁, hs₂⟩ := hsound p hp hnp
      rw [satisfied_spec (hl p hp), Result.ok.injEq] at hs₁
      rw [has_error_spec (hl p hp), Result.ok.injEq] at hs₂
      simp_all
  have := Cedar.Thm.isAuthorized_eq_for_sound_policy_slice _ _ _ _ hs
  rw [← h₂, ← h₄] at this
  rw [response_toSpec_inj this] at h₁
  exact ⟨r₂, h₁, h₃⟩

/-- `Cedar.Thm.determiningPolicies_of`: the determining policies are the IDs of
the satisfied permit (if allowed) or forbid (if denied) policies. -/
theorem determining_policies_of (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) (hl : Linked ps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      ∀ id, id ∈ List.toList r.determining_policies ↔
        ∃ p ∈ List.toList ps, p.id = id ∧
          p.effect = decisionEffect r.decision ∧
          authorizer.satisfied p req es = ok true := by
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, fun id => ?_⟩
  have hd := Cedar.Thm.determiningPolicies_of (Request.toSpec req) (Entities.toSpec es) (specsOf ps)
  simp only at hd
  rw [← h₂] at hd
  have hmem : id ∈ List.toList r.determining_policies ↔
      Str.toSpec id ∈ (Response.toSpec r).determiningPolicies := by
    simp only [Response.toSpec, ← Set.mem_set_iff_mem_mk, List.mem_map]
    exact ⟨fun h => ⟨id, h, rfl⟩, fun ⟨a, ha, he⟩ => str_toSpec_inj he ▸ ha⟩
  rw [hmem, hd]
  simp only [satisfiedPolicies, Set.mem_make, List.mem_filterMap, specsOf, List.mem_map]
  have hdec : (if (Response.toSpec r).decision = .allow then Cedar.Spec.Effect.permit else .forbid) =
      Effect.toSpec (decisionEffect r.decision) := by
    cases h : r.decision <;> simp [Response.toSpec, Decision.toSpec, Effect.toSpec, decisionEffect, h]
  rw [hdec]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hs⟩
    have hc := specOf_corresponds (hl p hp)
    simp only [satisfiedWithEffect, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hb, hid⟩ := hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    refine ⟨p, hp, str_toSpec_inj (hc.1 ▸ hid), effect_toSpec_inj (hc.2.1 ▸ hb.1), ?_⟩
    rw [satisfied_spec (hl p hp), hb.2]
  · rintro ⟨p, hp, hid, he, hs⟩
    have hc := specOf_corresponds (hl p hp)
    refine ⟨specOf p, ⟨p, hp, rfl⟩, ?_⟩
    rw [satisfied_spec (hl p hp), Result.ok.injEq] at hs
    simp only [satisfiedWithEffect, hc.1, hc.2.1, he, hid]
    simp_all

/-- The erroring policies are the IDs of the policies whose evaluation errors
(`Cedar.Spec.errorPolicies`). -/
theorem erroring_policies_of (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) (hl : Linked ps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      ∀ id, id ∈ List.toList r.erroring_policies ↔
        ∃ p ∈ List.toList ps, p.id = id ∧ authorizer.has_error p req es = ok true := by
  obtain ⟨r, h₁, h₂⟩ := is_authorized_spec req es hl
  refine ⟨r, h₁, fun id => ?_⟩
  have hmem : id ∈ List.toList r.erroring_policies ↔
      Str.toSpec id ∈ (Response.toSpec r).erroringPolicies := by
    simp only [Response.toSpec, ← Set.mem_set_iff_mem_mk, List.mem_map]
    exact ⟨fun h => ⟨id, h, rfl⟩, fun ⟨a, ha, he⟩ => str_toSpec_inj he ▸ ha⟩
  rw [hmem, h₂]
  have he : (isAuthorized (Request.toSpec req) (Entities.toSpec es) (specsOf ps)).erroringPolicies =
      errorPolicies (specsOf ps) (Request.toSpec req) (Entities.toSpec es) := by
    simp only [isAuthorized]; split <;> rfl
  rw [he]
  simp only [errorPolicies, Set.mem_make, List.mem_filterMap, specsOf, List.mem_map]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hs⟩
    have hc := specOf_corresponds (hl p hp)
    simp only [errored, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hb, hid⟩ := hs
    refine ⟨p, hp, str_toSpec_inj (hc.1 ▸ hid), ?_⟩
    rw [has_error_spec (hl p hp), hb]
  · rintro ⟨p, hp, hid, hs⟩
    have hc := specOf_corresponds (hl p hp)
    refine ⟨specOf p, ⟨p, hp, rfl⟩, ?_⟩
    rw [has_error_spec (hl p hp), Result.ok.injEq] at hs
    simp only [errored, hc.1, hid]
    simp_all

/-- `Cedar.Thm.determining_erroring_disjoint_when_unique_ids` -/
theorem determining_erroring_disjoint_when_unique_ids (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) (ps : value.List authorizer.Policy) (hl : Linked ps) :
    (∀ p₁ ∈ List.toList ps, ∀ p₂ ∈ List.toList ps, p₁.id = p₂.id → p₁ = p₂) →
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      ∀ id, ¬ (id ∈ List.toList r.determining_policies ∧ id ∈ List.toList r.erroring_policies) := by
  intro hu
  obtain ⟨r, h₁, h₂⟩ := determining_policies_of req es ps hl
  obtain ⟨r', h₃, h₄⟩ := erroring_policies_of req es ps hl
  rw [h₁, Result.ok.injEq] at h₃; subst h₃
  refine ⟨r, h₁, fun id ⟨hd, he⟩ => ?_⟩
  obtain ⟨p, hp, hid, _, hs⟩ := (h₂ id).mp hd
  obtain ⟨q, hq, hqid, he'⟩ := (h₄ id).mp he
  have := hu p hp q hq (hid.trans hqid.symm)
  subst this
  rw [satisfied_spec (hl p hp), Result.ok.injEq] at hs
  rw [has_error_spec (hl p hp), Result.ok.injEq] at he'
  simp only [Cedar.Spec.satisfied, Cedar.Spec.hasError] at hs he'
  split at he' <;> simp_all

end CedarRustModel.Thm

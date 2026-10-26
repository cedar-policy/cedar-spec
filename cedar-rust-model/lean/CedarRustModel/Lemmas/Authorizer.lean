module

public import CedarRustModel.Lemmas.Evaluate
import all Cedar.Data.Set
import all Cedar.Spec.Authorizer

/-! The model's authorizer agrees with `Cedar.Spec.isAuthorized`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

theorem satisfied_ok (p : authorizer.Policy) (lp : Cedar.Spec.Policy) (hp : Policy.Corresponds p lp)
    (req : request.Request) (es : value.List (value.EntityUID × entities.EntityData)) :
    authorizer.satisfied p req es =
      ok (Cedar.Spec.satisfied lp (Request.toSpec req) (Entities.toSpec es)) := by
  obtain ⟨_, _, hx⟩ := hp
  obtain ⟨r, h₁, h₂⟩ := evaluate_ok p.condition req es
  simp only [authorizer.satisfied, h₁, Std.bind_ok, Cedar.Spec.satisfied, hx, ← h₂]
  rcases r with (((b|_|_|_)|_|_|_)|_) <;> simp [Value.toSpec]
  cases b <;> simp

theorem has_error_ok (p : authorizer.Policy) (lp : Cedar.Spec.Policy) (hp : Policy.Corresponds p lp)
    (req : request.Request) (es : value.List (value.EntityUID × entities.EntityData)) :
    authorizer.has_error p req es =
      ok (Cedar.Spec.hasError lp (Request.toSpec req) (Entities.toSpec es)) := by
  obtain ⟨_, _, hx⟩ := hp
  obtain ⟨r, h₁, h₂⟩ := evaluate_ok p.condition req es
  simp only [authorizer.has_error, h₁, Std.bind_ok, Cedar.Spec.hasError, hx, ← h₂]
  cases r <;> simp

theorem satisfiedWithEffect_eq (eff : Cedar.Spec.Effect) (lp : Cedar.Spec.Policy) (req : Request)
    (es : Entities) :
    satisfiedWithEffect eff lp req es =
      if lp.effect == eff && Cedar.Spec.satisfied lp req es then some lp.id else none := by
  unfold satisfiedWithEffect; rfl

theorem errored_eq (lp : Cedar.Spec.Policy) (req : Request) (es : Entities) :
    errored lp req es = if hasError lp req es then some lp.id else none := by
  unfold errored; rfl

def effectOf (permit : Bool) : Cedar.Spec.Effect := if permit then .permit else .forbid

theorem satisfied_policies_ok (permit : Bool) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∀ (ps : value.List authorizer.Policy) (lps : _root_.List Cedar.Spec.Policy),
    _root_.List.Forall₂ Policy.Corresponds (List.toList ps) lps →
    ∃ l, authorizer.satisfied_policies permit ps req es = ok l ∧
      (List.toList l).map Str.toSpec =
        lps.filterMap (satisfiedWithEffect (effectOf permit) · (Request.toSpec req) (Entities.toSpec es)) := by
  intro ps
  induction ps with
  | Nil =>
    intro lps h
    cases h
    rw [authorizer.satisfied_policies.eq_def]; simp
  | Cons p ps ih =>
    intro lps h
    cases h with
    | cons hp hps =>
      rename_i lp lps
      obtain ⟨l, h₁, h₂⟩ := ih lps hps
      rw [authorizer.satisfied_policies.eq_def]
      simp only [h₁, Std.bind_ok, _root_.List.filterMap_cons]
      rw [satisfiedWithEffect_eq]
      have heff := hp.2.1
      have hid := hp.1
      have hsat := satisfied_ok p lp hp req es
      generalize Cedar.Spec.satisfied lp (Request.toSpec req) (Entities.toSpec es) = sb at hsat ⊢
      cases he : p.effect <;> cases permit <;> cases sb <;>
        simp [authorizer.is_permit, he, heff, effectOf, Effect.toSpec, h₂, hsat, clone_str_ok, hid]

theorem error_policies_ok (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∀ (ps : value.List authorizer.Policy) (lps : _root_.List Cedar.Spec.Policy),
    _root_.List.Forall₂ Policy.Corresponds (List.toList ps) lps →
    ∃ l, authorizer.error_policies ps req es = ok l ∧
      (List.toList l).map Str.toSpec =
        lps.filterMap (errored · (Request.toSpec req) (Entities.toSpec es)) := by
  intro ps
  induction ps with
  | Nil =>
    intro lps h
    cases h
    rw [authorizer.error_policies.eq_def]; simp
  | Cons p ps ih =>
    intro lps h
    cases h with
    | cons hp hps =>
      rename_i lp lps
      obtain ⟨l, h₁, h₂⟩ := ih lps hps
      rw [authorizer.error_policies.eq_def]
      simp only [h₁, Std.bind_ok, _root_.List.filterMap_cons, has_error_ok p lp hp req es]
      rw [errored_eq]
      cases Cedar.Spec.hasError lp (Request.toSpec req) (Entities.toSpec es) <;>
        simp [clone_str_ok, hp.1, h₂]

theorem is_authorized_ok
    (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData))
    (ps : value.List authorizer.Policy) (lps : _root_.List Cedar.Spec.Policy)
    (hps : _root_.List.Forall₂ Policy.Corresponds (List.toList ps) lps) :
    ∃ r, authorizer.is_authorized req es ps = ok r ∧
      Response.toSpec r =
        Cedar.Spec.isAuthorized (Request.toSpec req) (Entities.toSpec es) lps := by
  obtain ⟨f, hf₁, hf₂⟩ := satisfied_policies_ok false req es ps lps hps
  obtain ⟨p, hp₁, hp₂⟩ := satisfied_policies_ok true req es ps lps hps
  obtain ⟨e, he₁, he₂⟩ := error_policies_ok req es ps lps hps
  obtain ⟨f', hf₃, hf₄⟩ := strs_canonicalize_ok f
  obtain ⟨p', hp₃, hp₄⟩ := strs_canonicalize_ok p
  obtain ⟨e', he₃, he₄⟩ := strs_canonicalize_ok e
  simp only [authorizer.is_authorized, hf₁, hp₁, he₁, hf₃, hp₃, he₃, Std.bind_ok]
  have hF : satisfiedPolicies .forbid lps (Request.toSpec req) (Entities.toSpec es) =
      Set.mk ((List.toList f').map Str.toSpec) := by
    simp only [satisfiedPolicies, Set.make, hf₄, hf₂, effectOf]; rfl
  have hP : satisfiedPolicies .permit lps (Request.toSpec req) (Entities.toSpec es) =
      Set.mk ((List.toList p').map Str.toSpec) := by
    simp only [satisfiedPolicies, Set.make, hp₄, hp₂, effectOf]; rfl
  have hE : errorPolicies lps (Request.toSpec req) (Entities.toSpec es) =
      Set.mk ((List.toList e').map Str.toSpec) := by
    simp only [errorPolicies, Set.make, he₄, he₂]; rfl
  simp only [Cedar.Spec.isAuthorized, hF, hP, hE]
  cases f' <;> cases p' <;>
    simp [Response.toSpec, Decision.toSpec, Set.isEmpty, Set.empty]

end -- public section

end CedarRustModel

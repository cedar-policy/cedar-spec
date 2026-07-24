import Cedar.Spec
import Cedar.Frontend.Cst
import Cedar.Frontend.Cst.Semantics
import Cedar.Frontend.Cst.ToAst
import Cedar.Thm.Translation.AuxComplete
import Cedar.Thm.Translation.AuxSound
import Cedar.Thm.Translation.ExprComplete
import Cedar.Thm.Translation.ExprTranslation
import Cedar.Thm.Translation.PolicyToExpr

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Frontend
open Cedar.Frontend.Cst hiding Expr ExprImpl ExprData OrExpr AndExpr AddExpr MultExpr Name Policy PolicyImpl Policies Ident Literal Primary Member MemAccess Unary Relation RelOp Cond VariableDef Ref RecInit Str

/-- When `toPolicy?` succeeds, the CST policy's expression also translates to AST. -/
theorem toPolicy?_implies_toAExpr?
    {cp : Cst.Policy} {ap : Spec.Policy} :
    cp.toPolicy? = some ap →
    ∃ ae, cp.toExpr.toAExpr? = some ae := by
  intro htrans
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at htrans
  obtain ⟨eff, heff, ⟨ps, acts, rs⟩, hsc, conds, hconds, _⟩ := htrans
  -- Invert `extractScope?`: exactly three scope variables.
  simp only [Cst.Policy.toExpr, Cst.PolicyImpl.toExpr]
  match hvars : p.vars, hsc with
  | [a, b, c], hsc =>
    simp only [extractScope?, bind, Option.bind_eq_some_iff] at hsc
    obtain ⟨ps', hps, as', has, rs', hrs, _⟩ := hsc
    -- Each variable leaf translates.
    obtain ⟨lp, hlp⟩ := principal_leaf_isSome hps
    obtain ⟨la, hla⟩ := action_leaf_isSome has
    obtain ⟨lr, hlr⟩ := resource_leaf_isSome hrs
    -- The variable-expression list translates.
    have hvarsMapM : ∃ r, ([a, b, c].map Cst.VariableDef.toExpr).mapM Cst.Expr.toAExpr? = some r := by
      refine ⟨[lp, la, lr], ?_⟩
      simp [List.map_cons, List.mapM_cons, hlp, hla, hlr]
    -- The condition-expression list translates.
    have hcondsMapM := conds_mapM_toAExpr_isSome (by simpa [toConditions?] using hconds)
    -- The append translates.
    obtain ⟨r, hr⟩ := mapM_append_isSome hvarsMapM hcondsMapM
    -- Conclude via `foldAnd_toAExpr`.
    exact ⟨_, foldAnd_toAExpr _ r hr⟩
  | [], hsc => simp [extractScope?] at hsc
  | [_], hsc => simp [extractScope?] at hsc
  | [_, _], hsc => simp [extractScope?] at hsc
  | _ :: _ :: _ :: _ :: _, hsc => simp [extractScope?] at hsc

theorem policy_satisfied_agrees (cp : Cst.Policy) (ap : Spec.Policy)
  (req : Request) (es : Entities) :
  cp.toPolicy? = some ap →
  Cst.satisfied cp req es = satisfied ap req es := by
  intro htrans
  obtain ⟨ae, hae⟩ := toPolicy?_implies_toAExpr? htrans
  have heq : cp.toExpr.evaluate req es = evaluate ap.toExpr req es :=
    (expr_to_expr_sound hae).symm.trans
      (policy_to_expr_sound cp ap cp.toExpr ae req es htrans rfl hae)
  unfold Cst.satisfied Spec.satisfied
  rw [heq]

/-- Under a successful translation, `extractScope?` succeeds, so the new scope
    guard in `Cst.hasError` is a no-op and it reduces to the plain
    evaluate-the-policy-expression check. -/
theorem cst_hasError_eq_of_toPolicy {cp : Cst.Policy} {ap : Spec.Policy}
    {req : Request} {es : Entities} (htrans : cp.toPolicy? = some ap) :
    Cst.hasError cp req es =
      (match cp.toExpr.evaluate req es with | .ok _ => false | .error _ => true) := by
  obtain ⟨p⟩ := cp
  have hpp : p.toPolicy? = some ap := htrans
  have hcond : ¬ (p.toPolicy?.isNone = true) := by rw [hpp]; simp
  simp only [Cst.hasError, if_neg hcond]
  rfl

theorem policy_hasError_agrees (cp : Cst.Policy) (ap : Spec.Policy)
  (req : Request) (es : Entities) :
  cp.toPolicy? = some ap →
  Cst.hasError cp req es = hasError ap req es := by
  intro htrans
  obtain ⟨ae, hae⟩ := toPolicy?_implies_toAExpr? htrans
  have heq : cp.toExpr.evaluate req es = evaluate ap.toExpr req es :=
    (expr_to_expr_sound hae).symm.trans
      (policy_to_expr_sound cp ap cp.toExpr ae req es htrans rfl hae)
  rw [cst_hasError_eq_of_toPolicy htrans, heq]
  rfl

/-- Per-policy agreement of the error check. -/
theorem policy_errored_agrees (cp : Cst.Policy) (ap : Spec.Policy)
    (req : Request) (es : Entities)
    (htrans : cp.toPolicy? = some ap) :
    (if Cst.hasError cp req es then some cp.id else none) = errored ap req es := by
  have hhe : Cst.hasError cp req es = hasError ap req es :=
    policy_hasError_agrees cp ap req es htrans
  have hid : cp.id = ap.id := (toPolicy?_id_eq htrans).symm
  simp only [errored, hhe, hid]

/-- Per-policy agreement of the effect-filtered satisfaction check. -/
theorem policy_satisfiedWithEffect_agrees (cp : Cst.Policy) (ap : Spec.Policy)
    (req : Request) (es : Entities) (eff : Effect)
    (htrans : cp.toPolicy? = some ap) :
    (if Cst.satisfiedWithEffect eff cp req es then some cp.id else none)
      = Spec.satisfiedWithEffect eff ap req es := by
  obtain ⟨p⟩ := cp
  have htrans' := htrans
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at htrans'
  obtain ⟨e0, he0, ⟨ps, acts, rs⟩, hsc, conds, hconds, heq⟩ := htrans'
  have heffeq : e0 = ap.effect := by
    have := congrArg Spec.Policy.effect heq; simpa using this
  have heff : Cst.Ident.toEffect? p.effect = some ap.effect := by
    rw [he0, heffeq]
  have hsat : Cst.satisfied (.policy p) req es = satisfied ap req es :=
    policy_satisfied_agrees (.policy p) ap req es htrans
  have hid : (Cst.Policy.policy p).id = ap.id := (toPolicy?_id_eq htrans).symm
  simp only [Cst.satisfiedWithEffect, Spec.satisfiedWithEffect, heff, hsat, hid]
  by_cases hs : satisfied ap req es
  · simp only [hs, if_true, Bool.and_true]
    by_cases he : ap.effect = eff
    · simp [he]
    · simp [he]
  · simp [hs]

theorem satisfiedPolicies_agrees (cps : Cst.Policies) (aps : Spec.Policies)
  (req : Request) (es : Entities) (eff : Effect) :
  cps.toPolicies? = some aps →
  Cst.satisfiedPolicies eff cps req es = satisfiedPolicies eff aps req es := by
  intro htrans
  have hforall := toPolicies?_forall₂ htrans
  -- The two filterMaps agree pointwise.
  simp only [Cst.satisfiedPolicies, Spec.satisfiedPolicies]
  congr 1
  apply filterMap_congr_forall₂ hforall
  intro cp ap htp
  exact policy_satisfiedWithEffect_agrees cp ap req es eff htp

theorem errorPolicies_agrees (cps : Cst.Policies) (aps : Spec.Policies)
  (req : Request) (es : Entities) :
  cps.toPolicies? = some aps →
  Cst.errorPolicies cps req es = errorPolicies aps req es := by
  intro htrans
  have hforall := toPolicies?_forall₂ htrans
  simp only [Cst.errorPolicies, Spec.errorPolicies]
  congr 1
  apply filterMap_congr_forall₂ hforall
  intro cp ap htp
  exact policy_errored_agrees cp ap req es htp

theorem translation_is_sound (cps : Cst.Policies) (aps : Spec.Policies)
(req : Request) (es : Entities) :
  cps.toPolicies? = some aps →
  Cst.isAuthorized req es cps = Spec.isAuthorized req es aps := by
  intro htrans
  have hforbids := satisfiedPolicies_agrees cps aps req es .forbid htrans
  have hpermits := satisfiedPolicies_agrees cps aps req es .permit htrans
  have herrors := errorPolicies_agrees cps aps req es htrans
  simp [Cst.isAuthorized, Spec.isAuthorized]
  simp [hforbids, hpermits, herrors]

theorem noHasError_translates (cp : Cst.Policy) (req : Request) (es : Entities) :
  ¬ Cst.hasError cp req es →
  ∃ ap, cp.toPolicy? = some ap := by
  intro h
  obtain ⟨p⟩ := cp
  cases hp : p.toPolicy? with
  | none =>
    exfalso; apply h
    simp only [Cst.hasError, hp, Option.isNone_none, if_true]
  | some ap =>
    exact ⟨ap, by simp [Cst.Policy.toPolicy?, hp]⟩

theorem translation_is_complete (cps : Cst.Policies) (req : Request) (es : Entities) :
  ∀ cp ∈ cps.ps, cp.id ∉ (Cst.isAuthorized req es cps).erroringPolicies →
  ∃ ap, cp.toPolicy? = some ap := by
  intro cp hmem hnoterr
  apply noHasError_translates cp req es
  intro herr
  apply hnoterr
  have herrp : cp.id ∈ Cst.errorPolicies cps req es := by
    simp only [Cst.errorPolicies, Set.mem_make]
    exact List.mem_filterMap.mpr ⟨cp, hmem, by simp [herr]⟩
  simp only [Cst.isAuthorized]
  split <;> exact herrp


end Cedar.Thm

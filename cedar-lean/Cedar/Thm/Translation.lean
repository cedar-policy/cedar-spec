import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.ExprTranslation
import Cedar.Thm.Translation.PolicyToExpr

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

/-- When `toPolicy?` succeeds, the CST policy's expression also translates to AST. -/
private theorem toPolicy?_implies_toAExpr?
    {cp : Cst.Policy} {ap : Spec.Policy} :
    cp.toPolicy? = some ap →
    ∃ ae, cp.toExpr.toAExpr? = some ae := by
  intro htrans
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at htrans
  obtain ⟨eff, heff, ⟨ps, as, rs⟩, hsc, conds, hconds, _⟩ := htrans
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
  have h1 := @expr_to_expr_agrees _ _ req es hae (↑true : Value)
  have h2 := policy_to_expr_agrees cp ap cp.toExpr ae req es htrans rfl hae (val := (↑true : Value))
  have hiff : cp.toExpr.evaluate req es = .ok ↑true ↔ evaluate ap.toExpr req es = .ok ↑true :=
    ⟨fun hcst => h2.mp (h1.mpr hcst), fun hast => h1.mp (h2.mpr hast)⟩
  unfold Cst.satisfied satisfied
  simp only [show (cp.toExpr.evaluate req es = .ok ↑true) = (evaluate ap.toExpr req es = .ok ↑true)
      from propext hiff]

theorem policy_hasError_agrees (cp : Cst.Policy) (ap : Spec.Policy)
  (req : Request) (es : Entities) :
  cp.toPolicy? = some ap →
  Cst.hasError cp req es = hasError ap req es := by
  intro htrans
  obtain ⟨ae, hae⟩ := toPolicy?_implies_toAExpr? htrans
  have h1 : ∀ v, evaluate ae req es = .ok v ↔ cp.toExpr.evaluate req es = .ok v :=
    @expr_to_expr_agrees _ _ req es hae
  have h2 : ∀ v, evaluate ae req es = .ok v ↔ evaluate ap.toExpr req es = .ok v :=
    policy_to_expr_agrees cp ap cp.toExpr ae req es htrans rfl hae
  have hiff : ∀ v, cp.toExpr.evaluate req es = .ok v ↔ evaluate ap.toExpr req es = .ok v :=
    fun v => ⟨fun hcst => (h2 v).mp ((h1 v).mpr hcst), fun hast => (h1 v).mp ((h2 v).mpr hast)⟩
  unfold Cst.hasError hasError
  cases hcst : cp.toExpr.evaluate req es with
  | ok v => rw [(hiff v).mp hcst]
  | error e =>
    cases hast : evaluate ap.toExpr req es with
    | ok v => rw [(hiff v).mpr hast] at hcst; cases hcst
    | error e' => rfl

/-- Per-policy agreement of the error check. -/
theorem policy_errored_agrees (cp : Cst.Policy) (ap : Spec.Policy)
    (req : Request) (es : Entities)
    (htrans : cp.toPolicy? = some {ap with id := ""}) :
    (if Cst.hasError cp req es then some ap.id else none) = errored ap req es := by
  have hhe : Cst.hasError cp req es = hasError ap req es := by
    have h := policy_hasError_agrees cp {ap with id := ""} req es htrans
    simpa [hasError, Policy.toExpr] using h
  simp only [errored, hhe]

/-- Per-policy agreement of the effect-filtered satisfaction check. -/
theorem policy_satisfiedWithEffect_agrees (cp : Cst.Policy) (ap : Spec.Policy)
    (req : Request) (es : Entities) (eff : Effect)
    (htrans : cp.toPolicy? = some {ap with id := ""}) :
    (if Cst.satisfiedWithEffect eff cp req es then some ap.id else none)
      = Spec.satisfiedWithEffect eff ap req es := by
  obtain ⟨p⟩ := cp
  have htrans' := htrans
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at htrans'
  obtain ⟨e0, he0, ⟨ps, as, rs⟩, hsc, conds, hconds, heq⟩ := htrans'
  have heffeq : e0 = ap.effect := by
    have := congrArg Spec.Policy.effect heq; simpa using this
  have heff : CstCommon.Ident.toEffect? p.effect = some ap.effect := by
    rw [he0, heffeq]
  have hsat : Cst.satisfied (.policy p) req es = satisfied ap req es := by
    have h := policy_satisfied_agrees (.policy p) {ap with id := ""} req es htrans
    simpa [satisfied, Policy.toExpr] using h
  simp only [Cst.satisfiedWithEffect, Spec.satisfiedWithEffect, heff, hsat]
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
  have hforall := withIDs_toPolicies_forall₂ htrans
  -- The two filterMaps agree pointwise.
  simp only [Cst.satisfiedPolicies, satisfiedPolicies]
  congr 1
  apply filterMap_congr_forall₂ hforall
  intro a b hR
  obtain ⟨id, p⟩ := a
  obtain ⟨hid, htp⟩ := hR
  show (if Cst.satisfiedWithEffect eff p req es then some id else none)
      = Spec.satisfiedWithEffect eff b req es
  rw [show id = b.id from hid]
  exact policy_satisfiedWithEffect_agrees p b req es eff htp

theorem errorPolicies_agrees (cps : Cst.Policies) (aps : Spec.Policies)
  (req : Request) (es : Entities) :
  cps.toPolicies? = some aps →
  Cst.errorPolicies cps req es = errorPolicies aps req es := by
  intro htrans
  have hforall := withIDs_toPolicies_forall₂ htrans
  simp only [Cst.errorPolicies, errorPolicies]
  congr 1
  apply filterMap_congr_forall₂ hforall
  intro a b hR
  obtain ⟨id, p⟩ := a
  obtain ⟨hid, htp⟩ := hR
  show (if Cst.hasError p req es then some id else none) = errored b req es
  rw [show id = b.id from hid]
  exact policy_errored_agrees p b req es htp

theorem translation_is_sound (cps : Cst.Policies) (aps : Spec.Policies)
(req : Request) (es : Entities) :
  cps.toPolicies? = some aps →
  Cst.isAuthorized req es cps = Spec.isAuthorized req es aps := by
  intro htrans
  have hforbids := satisfiedPolicies_agrees cps aps req es .forbid htrans
  have hpermits := satisfiedPolicies_agrees cps aps req es .permit htrans
  have herrors := errorPolicies_agrees cps aps req es htrans
  simp [Cst.isAuthorized, isAuthorized]
  simp [hforbids, hpermits, herrors]

end Cedar.Thm

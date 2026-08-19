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
import Cedar.Frontend.Cst.ToAst
import Cedar.Thm.Frontend.Translation.AuxSound
import Cedar.Thm.Frontend.Translation.ExprTranslation
import Cedar.Thm.Frontend.Translation.PolicyToExpr
import Cedar.Thm.Frontend.Translation.CstErrorCollector
import Cedar.Thm.Frontend.CstSlice
import Cedar.Thm.Frontend.Authorizer
import Cedar.Thm.Frontend.Parser
import Cedar.Thm.Validation
namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Frontend
open Cedar.Validation


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
    simp only [Cst.extractScope?, bind, Option.bind_eq_some_iff] at hsc
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
    have hcondsMapM := conds_mapM_toAExpr_isSome (by simpa [Cst.toConditions?] using hconds)
    -- The append translates.
    obtain ⟨r, hr⟩ := mapM_append_isSome hvarsMapM hcondsMapM
    -- Conclude via `foldAnd_toAExpr`.
    exact ⟨_, foldAnd_toAExpr _ r hr⟩
  | [], hsc => simp [Cst.extractScope?] at hsc
  | [_], hsc => simp [Cst.extractScope?] at hsc
  | [_, _], hsc => simp [Cst.extractScope?] at hsc
  | _ :: _ :: _ :: _ :: _, hsc => simp [Cst.extractScope?] at hsc

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
    {req : Request} {es : Entities} (_htrans : cp.toPolicy? = some ap) :
    Cst.hasError cp req es =
      (match cp.toExpr.evaluate req es with | .ok _ => false | .error _ => true) := by
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

/-- **Strong completeness (headline).** If the comprehensive CST error collector
    reports no CST error for a policy set, then every policy translates to AST.
    Because the collector never short-circuits, a translation error can never be
    hidden behind a runtime error elsewhere. -/
theorem translation_is_strongly_complete (cps : Cst.Policies) (req : Request) (es : Entities) :
    noCstError (cps.collectErrors req es) →
    ∃ aps, cps.toPolicies? = some aps := by
  intro h
  unfold Cst.Policies.collectErrors at h
  unfold Cst.Policies.toPolicies?
  exact collectPolicies_complete cps.ps req es h

/-- Translating a sound CST policy slice yields a sound AST policy slice. -/
theorem cst_sound_slice_translates
    {req : Request} {entities : Entities} {slice policies : Cst.Policies}
    {sps aps : Spec.Policies}
    (hsound : Cst.IsSoundPolicySlice req entities slice policies)
    (hsps : slice.toPolicies? = some sps)
    (haps : policies.toPolicies? = some aps) :
    IsSoundPolicySlice req entities sps aps := by
  obtain ⟨hsub, hrest⟩ := hsound
  have hfs := toPolicies?_forall₂ hsps
  have hfp := toPolicies?_forall₂ haps
  refine ⟨?_, ?_⟩
  · intro ap hap
    obtain ⟨cp, hcp_mem, hcp⟩ := forall₂_exists_mem_right hfs hap
    obtain ⟨ap', hap'_mem, hr'⟩ := forall₂_exists_mem_left hfp (hsub hcp_mem)
    have : ap = ap' := by rw [hcp] at hr'; exact Option.some.inj hr'
    rw [this]; exact hap'_mem
  · intro ap hap_aps hap_not_sps
    obtain ⟨cp, hcp_mem_pol, hcp⟩ := forall₂_exists_mem_right hfp hap_aps
    have hcp_not_slice : cp ∉ slice.ps := by
      intro hcp_slice
      obtain ⟨ap'', hap''_mem, hr''⟩ := forall₂_exists_mem_left hfs hcp_slice
      have : ap = ap'' := by rw [hcp] at hr''; exact Option.some.inj hr''
      rw [this] at hap_not_sps
      exact hap_not_sps hap''_mem
    obtain ⟨hsat, herr⟩ := hrest cp hcp_mem_pol hcp_not_slice
    rw [← policy_satisfied_agrees cp ap req entities hcp,
        ← policy_hasError_agrees cp ap req entities hcp]
    exact ⟨hsat, herr⟩


/--
Scope analysis computed natively on a CST policy agrees with scope analysis
computed on the AST policy it translates to.
-/
theorem Cst.translation_preserves_scopeAnalysis
  {cp : Cst.Policy} {ap : Policy}
  (htrans : cp.toPolicy? = some ap) :
  ∃ h : (Cst.prVars? cp).isSome,
  Cst.scopeAnalysis cp h = Cedar.Slice.scopeAnalysis ap := by
  exists (policy_translation_success_prVars_isSome' htrans)
  apply translation_preserves_scopeAnalysis' htrans

/--
CST policy slicing soundness: `Cst.isAuthorized` produces the same result for a
sound slice (subset) of a collection of CST policies as it does for the original
policies.
-/
theorem Cst.isAuthorized_eq_for_sound_policy_slice
    (req : Request) (entities : Entities) (slice policies : Cst.Policies)
    (htrans : (policies.toPolicies?).isSome) :
    Cst.IsSoundPolicySlice req entities slice policies →
    Cst.isAuthorized req entities slice = Cst.isAuthorized req entities policies := by
  intro hsound
  obtain ⟨aps, haps⟩ := Option.isSome_iff_exists.mp htrans
  obtain ⟨sps, hsps⟩ := slice_toPolicies?_isSome hsound.1 haps
  have hast := cst_sound_slice_translates hsound hsps haps
  rw [translation_is_sound _ _ req entities hsps,
      _root_.Cedar.Thm.isAuthorized_eq_for_sound_policy_slice req entities sps aps hast,
      ← translation_is_sound _ _ req entities haps]

/--
A sound CST bound analysis produces sound CST policy slices.
-/
theorem Cst.sound_bound_analysis_produces_sound_slices
    (ba : Cst.BoundAnalysis) (request : Request) (entities : Entities)
    (policies : Cst.Policies)
    (htrans : (policies.toPolicies?).isSome) :
    Cst.IsSoundBoundAnalysis ba →
    ∃ (h : ∀ policy ∈ policies.ps, (Cst.prVars? policy).isSome),
    Cst.IsSoundPolicySlice request entities
      (Cst.BoundAnalysis.slice ba request entities policies h) policies := by
  intro hba
  have hwf := policies_translation_success_prVars_isSome htrans
  exists hwf
  refine ⟨cst_bound_slice_subset ba request entities policies hwf, ?_⟩
  intro policy hmem hnotin
  obtain ⟨hsat_imp, herr_imp⟩ := hba policy (hwf policy hmem)
    (policy_toPolicy?_isSome_of_mem htrans hmem) request entities
  exact ⟨
    fun hsat => hnotin (cst_bound_slice_kept ba request entities policies hwf hmem (hsat_imp hsat)),
    fun herr => hnotin (cst_bound_slice_kept ba request entities policies hwf hmem (herr_imp herr))⟩

/--
CST scope-based bounds are sound.
-/
theorem Cst.scope_bound_is_sound (policy : Cst.Policy)
    (htrans : (policy.toPolicy?).isSome) :
    ∃ h : (Cst.prVars? policy).isSome,
    Cst.IsSoundPolicyBound (Cst.scopeAnalysis policy h) policy := by
  obtain ⟨ap, hap⟩ := Option.isSome_iff_exists.mp htrans
  exists (policy_translation_success_prVars_isSome' hap)
  intro req es
  have hscope := translation_preserves_scopeAnalysis' hap (policy_translation_success_prVars_isSome' hap)
  have hsat := policy_satisfied_agrees policy ap req es hap
  have herr := policy_hasError_agrees policy ap req es hap
  rw [hscope, hsat, herr]
  exact _root_.Cedar.Thm.scope_bound_is_sound ap req es

/--
CST scope-based bound analysis is sound.
-/
theorem Cst.scope_analysis_is_sound :
    Cst.IsSoundBoundAnalysis Cst.scopeAnalysis := by
  intro policy _ hpt
  obtain ⟨_, hsound⟩ := Cst.scope_bound_is_sound policy hpt
  exact hsound

/--
CST scope-based slicing is sound: `Cst.isAuthorized` produces the same result for
a scope-based slice of a collection of CST policies as it does for the original
policies.
-/
theorem Cst.isAuthorized_eq_for_scope_based_policy_slice
    (request : Request) (entities : Entities) (policies : Cst.Policies)
    (htrans : (policies.toPolicies?).isSome) :
    ∃ (hwf : ∀ policy ∈ policies.ps, (Cst.prVars? policy).isSome),
    Cst.isAuthorized request entities
      (Cst.BoundAnalysis.slice Cst.scopeAnalysis request entities policies hwf) =
    Cst.isAuthorized request entities policies := by
  exists (policies_translation_success_prVars_isSome htrans)
  obtain ⟨aps, htrans'⟩ := Option.isSome_iff_exists.mp htrans
  have hslice := cst_slice_chooses_same_policies' request entities htrans'
    (policies_translation_success_prVars_isSome htrans)
  rw [translation_is_sound _ _ request entities hslice,
      _root_.Cedar.Thm.isAuthorized_eq_for_scope_based_policy_slice request entities aps,
      ← translation_is_sound _ _ request entities htrans']


/-- If a translated CST expression is well-typed, evaluating the CST expression
never throws a `typeError`. -/
theorem validated_no_type_error
    {cst : Cst.Expr} {ast : Spec.Expr} {c₁ c₂ : Capabilities} {ty : TypedExpr}
    {env : TypeEnv} {request : Request} {entities : Entities}
    (htrans : cst.toAExpr? = some ast)
    (hcap : CapabilitiesInvariant c₁ request entities)
    (hwf : InstanceOfWellFormedEnvironment request entities env)
    (hwt : typeOf ast c₁ env = .ok (ty, c₂)) :
    cst.evaluate request entities ≠ .error .typeError := by
  intro hcontra
  obtain ⟨_, v, hev, _⟩ := type_of_is_sound hcap hwf hwt
  have hast : evaluate ast request entities = .error .typeError := by
    rw [expr_to_expr_sound htrans, hcontra]
  simp [EvaluatesTo, hast] at hev

/--
**CST validation soundness (policy-set level).** The CST counterpart of
`validation_is_sound`: if a set of CST policies translates to a set of AST
policies that is validated with respect to the schema, and the request
and entities are consistent with the schema, then evaluating each CST policy's
expression never throws a `typeError`. -/
theorem cst_validation_is_sound (cps : Cst.Policies) (aps : Policies)
    (schema : Schema) (request : Request) (entities : Entities) :
    cps.toPolicies? = some aps →
    schema.validateWellFormed = .ok () →
    validate aps schema = .ok () →
    validateRequest schema request = .ok () →
    validateEntities schema entities = .ok () →
    ∀ cp ∈ cps.ps, cp.toExpr.evaluate request entities ≠ .error .typeError := by
  intro htrans hwf hval hreq hent cp hcp
  have hbool := validation_is_sound aps schema request entities hwf hval hreq hent
  obtain ⟨ap, hap_mem, hcp_ap⟩ :=
    List.forall₂_implies_all_left (toPolicies?_forall₂ htrans) cp hcp
  obtain ⟨_, hev⟩ := hbool ap hap_mem
  obtain ⟨ae, hae⟩ := toPolicy?_implies_toAExpr? hcp_ap
  have h1 : evaluate ae request entities = cp.toExpr.evaluate request entities :=
    expr_to_expr_sound hae
  have h2 : evaluate ae request entities = evaluate ap.toExpr request entities :=
    policy_to_expr_sound cp ap cp.toExpr ae request entities hcp_ap rfl hae
  intro hcontra
  have hap_te : evaluate ap.toExpr request entities = .error .typeError := by
    rw [← h2, h1]; exact hcontra
  simp [EvaluatesTo, hap_te] at hev

end Cedar.Thm

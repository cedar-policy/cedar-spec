import Cedar.Slice.PolicySlice
import Cedar.Slice.CstPolicySlice
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Translation.Aux

namespace Cedar.Thm
open Cedar.Spec Cedar.Slice Cedar.Slice.Cst Cedar.Data

/-- `toPRScope?` succeeding implies the variable's bound is interpretable. -/
private theorem varBoundWF_of_toPRScope? {v : Cst.VariableDef} (h : (v.toPRScope?).isSome) :
    varBoundWF v = true := by
  cases hineq : v.ineq with
  | none =>
    cases het : v.entityType with
    | none => simp [varBoundWF, hineq, het]
    | some t => simp [varBoundWF, hineq, het]
  | some opE =>
    obtain ⟨op, e⟩ := opE
    cases het : v.entityType with
    | none =>
      cases op with
      | rEq =>
        simp only [Cst.VariableDef.toPRScope?, hineq, het] at h
        cases hu : e.toEntityUID? with
        | none => rw [hu] at h; simp at h
        | some x => simp [varBoundWF, hineq, het, hu]
      | rIn =>
        simp only [Cst.VariableDef.toPRScope?, hineq, het] at h
        cases hu : e.toEntityUID? with
        | none => rw [hu] at h; simp at h
        | some x => simp [varBoundWF, hineq, het, hu]
      | rLess | rLessEq | rGreater | rGreaterEq | rNotEq =>
        simp [Cst.VariableDef.toPRScope?, hineq, het] at h
    | some t =>
      cases op with
      | rIn =>
        simp only [Cst.VariableDef.toPRScope?, hineq, het] at h
        cases hu : e.toEntityUID? with
        | none => rw [hu] at h; simp at h
        | some x => simp [varBoundWF, hineq, het, hu]
      | rEq | rLess | rLessEq | rGreater | rGreaterEq | rNotEq =>
        simp [Cst.VariableDef.toPRScope?, hineq, het] at h

private theorem toPrincipalScope?_inv {v : Cst.VariableDef} {ps : PrincipalScope}
    (h : v.toPrincipalScope? = some ps) : v.var = .idPrincipal ∧ (v.toPRScope?).isSome := by
  unfold Cst.VariableDef.toPrincipalScope? at h
  split at h
  · rename_i hvar
    refine ⟨hvar, ?_⟩
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨scope, hscope, _⟩ := h
    rw [hscope]; rfl
  · simp at h

private theorem toResourceScope?_inv {v : Cst.VariableDef} {rs : ResourceScope}
    (h : v.toResourceScope? = some rs) : v.var = .idResource ∧ (v.toPRScope?).isSome := by
  unfold Cst.VariableDef.toResourceScope? at h
  split at h
  · rename_i hvar
    refine ⟨hvar, ?_⟩
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨scope, hscope, _⟩ := h
    rw [hscope]; rfl
  · simp at h

private theorem toActionScope?_var {v : Cst.VariableDef} {as : ActionScope}
    (h : v.toActionScope? = some as) : v.var = .idAction := by
  cases hvar : v.var <;>
    simp_all [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?,
      bind, Option.bind_eq_some_iff]

-- When the policy translation is successful, the three scopes can be extracted
theorem policy_translation_success_prVars_isSome
  {cp : Cst.Policy} :
  (cp.toPolicy?).isSome →
  (prVars? cp).isSome := by
  intro htrans
  obtain ⟨ap, hap⟩ := Option.isSome_iff_exists.mp htrans
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hap
  obtain ⟨eff, heff, ⟨ps, as, rs⟩, hsc, conds, hconds, _⟩ := hap
  match hvars : p.vars, hsc with
  | [a, b, c], hsc =>
    simp only [extractScope?, bind, Option.bind_eq_some_iff] at hsc
    obtain ⟨ps', hps, as', has, rs', hrs, _⟩ := hsc
    have ⟨hpvar, hppr⟩ := toPrincipalScope?_inv hps
    have hbvar := toActionScope?_var has
    have ⟨hrvar, hrpr⟩ := toResourceScope?_inv hrs
    have hwfa := varBoundWF_of_toPRScope? hppr
    have hwfc := varBoundWF_of_toPRScope? hrpr
    simp [prVars?, hvars, hpvar, hbvar, hrvar, hwfa, hwfc]
  | [], hsc => simp [extractScope?] at hsc
  | [_], hsc => simp [extractScope?] at hsc
  | [_, _], hsc => simp [extractScope?] at hsc
  | _ :: _ :: _ :: _ :: _, hsc => simp [extractScope?] at hsc

theorem policy_translation_success_prVars_isSome'
  {cp : Cst.Policy} {ap : Policy} :
  cp.toPolicy? = some ap →
  (prVars? cp).isSome := by
  intro htrans
  have h : (cp.toPolicy?).isSome := by
    rw [Option.isSome_iff_exists]; exists ap
  apply (policy_translation_success_prVars_isSome h)

-- When the policies translation is successful, the three scopes can be extracted
theorem policies_translation_success_prVars_isSome
  {cps : Cst.Policies} :
  (cps.toPolicies?).isSome →
  ∀ cp ∈ cps.ps, (prVars? cp).isSome := by
  intro htrans
  obtain ⟨ps⟩ := cps
  simp [Cst.Policies.toPolicies?] at htrans
  have hmapM := Option.isSome_of_isSome_bind htrans
  rw [Option.isSome_iff_exists] at hmapM
  obtain ⟨aps, hmap⟩ := hmapM
  have hall := List.mapM_some_implies_all_some hmap
  intro cp hcp; simp at hcp
  apply policy_translation_success_prVars_isSome
  rw [Option.isSome_iff_exists]
  obtain ⟨ap, hap1, hap2⟩ := (hall cp hcp)
  exists ap

theorem policies_translation_success_prVars_isSome'
  {cps : Cst.Policies} {aps : Policies} :
  cps.toPolicies? = aps →
  ∀ cp ∈ cps.ps, (prVars? cp).isSome := by
  intro htrans
  have h : (cps.toPolicies?).isSome := by
    rw [Option.isSome_iff_exists]; exists aps
  apply (policies_translation_success_prVars_isSome h)

/-- The CST-native `varBound?` agrees with the AST `Scope.bound` of the scope the
    variable translates to. -/
private theorem varBound?_eq_scope_bound {v : Cst.VariableDef} {scope : Scope}
    (h : v.toPRScope? = some scope) : varBound? v = scope.bound := by
  cases hineq : v.ineq with
  | none =>
    cases het : v.entityType with
    | none =>
      simp only [Cst.VariableDef.toPRScope?, hineq, het, Option.some.injEq] at h
      subst h; simp [varBound?, hineq, het, Scope.bound]
    | some t =>
      simp only [Cst.VariableDef.toPRScope?, hineq, het, bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨ety, _, hsc⟩ := h; subst hsc
      simp [varBound?, hineq, het, Scope.bound]
  | some opE =>
    obtain ⟨op, e⟩ := opE
    cases het : v.entityType with
    | none =>
      cases op with
      | rEq =>
        simp only [Cst.VariableDef.toPRScope?, hineq, het, bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨eref, hu, hsc⟩ := h; subst hsc
        simp [varBound?, hineq, het, Scope.bound, hu]
      | rIn =>
        simp only [Cst.VariableDef.toPRScope?, hineq, het, bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨eref, hu, hsc⟩ := h; subst hsc
        simp [varBound?, hineq, het, Scope.bound, hu]
      | rLess | rLessEq | rGreater | rGreaterEq | rNotEq =>
        simp [Cst.VariableDef.toPRScope?, hineq, het] at h
    | some t =>
      cases op with
      | rIn =>
        simp only [Cst.VariableDef.toPRScope?, hineq, het, bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        obtain ⟨eref, hu, ety, _, hsc⟩ := h; subst hsc
        simp [varBound?, hineq, het, Scope.bound, hu]
      | rEq | rLess | rLessEq | rGreater | rGreaterEq | rNotEq =>
        simp [Cst.VariableDef.toPRScope?, hineq, het] at h

private theorem toPrincipalScope?_some {v : Cst.VariableDef} {ps : PrincipalScope}
    (h : v.toPrincipalScope? = some ps) :
    ∃ scope, v.toPRScope? = some scope ∧ ps = .principalScope scope := by
  unfold Cst.VariableDef.toPrincipalScope? at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨scope, hscope, hps⟩ := h
    exact ⟨scope, hscope, hps.symm⟩
  · simp at h

private theorem toResourceScope?_some {v : Cst.VariableDef} {rs : ResourceScope}
    (h : v.toResourceScope? = some rs) :
    ∃ scope, v.toPRScope? = some scope ∧ rs = .resourceScope scope := by
  unfold Cst.VariableDef.toResourceScope? at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨scope, hscope, hrs⟩ := h
    exact ⟨scope, hscope, hrs.symm⟩
  · simp at h

theorem translation_preserves_scopeAnalysis
  {cp : Cst.Policy} {ap : Policy}
  (htrans : cp.toPolicy? = some ap)
  (h : (prVars? cp).isSome) : -- redundant, but provides flexibility in future uses
  Cst.scopeAnalysis cp h = scopeAnalysis ap := by
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at htrans
  obtain ⟨eff, heff, ⟨ps, as, rs⟩, hsc, conds, hconds, hap⟩ := htrans
  match hvars : p.vars, hsc with
  | [a, b, c], hsc =>
    simp only [extractScope?, bind, Option.bind_eq_some_iff] at hsc
    obtain ⟨ps', hps, as', has, rs', hrs, hsceq⟩ := hsc
    obtain ⟨scope_p, hppr, hpseq⟩ := toPrincipalScope?_some hps
    have hbvar := toActionScope?_var has
    obtain ⟨scope_r, hrpr, hrseq⟩ := toResourceScope?_some hrs
    have ⟨hpvar, hpprS⟩ := toPrincipalScope?_inv hps
    have ⟨hrvar, hrprS⟩ := toResourceScope?_inv hrs
    have hwfa := varBoundWF_of_toPRScope? hpprS
    have hwfc := varBoundWF_of_toPRScope? hrprS
    have hpr : prVars? (Cst.Policy.policy p) = some (a, c) := by
      simp [prVars?, hvars, hpvar, hbvar, hrvar, hwfa, hwfc]
    have hba := varBound?_eq_scope_bound hppr
    have hbc := varBound?_eq_scope_bound hrpr
    simp only [Option.some.injEq, Prod.mk.injEq] at hsceq
    obtain ⟨hpe, _, hre⟩ := hsceq
    subst hpe; subst hre; subst hap
    have hget : (prVars? (Cst.Policy.policy p)).get h = (a, c) := Option.get_of_eq_some h hpr
    unfold Cedar.Slice.Cst.scopeAnalysis Cedar.Slice.scopeAnalysis
    simp only [hget, hpseq, hrseq, PrincipalScope.scope, ResourceScope.scope, hba, hbc]
  | [], hsc => simp [extractScope?] at hsc
  | [_], hsc => simp [extractScope?] at hsc
  | [_, _], hsc => simp [extractScope?] at hsc
  | _ :: _ :: _ :: _ :: _, hsc => simp [extractScope?] at hsc


/-- `scopeAnalysis` ignores the policy id. -/
theorem scopeAnalysis_id_indep (ap : Policy) (x : PolicyID) :
    Cedar.Slice.scopeAnalysis { ap with id := x } = Cedar.Slice.scopeAnalysis ap := rfl

/-- `Forall₂` is preserved by `filterMap` when, on related inputs, the two functions
    are both `none` or both `some` with related results. -/
theorem forall₂_filterMap_rel {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → Option γ} {g : β → Option δ} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys)
    (hfg : ∀ a b, R a b →
      (f a = none ∧ g b = none) ∨ (∃ c d, f a = some c ∧ g b = some d ∧ S c d)) :
    List.Forall₂ S (xs.filterMap f) (ys.filterMap g) := by
  induction h with
  | nil => simp
  | @cons a b l₁ l₂ hab _ ih =>
    rcases hfg a b hab with ⟨hfa, hgb⟩ | ⟨c, d, hfa, hgb, hsd⟩
    · simp only [List.filterMap_cons, hfa, hgb]; exact ih
    · simp only [List.filterMap_cons, hfa, hgb]; exact List.Forall₂.cons hsd ih

/-- Index-generalized base correspondence between CST policies and their stamped
    AST translations. The relation erases the id, so the mapIdx offset is irrelevant. -/
private theorem cps_ps_forall₂_aux :
    ∀ (k : Nat) (ps : List Cst.Policy) (rets : List Policy),
      ps.mapM Cst.Policy.toPolicy? = some rets →
      List.Forall₂ (fun cp ap => cp.toPolicy? = some { ap with id := "" })
        ps (rets.mapIdx (fun i p => { p with id := s!"policy{k+i}" })) := by
  intro k ps
  induction ps generalizing k with
  | nil =>
    intro rets h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons hd tl ih =>
    intro rets h
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r0, hr0, restRets, hrest, hretseq⟩ := h
    subst hretseq
    rw [List.mapIdx_cons]
    apply List.Forall₂.cons
    · rw [hr0]
      have hid := toPolicy?_id_empty hr0
      obtain ⟨id, e, pp, aa, rr, cc⟩ := r0
      subst hid; rfl
    · have hfun : (fun (i : Nat) (p : Policy) => ({p with id := s!"policy{k + (i + 1)}"} : Policy))
                = (fun i p => {p with id := s!"policy{(k + 1) + i}"}) := by
        funext i p
        have : k + (i + 1) = (k + 1) + i := by omega
        rw [this]
      rw [hfun]
      exact ih (k + 1) restRets hrest

/-- The base correspondence: each CST policy in the store translates to the
    corresponding AST policy (modulo the id field). -/
theorem cps_ps_forall₂ {cps : Cst.Policies} {aps : Policies}
    (htrans : cps.toPolicies? = some aps) :
    List.Forall₂ (fun cp ap => cp.toPolicy? = some { ap with id := "" }) cps.ps aps := by
  simp only [Cst.Policies.toPolicies?, bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
  obtain ⟨rets, hrets, hapeq⟩ := htrans
  subst hapeq
  have h := cps_ps_forall₂_aux 0 cps.ps rets hrets
  have hfun : (fun (i : Nat) (p : Policy) => ({p with id := s!"policy{0 + i}"} : Policy))
            = (fun i p => {p with id := s!"policy{i}"}) := by
    funext i p
    have : 0 + i = i := by omega
    rw [this]
  rwa [hfun] at h

/-- Push a left `map` through `Forall₂`. -/
theorem forall₂_map_left {α α' β : Type} {f : α → α'} {R : α' → β → Prop}
    {xs : List α} {ys : List β} :
    List.Forall₂ R (xs.map f) ys ↔ List.Forall₂ (fun a b => R (f a) b) xs ys := by
  constructor
  · induction xs generalizing ys with
    | nil => intro h; cases h; exact List.Forall₂.nil
    | cons a xs' ih =>
      intro h
      simp only [List.map_cons] at h
      cases h with
      | cons hab htl => exact List.Forall₂.cons hab (ih htl)
  · intro h
    induction h with
    | nil => simp
    | @cons a b l₁ l₂ hab _ ih => simp only [List.map_cons]; exact List.Forall₂.cons hab ih

theorem cst_slice_chooses_same_policies
  {cps : Cst.Policies} {aps : Policies} {req : Request} {es : Entities}
  (htrans : cps.toPolicies? = some aps)
  (hwf : ∀ cp ∈ cps.ps, (prVars? cp).isSome) :
  List.Forall₂
    (fun cp ap => cp.toPolicy? = some { ap with id := "" })
    (Cedar.Slice.Cst.BoundAnalysis.slice Cedar.Slice.Cst.scopeAnalysis req es cps hwf).ps
    (Cedar.Slice.BoundAnalysis.slice Cedar.Slice.scopeAnalysis req es aps) := by
  -- lift the base correspondence to the attached list
  have hattach : List.Forall₂
      (fun (x : {x // x ∈ cps.ps}) ap => x.1.toPolicy? = some { ap with id := "" })
      cps.ps.attach aps := by
    have h' : List.Forall₂ (fun cp ap => cp.toPolicy? = some { ap with id := "" })
        (cps.ps.attach.map Subtype.val) aps := by
      rw [List.attach_map_subtype_val]; exact cps_ps_forall₂ htrans
    exact forall₂_map_left.mp h'
  -- unfold both slices into `filterMap`s
  simp only [Cedar.Slice.Cst.BoundAnalysis.slice, Cedar.Slice.BoundAnalysis.slice]
  rw [← List.filterMap_eq_filter]
  apply forall₂_filterMap_rel hattach
  intro x ap hR
  obtain ⟨cp, hmem⟩ := x
  simp only at hR
  have hpres := translation_preserves_scopeAnalysis hR (hwf cp hmem)
  rw [scopeAnalysis_id_indep] at hpres
  by_cases hb : satisfiedBound (Cedar.Slice.scopeAnalysis ap) req es = true
  · right
    exact ⟨cp, ap, by simp [hpres, hb], by simp [Option.guard, hb], hR⟩
  · left
    simp only [Bool.not_eq_true] at hb
    exact ⟨by simp [hpres, hb], by simp [Option.guard, hb]⟩

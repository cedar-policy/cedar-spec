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

import Cedar.Slice.PolicySlice
import Cedar.Frontend.Cst.Slice
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Frontend.Translation.AuxSound
import Cedar.Thm.PolicySlice

namespace Cedar.Thm
open Cedar.Spec Cedar.Slice Cedar.Data
open Cedar.Frontend
open Cedar.Frontend.Cst hiding Expr ExprImpl ExprData OrExpr AndExpr AddExpr MultExpr Name Policy PolicyImpl Policies Ident Literal Primary Member MemAccess Unary Relation RelOp Cond VariableDef Ref RecInit Str



/-!
Key theorems in this file:

* `policy_translation_success_prVars_isSome`: Whenever a CST policy successfully
  translates to the AST, its principal/resource scope variables can be extracted
  via `prVars?` (i.e. `prVars?` is `isSome`). This well-formedness fact is the
  precondition required to run scope analysis on the CST. (The policy-store level
  variant `policies_translation_success_prVars_isSome` lives in
  `Cedar/Thm/Frontend/PolicySlice.lean`.)

* `translation_preserves_scopeAnalysis'`: Scope analysis computed natively on a CST
  policy (`Cst.scopeAnalysis`) agrees with scope analysis computed on the AST policy
  it translates to (`scopeAnalysis`). (The packaged form
  `translation_preserves_scopeAnalysis` lives in `Cedar/Thm/PolicySlice.lean`.)

* `cst_slice_chooses_same_policies`: Lifting the previous result to whole policy
  stores, the CST slice and the AST slice select corresponding policies in lockstep.

* `cst_slice_is_sound`: The headline result. Authorizing a request against the CST
  slice produces the same decision as authorizing against the full CST policy store, so slicing on the CST is decision-preserving.
-/

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

private theorem toActionScope?_var {v : Cst.VariableDef} {acts : ActionScope}
    (h : v.toActionScope? = some acts) : v.var = .idAction := by
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
  obtain ⟨eff, heff, ⟨ps, acts, rs⟩, hsc, conds, hconds, _⟩ := hap
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
  simp only [Cst.Policies.toPolicies?] at htrans
  rw [Option.isSome_iff_exists] at htrans
  obtain ⟨aps, hmap⟩ := htrans
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

theorem translation_preserves_scopeAnalysis'
  {cp : Cst.Policy} {ap : Policy}
  (htrans : cp.toPolicy? = some ap)
  (h : (prVars? cp).isSome) : -- redundant, but provides flexibility in future uses
  Cst.scopeAnalysis cp h = scopeAnalysis ap := by
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at htrans
  obtain ⟨eff, heff, ⟨ps, acts, rs⟩, hsc, conds, hconds, hap⟩ := htrans
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
    unfold Cst.scopeAnalysis Cedar.Slice.scopeAnalysis
    simp only [hget, hpseq, hrseq, PrincipalScope.scope, ResourceScope.scope, hba, hbc]
  | [], hsc => simp [extractScope?] at hsc
  | [_], hsc => simp [extractScope?] at hsc
  | [_, _], hsc => simp [extractScope?] at hsc
  | _ :: _ :: _ :: _ :: _, hsc => simp [extractScope?] at hsc

def Cst.IsSoundPolicySlice (req : Request) (entities : Entities) (slice policies : Cst.Policies) : Prop :=
  slice.ps ⊆ policies.ps ∧
  ∀ policy ∈ policies.ps,
    policy ∉ slice.ps →
    ¬ Cst.satisfied policy req entities ∧ ¬ Cst.hasError policy req entities

theorem Cst.sound_slice_transitive :
  Cst.IsSoundPolicySlice r es slice₁ ps →
  Cst.IsSoundPolicySlice r es slice₂ slice₁ →
  Cst.IsSoundPolicySlice r es slice₂ ps := by
  intro ⟨h_slice₁_sub, h_slice₁_sound⟩ ⟨h_slice₂_sub, h_slice₂_sound⟩
  constructor
  · exact List.Subset.trans h_slice₂_sub h_slice₁_sub
  · intro p h_mem_ps h_mem_slice₂
    by_cases h_mem_slice₁ : p ∈ slice₁.ps
    case pos =>
      exact h_slice₂_sound p h_mem_slice₁ h_mem_slice₂
    case neg =>
      exact h_slice₁_sound p h_mem_ps h_mem_slice₁

def Cst.IsSoundPolicyBound (bound : PolicyBound) (policy : Cst.Policy) : Prop :=
  ∀ (req : Request) (entities : Entities),
  (Cst.satisfied policy req entities → satisfiedBound bound req entities) ∧
  (Cst.hasError policy req entities → satisfiedBound bound req entities)

def Cst.IsSoundBoundAnalysis (ba : Cst.BoundAnalysis) : Prop :=
  ∀ (policy : Cst.Policy) (h : (prVars? policy).isSome),
    (policy.toPolicy?).isSome → Cst.IsSoundPolicyBound (ba policy h) policy

/-- `mapM`-cons helper specialised to `toPolicy?`. -/
private theorem mapM_toPolicy?_cons {hd : Cst.Policy} {ap : Spec.Policy}
    {tl : List Cst.Policy} {r : List Spec.Policy}
    (h1 : hd.toPolicy? = some ap) (h2 : tl.mapM Cst.Policy.toPolicy? = some r) :
    (hd :: tl).mapM Cst.Policy.toPolicy? = some (ap :: r) := by
  simp [List.mapM_cons, h1, h2]

/-- Core list-level commutation: scope-based slicing on a list of CST policies,
    followed by translation, yields the scope-based slice of the translated AST
    policies.  Proven by induction on the translation `Forall₂`, using
    `translation_preserves_scopeAnalysis'` (so the CST and AST `satisfiedBound`
    predicates agree on corresponding policies). -/
private theorem scope_slice_translate
    (req : Request) (entities : Entities) :
    ∀ (cps : List Cst.Policy) (aps : List Spec.Policy)
      (hwf : ∀ policy ∈ cps, (prVars? policy).isSome),
      List.Forall₂ (fun cp ap => cp.toPolicy? = some ap) cps aps →
      (cps.attach.filterMap (fun x =>
          if satisfiedBound (Cst.scopeAnalysis x.1 (hwf x.1 x.2)) req entities
          then some x.1 else none)).mapM Cst.Policy.toPolicy?
        = some (aps.filter (fun ap => satisfiedBound (Cedar.Slice.scopeAnalysis ap) req entities)) := by
  intro cps
  induction cps with
  | nil =>
    intro aps _ hforall
    cases hforall
    simp
  | cons hd tl ih =>
    intro aps hwf hforall
    cases hforall with
    | cons hhd htl =>
      rename_i ap aps'
      have ihtl := ih aps' (fun p hp => hwf p (List.mem_cons_of_mem hd hp)) htl
      have hsc : Cst.scopeAnalysis hd (hwf hd List.mem_cons_self)
               = Cedar.Slice.scopeAnalysis ap :=
        translation_preserves_scopeAnalysis' hhd (hwf hd List.mem_cons_self)
      cases hb : satisfiedBound (Cedar.Slice.scopeAnalysis ap) req entities
      · have hF : (fun x : {x // x ∈ hd :: tl} =>
            if satisfiedBound (Cst.scopeAnalysis x.1 (hwf x.1 x.2)) req entities
            then some x.1 else none) ⟨hd, List.mem_cons_self⟩ = none := by
          simp [hsc, hb]
        rw [List.attach_cons,
          List.filterMap_cons_none (f := fun x : {x // x ∈ hd :: tl} =>
            if satisfiedBound (Cst.scopeAnalysis x.1 (hwf x.1 x.2)) req entities
            then some x.1 else none) hF,
          List.filterMap_map, List.filter_cons]
        simp only [hb, Bool.false_eq_true, if_false]
        exact ihtl
      · have hF : (fun x : {x // x ∈ hd :: tl} =>
            if satisfiedBound (Cst.scopeAnalysis x.1 (hwf x.1 x.2)) req entities
            then some x.1 else none) ⟨hd, List.mem_cons_self⟩ = some hd := by
          simp [hsc, hb]
        rw [List.attach_cons,
          List.filterMap_cons_some (f := fun x : {x // x ∈ hd :: tl} =>
            if satisfiedBound (Cst.scopeAnalysis x.1 (hwf x.1 x.2)) req entities
            then some x.1 else none) hF,
          List.filterMap_map, List.filter_cons]
        simp only [hb, if_true]
        exact mapM_toPolicy?_cons hhd ihtl

/-- The CST scope-based slice and the AST scope-based slice choose the same
    policies: translating the CST slice yields exactly the AST slice of the
    translated policy store. -/
theorem cst_slice_chooses_same_policies'
    {cps : Cst.Policies} {aps : Spec.Policies}
    (req : Request) (entities : Entities)
    (htrans : cps.toPolicies? = some aps)
    (hwf : ∀ policy ∈ cps.ps, (prVars? policy).isSome) :
    (Cst.BoundAnalysis.slice Cst.scopeAnalysis req entities cps hwf).toPolicies?
      = some (Cedar.Slice.BoundAnalysis.slice Cedar.Slice.scopeAnalysis req entities aps) := by
  have hforall := toPolicies?_forall₂ htrans
  simp only [Cst.BoundAnalysis.slice, Cst.Policies.toPolicies?,
    Cedar.Slice.BoundAnalysis.slice]
  exact scope_slice_translate req entities cps.ps aps hwf hforall

theorem cst_slice_chooses_same_policies
  {cps : Cst.Policies} {aps : Spec.Policies}
  (req : Request) (entities : Entities)
  (htrans : cps.toPolicies? = some aps) :
    ∃ hwf : ∀ policy ∈ cps.ps, (prVars? policy).isSome,
    (Cst.BoundAnalysis.slice Cst.scopeAnalysis req entities cps hwf).toPolicies?
    = some (Cedar.Slice.BoundAnalysis.slice Cedar.Slice.scopeAnalysis req entities aps) := by
  have h := policies_translation_success_prVars_isSome' htrans
  exists h
  apply (cst_slice_chooses_same_policies' req entities htrans)


/-- From `Forall₂ R xs ys` and `y ∈ ys`, recover a related `x ∈ xs`. -/
public theorem forall₂_exists_mem_right {α β : Type _} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : ∀ {y}, y ∈ ys → ∃ x ∈ xs, R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | @cons x y' xs' ys' hr _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with heq | hmem
    · subst heq; exact ⟨x, List.mem_cons_self, hr⟩
    · obtain ⟨x', hx'mem, hx'r⟩ := ih hmem
      exact ⟨x', List.mem_cons_of_mem _ hx'mem, hx'r⟩

/-- From `Forall₂ R xs ys` and `x ∈ xs`, recover a related `y ∈ ys`. -/
public theorem forall₂_exists_mem_left {α β : Type _} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y := by
  induction h with
  | nil => intro x hx; simp at hx
  | @cons x' y' xs' ys' hr _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with heq | hmem
    · subst heq; exact ⟨y', List.mem_cons_self, hr⟩
    · obtain ⟨y'', hy''mem, hy''r⟩ := ih hmem
      exact ⟨y'', List.mem_cons_of_mem _ hy''mem, hy''r⟩

/-- If every element of `xs` maps to `some`, then `mapM` succeeds. -/
private theorem mapM_some_of_all_isSome {α β : Type _} {f : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, (f x).isSome) → ∃ ys, xs.mapM f = some ys := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[], by simp⟩
  | cons hd tl ih =>
    intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h hd List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]⟩

/-- A subset of a translating policy store also translates. -/
theorem slice_toPolicies?_isSome {slice policies : Cst.Policies} {aps : Spec.Policies}
    (hsub : slice.ps ⊆ policies.ps) (haps : policies.toPolicies? = some aps) :
    ∃ sps, slice.toPolicies? = some sps := by
  have hfp := toPolicies?_forall₂ haps
  simp only [Cst.Policies.toPolicies?]
  apply mapM_some_of_all_isSome
  intro cp hcp
  obtain ⟨ap, _, hr⟩ := forall₂_exists_mem_left hfp (hsub hcp)
  rw [Option.isSome_iff_exists]; exact ⟨ap, hr⟩



/-- Every policy kept by the CST bound-analysis slice is a member of the
    original policy store. -/
theorem cst_bound_slice_subset (ba : Cst.BoundAnalysis) (request : Request)
    (entities : Entities) (policies : Cst.Policies)
    (hwf : ∀ policy ∈ policies.ps, (prVars? policy).isSome) :
    (Cst.BoundAnalysis.slice ba request entities policies hwf).ps ⊆ policies.ps := by
  intro x hx
  simp only [Cst.BoundAnalysis.slice, List.mem_filterMap] at hx
  obtain ⟨⟨a, ha⟩, _, hF⟩ := hx
  split at hF
  · injection hF with h; exact h ▸ ha
  · contradiction

/-- If a policy's bound is satisfied, it is kept by the CST bound-analysis slice. -/
theorem cst_bound_slice_kept (ba : Cst.BoundAnalysis) (request : Request)
    (entities : Entities) (policies : Cst.Policies)
    (hwf : ∀ policy ∈ policies.ps, (prVars? policy).isSome)
    {policy : Cst.Policy} (hmem : policy ∈ policies.ps)
    (hsat : satisfiedBound (ba policy (hwf policy hmem)) request entities) :
    policy ∈ (Cst.BoundAnalysis.slice ba request entities policies hwf).ps := by
  simp only [Cst.BoundAnalysis.slice, List.mem_filterMap]
  exact ⟨⟨policy, hmem⟩, List.mem_attach _ _, by simp [hsat]⟩


/-- A policy belonging to a store that translates also translates. -/
theorem policy_toPolicy?_isSome_of_mem {policies : Cst.Policies} {policy : Cst.Policy}
    (htrans : (policies.toPolicies?).isSome) (hmem : policy ∈ policies.ps) :
    (policy.toPolicy?).isSome := by
  obtain ⟨aps, haps⟩ := Option.isSome_iff_exists.mp htrans
  obtain ⟨ap, _, hr⟩ := forall₂_exists_mem_left (toPolicies?_forall₂ haps) hmem
  rw [Option.isSome_iff_exists]; exact ⟨ap, hr⟩

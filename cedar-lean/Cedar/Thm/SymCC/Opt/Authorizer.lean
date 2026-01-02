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

import Cedar.SymCC.Authorizer
import Cedar.SymCC.Enforcer
import Cedar.SymCCOpt.Authorizer
import Cedar.Thm.SymCC.Data.LT
import Cedar.Thm.SymCC.Enforcer
import Cedar.Thm.SymCC.Opt.Compiler

namespace Cedar.Thm

open Cedar Spec SymCC

/--
Correctness theorem for `Opt.compileWithEffect`:

`Opt.compileWithEffect` produces the same `term` as `SymCC.compileWithEffect`, and
`Opt.compileWithEffect` produces the same `footprint` as `footprint`
-/
theorem Opt.compileWithEffect.correctness (effect : Effect) (p : Policy) (εnv : SymEnv) :
  Opt.compileWithEffect effect p εnv = (do
    let term ← SymCC.compileWithEffect effect p εnv
    let footprint := footprint p.toExpr εnv
    .ok $ term.map λ term => { term, footprint }
  )
:= by
  simp [Opt.compileWithEffect, SymCC.compileWithEffect]
  split <;> simp
  simp [Functor.map, Except.map]
  rw [Opt.compile.correctness]
  simp_do_let SymCC.compile _ _

/--
Helper lemma
-/
private theorem compileWithEffect_ok_none {effect : Effect} {p : Policy} {εnv : SymEnv} :
  SymCC.compileWithEffect effect p εnv = .ok none →
  p.effect ≠ effect
:= by
  simp only [SymCC.compileWithEffect, beq_iff_eq, bind_pure_comp, Functor.map, Except.map,
    ite_eq_right_iff, ne_eq]
  split <;> simp

/--
Helper lemma
-/
private theorem compileWithEffect_ok_some {effect : Effect} {p : Policy} {εnv : SymEnv} :
  SymCC.compileWithEffect effect p εnv = .ok (some t) →
  p.effect = effect
:= by
  simp only [SymCC.compileWithEffect, beq_iff_eq, bind_pure_comp, Functor.map, Except.map]
  grind

/--
Lemma supporting the next theorem
-/
private theorem filterMapM_compileWithEffect_correctness (effect : Effect) (ps : Policies) (εnv : SymEnv) (ress : List Opt.CompileResult) :
  let optRess := ps.filterMapM (Opt.compileWithEffect effect · εnv)
  let unoptTerms := ps.filterMapM (SymCC.compileWithEffect effect · εnv)
  let unoptFootprints := ps.filterMap (λ p => if p.effect = effect then some (footprint p.toExpr εnv) else none)
  optRess.map (λ ress => ress.map Opt.CompileResult.term) = unoptTerms
  ∧ (optRess = .ok ress → optRess.map (λ ress => ress.map Opt.CompileResult.footprint) = unoptFootprints)
:= by
  induction ps generalizing ress
  case nil => simp [pure, Except.pure, Except.map]
  case cons hd tl ih =>
    simp only [List.filterMapM_cons, bind_pure_comp]
    rw [Opt.compileWithEffect.correctness _ hd]
    simp only [bind_assoc, Except.bind_ok]
    simp_do_let SymCC.compileWithEffect effect hd εnv
    case error e hhd => simp [Except.map]
    case ok thd hhd =>
      cases htl : tl.filterMapM (Opt.compileWithEffect effect · εnv)
      case error e =>
        simp [htl, Except.map] at ih
        symm at ih
        simp [ih, Except.map]
        cases thd <;> simp
      case ok restl =>
        specialize ih restl
        simp [htl, Except.map] at ih
        cases thd
        case none => simp [Except.map, ih, compileWithEffect_ok_none hhd]
        case some thd =>
          simp only [Except.map, Option.map, Functor.map, ih, compileWithEffect_ok_some hhd,
            List.map_cons, Except.ok.injEq, ↓reduceIte, Option.some.injEq,
            List.filterMap_cons_some, implies_true, and_true]
          split <;> simp_all

/--
Correctness theorem for `Opt.satisfiedPolicies`:

`Opt.satisfiedPolicies` produces the same `term` as `SymCC.satisfiedPolicies`, and
`Opt.satisfiedPolicies` produces the same `footprint` as `footprints` applied to
just the policies with the appropriate `effect`
-/
theorem Opt.satisfiedPolicies.correctness (effect : Effect) (ps : Policies) (εnv : SymEnv) :
  Opt.satisfiedPolicies effect ps εnv = (do
    let term ← SymCC.satisfiedPolicies effect ps εnv
    let footprint := footprints (ps.filterMap λ p => if p.effect = effect then p.toExpr else none) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.satisfiedPolicies, SymCC.satisfiedPolicies]
  have := filterMapM_compileWithEffect_correctness effect ps εnv
  simp_do_let ps.filterMapM (Opt.compileWithEffect effect · εnv)
  case error e h =>
    specialize this [] -- doesn't matter what we choose in this case
    simp_all [Except.map, ← this]
  case ok ress hress =>
    specialize this ress
    simp_all [Except.map, ← this.left, footprints]
    conv => lhs ; rw [Data.Set.mapUnion_eq_mapUnion_id_map]
    simp [this, Data.Set.mapUnion_filterMap]
    apply Data.Set.mapUnion_congr
    intro p hp
    simp only [Option.mapD, id_eq]
    grind
    /- if `grind` turns out to be unstable, the following works instead as of this writing:
    split
    · split <;> simp_all
    · simp_all
    -/

/--
Correctness theorem for `Opt.isAuthorized`:

`Opt.isAuthorized` produces the same `term` as `SymCC.isAuthorized`, and
`Opt.isAuthorized` produces the same `footprint` as `footprints`
-/
theorem Opt.isAuthorized.correctness (ps : Policies) (εnv : SymEnv) :
  Opt.isAuthorized ps εnv = (do
    let term ← SymCC.isAuthorized ps εnv
    let footprint := footprints (ps.map Policy.toExpr) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.isAuthorized, SymCC.isAuthorized]
  rw [Opt.satisfiedPolicies.correctness .permit]
  rw [Opt.satisfiedPolicies.correctness .forbid]
  simp_do_let SymCC.satisfiedPolicies .forbid ps εnv ; rename_i ft hforbid
  simp_do_let SymCC.satisfiedPolicies .permit ps εnv ; rename_i pt hpermit
  simp only [Except.ok.injEq, Opt.CompileResult.mk.injEq, true_and]
  simp [footprints]
  rw [Data.Set.mapUnion_union_mapUnion]
  · apply Data.Set.map_eqv_implies_mapUnion_eq
    simp [List.Equiv, List.subset_def]
    constructor
    intro ts h₁
    cases h₁ <;> rename_i h₁
    · replace ⟨x, ⟨p, hp, h₁, hx⟩, h₂⟩ := h₁
      subst x ts
      exists p
    · replace ⟨x, ⟨p, hp, h₁, hx⟩, h₂⟩ := h₁
      subst x ts
      exists p
    · intro p hp
      cases heff : p.effect
      case' permit => left
      case' forbid => right
      all_goals {
        exists p.toExpr
        simp only [and_true]
        exists p
      }
  · simp [footprint_wf]

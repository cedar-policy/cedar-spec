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

import Cedar.SymCC.Enforcer
import Cedar.SymCCOpt.Compiler
import Cedar.Thm.SymbolicCompilation
import Cedar.Thm.SymCC.Data.LT
import Cedar.Thm.SymCC.Enforcer.Footprint

namespace Cedar.Thm

open Cedar Spec SymCC
open Cedar.Validation (ExtType)

/--
Helper lemma
-/
private theorem Opt.directFootprint.correctness {x : Expr} {εnv : SymEnv} {t : Term} :
  SymCC.compile x εnv = .ok t →
  Opt.directFootprint t = footprint.ofEntity x εnv
:= by
  intro h
  simp only [Opt.directFootprint, footprint.ofEntity, h]

/--
Helper lemma
-/
private theorem Opt.directFootprint.someFalse :
  Opt.directFootprint (⊙false) = ∅
:= by
  simp only [Opt.directFootprint, TermType.isOptionEntityType, Factory.someOf, typeOf_term_some,
    typeOf_bool, Bool.false_eq_true, ↓reduceIte, EmptyCollection.emptyCollection]

/--
Correctness lemma for `Opt.compileApp₁`, at least as to the `term`:
`Opt.compileApp₁` produces the same `term` as `SymCC.compileApp₁`
-/
private theorem Opt.compileApp₁.correctness (op : UnaryOp) (term : Term) (footprint : Data.Set Term) :
  Opt.compileApp₁ op { term, footprint } =
  (do let term ← SymCC.compileApp₁ op term ; .ok { term, footprint })
:= by
  cases op <;> simp only [Opt.compileApp₁, SymCC.compileApp₁]
  all_goals split <;> simp_all only [ExceptT.stM_eq, Opt.CompileResult.mapTerm, Except.bind_ok,
                        reduceCtorEq, imp_false, forall_const, implies_true, Except.bind_err,
                        UnaryOp.like.injEq, forall_eq', UnaryOp.is.injEq]

/--
Correctness lemma for `Opt.compileApp₂`, at least as to the `term`:
`Opt.compileApp₂` produces the same `term` as `SymCC.compileApp₂`

This theorem has to be adjusted for the fact that `SymCC.compileApp₂`
expects arguments that have `option.get` applied, while `Opt.compileApp₂`
does not. See detailed note in `Opt.compile`.
-/
private theorem Opt.compileApp₂.correctness (op : BinaryOp) (t₁ t₂ : Term) (ft₁ ft₂ : Data.Set Term) (εs : SymEntities) :
  Opt.compileApp₂ op
    { term := t₁, footprint := ft₁ }
    { term := t₂, footprint := ft₂ }
    εs =
  (do
    let term ← SymCC.compileApp₂ op (Factory.option.get t₁) (Factory.option.get t₂) εs
    let footprint := ft₁ ∪ ft₂ ∪ Opt.directFootprint (Factory.ifSome t₁ (Factory.ifSome t₂ term))
    .ok { term, footprint }
  )
:= by
  unfold Opt.compileApp₂ SymCC.compileApp₂
  split
  case h_1 =>
    cases h : reducibleEq (Factory.option.get t₁).typeOf (Factory.option.get t₂).typeOf
    case error => simp only [ExceptT.stM_eq, h, Except.bind_err]
    case ok b => cases b <;>
      simp only [ExceptT.stM_eq, h, Except.bind_ok, Bool.false_eq_true, ↓reduceIte]
  any_goals (split <;> simp_all only [ExceptT.stM_eq, ↓reduceIte, Except.bind_ok, Except.bind_err])
  all_goals simp_all only [ExceptT.stM_eq, Except.bind_ok, imp_false, TermType.prim.injEq, TermPrimType.entity.injEq, Except.bind_err]

/--
Correctness lemma for `Opt.compileGetAttr`, at least as to the `term`:
`Opt.compileGetAttr` produces the same `term` as `SymCC.compileGetAttr`

This theorem has to be adjusted for the fact that `SymCC.compileGetAttr`
expects arguments that have `option.get` applied, while `Opt.compileGetAttr`
does not. See detailed note in `Opt.compile`.
-/
private theorem Opt.compileGetAttr.correctness (t₁ : Term) (attr : Attr) (εs : SymEntities) (footprint : Data.Set Term) :
  Opt.compileGetAttr { term := t₁, footprint } attr εs =
  (do let term ← SymCC.compileGetAttr (Factory.option.get t₁) attr εs ; .ok { term, footprint := footprint ∪ Opt.directFootprint (Factory.ifSome t₁ term) })
:= by
  simp only [Opt.compileGetAttr, SymCC.compileGetAttr, Except.bind_ok, Except.bind_err, bind_assoc]
  simp_do_let compileAttrsOf (Factory.option.get t₁) εs
  split <;> rename_i h <;> simp only [ExceptT.stM_eq, h, Except.bind_err]
  split <;> rename_i h <;> simp only [h, Except.bind_ok, Except.ok.injEq, Opt.CompileResult.mk.injEq,
                             true_and, Except.bind_err]
  all_goals apply Data.Set.union_comm

/--
Correctness lemma for `Opt.compileHasAttr`, at least as to the `term`:
`Opt.compileHasAttr` produces the same `term` as `SymCC.compileHasAttr`
-/
private theorem Opt.compileHasAttr.correctness (t₁ : Term) (attr : Attr) (εs : SymEntities) (footprint : Data.Set Term) :
  Opt.compileHasAttr { term := t₁, footprint } attr εs =
  (do let term ← SymCC.compileHasAttr t₁ attr εs ; .ok { term, footprint })
:= by
  simp only [Opt.compileHasAttr, SymCC.compileHasAttr, bind_assoc]
  simp_do_let compileAttrsOf t₁ εs as h₁
  split <;> rename_i h <;> simp only [ExceptT.stM_eq, h, Except.bind_err]
  split <;> rename_i h <;> simp only [h, Except.bind_ok]

/--
Correctness lemma for `Opt.compileSet`, at least as to the `term`:
`Opt.compileSet` produces the same `term` as `SymCC.compileSet`
-/
private theorem Opt.compileSet.correctness (ress : List Opt.CompileResult) :
  Opt.compileSet ress =
  (do let term ← SymCC.compileSet (ress.map Opt.CompileResult.term) ; .ok { term, footprint := ress.mapUnion Opt.CompileResult.footprint })
:= by
  simp only [Opt.compileSet, SymCC.compileSet, List.all_map, List.all_eq_true, Function.comp_apply,
    decide_eq_true_eq, List.map_map]
  cases ress
  case nil => simp only [ExceptT.stM_eq, List.map_nil, List.mapUnion_nil, Except.bind_err]
  case cons hd tl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Function.comp_apply]
    split <;> rename_i hhd <;> simp only [ExceptT.stM_eq, hhd, true_and, Except.bind_err]
    split <;> rename_i htl <;> simp only [Except.bind_ok, Except.bind_err]

/--
Correctness lemma for `Opt.compileRecord`, at least as to the `term`:
`Opt.compileRecord` produces the same `term` as `SymCC.compileRecord`
-/
private theorem Opt.compileRecord.correctness (ress : List (Attr × Opt.CompileResult)) :
  Opt.compileRecord ress =
  {
    term := SymCC.compileRecord (ress.map λ (a, res) => (a, res.term))
    footprint := ress.mapUnion λ (_, res) => res.footprint
  }
:= by
  simp only [Opt.compileRecord, SymCC.compileRecord, List.map_map, Opt.CompileResult.mk.injEq, and_true]
  cases ress
  case nil => simp only [List.map_nil]
  case cons hd tl =>
    simp only [List.map_cons, Function.comp_apply, Prod.map_apply, id_eq]
    congr

/--
Correctness lemma for `Opt.compileCall₀`, at least as to the `term`:
`Opt.compileCall₀` produces the same `term` as `SymCC.compileCall₀`
-/
private theorem Opt.compileCall₀.correctness {α} [Coe α Ext] (mk : String → Option α) (res : Opt.CompileResult) :
  Opt.compileCall₀ mk res =
  (do let term ← SymCC.compileCall₀ mk res.term ; .ok { term, footprint := res.footprint })
:= by
  simp only [Opt.compileCall₀, compileCall₀]
  split
  · split <;> rename_i hs <;> simp only [ExceptT.stM_eq, hs, Except.bind_ok, Except.bind_err]
  · symm ; rw [do_error]
    split
    · exfalso
      rename_i h₁ t s h₂
      apply h₁ s res.footprint ; clear h₁
      cases res ; simp_all only
    · rfl

/--
Correctness lemma for `Opt.compileCallWithError₁`, at least as to the `term`:
`Opt.compileCall₁` produces the same `term` as `SymCC.compileCallWithError₁`
-/
private theorem Opt.compileCallWithError₁.correctness (xty : ExtType) (enc : Term → Term) (res : Opt.CompileResult) :
  Opt.compileCallWithError₁ xty enc res =
  (do let term ← SymCC.compileCallWithError₁ xty enc res.term ; .ok { term, footprint := res.footprint })
:= by
  simp only [Opt.compileCallWithError₁, compileCallWithError₁]
  split <;> simp only [ExceptT.stM_eq, Except.bind_ok, Except.bind_err]

/--
Correctness lemma for `Opt.compileCall₁`, at least as to the `term`:
`Opt.compileCall₁` produces the same `term` as `SymCC.compileCall₁`
-/
private theorem Opt.compileCall₁.correctness (xty : ExtType) (enc : Term → Term) (res : Opt.CompileResult) :
  Opt.compileCall₁ xty enc res =
  (do let term ← SymCC.compileCall₁ xty enc res.term ; .ok { term, footprint := res.footprint })
:= by
  simp only [Opt.compileCall₁, SymCC.compileCall₁]
  rw [Opt.compileCallWithError₁.correctness]

/--
Correctness lemma for `Opt.compileCallWithError₂`, at least as to the `term`:
`Opt.compileCallWithError₂` produces the same `term` as `SymCC.compileCallWithError₂`
-/
private theorem Opt.compileCallWithError₂.correctness (xty₁ xty₂ : ExtType) (enc : Term → Term → Term) (res₁ res₂ : Opt.CompileResult) :
  Opt.compileCallWithError₂ xty₁ xty₂ enc res₁ res₂ =
  (do let term ← SymCC.compileCallWithError₂ xty₁ xty₂ enc res₁.term res₂.term ; .ok { term, footprint := res₁.footprint ∪ res₂.footprint })
:= by
  simp only [Opt.compileCallWithError₂, SymCC.compileCallWithError₂]
  split <;> simp only [ExceptT.stM_eq, Except.bind_ok, Except.bind_err]

/--
Correctness lemma for `Opt.compileCall₂`, at least as to the `term`:
`Opt.compileCall₂` produces the same `term` as `SymCC.compileCall₂`
-/
private theorem Opt.compileCall₂.correctness (xty : ExtType) (enc : Term → Term → Term) (res₁ res₂ : Opt.CompileResult) :
  Opt.compileCall₂ xty enc res₁ res₂ =
  (do let term ← SymCC.compileCall₂ xty enc res₁.term res₂.term ; .ok { term, footprint := res₁.footprint ∪ res₂.footprint })
:= by
  simp only [Opt.compileCall₂, SymCC.compileCall₂]
  rw [Opt.compileCallWithError₂.correctness]

private theorem Opt.absurd_map_singleton {α β γ : Type} {f : α → β} {ress : List α} {t : β}
  {a : γ} (heq : ress.map f = [t]) (hno : ∀ r, a = a → ress = [r] → False) :
  False
:= by
  have ⟨r, hr, _⟩ := List.map_eq_singleton_iff.mp heq
  exact hno r rfl hr

private theorem Opt.absurd_map_doubleton {α β γ : Type} {f : α → β} {ress : List α} {t₁ t₂ : β}
  {a : γ} (heq : ress.map f = [t₁, t₂]) (hno : ∀ r₁ r₂, a = a → ress = [r₁, r₂] → False) :
  False
:= by
  have ⟨r₁, r₂, hr⟩ := List.map_eq_doubleton heq
  exact hno r₁ r₂ rfl hr

/--
Correctness lemma for `Opt.compileCall`, at least as to the `term`:
`Opt.compileCall` produces the same `term` as `SymCC.compileCall`
-/
private theorem Opt.compileCall.correctness (xfn : ExtFun) (ress : List Opt.CompileResult)
  (hwf : ∀ res ∈ ress, res.footprint.WellFormed) :
  Opt.compileCall xfn ress =
  (do let term ← SymCC.compileCall xfn (ress.map Opt.CompileResult.term) ; .ok { term, footprint := ress.mapUnion Opt.CompileResult.footprint })
:= by
  have h_mem_single : ∀ {res : Opt.CompileResult}, res ∈ [res] :=
    List.mem_singleton.mpr rfl
  have h_mem_pair : ∀ {res₁ res₂ : Opt.CompileResult}, res₂ ∈ [res₁, res₂] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, implies_true]
  simp only [Opt.compileCall, SymCC.compileCall]
  split <;> try simp only [List.map_cons, List.map_nil]
  · simp only [Opt.compileCall₀.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₀ Ext.Decimal.decimal res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.lessThan res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCall₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.lessThanOrEqual res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCall₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.greaterThan res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCall₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.greaterThanOrEqual res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCall₀.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₀ Ext.IPAddr.ip res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [ Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isIpv4 res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isIpv6 res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isLoopback res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isMulticast res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ IPAddr.isInRange res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCall₀.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₀ Ext.Datetime.datetime res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₀.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₀ Ext.Datetime.duration res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCallWithError₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCallWithError₂ _ _ Datetime.offset res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCallWithError₂.correctness]
    rename_i res₁ res₂ ; simp_do_let SymCC.compileCallWithError₂ _ _ Datetime.durationSince res₁.term res₂.term
    rw [List.mapUnion_cons hwf]
    rw [List.mapUnion_singleton (hwf res₂ h_mem_pair)]
  · simp only [Opt.compileCallWithError₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCallWithError₁ _ Datetime.toDate res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ Datetime.toTime res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toMilliseconds res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toSeconds res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toMinutes res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toHours res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · simp only [Opt.compileCall₁.correctness]
    rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toDays res.term
    rw [List.mapUnion_singleton (hwf res h_mem_single)]
  · symm
    rw [do_error]
    split
    all_goals first
      | rfl
      | exfalso; apply Opt.absurd_map_singleton <;> assumption
      | exfalso; apply Opt.absurd_map_doubleton <;> assumption

/--
Helper lemma that `Opt.compileCall₀` produces a well-formed footprint set.
-/
private theorem Opt.compileCall₀_footprint_wf [Coe α Ext] {mk : String → Option α} {term : Term} {footprint : Data.Set Term} {res : Opt.CompileResult} :
  footprint.WellFormed →
  Opt.compileCall₀ mk { term, footprint } = .ok res →
  res.footprint.WellFormed
:= by
  simp only [ExceptT.stM_eq, Opt.compileCall₀]
  split <;> rename_i h
  · simp only [Opt.CompileResult.mk.injEq] at h; replace ⟨h, h'⟩ := h ; subst term footprint
    split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies, implies_true]
    intro wf h ; subst res ; simp only [wf]
  · simp only [reduceCtorEq, false_implies, implies_true]

/--
Helper lemma that `Opt.compileCallWithError₁` produces a well-formed footprint set.
-/
private theorem Opt.compileCallWithError₁_footprint_wf {xty : ExtType} {arg res : Opt.CompileResult} :
  arg.footprint.WellFormed →
  Opt.compileCallWithError₁ xty enc arg = .ok res →
  res.footprint.WellFormed
:= by
  simp only [ExceptT.stM_eq, Opt.compileCallWithError₁]
  split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies, implies_true]
  intro wf h ; subst res ; simp only [wf]

/--
Helper lemma that `Opt.compileCall₁` produces a well-formed footprint set.
-/
private theorem Opt.compileCall₁_footprint_wf {xty : ExtType} {arg res : Opt.CompileResult} :
  arg.footprint.WellFormed →
  Opt.compileCall₁ xty enc arg = .ok res →
  res.footprint.WellFormed
:= by
  unfold Opt.compileCall₁
  exact Opt.compileCallWithError₁_footprint_wf

/--
Helper lemma that `Opt.compileCallWithError₂` produces a well-formed footprint set.

Unlike the ₀ and ₁ cases, this case does not require that the args are well-formed.
-/
private theorem Opt.compileCallWithError₂_footprint_wf {xty₁ xty₂ : ExtType} {arg₁ arg₂ res : Opt.CompileResult} :
  Opt.compileCallWithError₂ xty₁ xty₂ enc arg₁ arg₂ = .ok res →
  res.footprint.WellFormed
:= by
  simp only [ExceptT.stM_eq, Opt.compileCallWithError₂, Bool.and_eq_true, decide_eq_true_eq]
  split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
  intro h ; subst res ; simp only [Data.Set.union_wf]

/--
Helper lemma that `Opt.compileCall₂` produces a well-formed footprint set.

Unlike the ₀ and ₁ cases, this case does not require that the args are well-formed.
-/
private theorem Opt.compileCall₂_footprint_wf {xty : ExtType} {arg₁ arg₂ res : Opt.CompileResult} :
  Opt.compileCall₂ xty enc arg₁ arg₂ = .ok res →
  res.footprint.WellFormed
:= by
  unfold Opt.compileCall₂
  exact Opt.compileCallWithError₂_footprint_wf

/--
Helper lemma: the footprint `Opt.compileCall` produces is well-formed, given that the argument
results' footprints are.
-/
private theorem Opt.compileCall_footprint_wf {xfn : ExtFun} {ress : List Opt.CompileResult}
  {res : Opt.CompileResult} :
  (∀ r ∈ ress, r.footprint.WellFormed) →
  Opt.compileCall xfn ress = .ok res →
  res.footprint.WellFormed
:= by
  intro hwf
  have h_mem_single : ∀ {r : Opt.CompileResult}, r ∈ [r] := List.mem_singleton.mpr rfl
  simp only [Opt.compileCall, ExceptT.stM_eq]
  split
  · apply Opt.compileCall₀_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · exact Opt.compileCall₂_footprint_wf
  · exact Opt.compileCall₂_footprint_wf
  · exact Opt.compileCall₂_footprint_wf
  · exact Opt.compileCall₂_footprint_wf
  · apply Opt.compileCall₀_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · exact Opt.compileCall₂_footprint_wf
  · apply Opt.compileCall₀_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₀_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · exact Opt.compileCallWithError₂_footprint_wf
  · exact Opt.compileCallWithError₂_footprint_wf
  · apply Opt.compileCallWithError₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · apply Opt.compileCall₁_footprint_wf
    rename_i res'
    exact hwf res' h_mem_single
  · simp only [reduceCtorEq, false_implies]

/--
Helper lemma that `Opt.compileAnd` and `Opt.compileOr` produce a well-formed footprint set.

The two are proved together: they differ only in the short-circuiting literal and which branch of
the compiled `ite` the second argument lands in, and neither of those affects the footprint,
which in both cases is `∅`, the second argument's, or the union of the two.
-/
private theorem Opt.compileAndOr_footprint_wf {c : Opt.CompileResult}
  {e₂ : Except SymCC.Error Opt.CompileResult} {res : Opt.CompileResult} :
  (∀ r, e₂ = .ok r → r.footprint.WellFormed) →
  (Opt.compileAnd c e₂ = .ok res ∨ Opt.compileOr c e₂ = .ok res) →
  res.footprint.WellFormed
:= by
  intro h₂ h
  rcases h with h | h <;> revert h <;>
    simp only [Opt.compileAnd, Opt.compileOr, ExceptT.stM_eq] <;> split
  all_goals first
    | simp only [reduceCtorEq, false_implies]
    | (simp only [Except.ok.injEq] ; intro h ; subst res
       simp only [EmptyCollection.emptyCollection, Data.Set.empty_wf])
    | (simp_do_let e₂
       case error => simp only [false_implies]
       case ok =>
         split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
         intro h ; subst res ; simp only
         split
         · exact h₂ _ (by assumption)
         · simp only [Data.Set.union_wf])

/--
Helper lemma that `Opt.compileIf` produces a well-formed footprint set, given that the branch
results' footprints are. The branches are passed unevaluated, so the hypotheses are stated over
whatever they produce.
-/
private theorem Opt.compileIf_footprint_wf {c : Opt.CompileResult}
  {e₂ e₃ : Except SymCC.Error Opt.CompileResult} {res : Opt.CompileResult} :
  (∀ r, e₂ = .ok r → r.footprint.WellFormed) →
  (∀ r, e₃ = .ok r → r.footprint.WellFormed) →
  Opt.compileIf c e₂ e₃ = .ok res →
  res.footprint.WellFormed
:= by
  intro h₂ h₃
  simp only [Opt.compileIf, ExceptT.stM_eq]
  split
  · exact h₂ _
  · exact h₃ _
  · simp_do_let e₂
    case error => simp only [false_implies]
    case ok =>
      simp_do_let e₃
      case error => simp only [false_implies]
      case ok =>
        split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
        intro h ; subst res ; simp only [Data.Set.union_wf]
  · simp only [reduceCtorEq, false_implies]

/-- Helper lemma that `Opt.compilePrim` produces a well-formed footprint set. -/
private theorem Opt.compilePrim_footprint_wf {p : Prim} {εs : SymEntities}
  {res : Opt.CompileResult} :
  Opt.compilePrim p εs = .ok res →
  res.footprint.WellFormed
:= by
  cases p <;> simp only [Opt.compilePrim, Except.ok.injEq, ExceptT.stM_eq]
  case bool | int | string =>
    intro h ; subst res ; simp only [EmptyCollection.emptyCollection, Data.Set.empty_wf]
  case entityUID =>
    split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
    · intro h ; subst res ; simp only [Data.Set.singleton_wf]

/-- Helper lemma that `Opt.compileVar` produces a well-formed footprint set. -/
private theorem Opt.compileVar_footprint_wf {v : Var} {req : SymRequest}
  {res : Opt.CompileResult} :
  Opt.compileVar v req = .ok res →
  res.footprint.WellFormed
:= by
  cases v <;> simp only [Opt.compileVar, ExceptT.stM_eq] <;> split <;>
    simp only [Except.ok.injEq, reduceCtorEq, false_implies]
  · intro h ; subst res ; simp only [Data.Set.singleton_wf]
  · intro h ; subst res ; simp only [Data.Set.singleton_wf]
  · intro h ; subst res ; simp only [Data.Set.singleton_wf]
  · intro h ; subst res ; simp only [EmptyCollection.emptyCollection, Data.Set.empty_wf]

/-- Helper lemma that `Opt.compileSet` produces a well-formed footprint set. -/
private theorem Opt.compileSet_footprint_wf {ress : List Opt.CompileResult}
  {res : Opt.CompileResult} :
  Opt.compileSet ress = .ok res →
  res.footprint.WellFormed
:= by
  simp only [Opt.compileSet, ExceptT.stM_eq, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq, List.map_map]
  split
  · simp only [reduceCtorEq, false_implies]
  · split
    · split <;>
        simp only [List.map_cons, Function.comp_apply, Except.ok.injEq, reduceCtorEq, false_implies]
      intro h ; subst res ; simp only [List.mapUnion_wf]
    · simp only [reduceCtorEq, false_implies]

/-- Helper lemma that `Opt.compileRecord` produces a well-formed footprint set. -/
private theorem Opt.compileRecord_footprint_wf {aress : List (Attr × Opt.CompileResult)} :
  (Opt.compileRecord aress).footprint.WellFormed
:= by simp only [Opt.compileRecord, List.mapUnion_wf]

/-- Helper lemma that `Opt.compileHasAttr` produces a well-formed footprint set. -/
private theorem Opt.compileHasAttr_footprint_wf {arg res₂ : Opt.CompileResult} {attr : Attr}
  {εs : SymEntities} :
  arg.footprint.WellFormed →
  Opt.compileHasAttr arg attr εs = .ok res₂ →
  res₂.footprint.WellFormed
:= by
  intro hwf
  simp only [ExceptT.stM_eq, Opt.compileHasAttr]
  simp_do_let compileAttrsOf _ _
  case error => simp only [false_implies]
  case ok t ht =>
    split
    · split <;> simp only [Except.ok.injEq]
      all_goals {
        intro h ; subst res₂
        exact hwf
      }
    · simp only [reduceCtorEq, false_implies]

/-- Helper lemma that `Opt.compileGetAttr` produces a well-formed footprint set. -/
private theorem Opt.compileGetAttr_footprint_wf {res₁ res₂ : Opt.CompileResult} {attr : Attr}
  {εs : SymEntities} :
  Opt.compileGetAttr res₁ attr εs = .ok res₂ →
  res₂.footprint.WellFormed
:= by
  simp only [ExceptT.stM_eq, Opt.compileGetAttr, Except.bind_ok, Except.bind_err]
  simp_do_let compileAttrsOf _ _
  case error => simp only [false_implies]
  case ok t ht =>
    split
    · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
      all_goals {
        intro h ; subst res₂ ; simp only [Data.Set.union_wf]
      }
    · simp only [reduceCtorEq, false_implies]

/-- Helper lemma that `Opt.compileApp₁` produces a well-formed footprint set. -/
private theorem Opt.compileApp₁_footprint_wf {op : UnaryOp} {arg resApp : Opt.CompileResult} :
  arg.footprint.WellFormed →
  Opt.compileApp₁ op arg = .ok resApp →
  resApp.footprint.WellFormed
:= by
  intro hwf
  simp only [ExceptT.stM_eq, Opt.compileApp₁]
  split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
  all_goals {
    intro h ; subst resApp
    simp only [Opt.CompileResult.mapTerm]
    exact hwf
  }

/--
Helper lemma: the footprint `Opt.compileApp₂` produces is well-formed.
-/
private theorem Opt.compileApp₂_footprint_wf {op : BinaryOp} {t₁ t₂ : Term}
  {ft₁ ft₂ : Data.Set Term} {resApp : Opt.CompileResult} {εs : SymEntities} :
  Opt.compileApp₂ op { term := t₁, footprint := ft₁ } { term := t₂, footprint := ft₂ } εs
    = .ok resApp →
  resApp.footprint.WellFormed
:= by
  simp only [ExceptT.stM_eq]
  unfold Opt.compileApp₂
  simp only [ExceptT.stM_eq]
  split
  · simp_do_let reducibleEq _ _
    case error => simp only [false_implies]
    case ok b hb =>
      simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
    intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
    intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · split <;> simp only [Except.ok.injEq, reduceCtorEq, false_implies]
    intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp_do_let compileHasTag _ _ _
    case error => simp only [false_implies]
    case ok => simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp_do_let compileGetTag _ _ _
    case error => simp only [false_implies]
    case ok => simp only [Except.ok.injEq] ; intro h ; subst resApp ; simp only [Data.Set.union_wf]
  · simp only [reduceCtorEq, false_implies]

/--
Lemma that `Opt.compile` produces a well-formed footprint set.
-/
theorem Opt.compile_footprint_wf {x : Expr} {εnv : SymEnv} {res : Opt.CompileResult} :
  Opt.compile x εnv = .ok res →
  res.footprint.WellFormed
:= by
  cases x <;> simp only [ExceptT.stM_eq, Opt.compile]
  case lit p => exact Opt.compilePrim_footprint_wf
  case var v => exact Opt.compileVar_footprint_wf
  case ite x₁ x₂ x₃ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp only [false_implies]
    case ok =>
      exact Opt.compileIf_footprint_wf
        (fun _ h => Opt.compile_footprint_wf h) (fun _ h => Opt.compile_footprint_wf h)
  case and x₁ x₂ | or x₁ x₂ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp only [false_implies]
    case ok =>
      rename_i res' _
      intro h₂
      exact Opt.compileAndOr_footprint_wf (fun _ h => Opt.compile_footprint_wf h)
        (by first | exact .inl h₂ | exact .inr h₂)
  case unaryApp op x₁ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp only [false_implies]
    case ok res₁ =>
      simp_do_let Opt.compileApp₁ op _
      case error => simp only [false_implies]
      case ok resApp _ =>
        simp only [Except.ok.injEq] ; intro h ; subst res
        simp only [Opt.CompileResult.mapTerm]
        refine Opt.compileApp₁_footprint_wf ?_ (by assumption)
        simp only [Opt.CompileResult.mapTerm]
        exact Opt.compile_footprint_wf (by assumption)
  case binaryApp op x₁ x₂ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp only [false_implies]
    case ok res₁ h₁ =>
      simp_do_let Opt.compile x₂ εnv
      case error => simp only [false_implies]
      case ok res₂ h₂ =>
        simp_do_let Opt.compileApp₂ op res₁ res₂ εnv.entities
        case error => simp only [false_implies]
        case ok resApp h₃ =>
          simp only [Except.ok.injEq] ; intro h ; subst res
          simp only [Opt.CompileResult.mapTerm]
          obtain ⟨t₁, ft₁⟩ := res₁ ; obtain ⟨t₂, ft₂⟩ := res₂
          exact Opt.compileApp₂_footprint_wf h₃
  case hasAttr x₁ attr =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp only [false_implies]
    case ok res₁ h₁ =>
      simp_do_let Opt.compileHasAttr _ _ _
      case error => simp only [false_implies]
      case ok res₂ h₂ =>
        simp only [Except.ok.injEq] ; intro h ; subst res
        simp only [Opt.CompileResult.mapTerm]
        refine Opt.compileHasAttr_footprint_wf ?_ h₂
        simp only [Opt.CompileResult.mapTerm]
        exact Opt.compile_footprint_wf h₁
  case getAttr x₁ attr =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp only [false_implies]
    case ok res₁ h₁ =>
      simp_do_let Opt.compileGetAttr res₁ attr εnv.entities
      case error => simp only [false_implies]
      case ok res₂ h₂ =>
        simp only [Except.ok.injEq] ; intro h ; subst res
        simp only [Opt.CompileResult.mapTerm]
        exact Opt.compileGetAttr_footprint_wf h₂
  case set xs =>
    rw [List.mapM₁_eq_mapM (Opt.compile · εnv)]
    simp_do_let xs.mapM (Opt.compile · εnv)
    case error => simp only [false_implies]
    case ok ress hress =>
      exact Opt.compileSet_footprint_wf
  case record axs =>
    rw [do_eq_ok]
    intro h ; replace ⟨aress, haress, h⟩ := h
    simp only [Except.ok.injEq] at h; subst res
    exact Opt.compileRecord_footprint_wf
  case call xfn args =>
    rw [List.mapM₁_eq_mapM (Opt.compile · εnv)]
    simp_do_let args.mapM (Opt.compile · εnv)
    case error => simp only [false_implies]
    case ok ress hress =>
      replace hress := List.mapM_ok_implies_all_from_ok hress
      exact Opt.compileCall_footprint_wf fun r hr => by
        have ⟨arg, harg, h₁⟩ := hress r hr
        exact Opt.compile_footprint_wf h₁

/--
Proved on its own by induction, taking the correctness of `Opt.compile` on the list's elements as
an explicit hypothesis, so that it does not participate in `Opt.compile.correctness`'s recursion.
-/
private theorem both_lists_error_then_errors_same {xs : List Expr} {εnv : SymEnv} :
  xs.mapM (Opt.compile · εnv) = Except.error e₁ →
  xs.mapM (SymCC.compile · εnv) = Except.error e₂ →
  (∀ x ∈ xs, Opt.compile x εnv = (do
    let term ← SymCC.compile x εnv
    let footprint := footprint x εnv
    .ok { term, footprint }
  )) →
  e₁ = e₂
:= by
  cases xs
  case nil =>
    simp only [ExceptT.stM_eq, List.mapM_nil, pure, Except.pure, reduceCtorEq, List.not_mem_nil, false_implies, implies_true, forall_const]
  case cons hd tl =>
    simp only [ExceptT.stM_eq, List.mapM_cons, bind_pure_comp, List.mem_cons, forall_eq_or_imp, and_imp]
    intro h₁ h₂ ihhd ihtl
    rw [ihhd] at h₁
    cases hhd : SymCC.compile hd εnv <;>
      simp only [hhd, Except.bind_err, Except.error.injEq, Except.bind_ok] at h₁ h₂
    case error e' => simp only [← h₁, ← h₂]
    case ok t =>
      simp only [Functor.map, Except.map] at h₁
      split at h₁ <;> simp only [Except.error.injEq, reduceCtorEq] at h₁
      rename_i e' htl₁
      subst e'
      simp only [Functor.map, Except.map] at h₂
      split at h₂ <;> simp only [Except.error.injEq, reduceCtorEq] at h₂
      rename_i e' htl₂
      subst e'
      exact both_lists_error_then_errors_same htl₁ htl₂ ihtl

/--
Proved on its own by induction, taking the correctness of `Opt.compile` on the list's elements as
an explicit hypothesis, so that it does not participate in `Opt.compile.correctness`'s recursion.
-/
private theorem both_lists_pairs_error_then_errors_same {xs : List (Attr × Expr)} {εnv : SymEnv} :
  xs.mapM (λ pair => do .ok (pair.fst, ← Opt.compile pair.snd εnv)) = Except.error e₁ →
  xs.mapM (λ pair => do .ok (pair.fst, ← SymCC.compile pair.snd εnv)) = Except.error e₂ →
  (∀ pair ∈ xs, Opt.compile pair.snd εnv = (do
    let term ← SymCC.compile pair.snd εnv
    let footprint := footprint pair.snd εnv
    .ok { term, footprint }
  )) →
  e₁ = e₂
:= by
  cases xs
  case nil =>
    simp only [List.mapM_nil, pure, Except.pure, reduceCtorEq, List.not_mem_nil, ExceptT.stM_eq, false_implies, implies_true, forall_const]
  case cons hd tl =>
    simp only [List.mapM_cons, bind_pure_comp, bind_assoc, Except.bind_ok, List.mem_cons, ExceptT.stM_eq, forall_eq_or_imp, Prod.forall, and_imp]
    intro h₁ h₂ ihhd ihtl
    rw [ihhd] at h₁
    cases hhd : SymCC.compile hd.snd εnv <;>
      simp only [hhd, Except.bind_err, Except.error.injEq, Except.bind_ok] at h₁ h₂
    case error e' => simp only [← h₁, ← h₂]
    case ok t =>
      simp only [Functor.map, Except.map] at h₁
      split at h₁ <;> simp only [Except.error.injEq, reduceCtorEq] at h₁
      rename_i e' htl₁
      subst e'
      simp only [Functor.map, Except.map] at h₂
      split at h₂ <;> simp only [Except.error.injEq, reduceCtorEq] at h₂
      rename_i e' htl₂
      subst e'
      apply both_lists_pairs_error_then_errors_same htl₁ htl₂
      intro pair hpair
      exact ihtl pair.fst pair.snd hpair

/--
Proved on its own by induction, taking the correctness of `Opt.compile` on the list's elements as
an explicit hypothesis, so that it does not participate in `Opt.compile.correctness`'s recursion.
-/
private theorem both_lists_ok_then_elts_correspond {xs : List Expr} {εnv : SymEnv} :
  xs.mapM (Opt.compile · εnv) = Except.ok ts₁ →
  xs.mapM (SymCC.compile · εnv) = Except.ok ts₂ →
  (∀ x ∈ xs, Opt.compile x εnv = (do
    let term ← SymCC.compile x εnv
    let footprint := footprint x εnv
    .ok { term, footprint }
  )) →
  ts₁.map Opt.CompileResult.term = ts₂
  ∧ ts₁.map Opt.CompileResult.footprint = xs.map (footprint · εnv)
:= by
  intro h₁ h₂ ih
  cases xs
  case nil =>
    simp only [ExceptT.stM_eq, List.mapM_nil, pure, Except.pure, Except.ok.injEq, List.nil_eq] at h₁ h₂
    simp only [h₁, List.map_nil, h₂, and_self]
  case cons hd tl =>
    simp only [ExceptT.stM_eq, List.mapM_cons, bind_pure_comp, Functor.map, Except.map] at h₁ h₂
    rw [ih _ (by simp only [List.mem_cons, true_or])] at h₁
    simp_do_let SymCC.compile hd εnv as hhd at h₁
    case ok t =>
    simp only [hhd, Except.bind_ok] at h₂
    split at h₁ <;> simp only [reduceCtorEq, Except.ok.injEq] at h₁
    rename_i restl htl₁
    subst ts₁
    split at h₂ <;> simp only [reduceCtorEq, Except.ok.injEq] at h₂
    rename_i tstl htl₂
    subst ts₂
    have ⟨htemp, ih'⟩ := both_lists_ok_then_elts_correspond htl₁ htl₂ (by
      intro x hx
      apply ih x (by simp only [List.mem_cons, hx, or_true])
    )
    subst tstl
    simp only [List.map_cons, ih', and_self]

/--
Proved on its own by induction, taking the correctness of `Opt.compile` on the list's elements as
an explicit hypothesis, so that it does not participate in `Opt.compile.correctness`'s recursion.
-/
private theorem both_lists_pairs_ok_then_elts_correspond {xs : List (Attr × Expr)} {εnv : SymEnv} :
  xs.mapM (λ pair => do .ok (pair.fst, ← Opt.compile pair.snd εnv)) = Except.ok ts₁ →
  xs.mapM (λ pair => do .ok (pair.fst, ← SymCC.compile pair.snd εnv)) = Except.ok ts₂ →
  (∀ pair ∈ xs, Opt.compile pair.snd εnv = (do
    let term ← SymCC.compile pair.snd εnv
    let footprint := footprint pair.snd εnv
    .ok { term, footprint }
  )) →
  ts₁.map (λ (a, res) => (a, res.term)) = ts₂
  ∧ ts₁.map (λ (_, res) => res.footprint) = xs.map (λ (_, x) => footprint x εnv)
:= by
  intro h₁ h₂ ih
  cases xs
  case nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq, List.nil_eq] at h₁ h₂
    simp only [h₁, List.map_nil, h₂, and_self]
  case cons hd tl =>
    simp only [List.mapM_cons, bind_pure_comp, Functor.map, Except.map, bind_assoc, Except.bind_ok] at h₁ h₂
    rw [ih _ (by simp only [List.mem_cons, true_or])] at h₁
    simp_do_let compile hd.snd εnv as hhd at h₁
    case ok t =>
    simp only [hhd, Except.bind_ok] at h₂
    split at h₁ <;> simp only [reduceCtorEq, Except.ok.injEq] at h₁
    rename_i restl htl₁
    subst ts₁
    split at h₂ <;> simp only [reduceCtorEq, Except.ok.injEq] at h₂
    rename_i tstl htl₂
    subst ts₂
    have ⟨htemp, ih'⟩ := both_lists_pairs_ok_then_elts_correspond htl₁ htl₂ (by
      intro x hx
      apply ih x (by simp only [List.mem_cons, hx, or_true])
    )
    subst tstl
    simp only [List.map_cons, ih', and_self]

/--
The statement proved by `Opt.compile.correctness`, named so that the per-case lemmas below can take
it as an explicit induction hypothesis rather than recursing into `Opt.compile.correctness`
themselves.
-/
private abbrev Opt.compile.Spec (x : Expr) (εnv : SymEnv) : Prop :=
  Opt.compile x εnv = (do
    let term ← SymCC.compile x εnv
    let footprint := footprint x εnv
    .ok { term, footprint }
  )

/--
Correctness theorem for `Opt.compile` -- `lit` case
-/
private theorem Opt.compile.correctness.lit (p : Prim) (εnv : SymEnv) :
  Opt.compile.Spec (.lit p) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint]
  cases p <;> simp only [Opt.compilePrim, Factory.someOf, EmptyCollection.emptyCollection, compilePrim,
                footprint.ofEntity, compile, TermType.isOptionEntityType, typeOf_term_some,
                typeOf_bool, Bool.false_eq_true, ↓reduceIte, Except.bind_ok, typeOf_bv,
                typeOf_term_prim_string, ExceptT.stM_eq]
  case entityUID uid => split <;>
    simp only [typeOf_term_some, typeOf_term_prim_entity, ↓reduceIte, Except.bind_ok, Except.bind_err]

/--
Correctness theorem for `Opt.compile` -- `var` case
-/
private theorem Opt.compile.correctness.var (v : Var) (εnv : SymEnv) :
  Opt.compile.Spec (.var v) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint]
  cases v <;> simp only [Opt.compileVar, Factory.someOf, ExceptT.stM_eq,
                compileVar, footprint.ofEntity, compile, TermType.isOptionEntityType,
                EmptyCollection.emptyCollection]
  case principal | action | resource =>
    split
    case isTrue hety =>
      replace ⟨_, hety⟩ := isEntityType_implies_entity_type hety
      simp only [↓reduceIte, typeOf_term_some, Except.bind_ok, hety]
    case isFalse hety =>
      simp only [Except.bind_err]
  case context =>
    split
    case isTrue hrty =>
      replace ⟨_, hrty⟩ := isRecordType_implies_record_type hrty
      simp only [typeOf_term_some, hrty, Bool.false_eq_true, ↓reduceIte, Except.bind_ok]
    case isFalse =>
      simp only [Except.bind_err]

/--
Correctness theorem for `Opt.compile` -- `ite` case
-/
private theorem Opt.compile.correctness.ite (x₁ x₂ x₃ : Expr) (εnv : SymEnv)
  (ih₁ : Opt.compile.Spec x₁ εnv)
  (ih₂ : Opt.compile.Spec x₂ εnv)
  (ih₃ : Opt.compile.Spec x₃ εnv) :
  Opt.compile.Spec (.ite x₁ x₂ x₃) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc]
  rw [ih₁, ih₂, ih₃]
  simp only [Opt.compileIf, ExceptT.stM_eq, bind_assoc, Except.bind_ok, compileIf, footprint.ofBranch]
  cases h₁ : SymCC.compile x₁ εnv <;> simp only [Except.bind_err, Except.bind_ok]
  case ok t₁ =>
    split <;> simp only [Except.bind_err]
    cases h₂ : SymCC.compile x₂ εnv <;>
      simp_all only [imp_false, ExceptT.stM_eq, Except.bind_err, Except.bind_ok, bind_assoc]
    case ok t₁ _ _ t₂ _ _ ht₁ =>
      cases h₃ : SymCC.compile x₃ εnv <;>
        simp_all only [ExceptT.stM_eq, Except.bind_err, Except.bind_ok]
      case ok t₃ => split <;> simp only [Except.bind_ok, Except.bind_err]

/--
Correctness theorem for `Opt.compile` -- `and` and `or` cases
-/
private theorem Opt.compile.correctness.andor (x₁ x₂ : Expr) (εnv : SymEnv)
  (ih₁ : Opt.compile.Spec x₁ εnv)
  (ih₂ : Opt.compile.Spec x₂ εnv) :
  Opt.compile.Spec (.and x₁ x₂) εnv ∧ Opt.compile.Spec (.or x₁ x₂) εnv
:= by
  constructor
  all_goals {
    simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc]
    rw [ih₁, ih₂]
    simp only [Opt.compileAnd, ExceptT.stM_eq, EmptyCollection.emptyCollection, bind_assoc,
      Except.bind_ok, compileAnd, footprint.ofBranch, Opt.compileOr, compileOr]
    cases h₁ : SymCC.compile x₁ εnv <;> simp only [Except.bind_ok, Except.bind_err]
    case ok t₁ =>
      cases h₂ : SymCC.compile x₂ εnv <;> simp only [Except.bind_ok, Except.bind_err]
      case error e => split <;> simp only [Except.bind_ok, Except.bind_err, *]
      case ok t₂ =>
        split <;> simp only [Except.bind_ok, *, Except.bind_err]
        split <;> simp only [ExceptT.stM_eq, imp_false, Except.bind_ok, Except.ok.injEq, Opt.CompileResult.mk.injEq, true_and, Except.bind_err] at *
        split <;> simp only [*]
        first
        | rw [Data.Set.union_empty_right (Data.Set.union_wf _ _)]
        | rw [Data.Set.union_empty_right (footprint_wf _ _)]
  }

/--
Correctness theorem for `Opt.compile` -- `unaryApp` case
-/
private theorem Opt.compile.correctness.unaryApp (op : UnaryOp) (x : Expr) (εnv : SymEnv)
  (ih : Opt.compile.Spec x εnv) :
  Opt.compile.Spec (.unaryApp op x) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc, Except.bind_ok]
  rw [ih]
  cases h₁ : SymCC.compile x εnv <;> simp only [Except.bind_err, Except.bind_ok]
  rw [Opt.compileApp₁.correctness op]
  simp only [Opt.CompileResult.mapTerm, bind_assoc, Except.bind_ok]

/--
Correctness theorem for `Opt.compile` -- `binaryApp` case
-/
private theorem Opt.compile.correctness.binaryApp (op : BinaryOp) (x₁ x₂ : Expr) (εnv : SymEnv)
  (ih₁ : Opt.compile.Spec x₁ εnv)
  (ih₂ : Opt.compile.Spec x₂ εnv) :
  Opt.compile.Spec (.binaryApp op x₁ x₂) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc, Except.bind_ok]
  rw [ih₁, ih₂]
  cases h₁ : SymCC.compile x₁ εnv <;> simp only [Except.bind_err, bind_assoc, Except.bind_ok]
  case ok t₁ =>
    cases h₂ : SymCC.compile x₂ εnv <;> simp only [Except.bind_err, Except.bind_ok]
    case ok t₂ =>
      rw [Opt.compileApp₂.correctness op]
      simp only [Opt.CompileResult.mapTerm, bind_assoc, Except.bind_ok]
      cases h : SymCC.compileApp₂ op (Factory.option.get t₁) (Factory.option.get t₂) εnv.entities <;>
        simp only [Except.bind_err, Except.bind_ok, Except.ok.injEq, Opt.CompileResult.mk.injEq, true_and]
      case ok t =>
        rw [Opt.directFootprint.correctness (t := Factory.ifSome t₁ (Factory.ifSome t₂ t)) (εnv := εnv) (x := .binaryApp op x₁ x₂)]
        · conv => rhs ; rw [Data.Set.union_assoc, Data.Set.union_comm]
        · -- here we have to show that the `t` and `x` arguments we chose for `Opt.directFootprint.correctness` in the `rw` above correspond to each other correctly
          simp only [ExceptT.stM_eq, compile, h₁, h₂, Except.bind_ok, h]

/--
Correctness theorem for `Opt.compile` -- `getAttr` case
-/
private theorem Opt.compile.correctness.getAttr (expr : Expr) (attr : Attr) (εnv : SymEnv)
  (ih : Opt.compile.Spec expr εnv) :
  Opt.compile.Spec (.getAttr expr attr) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc,
    Except.bind_ok]
  rw [ih]
  cases h₁ : SymCC.compile expr εnv <;> simp only [Except.bind_err, Except.bind_ok]
  case ok t =>
    rw [Opt.compileGetAttr.correctness]
    simp only [Opt.CompileResult.mapTerm, bind_assoc, Except.bind_ok]
    simp_do_let compileGetAttr (Factory.option.get t) attr εnv.entities ; rename_i t' h₂
    simp only [Except.ok.injEq, Opt.CompileResult.mk.injEq, true_and]
    rw [Opt.directFootprint.correctness (t := Factory.ifSome t t') (x := .getAttr expr attr) (εnv := εnv)]
    · apply Data.Set.union_comm
    · -- here we have to show that the `t` and `x` arguments we chose for `Opt.directFootprint.correctness` in the `rw` above correspond to each other correctly
      simp only [ExceptT.stM_eq, compile, h₁, Except.bind_ok, h₂]

/--
Correctness theorem for `Opt.compile` -- `hasAttr` case
-/
private theorem Opt.compile.correctness.hasAttr (expr : Expr) (attr : Attr) (εnv : SymEnv)
  (ih : Opt.compile.Spec expr εnv) :
  Opt.compile.Spec (.hasAttr expr attr) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc,
    Except.bind_ok]
  rw [ih]
  cases h₁ : SymCC.compile expr εnv <;> simp only [Except.bind_err, Except.bind_ok]
  case ok t =>
    rw [Opt.compileHasAttr.correctness]
    simp only [Opt.CompileResult.mapTerm, bind_assoc, Except.bind_ok]

/--
Correctness theorem for `Opt.compile` -- `set` case
-/
private theorem Opt.compile.correctness.set (ls : List Expr) (εnv : SymEnv)
  (ih : ∀ x ∈ ls, Opt.compile.Spec x εnv) :
  Opt.compile.Spec (.set ls) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc]
  rw [List.mapM₁_eq_mapM (Opt.compile · εnv), List.mapM₁_eq_mapM (SymCC.compile · εnv)]
  rw [List.mapUnion₁_eq_mapUnion (footprint · εnv)]
  simp_do_let ls.mapM (Opt.compile · εnv) as hmap₁
  <;> simp_do_let ls.mapM (SymCC.compile · εnv) as hmap₂
  case error.error e₁ e₂ =>
    simp only [Except.error.injEq]
    exact both_lists_error_then_errors_same hmap₁ hmap₂ ih
  case ok.error ts e =>
    exfalso
    replace ⟨x, hx, hmap₂⟩ := List.mapM_error_implies_exists_error hmap₂
    replace ⟨t, ht, hmap₁⟩ := List.mapM_ok_implies_all_ok hmap₁ x hx
    rw [ih x hx] at hmap₁
    simp only [hmap₂, Except.bind_err, reduceCtorEq] at hmap₁
  case error.ok e ts =>
    exfalso
    replace ⟨x, hx, hmap₁⟩ := List.mapM_error_implies_exists_error hmap₁
    replace ⟨t, ht, hmap₂⟩ := List.mapM_ok_implies_all_ok hmap₂ x hx
    rw [ih x hx] at hmap₁
    simp only [hmap₂, Except.bind_ok, reduceCtorEq] at hmap₁
  case ok.ok ts₁ ts₂ =>
    rw [Opt.compileSet.correctness]
    suffices
      SymCC.compileSet (List.map Opt.CompileResult.term ts₁) = SymCC.compileSet ts₂
      ∧ ts₁.mapUnion Opt.CompileResult.footprint = ls.mapUnion (footprint · εnv)
      by simp only [this]
    have ⟨h₁, h₂⟩ := both_lists_ok_then_elts_correspond hmap₁ hmap₂ ih
    subst ts₂ ; simp only [ExceptT.stM_eq, true_and]
    apply List.map_eqv_implies_mapUnion_eq (by simp only [h₂, List.Equiv.refl])

/--
Correctness theorem for `Opt.compile` -- `record` case
-/
private theorem Opt.compile.correctness.record (m : List (Attr × Expr)) (εnv : SymEnv)
  (ih : ∀ pair ∈ m, Opt.compile.Spec pair.snd εnv) :
  Opt.compile.Spec (.record m) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc,
    Except.bind_ok]
  simp only [List.mapM₂_eq_mapM (λ x => do Except.ok (x.fst, ← Opt.compile x.snd εnv)) m]
  simp only [List.mapM₂_eq_mapM (λ x => do Except.ok (x.fst, ← SymCC.compile x.snd εnv)) m]
  rw [List.mapUnion₂_eq_mapUnion (λ x => footprint x.snd εnv)]
  simp_do_let m.mapM (m := SymCC.Result) _ as hmap₁
  <;> simp_do_let m.mapM (m := SymCC.Result) _ as hmap₂
  case error.error e₁ e₂ =>
    simp only [Except.error.injEq]
    exact both_lists_pairs_error_then_errors_same hmap₁ hmap₂ ih
  case ok.error ts e =>
    exfalso
    replace ⟨x, hx, hmap₂⟩ := List.mapM_error_implies_exists_error hmap₂
    replace ⟨t, ht, hmap₁⟩ := List.mapM_ok_implies_all_ok hmap₁ x hx
    rw [ih x hx] at hmap₁
    simp only [do_error] at hmap₂
    simp only [hmap₂, Except.bind_err, reduceCtorEq] at hmap₁
  case error.ok e ts =>
    exfalso
    replace ⟨x, hx, hmap₁⟩ := List.mapM_error_implies_exists_error hmap₁
    replace ⟨t, ht, hmap₂⟩ := List.mapM_ok_implies_all_ok hmap₂ x hx
    rw [ih x hx] at hmap₁
    simp only [bind_assoc, Except.bind_ok, do_error] at hmap₁
    simp only [hmap₁, Except.bind_err, reduceCtorEq] at hmap₂
  case ok.ok ts₁ ts₂ =>
    rw [Opt.compileRecord.correctness]
    simp only [Except.ok.injEq, Opt.CompileResult.mk.injEq]
    have ⟨h₁, h₂⟩ := both_lists_pairs_ok_then_elts_correspond hmap₁ hmap₂ ih
    subst ts₂ ; simp only [true_and]
    apply List.map_eqv_implies_mapUnion_eq (by simp only [h₂, List.Equiv.refl])

/--
Correctness theorem for `Opt.compile` -- `call` case
-/
private theorem Opt.compile.correctness.call (xfn : ExtFun) (args : List Expr) (εnv : SymEnv)
  (ih : ∀ x ∈ args, Opt.compile.Spec x εnv) :
  Opt.compile.Spec (.call xfn args) εnv
:= by
  simp only [Opt.compile.Spec, ExceptT.stM_eq, Opt.compile, compile, footprint, bind_assoc]
  rw [List.mapM₁_eq_mapM (Opt.compile · εnv), List.mapM₁_eq_mapM (SymCC.compile · εnv)]
  rw [List.mapUnion₁_eq_mapUnion (footprint · εnv)]
  simp_do_let args.mapM (Opt.compile · εnv) as hmap₁
  <;> simp_do_let args.mapM (SymCC.compile · εnv) as hmap₂
  case error.error e₁ e₂ =>
    simp only [Except.error.injEq]
    exact both_lists_error_then_errors_same hmap₁ hmap₂ ih
  case ok.error ts e =>
    exfalso
    replace ⟨x, hx, hmap₂⟩ := List.mapM_error_implies_exists_error hmap₂
    replace ⟨t, ht, hmap₁⟩ := List.mapM_ok_implies_all_ok hmap₁ x hx
    rw [ih x hx] at hmap₁
    simp only [hmap₂, Except.bind_err, reduceCtorEq] at hmap₁
  case error.ok e ts =>
    exfalso
    replace ⟨x, hx, hmap₁⟩ := List.mapM_error_implies_exists_error hmap₁
    replace ⟨t, ht, hmap₂⟩ := List.mapM_ok_implies_all_ok hmap₂ x hx
    rw [ih x hx] at hmap₁
    simp only [hmap₂, Except.bind_ok, reduceCtorEq] at hmap₁
  case ok.ok ts₁ ts₂ =>
    rw [Opt.compileCall.correctness]
    · suffices
        SymCC.compileCall xfn (List.map Opt.CompileResult.term ts₁) = SymCC.compileCall xfn ts₂
        ∧ ts₁.mapUnion Opt.CompileResult.footprint = args.mapUnion (footprint · εnv)
        by simp only [this]
      have ⟨h₁, h₂⟩ := both_lists_ok_then_elts_correspond hmap₁ hmap₂ ih
      subst ts₂ ; simp only [ExceptT.stM_eq, true_and]
      apply List.map_eqv_implies_mapUnion_eq (by simp only [h₂, List.Equiv.refl])
    case hwf =>
      intro res hres
      have ⟨arg, harg, h₁⟩ := List.mapM_ok_implies_all_from_ok hmap₁ res hres
      exact Opt.compile_footprint_wf h₁

/--
Correctness theorem for `Opt.compile`:

`Opt.compile` produces the same `term` as `SymCC.compile`, and
`Opt.compile` produces the same `footprint` as `footprint`
-/
theorem Opt.compile.correctness (x : Expr) (εnv : SymEnv) :
  Opt.compile x εnv = (do
    let term ← SymCC.compile x εnv
    let footprint := footprint x εnv
    .ok { term, footprint }
  )
:= by
  cases x
  case lit p => exact Opt.compile.correctness.lit p εnv
  case var v => exact Opt.compile.correctness.var v εnv
  case and x₁ x₂ | or x₁ x₂ =>
    have ih := Opt.compile.correctness.andor x₁ x₂ εnv
      (Opt.compile.correctness x₁ εnv) (Opt.compile.correctness x₂ εnv)
    first
    | exact ih.left
    | exact ih.right
  case ite x₁ x₂ x₃ =>
    exact Opt.compile.correctness.ite x₁ x₂ x₃ εnv
      (Opt.compile.correctness x₁ εnv) (Opt.compile.correctness x₂ εnv)
      (Opt.compile.correctness x₃ εnv)
  case unaryApp op x₁ =>
    exact Opt.compile.correctness.unaryApp op x₁ εnv (Opt.compile.correctness x₁ εnv)
  case binaryApp op x₁ x₂ =>
    exact Opt.compile.correctness.binaryApp op x₁ x₂ εnv
      (Opt.compile.correctness x₁ εnv) (Opt.compile.correctness x₂ εnv)
  case getAttr x₁ attr =>
    exact Opt.compile.correctness.getAttr x₁ attr εnv (Opt.compile.correctness x₁ εnv)
  case hasAttr x₁ attr =>
    exact Opt.compile.correctness.hasAttr x₁ attr εnv (Opt.compile.correctness x₁ εnv)
  case set xs =>
    exact Opt.compile.correctness.set xs εnv (by
      intro x hx
      have := List.sizeOf_lt_of_mem hx -- for termination
      exact Opt.compile.correctness x εnv)
  case record m =>
    exact Opt.compile.correctness.record m εnv (by
      intro pair hpair
      have := List.sizeOf_lt_of_mem hpair -- for termination
      have : sizeOf pair.snd < sizeOf pair := by
        simp only [sizeOf, Prod._sizeOf_1, Nat.lt_add_left_iff_pos] ; omega
      exact Opt.compile.correctness pair.snd εnv)
  case call xfn args =>
    exact Opt.compile.correctness.call xfn args εnv (by
      intro x hx
      have := List.sizeOf_lt_of_mem hx -- for termination
      exact Opt.compile.correctness x εnv)
termination_by sizeOf x

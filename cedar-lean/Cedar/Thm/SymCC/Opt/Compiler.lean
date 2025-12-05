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
  simp [Opt.directFootprint, footprint.ofEntity, h]

/--
Helper lemma
-/
private theorem Opt.directFootprint.someFalse :
  Opt.directFootprint (⊙false) = ∅
:= by
  simp [EmptyCollection.emptyCollection, Opt.directFootprint, Factory.someOf, Term.typeOf, TermPrim.typeOf, TermType.isOptionEntityType]

/--
Correctness lemma for `Opt.compileApp₁`, at least as to the `term`:
`Opt.compileApp₁` produces the same `term` as `SymCC.compileApp₁`
-/
private theorem Opt.compileApp₁.correctness (op : UnaryOp) (term : Term) (footprint : Data.Set Term) :
  Opt.compileApp₁ op { term, footprint } =
  (do let term ← SymCC.compileApp₁ op term ; .ok { term, footprint })
:= by
  cases op <;> simp only [Opt.compileApp₁, SymCC.compileApp₁]
  all_goals split <;> simp_all [Opt.CompileResult.mapTerm]

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
  cases op <;> simp only [Opt.compileApp₂, SymCC.compileApp₂]
  case eq =>
    cases reducibleEq (Factory.option.get t₁).typeOf (Factory.option.get t₂).typeOf <;> simp
    case ok b => cases b <;> simp
  case getTag | hasTag =>
    split <;> simp at *
    split <;> simp_all
  case mem | less | lessEq | add | sub | mul =>
    split <;> simp_all
  case contains | containsAll | containsAny =>
    split <;> simp at *
    split <;> simp_all

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
  split <;> rename_i h <;> simp [h]
  split <;> rename_i h <;> simp [h]
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
  simp_do_let compileAttrsOf t₁ εs ; rename_i h₁
  split <;> rename_i h <;> simp [h]
  split <;> rename_i h <;> simp [h]

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
  case nil => simp
  case cons hd tl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Function.comp_apply]
    split <;> rename_i hhd <;> simp [hhd]
    split <;> rename_i htl <;> simp

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
  case nil => simp
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
  · split <;> rename_i hs <;> simp [hs]
  · symm ; rw [do_error]
    split
    · exfalso
      rename_i h₁ t s h₂
      apply h₁ s res.footprint ; clear h₁
      cases res ; simp_all
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
  split <;> simp

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
  split <;> simp

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

/--
Correctness lemma for `Opt.compileCall`, at least as to the `term`:
`Opt.compileCall` produces the same `term` as `SymCC.compileCall`
-/
private theorem Opt.compileCall.correctness (xfn : ExtFun) (ress : List Opt.CompileResult)
  (hwf : ∀ res ∈ ress, res.footprint.WellFormed) :
  Opt.compileCall xfn ress =
  (do let term ← SymCC.compileCall xfn (ress.map Opt.CompileResult.term) ; .ok { term, footprint := ress.mapUnion Opt.CompileResult.footprint })
:= by
  simp only [Opt.compileCall, SymCC.compileCall]
  split <;> try simp only [Opt.compileCall₀.correctness, Opt.compileCall₁.correctness, Opt.compileCall₂.correctness, List.map_cons, List.map_nil]
  all_goals first
  | simp only [Opt.compileCall₀.correctness] | simp only [Opt.compileCall₁.correctness] | simp only [Opt.compileCall₂.correctness] | simp only [Opt.compileCallWithError₁.correctness] | simp only [Opt.compileCallWithError₂.correctness] | symm
  · rename_i res ; simp_do_let SymCC.compileCall₀ Ext.Decimal.decimal res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.lessThan res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.lessThanOrEqual res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.greaterThan res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ Decimal.greaterThanOrEqual res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₀ Ext.IPAddr.ip res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isIpv4 res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isIpv6 res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isLoopback res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ IPAddr.isMulticast res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCall₂ _ IPAddr.isInRange res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₀ Ext.Datetime.datetime res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₀ Ext.Datetime.duration res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCallWithError₂ _ _ Datetime.offset res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res₁ res₂ ; simp_do_let SymCC.compileCallWithError₂ _ _ Datetime.durationSince res₁.term res₂.term
    rw [Data.Set.mapUnion_cons hwf]
    rw [Data.Set.mapUnion_singleton (by apply hwf res₂ (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCallWithError₁ _ Datetime.toDate res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ Datetime.toTime res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toMilliseconds res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toSeconds res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toMinutes res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toHours res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rename_i res ; simp_do_let SymCC.compileCall₁ _ Duration.toDays res.term
    rw [Data.Set.mapUnion_singleton (by apply hwf res (by simp))]
  · rw [do_error]
    split <;> simp_all
    all_goals {
      rename_i t₁ t₂ h₁ h₂
      have ⟨res₁, res₂, hres⟩ := List.map_eq_doubleton h₁
      specialize h₂ res₁ res₂ ; contradiction
    }

/--
Helper lemma that `Opt.compileCall₀` produces a well-formed footprint set.
-/
private theorem Opt.compileCall₀_footprint_wf [Coe α Ext] {mk : String → Option α} {term : Term} {footprint : Data.Set Term} {res : Opt.CompileResult} :
  footprint.WellFormed →
  Opt.compileCall₀ mk { term, footprint } = .ok res →
  res.footprint.WellFormed
:= by
  simp [Opt.compileCall₀]
  split <;> rename_i h
  · simp at h ; replace ⟨h, h'⟩ := h ; subst term footprint
    split <;> simp
    intro wf h ; subst res ; simp [wf]
  · simp

/--
Helper lemma that `Opt.compileCallWithError₁` produces a well-formed footprint set.
-/
private theorem Opt.compileCallWithError₁_footprint_wf {xty : ExtType} {arg res : Opt.CompileResult} :
  arg.footprint.WellFormed →
  Opt.compileCallWithError₁ xty enc arg = .ok res →
  res.footprint.WellFormed
:= by
  simp [Opt.compileCallWithError₁]
  split <;> simp
  intro wf h ; subst res ; simp [wf]

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
  simp [Opt.compileCallWithError₂]
  split <;> simp
  intro h ; subst res ; simp [Data.Set.union_wf]

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
Lemma that `Opt.compile` produces a well-formed footprint set.
-/
theorem Opt.compile_footprint_wf {x : Expr} {εnv : SymEnv} {res : Opt.CompileResult} :
  Opt.compile x εnv = .ok res →
  res.footprint.WellFormed
:= by
  cases x <;> simp [Opt.compile]
  case lit p =>
    cases p <;> simp [Opt.compilePrim]
    case bool | int | string =>
      intro h ; subst res ; simp [EmptyCollection.emptyCollection, Data.Set.empty_wf]
    case entityUID =>
      split <;> simp
      · intro h ; subst res ; simp [Data.Set.singleton_wf]
  case var v =>
    cases v <;> simp [Opt.compileVar] <;> split <;> simp
    · intro h ; subst res ; simp [Data.Set.singleton_wf]
    · intro h ; subst res ; simp [Data.Set.singleton_wf]
    · intro h ; subst res ; simp [Data.Set.singleton_wf]
    · intro h ; subst res ; simp [EmptyCollection.emptyCollection, Data.Set.empty_wf]
  case ite x₁ x₂ x₃ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp
    case ok =>
      simp [Opt.compileIf]
      split
      · exact Opt.compile_footprint_wf
      · exact Opt.compile_footprint_wf
      · simp_do_let Opt.compile x₂ εnv
        case error => simp
        case ok =>
          simp_do_let Opt.compile x₃ εnv
          case error => simp
          case ok =>
            split <;> simp
            intro h ; subst res ; simp [Data.Set.union_wf]
      · simp
  case and x₁ x₂ | or x₁ x₂ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp
    case ok =>
      rename_i res' h₁
      simp [Opt.compileAnd, Opt.compileOr]
      split
      · simp ; intro h ; subst res ; simp [EmptyCollection.emptyCollection, Data.Set.empty_wf]
      · simp_do_let Opt.compile x₂ εnv
        case error => simp
        case ok =>
          split <;> simp
          intro h ; subst res ; simp
          split
          · apply Opt.compile_footprint_wf ; assumption
          · simp [Data.Set.union_wf]
      · simp
  case unaryApp op x₁ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp
    case ok res₁ =>
      simp_do_let Opt.compileApp₁ op _
      case error => simp
      case ok resApp _ =>
        simp ; intro h ; subst res
        simp [Opt.CompileResult.mapTerm]
        -- we could make the remainder of this case a separate lemma `Opt.compileApp₁_footprint_wf`, but leaving it inline for now
        rename_i h₁ ; revert h₁
        simp [Opt.compileApp₁]
        split <;> simp
        all_goals {
          intro h ; subst resApp
          simp [Opt.CompileResult.mapTerm]
          apply Opt.compile_footprint_wf ; assumption
        }
  case binaryApp op x₁ x₂ =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp
    case ok res₁ h₁ =>
      simp_do_let Opt.compile x₂ εnv
      case error => simp
      case ok res₂ h₂ =>
        simp_do_let Opt.compileApp₂ op res₁ res₂ εnv.entities
        case error => simp
        case ok resApp h₃ =>
          simp ; intro h ; subst res
          simp [Opt.CompileResult.mapTerm]
          -- we could make the remainder of this case a separate lemma `Opt.compileApp₂_footprint_wf`, but leaving it inline for now
          revert h₃
          simp [Opt.compileApp₂]
          split
          · simp_do_let reducibleEq _ _
            case error => simp
            case ok b hb =>
              simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · split <;> simp
            intro h ; subst resApp ; simp [Data.Set.union_wf]
          · split <;> simp
            intro h ; subst resApp ; simp [Data.Set.union_wf]
          · split <;> simp
            intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp_do_let compileHasTag _ _ _
            case error => simp
            case ok => simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp_do_let compileGetTag _ _ _
            case error => simp
            case ok => simp ; intro h ; subst resApp ; simp [Data.Set.union_wf]
          · simp
  case hasAttr x₁ attr =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp
    case ok res₁ h₁ =>
      simp_do_let Opt.compileHasAttr _ _ _
      case error => simp
      case ok res₂ h₂ =>
        simp ; intro h ; subst res
        simp [Opt.CompileResult.mapTerm]
        -- we could make the remainder of this case a separate lemma `Opt.compileHasAttr_footprint_wf`, but leaving it inline for now
        revert h₂
        simp [Opt.compileHasAttr]
        simp_do_let compileAttrsOf _ _
        case error => simp
        case ok t ht =>
          split
          · split <;> simp
            all_goals {
              intro h ; subst res₂
              simp [Opt.CompileResult.mapTerm]
              exact Opt.compile_footprint_wf h₁
            }
          · simp
  case getAttr x₁ attr =>
    simp_do_let Opt.compile x₁ εnv
    case error => simp
    case ok res₁ h₁ =>
      simp_do_let Opt.compileGetAttr res₁ attr εnv.entities
      case error => simp
      case ok res₂ h₂ =>
        simp ; intro h ; subst res
        simp [Opt.CompileResult.mapTerm]
        -- we could make the remainder of this case a separate lemma `Opt.compileGetAttr_footprint_wf`, but leaving it inline for now
        revert h₂
        simp [Opt.compileGetAttr]
        simp_do_let compileAttrsOf _ _
        case error => simp
        case ok t ht =>
          split
          · split <;> simp
            all_goals {
              intro h ; subst res₂ ; simp [Data.Set.union_wf]
            }
          · simp
  case set xs =>
    rw [List.mapM₁_eq_mapM (Opt.compile · εnv)]
    simp_do_let xs.mapM (Opt.compile · εnv)
    case error => simp
    case ok ress hress =>
      -- we could make the remainder of this case a separate lemma `Opt.compileSet_footprint_wf`, but leaving it inline for now
      simp [Opt.compileSet]
      split
      · simp
      · split
        · split <;> simp
          intro h ; subst res ; simp [Data.Set.mapUnion_wf]
        · simp
  case record axs =>
    rw [do_eq_ok]
    intro h ; replace ⟨aress, haress, h⟩ := h
    simp at h ; subst res
    -- we could make the remainder of this case a separate lemma `Opt.compileRecord_footprint_wf`, but leaving it inline for now
    simp [Opt.compileRecord, Data.Set.mapUnion_wf]
  case call xfn args =>
    rw [List.mapM₁_eq_mapM (Opt.compile · εnv)]
    simp_do_let args.mapM (Opt.compile · εnv)
    case error => simp
    case ok ress hress =>
      -- we could make the remainder of this case a separate lemma `Opt.compileCall_footprint_wf`, but leaving it inline for now
      simp [Opt.compileCall]
      replace hress := List.mapM_ok_implies_all_from_ok hress
      split
      · apply Opt.compileCall₀_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · exact Opt.compileCall₂_footprint_wf
      · exact Opt.compileCall₂_footprint_wf
      · exact Opt.compileCall₂_footprint_wf
      · exact Opt.compileCall₂_footprint_wf
      · apply Opt.compileCall₀_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · exact Opt.compileCall₂_footprint_wf
      · apply Opt.compileCall₀_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₀_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · exact Opt.compileCallWithError₂_footprint_wf
      · exact Opt.compileCallWithError₂_footprint_wf
      · apply Opt.compileCallWithError₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · apply Opt.compileCall₁_footprint_wf
        rename_i res'
        have ⟨arg, harg, h₁⟩ := hress res' (by simp)
        exact Opt.compile_footprint_wf h₁
      · simp

/--
Lemma pulled out from the below `mutual` block so that we can prove it on its own by induction
without worrying about making the `mutual` block's termination proof even more complicated
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
  case nil => simp [List.mapM_nil, pure, Except.pure]
  case cons hd tl =>
    simp [List.mapM_cons]
    intro h₁ h₂ ihhd ihtl
    rw [ihhd] at h₁
    cases hhd : SymCC.compile hd εnv <;> simp [hhd] at h₁ h₂
    case error e' => simp [← h₁, ← h₂]
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
Lemma pulled out from the below `mutual` block so that we can prove it on its own by induction
without worrying about making the `mutual` block's termination proof even more complicated
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
  case nil => simp [List.mapM_nil, pure, Except.pure]
  case cons hd tl =>
    simp [List.mapM_cons]
    intro h₁ h₂ ihhd ihtl
    rw [ihhd] at h₁
    cases hhd : SymCC.compile hd.snd εnv <;> simp [hhd] at h₁ h₂
    case error e' => simp [← h₁, ← h₂]
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
Lemma pulled out from the below `mutual` block so that we can prove it on its own by induction
without worrying about making the `mutual` block's termination proof even more complicated
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
  case nil => simp [List.mapM_nil, pure, Except.pure] at h₁ h₂ ; simp [h₁, h₂]
  case cons hd tl =>
    simp [List.mapM_cons, Functor.map, Except.map] at h₁ h₂
    rw [ih _ (by simp)] at h₁
    simp_do_let SymCC.compile hd εnv at h₁ ; rename_i hhd
    case ok t =>
    simp [hhd] at h₂
    split at h₁ <;> simp at h₁
    rename_i restl htl₁
    subst ts₁
    split at h₂ <;> simp at h₂
    rename_i tstl htl₂
    subst ts₂
    have ⟨htemp, ih'⟩ := both_lists_ok_then_elts_correspond htl₁ htl₂ (by
      intro x hx
      apply ih x (by simp [hx])
    )
    subst tstl
    simp [List.map_cons, ih']

/--
Lemma pulled out from the below `mutual` block so that we can prove it on its own by induction
without worrying about making the `mutual` block's termination proof even more complicated
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
  case nil => simp [List.mapM_nil, pure, Except.pure] at h₁ h₂ ; simp [h₁, h₂]
  case cons hd tl =>
    simp [List.mapM_cons, Functor.map, Except.map] at h₁ h₂
    rw [ih _ (by simp)] at h₁
    simp_do_let compile hd.snd εnv at h₁ ; rename_i hhd
    case ok t =>
    simp [hhd] at h₂
    split at h₁ <;> simp at h₁
    rename_i restl htl₁
    subst ts₁
    split at h₂ <;> simp at h₂
    rename_i tstl htl₂
    subst ts₂
    have ⟨htemp, ih'⟩ := both_lists_pairs_ok_then_elts_correspond htl₁ htl₂ (by
      intro x hx
      apply ih x (by simp [hx])
    )
    subst tstl
    simp [List.map_cons, ih']

mutual

/--
Correctness theorem for `Opt.compile` -- `lit` case
-/
theorem Opt.compile.correctness.lit (p : Prim) (εnv : SymEnv) :
  Opt.compile (.lit p) εnv = (do
    let term ← SymCC.compile (.lit p) εnv
    let footprint := footprint (.lit p) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  cases p <;> simp [Opt.compilePrim, SymCC.compilePrim, footprint.ofEntity, SymCC.compile, EmptyCollection.emptyCollection, Factory.someOf, TermType.isOptionEntityType, Term.typeOf, TermPrim.typeOf]
  case entityUID uid => split <;> simp [Term.typeOf, TermPrim.typeOf]

/--
Correctness theorem for `Opt.compile` -- `var` case
-/
theorem Opt.compile.correctness.var (v : Var) (εnv : SymEnv) :
  Opt.compile (.var v) εnv = (do
    let term ← SymCC.compile (.var v) εnv
    let footprint := footprint (.var v) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  cases v <;> simp [Opt.compileVar, SymCC.compileVar, footprint.ofEntity, SymCC.compile, EmptyCollection.emptyCollection, Factory.someOf, TermType.isEntityType, TermType.isOptionEntityType]
  case principal | action | resource => split <;> simp [Term.typeOf, *]
  case context =>
    split <;> rename_i h
    · simp [Term.typeOf, TermType.isRecordType] at *
      split at h <;> simp_all
    · simp

/--
Correctness theorem for `Opt.compile` -- `ite` case
-/
theorem Opt.compile.correctness.ite (x₁ x₂ x₃ : Expr) (εnv : SymEnv) :
  Opt.compile (.ite x₁ x₂ x₃) εnv = (do
    let term ← SymCC.compile (.ite x₁ x₂ x₃) εnv
    let footprint := footprint (.ite x₁ x₂ x₃) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [Opt.compile.correctness x₁ εnv, Opt.compile.correctness x₂ εnv, Opt.compile.correctness x₃ εnv]
  simp [Opt.compileIf, SymCC.compileIf, footprint.ofBranch]
  cases h₁ : SymCC.compile x₁ εnv <;> simp
  case ok t₁ =>
    split <;> simp
    cases h₂ : SymCC.compile x₂ εnv <;> simp_all
    case ok t₁ _ _ t₂ _ _ ht₁ =>
      cases h₃ : SymCC.compile x₃ εnv <;> simp_all
      case ok t₃ => split <;> simp
termination_by 1 + 2 * sizeOf x₁ + 2 * sizeOf x₂ + 2 * sizeOf x₃
decreasing_by all_goals {
  have : ∀ x : Expr, sizeOf x > 0 := by
    intro x ; cases x <;> simp [sizeOf, Expr._sizeOf_1] <;> omega
  have hx₁ := this x₁
  have hx₂ := this x₂
  have hx₃ := this x₃
  omega
}

/--
Correctness theorem for `Opt.compile` -- `and` and `or` cases
-/
theorem Opt.compile.correctness.andor (x₁ x₂ : Expr) (εnv : SymEnv) :
  Opt.compile (.and x₁ x₂) εnv = (do
    let term ← SymCC.compile (.and x₁ x₂) εnv
    let footprint := footprint (.and x₁ x₂) εnv
    .ok { term, footprint }
  )
  ∧
  Opt.compile (.or x₁ x₂) εnv = (do
    let term ← SymCC.compile (.or x₁ x₂) εnv
    let footprint := footprint (.or x₁ x₂) εnv
    .ok { term, footprint }
  )
:= by
  constructor
  all_goals {
    simp [Opt.compile, SymCC.compile, footprint]
    rw [Opt.compile.correctness x₁ εnv, Opt.compile.correctness x₂ εnv]
    simp [Opt.compileAnd, SymCC.compileAnd, Opt.compileOr, SymCC.compileOr, footprint.ofBranch, EmptyCollection.emptyCollection]
    cases h₁ : SymCC.compile x₁ εnv <;> simp only [Except.bind_ok, Except.bind_err]
    case ok t₁ =>
      cases h₂ : SymCC.compile x₂ εnv <;> simp only [Except.bind_ok, Except.bind_err]
      case error e => split <;> simp [*]
      case ok t₂ =>
        split <;> simp [*]
        split <;> simp at *
        split <;> simp [*]
        first
        | rw [Data.Set.union_empty_right (Data.Set.union_wf _ _)]
        | rw [Data.Set.union_empty_right (footprint_wf _ _)]
  }
termination_by 1 + 2 * sizeOf x₁ + 2 * sizeOf x₂

/--
Correctness theorem for `Opt.compile` -- `unaryApp` case
-/
theorem Opt.compile.correctness.unaryApp (op : UnaryOp) (x : Expr) (εnv : SymEnv) :
  Opt.compile (.unaryApp op x) εnv = (do
    let term ← SymCC.compile (.unaryApp op x) εnv
    let footprint := footprint (.unaryApp op x) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [Opt.compile.correctness x εnv]
  cases h₁ : SymCC.compile x εnv <;> simp
  rw [Opt.compileApp₁.correctness op]
  simp [Opt.CompileResult.mapTerm]
termination_by 1 + 2 * sizeOf x

/--
Correctness theorem for `Opt.compile` -- `binaryApp` case
-/
theorem Opt.compile.correctness.binaryApp (op : BinaryOp) (x₁ x₂ : Expr) (εnv : SymEnv) :
  Opt.compile (.binaryApp op x₁ x₂) εnv = (do
    let term ← SymCC.compile (.binaryApp op x₁ x₂) εnv
    let footprint := footprint (.binaryApp op x₁ x₂) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [Opt.compile.correctness x₁ εnv, Opt.compile.correctness x₂ εnv]
  cases h₁ : SymCC.compile x₁ εnv <;> simp
  case ok t₁ =>
    cases h₂ : SymCC.compile x₂ εnv <;> simp
    case ok t₂ =>
      rw [Opt.compileApp₂.correctness op]
      simp [Opt.CompileResult.mapTerm]
      cases h : SymCC.compileApp₂ op (Factory.option.get t₁) (Factory.option.get t₂) εnv.entities <;> simp
      case ok t =>
        rw [Opt.directFootprint.correctness (t := Factory.ifSome t₁ (Factory.ifSome t₂ t)) (εnv := εnv) (x := .binaryApp op x₁ x₂)]
        · conv => rhs ; rw [Data.Set.union_assoc, Data.Set.union_comm]
        · -- here we have to show that the `t` and `x` arguments we chose for `Opt.directFootprint.correctness` in the `rw` above correspond to each other correctly
          simp [SymCC.compile, h₁, h₂, h]
termination_by 1 + 2 * sizeOf x₁ + 2 * sizeOf x₂
decreasing_by all_goals {
  have : ∀ x : Expr, sizeOf x > 0 := by
    intro x ; cases x <;> simp [sizeOf, Expr._sizeOf_1] <;> omega
  have hx₁ := this x₁
  have hx₂ := this x₂
  omega
}

/--
Correctness theorem for `Opt.compile` -- `getAttr` case
-/
theorem Opt.compile.correctness.getAttr (expr : Expr) (attr : Attr) (εnv : SymEnv) :
  Opt.compile (.getAttr expr attr) εnv = (do
    let term ← SymCC.compile (.getAttr expr attr) εnv
    let footprint := footprint (.getAttr expr attr) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [Opt.compile.correctness expr εnv]
  cases h₁ : SymCC.compile expr εnv <;> simp
  case ok t =>
    rw [Opt.compileGetAttr.correctness]
    simp only [Opt.CompileResult.mapTerm, bind_assoc, Except.bind_ok]
    simp_do_let compileGetAttr (Factory.option.get t) attr εnv.entities ; rename_i t' h₂
    simp only [Except.ok.injEq, Opt.CompileResult.mk.injEq, true_and]
    rw [Opt.directFootprint.correctness (t := Factory.ifSome t t') (x := .getAttr expr attr) (εnv := εnv)]
    · apply Data.Set.union_comm
    · -- here we have to show that the `t` and `x` arguments we chose for `Opt.directFootprint.correctness` in the `rw` above correspond to each other correctly
      simp [SymCC.compile, h₁, h₂]
termination_by 1 + 2 * sizeOf expr

/--
Correctness theorem for `Opt.compile` -- `hasAttr` case
-/
theorem Opt.compile.correctness.hasAttr (expr : Expr) (attr : Attr) (εnv : SymEnv) :
  Opt.compile (.hasAttr expr attr) εnv = (do
    let term ← SymCC.compile (.hasAttr expr attr) εnv
    let footprint := footprint (.hasAttr expr attr) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [Opt.compile.correctness expr εnv]
  cases h₁ : SymCC.compile expr εnv <;> simp
  case ok t =>
    rw [Opt.compileHasAttr.correctness]
    simp only [Opt.CompileResult.mapTerm, bind_assoc, Except.bind_ok]
termination_by 1 + 2 * sizeOf expr

/--
Correctness theorem for `Opt.compile` -- `set` case
-/
theorem Opt.compile.correctness.set (ls : List Expr) (εnv : SymEnv) :
  Opt.compile (.set ls) εnv = (do
    let term ← SymCC.compile (.set ls) εnv
    let footprint := footprint (.set ls) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [List.mapM₁_eq_mapM (Opt.compile · εnv), List.mapM₁_eq_mapM (SymCC.compile · εnv)]
  rw [List.mapUnion_attach (footprint · εnv)]
  simp_do_let ls.mapM (Opt.compile · εnv) <;> rename_i hmap₁
  <;> simp_do_let ls.mapM (SymCC.compile · εnv) <;> rename_i hmap₂
  case error.error e₁ e₂ =>
    simp only [Except.error.injEq]
    apply both_lists_error_then_errors_same hmap₁ hmap₂
    intro x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    exact Opt.compile.correctness x εnv
  case ok.error ts e =>
    exfalso
    replace ⟨x, hx, hmap₂⟩ := List.mapM_error_implies_exists_error hmap₂
    replace ⟨t, ht, hmap₁⟩ := List.mapM_ok_implies_all_ok hmap₁ x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    rw [Opt.compile.correctness] at hmap₁
    simp [hmap₂] at hmap₁
  case error.ok e ts =>
    exfalso
    replace ⟨x, hx, hmap₁⟩ := List.mapM_error_implies_exists_error hmap₁
    replace ⟨t, ht, hmap₂⟩ := List.mapM_ok_implies_all_ok hmap₂ x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    rw [Opt.compile.correctness] at hmap₁
    simp [hmap₂] at hmap₁
  case ok.ok ts₁ ts₂ =>
    rw [Opt.compileSet.correctness]
    suffices
      SymCC.compileSet (List.map Opt.CompileResult.term ts₁) = SymCC.compileSet ts₂
      ∧ ts₁.mapUnion Opt.CompileResult.footprint = ls.mapUnion (footprint · εnv)
      by simp [this]
    have ⟨h₁, h₂⟩ := both_lists_ok_then_elts_correspond hmap₁ hmap₂ (by
      intro x hx
      have := List.sizeOf_lt_of_mem hx -- for termination
      exact Opt.compile.correctness x εnv
    )
    subst ts₂ ; simp
    apply Data.Set.map_eqv_implies_mapUnion_eq (by simp [h₂, List.Equiv.refl])
termination_by 1 + 2 * sizeOf ls

/--
Correctness theorem for `Opt.compile` -- `record` case
-/
theorem Opt.compile.correctness.record (m : List (Attr × Expr)) (εnv : SymEnv) :
  Opt.compile (.record m) εnv = (do
    let term ← SymCC.compile (.record m) εnv
    let footprint := footprint (.record m) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  simp only [List.mapM₂_eq_mapM (λ x => do Except.ok (x.fst, ← Opt.compile x.snd εnv)) m]
  simp only [List.mapM₂_eq_mapM (λ x => do Except.ok (x.fst, ← SymCC.compile x.snd εnv)) m]
  rw [List.mapUnion_attach₂ (λ x => footprint x.snd εnv)]
  simp_do_let m.mapM (m := SymCC.Result) _ <;> rename_i hmap₁
  <;> simp_do_let m.mapM (m := SymCC.Result) _ <;> rename_i hmap₂
  case error.error e₁ e₂ =>
    simp only [Except.error.injEq]
    apply both_lists_pairs_error_then_errors_same hmap₁ hmap₂
    intro pair hpair
    have := List.sizeOf_lt_of_mem hpair -- for termination
    have : sizeOf pair.snd < sizeOf pair := by simp [sizeOf, Prod._sizeOf_1] ; omega
    exact Opt.compile.correctness pair.snd εnv
  case ok.error ts e =>
    exfalso
    replace ⟨x, hx, hmap₂⟩ := List.mapM_error_implies_exists_error hmap₂
    replace ⟨t, ht, hmap₁⟩ := List.mapM_ok_implies_all_ok hmap₁ x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    have : sizeOf x.snd < sizeOf x := by simp [sizeOf, Prod._sizeOf_1] ; omega
    rw [Opt.compile.correctness] at hmap₁
    simp [do_error] at hmap₂
    simp [hmap₂] at hmap₁
  case error.ok e ts =>
    exfalso
    replace ⟨x, hx, hmap₁⟩ := List.mapM_error_implies_exists_error hmap₁
    replace ⟨t, ht, hmap₂⟩ := List.mapM_ok_implies_all_ok hmap₂ x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    have : sizeOf x.snd < sizeOf x := by simp [sizeOf, Prod._sizeOf_1] ; omega
    rw [Opt.compile.correctness] at hmap₁
    simp [do_error] at hmap₁
    simp [hmap₁] at hmap₂
  case ok.ok ts₁ ts₂ =>
    rw [Opt.compileRecord.correctness]
    simp only [Except.ok.injEq, Opt.CompileResult.mk.injEq]
    have ⟨h₁, h₂⟩ := both_lists_pairs_ok_then_elts_correspond hmap₁ hmap₂ (by
      intro pair hpair
      have := List.sizeOf_lt_of_mem hpair -- for termination
      have : sizeOf pair.snd < sizeOf pair := by simp [sizeOf, Prod._sizeOf_1] ; omega
      exact Opt.compile.correctness pair.snd εnv
    )
    subst ts₂ ; simp
    apply Data.Set.map_eqv_implies_mapUnion_eq (by simp [h₂, List.Equiv.refl])
termination_by 1 + 2 * sizeOf m

/--
Correctness theorem for `Opt.compile` -- `call` case
-/
theorem Opt.compile.correctness.call (xfn : ExtFun) (args : List Expr) (εnv : SymEnv) :
  Opt.compile (.call xfn args) εnv = (do
    let term ← SymCC.compile (.call xfn args) εnv
    let footprint := footprint (.call xfn args) εnv
    .ok { term, footprint }
  )
:= by
  simp [Opt.compile, SymCC.compile, footprint]
  rw [List.mapM₁_eq_mapM (Opt.compile · εnv), List.mapM₁_eq_mapM (SymCC.compile · εnv)]
  rw [List.mapUnion_attach (footprint · εnv)]
  simp_do_let args.mapM (Opt.compile · εnv) <;> rename_i hmap₁
  <;> simp_do_let args.mapM (SymCC.compile · εnv) <;> rename_i hmap₂
  case error.error e₁ e₂ =>
    simp only [Except.error.injEq]
    apply both_lists_error_then_errors_same hmap₁ hmap₂
    intro x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    exact Opt.compile.correctness x εnv
  case ok.error ts e =>
    exfalso
    replace ⟨x, hx, hmap₂⟩ := List.mapM_error_implies_exists_error hmap₂
    replace ⟨t, ht, hmap₁⟩ := List.mapM_ok_implies_all_ok hmap₁ x hx
    have := List.sizeOf_lt_of_mem hx -- for termination
    rw [Opt.compile.correctness] at hmap₁
    simp [hmap₂] at hmap₁
  case error.ok e ts =>
    exfalso
    replace ⟨x, hx, hmap₁⟩ := List.mapM_error_implies_exists_error hmap₁
    replace ⟨t, ht, hmap₂⟩ := List.mapM_ok_implies_all_ok hmap₂ x hx
    have hterm := List.sizeOf_lt_of_mem hx -- for termination
    rw [Opt.compile.correctness] at hmap₁
    simp [hmap₂] at hmap₁
  case ok.ok ts₁ ts₂ =>
    rw [Opt.compileCall.correctness]
    · suffices
        SymCC.compileCall xfn (List.map Opt.CompileResult.term ts₁) = SymCC.compileCall xfn ts₂
        ∧ ts₁.mapUnion Opt.CompileResult.footprint = args.mapUnion (footprint · εnv)
        by simp [this]
      have ⟨h₁, h₂⟩ := both_lists_ok_then_elts_correspond hmap₁ hmap₂ (by
        intro x hx
        have := List.sizeOf_lt_of_mem hx -- for termination
        exact Opt.compile.correctness x εnv
      )
      subst ts₂ ; simp
      apply Data.Set.map_eqv_implies_mapUnion_eq (by simp [h₂, List.Equiv.refl])
    case hwf =>
      intro res hres
      have ⟨arg, harg, h₁⟩ := List.mapM_ok_implies_all_from_ok hmap₁ res hres
      exact Opt.compile_footprint_wf h₁
termination_by 1 + 2 * sizeOf args

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
    first
    | exact (Opt.compile.correctness.andor x₁ x₂ εnv).left
    | exact (Opt.compile.correctness.andor x₁ x₂ εnv).right
  case ite x₁ x₂ x₃       => exact Opt.compile.correctness.ite x₁ x₂ x₃ εnv
  case unaryApp op x₁     => exact Opt.compile.correctness.unaryApp op x₁ εnv
  case binaryApp op x₁ x₂ => exact Opt.compile.correctness.binaryApp op x₁ x₂ εnv
  case getAttr x₁ attr    => exact Opt.compile.correctness.getAttr x₁ attr εnv
  case hasAttr x₁ attr    => exact Opt.compile.correctness.hasAttr x₁ attr εnv
  case set xs             => exact Opt.compile.correctness.set xs εnv
  case record m           => exact Opt.compile.correctness.record m εnv
  case call xfn args      => exact Opt.compile.correctness.call xfn args εnv
termination_by 2 * sizeOf x

end

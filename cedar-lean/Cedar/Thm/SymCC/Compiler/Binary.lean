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

import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

/-!
This file proves the compilation lemmas for `.binaryApp` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory


private theorem interpret_compileInₑ.isEq {t₁ t₂: Term} {εs : SymEntities} {I : Interpretation}
  (hI : Interpretation.WellFormed I εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hwl₁ : Term.WellFormed εs (Term.interpret I t₁) ∧ Term.typeOf (Term.interpret I t₁) = Term.typeOf t₁)
  (hwl₂ : Term.WellFormed εs (Term.interpret I t₂) ∧ Term.typeOf (Term.interpret I t₂) = Term.typeOf t₂) :
  Term.interpret I (compileInₑ.isEq t₁ t₂) =
  compileInₑ.isEq (Term.interpret I t₁) (Term.interpret I t₂)
:= by
  simp only [compileInₑ.isEq]
  split
  case isTrue heq =>
    simp only [hwl₁, hwl₂, heq, interpret_eq hI hwφ₁ hwφ₂, ite_true]
  case isFalse heq =>
    simp only [hwl₁, hwl₂, heq, interpret_term_prim, ite_false]

private theorem interpret_compileInₑ.isIn {t₁ t₂: Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} {I : Interpretation}
  (hwε : SymEntities.WellFormed εs)
  (hI : Interpretation.WellFormed I εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hty₁ : Term.typeOf t₁ = TermType.entity ety₁) :
  Term.interpret I (compileInₑ.isIn t₁ t₂ (SymEntities.ancestorsOfType εs ety₁ ety₂)) =
  compileInₑ.isIn (Term.interpret I t₁) (Term.interpret I t₂) (SymEntities.ancestorsOfType (SymEntities.interpret I εs) ety₁ ety₂)
:= by
  simp only [compileInₑ.isIn]
  split
  case h_1 ancs heq =>
    have hwf := wf_εs_implies_wf_ancs hwε heq
    rw [← hwf.right.left] at hty₁
    have hwa := wf_app hwφ₁ hty₁ hwf.left
    simp only [interpret_entities_ancestorsOfType_some heq,
      interpret_set_member hwφ₂ hwa.left,
      interpret_app hI hwφ₁ hwf.left hty₁]
  case h_2 heq =>
    simp only [interpret_term_prim, interpret_entities_ancestorsOfType_none heq]

theorem interpret_compileInₑ {t₁ t₂: Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} {I : Interpretation}
  (hwε : SymEntities.WellFormed εs)
  (hI : Interpretation.WellFormed I εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hwl₁ : Term.WellFormed εs (Term.interpret I t₁) ∧ Term.typeOf (Term.interpret I t₁) = Term.typeOf t₁)
  (hwl₂ : Term.WellFormed εs (Term.interpret I t₂) ∧ Term.typeOf (Term.interpret I t₂) = Term.typeOf t₂)
  (hty₁ : Term.typeOf t₁ = TermType.entity ety₁)
  (hty₂ : Term.typeOf t₂ = TermType.entity ety₂) :
  Term.interpret I (compileInₑ t₁ t₂ (SymEntities.ancestorsOfType εs ety₁ ety₂)) =
  compileInₑ (Term.interpret I t₁) (Term.interpret I t₂) (SymEntities.ancestorsOfType (SymEntities.interpret I εs) ety₁ ety₂)
:= by
  have hweq := compileInₑ.isEq_wf hwφ₁ hwφ₂
  have hwin := compileInₑ.isIn_wf hwε hwφ₁ hty₁ hwφ₂ hty₂ rfl
  simp only [compileInₑ_def,
    interpret_or hI hweq.left hwin.left hweq.right hwin.right,
    interpret_compileInₑ.isEq hI hwφ₁ hwφ₂ hwl₁ hwl₂,
    interpret_compileInₑ.isIn hwε hI hwφ₁ hwφ₂ hty₁]

private theorem interpret_compileInₛ.isIn₁ {t₁ t₂: Term} {εs : SymEntities} {I : Interpretation}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hwl₁ : Term.WellFormed εs (Term.interpret I t₁) ∧ Term.typeOf (Term.interpret I t₁) = Term.typeOf t₁)
  (hwl₂ : Term.WellFormed εs (Term.interpret I t₂) ∧ Term.typeOf (Term.interpret I t₂) = Term.typeOf t₂) :
  Term.interpret I (compileInₛ.isIn₁ t₁ t₂) =
  compileInₛ.isIn₁ (Term.interpret I t₁) (Term.interpret I t₂)
:= by
  simp only [compileInₛ.isIn₁]
  split
  case isTrue heq =>
    simp only [hwl₁, hwl₂, heq, interpret_set_member hwφ₁ hwφ₂, ite_true]
  case isFalse heq =>
    simp only [hwl₁, hwl₂, heq, interpret_term_prim, ite_false]

private theorem interpret_compileInₛ.isIn₂ {t₁ t₂: Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} {I : Interpretation}
  (hwε : SymEntities.WellFormed εs)
  (hI : Interpretation.WellFormed I εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hty₁ : Term.typeOf t₁ = .entity ety₁)
  (hty₂ : Term.typeOf t₂ = .set (.entity ety₂)) :
  Term.interpret I (compileInₛ.isIn₂ t₁ t₂ (SymEntities.ancestorsOfType εs ety₁ ety₂)) =
  compileInₛ.isIn₂ (Term.interpret I t₁) (Term.interpret I t₂) (SymEntities.ancestorsOfType (SymEntities.interpret I εs) ety₁ ety₂)
:= by
  simp only [compileInₛ.isIn₂]
  split
  case h_1 ancs heq =>
    have hwf := wf_εs_implies_wf_ancs hwε heq
    rw [← hwf.right.left] at hty₁
    have hwa := wf_app hwφ₁ hty₁ hwf.left
    simp only [hwf.right.right] at hwa
    simp only [interpret_entities_ancestorsOfType_some heq,
      interpret_set_intersects hI hwφ₂ hwa.left hty₂ hwa.right,
      interpret_app hI hwφ₁ hwf.left hty₁]
  case h_2 heq =>
    simp only [interpret_term_prim, interpret_entities_ancestorsOfType_none heq]

theorem interpret_compileInₛ {t₁ t₂: Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} {I : Interpretation}
  (hwε : SymEntities.WellFormed εs)
  (hI : Interpretation.WellFormed I εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hwl₁ : Term.WellFormed εs (Term.interpret I t₁) ∧ Term.typeOf (Term.interpret I t₁) = Term.typeOf t₁)
  (hwl₂ : Term.WellFormed εs (Term.interpret I t₂) ∧ Term.typeOf (Term.interpret I t₂) = Term.typeOf t₂)
  (hty₁ : Term.typeOf t₁ = .entity ety₁)
  (hty₂ : Term.typeOf t₂ = .set (.entity ety₂)) :
  Term.interpret I (compileInₛ t₁ t₂ (SymEntities.ancestorsOfType εs ety₁ ety₂)) =
  compileInₛ (Term.interpret I t₁) (Term.interpret I t₂) (SymEntities.ancestorsOfType (SymEntities.interpret I εs) ety₁ ety₂)
:= by
  have hwin₁ := compileInₛ.isIn₁_wf hwφ₁ hwφ₂
  have hwin₂ := compileInₛ.isIn₂_wf hwε hwφ₁ hty₁ hwφ₂ hty₂ rfl
  simp only [compileInₛ_def,
    interpret_or hI hwin₁.left hwin₂.left hwin₁.right hwin₂.right,
    interpret_compileInₛ.isIn₁ hwφ₁ hwφ₂ hwl₁ hwl₂,
    interpret_compileInₛ.isIn₂ hwε hI hwφ₁ hwφ₂ hty₁ hty₂]

theorem interpret_hasTag {t₁ t₂ : Term} {ety : EntityType} {εs : SymEntities} {τs : SymTags} {I : Interpretation}
  (hwτ : τs.WellFormed εs ety)
  (hI : I.WellFormed εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hty₁ : t₁.typeOf = TermType.entity ety) :
  (SymTags.interpret I τs).hasTag (Term.interpret I t₁) (Term.interpret I t₂) = Term.interpret I (τs.hasTag t₁ t₂)
:= by
  replace ⟨hwf, harg, hout, hwτ⟩ := hwτ
  rw [← harg] at hty₁
  have happ := wf_app hwφ₁ hty₁ hwf
  simp only [SymTags.hasTag, SymTags.interpret,
    interpret_set_member hwφ₂ happ.left, interpret_app hI hwφ₁ hwf hty₁]

theorem interpret_getTag {t₁ t₂ : Term} {ety : EntityType} {εs : SymEntities} {τs : SymTags} {I : Interpretation}
  (hwτ : τs.WellFormed εs ety)
  (hI : I.WellFormed εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hty₁ : t₁.typeOf = TermType.entity ety)
  (hty₂ : t₂.typeOf = .string) :
  (SymTags.interpret I τs).getTag (Term.interpret I t₁) (Term.interpret I t₂) = Term.interpret I (τs.getTag t₁ t₂)
:= by
  have hhas := wf_tags_hasTag hwτ hwφ₁ hwφ₂ hty₁ hty₂
  have hget := wf_tags_getTag! hwτ hwφ₁ hwφ₂ hty₁ hty₂
  simp only [SymTags.getTag, interpret_hasTag hwτ hI hwφ₁ hwφ₂ hty₁,
    interpret_ifTrue hI hhas.left hhas.right hget.left]
  have ⟨hwf, harg, _⟩ := hwτ.right.right.right
  have hto := wf_tagOf hwφ₁ hwφ₂ hty₁ hty₂
  rw [← harg] at hto
  simp only [SymTags.getTag!, SymTags.interpret, interpret_app hI hto.left hwf hto.right,
    interpret_tagOf]

private theorem interpret_compileApp₂ {op₂ : BinaryOp} {t t₁ t₂: Term} {εs : SymEntities} {I : Interpretation}
  (hwε  : εs.WellFormed)
  (hI   : Interpretation.WellFormed I εs)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (hok  : compileApp₂ op₂ t₁ t₂ εs = Except.ok t) :
  compileApp₂ op₂ (t₁.interpret I) (t₂.interpret I) (εs.interpret I) = .ok (t.interpret I)
:= by
  have hwl₁ := interpret_term_wf hI hwφ₁
  have hwl₂ := interpret_term_wf hI hwφ₂
  cases op₂
  case eq =>
    replace hok := compileApp₂_eq_ok_implies hok
    rcases hok with ⟨hok, ht⟩ | ⟨hok, ht⟩ <;>
    simp only [ht, compileApp₂, hwl₁, hwl₂, hok, someOf, interpret_term_some,
      interpret_eq hI hwφ₁ hwφ₂, interpret_term_prim,
      Term.some.injEq, Except.bind_ok, Except.ok.injEq, ite_true, ite_false, reduceCtorEq]
  case less =>
    rcases compileApp₂_less_ok_implies hok with hok | hok | hok <;>
      simp [compileApp₂, hwl₁, hwl₂, hok, someOf, interpret_term_some,
        interpret_ext_duration_val, interpret_ext_datetime_val, interpret_bvslt]
  case lessEq =>
    rcases compileApp₂_lessEq_ok_implies hok with hok | hok | hok <;>
      simp only [compileApp₂, hwl₁, hwl₂, hok, someOf, interpret_term_some,
        interpret_ext_duration_val, interpret_ext_datetime_val, interpret_bvsle]
  case add =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_add_ok_implies hok
    have hwg := wf_bvsaddo hwφ₁ hwφ₂ hty₁ hty₂
    have hwt := wf_bvadd hwφ₁ hwφ₂ hty₁ hty₂
    simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some,
      interpret_ifFalse hI hwg.left hwg.right hwt.left, interpret_bvsaddo, interpret_bvadd]
  case sub =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_sub_ok_implies hok
    have hwg := wf_bvssubo hwφ₁ hwφ₂ hty₁ hty₂
    have hwt := wf_bvsub hwφ₁ hwφ₂ hty₁ hty₂
    simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some,
      interpret_ifFalse hI hwg.left hwg.right hwt.left, interpret_bvssubo, interpret_bvsub]
  case mul =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_mul_ok_implies hok
    have hwg := wf_bvsmulo hwφ₁ hwφ₂ hty₁ hty₂
    have hwt := wf_bvmul hwφ₁ hwφ₂ hty₁ hty₂
    simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some,
      interpret_ifFalse hI hwg.left hwg.right hwt.left, interpret_bvsmulo, interpret_bvmul]
  case contains =>
    replace ⟨hty, hok⟩ := compileApp₂_contains_ok_implies hok
    simp only [compileApp₂, hwl₁, hwl₂, hty, hok, someOf, interpret_term_some, interpret_set_member hwφ₂ hwφ₁, ite_true]
  case containsAll =>
    replace ⟨_, hty₁, hty₂, hok⟩ := compileApp₂_containsAll_ok_implies hok
    simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some, interpret_set_subset hwφ₂ hwφ₁, ite_true]
  case containsAny =>
    replace ⟨_, hty₁, hty₂, hok⟩ := compileApp₂_containsAny_ok_implies hok
    simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some, interpret_set_intersects hI hwφ₁ hwφ₂ hty₁ hty₂, ite_true]
  case mem =>
    replace ⟨ety₁, ety₂, hty₁, hok⟩ := compileApp₂_mem_ok_implies hok
    rcases hok with ⟨hty₂, hok⟩ | ⟨hty₂, hok⟩
    case inl =>
      simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some,
        interpret_compileInₑ hwε hI hwφ₁ hwφ₂ hwl₁ hwl₂ hty₁ hty₂,
        Except.ok.injEq, Term.some.injEq]
    case inr =>
      simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, hok, someOf, interpret_term_some,
        interpret_compileInₛ hwε hI hwφ₁ hwφ₂ hwl₁ hwl₂ hty₁ hty₂,
        Except.ok.injEq, Term.some.injEq]
  case hasTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    simp only [compileApp₂, hwl₁, hty₁, hwl₂, hty₂, compileHasTag]
    rcases hok with ⟨hτs, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [interpret_entities_tags_none hτs, someOf, interpret_term_some,
      interpret_term_prim]
    · simp only [interpret_entities_tags_some hτs, Option.pure_def, Option.bind_some_fun, someOf,
      interpret_hasTag (wf_εs_implies_wf_tags hwε hτs) hI hwφ₁ hwφ₂ hty₁, interpret_term_some]
  case getTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    simp only [compileApp₂, hwl₁, hwl₂, hty₁, hty₂, compileGetTag,
      interpret_entities_tags_some hτs,
      interpret_getTag (wf_εs_implies_wf_tags hwε hτs) hI hwφ₁ hwφ₂ hty₁ hty₂,
      Option.pure_def, Option.bind_some_fun]

private theorem compileApp₂_ok_typeOf {op₂ : BinaryOp} {t₁ t₁' t₂ t₂' t₃ : Term} {εs : SymEntities} (I : Interpretation)
  (hty₁ : t₁.typeOf = t₁'.typeOf)
  (hty₂ : t₂.typeOf = t₂'.typeOf)
  (hok  : compileApp₂ op₂ t₁ t₂ εs = Except.ok t₃)  :
  ∃ t₃', compileApp₂ op₂ t₁' t₂' (εs.interpret I) = Except.ok t₃'
:= by
  cases op₂
  case eq =>
    have hok := compileApp₂_eq_ok_implies hok
    rcases hok with ⟨hty, _⟩ | ⟨hty, _⟩ <;>
    simp only [compileApp₂, ← hty₁, ← hty₂, hty, Except.bind_ok, ite_true, ite_false, Except.ok.injEq, exists_eq', reduceCtorEq]
  case contains =>
    have ⟨hty, _⟩ := compileApp₂_contains_ok_implies hok
    simp only [compileApp₂, ← hty₁, ← hty₂, hty, ite_true, Except.ok.injEq, exists_eq']
  case' containsAll => have ⟨_, hty₁', hty₂', _⟩ := compileApp₂_containsAll_ok_implies hok
  case' containsAny => have ⟨_, hty₁', hty₂', _⟩ := compileApp₂_containsAny_ok_implies hok
  case' less =>
    rcases compileApp₂_less_ok_implies hok with ⟨hty₁', hty₂', _⟩ | ⟨hty₁', hty₂', _⟩ | ⟨hty₁', hty₂', _⟩
  case' lessEq =>
    rcases compileApp₂_lessEq_ok_implies hok with ⟨hty₁', hty₂', _⟩ | ⟨hty₁', hty₂', _⟩ | ⟨hty₁', hty₂', _⟩
  case' add => have ⟨hty₁', hty₂', _⟩ := compileApp₂_add_ok_implies hok
  case' sub => have ⟨hty₁', hty₂', _⟩ := compileApp₂_sub_ok_implies hok
  case' mul => have ⟨hty₁', hty₂', _⟩ := compileApp₂_mul_ok_implies hok
  case' mem =>
    replace ⟨_, _, hty₁', hok⟩ := compileApp₂_mem_ok_implies hok
    rcases hok with ⟨hty₂', _⟩ | ⟨hty₂', _⟩
  case hasTag =>
    have ⟨ety, hty₁', hty₂', hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    simp only [compileApp₂, ← hty₁, hty₁', ← hty₂, hty₂', compileHasTag]
    rcases hok with ⟨hτs, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [interpret_entities_tags_none hτs, Except.ok.injEq, exists_eq']
    · simp only [interpret_entities_tags_some hτs, Option.pure_def, Option.bind_some_fun,
      Except.ok.injEq, exists_eq']
  case getTag =>
    replace ⟨ety, hty₁', hty₂', hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    simp only [compileApp₂, ← hty₁, hty₁', ← hty₂, hty₂', compileGetTag,
      interpret_entities_tags_some hτs, Option.pure_def, Option.bind_some_fun, Except.ok.injEq,
      exists_eq']
  all_goals {
    simp only [compileApp₂, ← hty₁, ← hty₂, hty₁', hty₂', ite_true, Except.ok.injEq, exists_eq']
  }

private theorem compileApp₂_ok_typeOf_eq {op₂ : BinaryOp} {t₁ t₁' t₂ t₂' t₃ t₃' : Term} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : t₁.WellFormed εs)
  (hw₂  : t₂.WellFormed εs)
  (hw₁' : t₁'.WellFormed εs)
  (hw₂' : t₂'.WellFormed εs)
  (heq₁ : t₁.typeOf = t₁'.typeOf)
  (hok  : compileApp₂ op₂ t₁ t₂ εs = Except.ok t₃)
  (hok' : compileApp₂ op₂ t₁' t₂' εs = Except.ok t₃') :
  t₃'.typeOf = t₃.typeOf
:= by
  have h₁ := (compileApp₂_wf_types hwε hw₁ hw₂ hok).right
  have h₂ := (compileApp₂_wf_types hwε hw₁' hw₂' hok').right
  cases op₂ <;> simp only at h₁ h₂
  case getTag =>
    replace ⟨_, _, h₁⟩ := h₁
    replace ⟨_, _, h₂⟩ := h₂
    simp only [heq₁] at h₁
    simp only [h₁, TermType.prim.injEq, TermPrimType.entity.injEq] at h₂
    replace ⟨h₃, h₂⟩ := h₂
    subst h₃
    simp only [h₁, Option.some.injEq] at h₂
    replace ⟨h₃, h₂⟩ := h₂
    subst h₃
    simp only [h₂, h₁]
  all_goals {
    simp only [h₂, h₁]
  }

theorem compile_interpret_binaryApp {op₂ : BinaryOp} {x₁ x₂ : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.binaryApp op₂ x₁ x₂))
  (hok : compile (.binaryApp op₂ x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpret x₁)
  (ih₂ : CompileInterpret x₂) :
  compile (.binaryApp op₂ x₁ x₂) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compile_binaryApp_ok_implies hok
  subst ht
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_binaryApp_implies hwε
  ------
  replace ih₁ := ih₁ hI hwφ₁ hok₁
  replace ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok₁
  have hwo₁ := wf_option_get hwφ₁ hty₁
  have hwφ₁' := interpret_term_wfl hI hwφ₁
  rw [hty₁] at hwφ₁'
  have hwo₁' := wf_option_get hwφ₁'.left.left hwφ₁'.right
  rw [eq_comm, ← hwo₁.right] at hwo₁'
  ------
  replace ih₂ := ih₂ hI hwφ₂ hok₂
  replace ⟨hwφ₂, ty₂, hty₂⟩ := compile_wf hwφ₂ hok₂
  have hwo₂ := wf_option_get hwφ₂ hty₂
  have hwφ₂' := interpret_term_wfl hI hwφ₂
  rw [hty₂] at hwφ₂'
  have hwo₂' := wf_option_get hwφ₂'.left.left hwφ₂'.right
  rw [eq_comm, ← hwo₂.right] at hwo₂'
  -------
  simp only [compile, ih₁, ih₂, Except.bind_ok]
  have hi := interpret_compileApp₂ hwε.left.right hI hwo₁.left hwo₂.left hok
  simp_do_let (compileApp₂ op₂ (option.get (Term.interpret I t₁)) (option.get (Term.interpret I t₂)) (SymEnv.interpret I εnv).entities) <;>
  rename_i heq
  case error =>
    simp only [SymEnv.interpret] at heq
    have ⟨_, hok'⟩ := compileApp₂_ok_typeOf I hwo₁'.right hwo₂'.right hok
    simp only [heq, reduceCtorEq] at hok'
  case ok t₄ =>
    simp only [SymEnv.interpret] at heq
    replace hwε := hwε.left.right
    have ⟨hwφ₃, ty₃, hty₃⟩ := compileApp₂_wf hwε hwo₁.left hwo₂.left hok
    have hwφ₄ := wf_ifSome_option hwφ₂ hwφ₃ hty₃
    simp only [interpret_ifSome hI hwφ₁ hwφ₄.left, interpret_ifSome hI hwφ₂ hwφ₃, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁, interpret_option_get I hwφ₂ hty₂] at hi
    have hty₄ : Term.typeOf t₄ = TermType.option ty₃ := by
      rw [← hty₃, ← (interpret_term_wf hI hwφ₃).right]
      have hdom := interpret_entities_same_domain εnv.entities I
      have hty₅ : (option.get' I (Term.interpret I t₁)).typeOf = (option.get (Term.interpret I t₁)).typeOf := by
        simp only [wf_option_get' hI hwφ₁'.left.left hwφ₁'.right, ← hwo₁.right, ← hwo₁'.right]
      exact compileApp₂_ok_typeOf_eq (interpret_εntities_wf hwε hI)
        (wf_term_same_domain hdom (wf_option_get' hI hwφ₁'.left.left hwφ₁'.right).left)
        (wf_term_same_domain hdom (wf_option_get' hI hwφ₂'.left.left hwφ₂'.right).left)
        (wf_term_same_domain hdom hwo₁'.left)
        (wf_term_same_domain hdom hwo₂'.left)
        hty₅ hi heq
    rw [← (interpret_term_wf hI hwφ₃).right] at hty₃
    exact pe_ifSome_ok_get_eq_get'₂ I (compileApp₂ op₂ · · (SymEntities.interpret I εnv.entities))
      hwφ₁' hwφ₂' hty₃ hty₄ hi heq

private theorem compileApp₂_eq_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .eq t₁ t₂ εs = Except.ok t₃) :
  apply₂ .eq v₁ v₂ es ∼ t₃
:= by
  replace hok := compileApp₂_eq_ok_implies hok
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  simp only [apply₂]
  rcases hok with ⟨hty, hok⟩ | ⟨hty, hok⟩
  case inl =>
    subst hok
    replace hty := reducibleEq_ok_true_implies hty
    simp only [Same.same, SameResults, SameValues, pe_eq_lit hlit₁ hlit₂]
    cases hb : (t₁ == t₂)
    case false =>
      simp only [beq_eq_false_iff_ne, ne_eq] at hb
      simp only [Term.value?, TermPrim.value?, Option.some.injEq, Value.prim.injEq, Prim.bool.injEq]
      by_contra hc
      rw [eq_comm, Bool.not_eq_false] at hc
      simp only [BEq.beq, decide_eq_true_eq] at hc
      subst hc
      simp only [same_value_inj hwφ₁ hwφ₂ hty ih₁ ih₂, not_true_eq_false] at hb
    case true =>
      simp only [beq_iff_eq] at hb
      subst hb
      simp only [Same.same, SameValues] at ih₁ ih₂
      simp only [ih₁, Option.some.injEq] at ih₂
      simp only [bool_value?, ih₂, beq_self_eq_true]
  case inr =>
    subst hok
    replace ⟨hty, hp₁, _⟩ := reducibleEq_ok_false_implies hty
    simp only [Same.same, SameResults, SameValues, Term.value?, TermPrim.value?, Option.some.injEq,
      Value.prim.injEq, Prim.bool.injEq]
    by_contra hc
    rw [eq_comm, Bool.not_eq_false] at hc
    simp only [BEq.beq, decide_eq_true_eq] at hc
    subst hc
    have ht : ¬ t₁ = t₂ := by by_contra h; simp only [h, not_true_eq_false] at hty
    replace ⟨_, hp₁⟩ := isPrimType_implies_prim_type hp₁
    replace ⟨_, hp₁⟩ := wfl_of_prim_type_is_prim (And.intro hwφ₁ hlit₁) hp₁
    subst hp₁
    simp only [same_prim_value_inj ih₁ ih₂, not_true_eq_false] at ht

local macro "simp_binaryApp_bv_inputs" compile_thm:ident hok:ident hwφ₁:ident hwφ₂:ident ih₁:ident ih₂:ident : tactic => do
 `(tactic| (
    replace ⟨hty₁, hty₂, $hok:ident⟩ := $compile_thm:ident $hok:ident
    subst $hok:ident
    have ⟨bv₁, ht₁⟩ := wfl_of_type_bitvec_is_bitvec (And.intro $hwφ₁:ident (same_value_implies_lit $ih₁:ident)) hty₁
    have ⟨bv₂, ht₂⟩ := wfl_of_type_bitvec_is_bitvec (And.intro $hwφ₂:ident (same_value_implies_lit $ih₂:ident)) hty₂
    subst ht₁ ht₂
    replace ⟨i₁, hv₁, $ih₁:ident⟩ := same_bitvec64_term_implies $ih₁:ident
    replace ⟨i₂, hv₂, $ih₂:ident⟩ := same_bitvec64_term_implies $ih₂:ident
    subst hv₁ hv₂
    ))

private theorem compileApp₂_less_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .less t₁ t₂ εs = Except.ok t₃) :
  apply₂ .less v₁ v₂ es ∼ t₃
:= by
    rcases compileApp₂_less_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    case _ => -- BitVec
      have ⟨bv₁, ht₁⟩ := wfl_of_type_bitvec_is_bitvec (And.intro hwφ₁ (same_value_implies_lit ih₁)) hty₁
      have ⟨bv₂, ht₂⟩ := wfl_of_type_bitvec_is_bitvec (And.intro hwφ₂ (same_value_implies_lit ih₂)) hty₂
      subst ht₁ ht₂
      replace ⟨i₁, hv₁, ih₁⟩ := same_bitvec64_term_implies ih₁
      replace ⟨i₂, hv₂, ih₂⟩ := same_bitvec64_term_implies ih₂
      subst hv₁ hv₂ hok
      simp only [apply₂, pe_bvslt, ← same_ok_bool_iff]
      simp only [Int64.toInt, BitVec.toInt_inj] at ih₁ ih₂
      simp only [LT.lt, Int64.lt, Bool.decide_eq_true, ih₁, ih₂]
    case _ => -- Duration
      have ⟨d₁, ht₁⟩ := wfl_of_type_duration_is_duration (And.intro hwφ₁ (same_value_implies_lit ih₁)) hty₁
      have ⟨d₂, ht₂⟩ := wfl_of_type_duration_is_duration (And.intro hwφ₂ (same_value_implies_lit ih₂)) hty₂
      subst ht₁ ht₂
      have hv₁ := same_ext_term_implies ih₁
      have hv₂ := same_ext_term_implies ih₂
      subst hv₁ hv₂ hok
      simp only [apply₂, pe_ext_duration_val, LT.lt, Ext.Datetime.Duration.lt, pe_bvslt, ← same_ok_bool_iff]
      simp only [Int64.lt, Bool.decide_eq_true]
    case _ => -- Datetime
      have ⟨d₁, ht₁⟩ := wfl_of_type_datetime_is_datetime (And.intro hwφ₁ (same_value_implies_lit ih₁)) hty₁
      have ⟨d₂, ht₂⟩ := wfl_of_type_datetime_is_datetime (And.intro hwφ₂ (same_value_implies_lit ih₂)) hty₂
      subst ht₁ ht₂
      have hv₁ := same_ext_term_implies ih₁
      have hv₂ := same_ext_term_implies ih₂
      subst hv₁ hv₂ hok
      simp only [apply₂, pe_ext_datetime_val, LT.lt, Ext.Datetime.lt, pe_bvslt, ← same_ok_bool_iff]
      simp only [Int64.lt, Bool.decide_eq_true]

private theorem compileApp₂_lessEq_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .lessEq t₁ t₂ εs = Except.ok t₃) :
  apply₂ .lessEq v₁ v₂ es ∼ t₃
:= by
    rcases compileApp₂_lessEq_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    case _ => -- Decimal
      have ⟨bv₁, ht₁⟩ := wfl_of_type_bitvec_is_bitvec (And.intro hwφ₁ (same_value_implies_lit ih₁)) hty₁
      have ⟨bv₂, ht₂⟩ := wfl_of_type_bitvec_is_bitvec (And.intro hwφ₂ (same_value_implies_lit ih₂)) hty₂
      subst ht₁ ht₂
      replace ⟨i₁, hv₁, ih₁⟩ := same_bitvec64_term_implies ih₁
      replace ⟨i₂, hv₂, ih₂⟩ := same_bitvec64_term_implies ih₂
      subst hv₁ hv₂ hok
      simp only [apply₂, pe_bvsle, ← same_ok_bool_iff]
      simp only [Int64.toInt, BitVec.toInt_inj] at ih₁ ih₂
      simp only [LE.le, Int64.le, Bool.decide_eq_true, ih₁, ih₂]
    case _ => -- Duration
      have ⟨d₁, ht₁⟩ := wfl_of_type_duration_is_duration (And.intro hwφ₁ (same_value_implies_lit ih₁)) hty₁
      have ⟨d₂, ht₂⟩ := wfl_of_type_duration_is_duration (And.intro hwφ₂ (same_value_implies_lit ih₂)) hty₂
      subst ht₁ ht₂
      have hv₁ := same_ext_term_implies ih₁
      have hv₂ := same_ext_term_implies ih₂
      subst hv₁ hv₂ hok
      simp only [apply₂, pe_ext_duration_val, LE.le, Ext.Datetime.Duration.le, pe_bvsle, ← same_ok_bool_iff]
      simp only [Int64.le, Bool.decide_eq_true]
    case _ => -- Datetime
      have ⟨d₁, ht₁⟩ := wfl_of_type_datetime_is_datetime (And.intro hwφ₁ (same_value_implies_lit ih₁)) hty₁
      have ⟨d₂, ht₂⟩ := wfl_of_type_datetime_is_datetime (And.intro hwφ₂ (same_value_implies_lit ih₂)) hty₂
      subst ht₁ ht₂
      have hv₁ := same_ext_term_implies ih₁
      have hv₂ := same_ext_term_implies ih₂
      subst hv₁ hv₂ hok
      simp only [apply₂, pe_ext_datetime_val, LE.le, Ext.Datetime.le, pe_bvsle, ← same_ok_bool_iff]
      simp only [Int64.le, Bool.decide_eq_true]

private theorem compileApp₂_add_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .add t₁ t₂ εs = Except.ok t₃) :
  apply₂ .add v₁ v₂ es ∼ t₃
:= by
  simp_binaryApp_bv_inputs compileApp₂_add_ok_implies hok hwφ₁ hwφ₂ ih₁ ih₂
  simp only [apply₂, Int64.add?, Int64.ofInt?, bvsaddo, bvso, bvadd, bvapp, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.add_eq]
  split
  case isTrue h =>
    simp only [Same.same, SameResults, intOrErr, ih₁, ih₂, BitVec.overflows_false_64 h, pe_ifFalse_false]
    apply same_implies_same_value
    apply same_int
    exact BitVec.add_toInt_eq_add_64 h ih₁ ih₂
  case isFalse h =>
    simp only [Same.same, SameResults, intOrErr, ih₁, ih₂, BitVec.overflows_true_64 h,
      pe_ifFalse_true, ne_eq, not_false_eq_true, reduceCtorEq]

private theorem compileApp₂_sub_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .sub t₁ t₂ εs = Except.ok t₃) :
  apply₂ .sub v₁ v₂ es ∼ t₃
:= by
  simp_binaryApp_bv_inputs compileApp₂_sub_ok_implies hok hwφ₁ hwφ₂ ih₁ ih₂
  simp only [apply₂, Int64.sub?, Int64.ofInt?, bvssubo, bvso, bvsub, bvapp, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.add_eq]
  split
  case isTrue h =>
    simp only [Same.same, SameResults, intOrErr, ih₁, ih₂, BitVec.overflows_false_64 h, pe_ifFalse_false]
    apply same_implies_same_value
    apply same_int
    exact BitVec.sub_toInt_eq_sub_64 h ih₁ ih₂
  case isFalse h =>
    simp only [Same.same, SameResults, intOrErr, ih₁, ih₂, BitVec.overflows_true_64 h,
      pe_ifFalse_true, ne_eq, not_false_eq_true, reduceCtorEq]

private theorem compileApp₂_mul_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .mul t₁ t₂ εs = Except.ok t₃) :
  apply₂ .mul v₁ v₂ es ∼ t₃
:= by
  simp_binaryApp_bv_inputs compileApp₂_mul_ok_implies hok hwφ₁ hwφ₂ ih₁ ih₂
  simp only [apply₂, Int64.mul?, Int64.ofInt?, bvsmulo, bvso, bvmul, bvapp, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.add_eq]
  split
  case isTrue h =>
    simp only [Same.same, SameResults, intOrErr, ih₁, ih₂, BitVec.overflows_false_64 h, pe_ifFalse_false]
    apply same_implies_same_value
    apply same_int
    exact BitVec.mul_toInt_eq_mul_64 h ih₁ ih₂
  case isFalse h =>
    simp only [Same.same, SameResults, intOrErr, ih₁, ih₂, BitVec.overflows_true_64 h,
      pe_ifFalse_true, ne_eq, not_false_eq_true, reduceCtorEq]

private theorem same_set_mem {εs : SymEntities} {ts : Set Term} {vs : Set Value} {t : Term} {v : Value}
  (hwφ₁ : Term.WellFormed εs (Term.set ts (Term.typeOf t)))
  (hwφ₂ : Term.WellFormed εs t)
  (hs₁ : Term.value? (Term.set ts (Term.typeOf t)) = some (Value.set vs))
  (hs₂ : v ∼ t) :
  v ∈ vs ↔ t ∈ ts
:= by
  constructor <;> intro h
  case mp =>
    replace ⟨t', hs₁, hs₁'⟩ := set_value?_implies_in_term hs₁ v h
    rw [← same_values_def] at hs₁'
    have heq := same_value_inj
      (wf_term_set_implies_wf_elt hwφ₁ hs₁)
      hwφ₂
      (wf_term_set_implies_typeOf_elt hwφ₁ hs₁)
      hs₁' hs₂
    subst heq
    exact hs₁
  case mpr =>
    by_contra hc
    replace ⟨v', hs₁, hs₁'⟩ := set_value?_implies_in_value hs₁ t h
    rw [same_values_def] at hs₂
    simp [hs₂] at hs₁'
    subst hs₁'
    contradiction

private theorem same_set_contains {εs : SymEntities} {s₁ : Set Term} {vs : Set Value} {t₂ : Term} {v₂ : Value}
  (hwφ₁ : Term.WellFormed εs (Term.set s₁ (Term.typeOf t₂)))
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁ : Term.value? (Term.set s₁ (Term.typeOf t₂)) = some (Value.set vs))
  (ih₂ : v₂ ∼ t₂) :
  Set.contains vs v₂ = Set.contains s₁ t₂
:= by
  have hm := same_set_mem hwφ₁ hwφ₂ ih₁ ih₂
  simp only [← Set.contains_prop_bool_equiv] at hm
  rw [Bool.eq_iff_iff, hm]

private theorem compileApp₂_contains_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .contains t₁ t₂ εs = Except.ok t₃) :
  apply₂ .contains v₁ v₂ es ∼ t₃
:= by
  replace ⟨hty, hok⟩ := compileApp₂_contains_ok_implies hok
  subst hok
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  have ⟨s₁, ht₁⟩ := wfl_of_type_set_is_set (And.intro hwφ₁ hlit₁) hty
  subst ht₁
  replace ⟨vs, hv₁, ih₁⟩ := same_set_term_implies ih₁
  subst hv₁
  simp only [pe_set_member hlit₁ hlit₂, apply₂, ← same_ok_bool_iff]
  exact same_set_contains hwφ₁ hwφ₂ ih₁ ih₂

private theorem same_set_subset {εs : SymEntities} {s₁ s₂ : Set Term} {ty : TermType} {vs₁ vs₂ : Set Value}
  (hwφ₁ : Term.WellFormed εs (Term.set s₁ ty))
  (hwφ₂ : Term.WellFormed εs (Term.set s₂ ty))
  (ih₁  : Term.value? (Term.set s₁ ty) = some (Value.set vs₁))
  (ih₂  : Term.value? (Term.set s₂ ty) = some (Value.set vs₂)) :
  Set.subset vs₂ vs₁ = Set.subset s₂ s₁
:= by
  have ht := @Set.subset_def _ _ s₂ s₁
  have hv := @Set.subset_def _ _ vs₂ vs₁
  simp only [Subset] at ht hv
  cases hs : Set.subset s₂ s₁
  case false =>
    by_contra hc
    simp only [ne_eq, Bool.not_eq_false] at hc
    replace hv := hv.mp hc
    replace ht := ht.mpr
    have ht' : Set.subset s₂ s₁ = true := by
      apply ht
      intro t hin
      have ⟨v, hin'⟩ := set_value?_implies_in_value ih₂ t hin
      have hty := wf_term_set_implies_typeOf_elt hwφ₂ hin
      subst hty
      have hφt := wf_term_set_implies_wf_elt hwφ₂ hin
      rw [← same_values_def] at hin'
      replace hv := hv v hin'.left
      exact (same_set_mem hwφ₁ hφt ih₁ hin'.right).mp hv
    simp only [hs, reduceCtorEq] at ht'
  case true =>
    replace ht := ht.mp hs
    rw [hv]
    intro v hvs₂
    have ⟨t, hin⟩ := set_value?_implies_in_term ih₂ v hvs₂
    replace ht := ht t hin.left
    have hty := wf_term_set_implies_typeOf_elt hwφ₁ ht
    subst hty
    have hφt := wf_term_set_implies_wf_elt hwφ₁ ht
    rw [← same_values_def] at hin
    exact (same_set_mem hwφ₁ hφt ih₁ hin.right).mpr ht

private theorem compileApp₂_containsAll_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .containsAll t₁ t₂ εs = Except.ok t₃) :
  apply₂ .containsAll v₁ v₂ es ∼ t₃
:= by
  replace ⟨ty, hty₁, hty₂, hok⟩ := compileApp₂_containsAll_ok_implies hok
  subst hok
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  have ⟨s₁, ht₁⟩ := wfl_of_type_set_is_set (And.intro hwφ₁ hlit₁) hty₁
  have ⟨s₂, ht₂⟩ := wfl_of_type_set_is_set (And.intro hwφ₂ hlit₂) hty₂
  subst ht₁ ht₂
  replace ⟨vs₁, hv₁, ih₁⟩ := same_set_term_implies ih₁
  replace ⟨vs₂, hv₂, ih₂⟩ := same_set_term_implies ih₂
  subst hv₁ hv₂
  simp only [pe_set_subset hlit₂ hlit₁, apply₂, ← same_ok_bool_iff]
  exact same_set_subset hwφ₁ hwφ₂ ih₁ ih₂

private theorem same_set_intersects {εs : SymEntities} {s₁ s₂ : Set Term} {ty : TermType} {vs₁ vs₂ : Set Value}
  (hwφ₁ : Term.WellFormed εs (Term.set s₁ ty))
  (hwφ₂ : Term.WellFormed εs (Term.set s₂ ty))
  (ih₁  : Term.value? (Term.set s₁ ty) = some (Value.set vs₁))
  (ih₂  : Term.value? (Term.set s₂ ty) = some (Value.set vs₂)) :
  Set.intersects vs₁ vs₂ = Set.intersects s₁ s₂
:= by
  cases h : Set.intersects s₁ s₂
  case false =>
    by_contra hc
    simp only [Bool.not_eq_false, Set.intersects_iff_exists] at hc
    replace ⟨v, hc⟩ := hc
    have ⟨t₁, ht₁, ht₂⟩ := set_value?_implies_in_term ih₁ v hc.left
    have ⟨t₂, ht₃, ht₄⟩ := set_value?_implies_in_term ih₂ v hc.right
    rw [← same_values_def] at ht₂ ht₄
    have hw₁ := wf_term_set_implies_wf_elt hwφ₁ ht₁
    have hw₂ := wf_term_set_implies_wf_elt hwφ₂ ht₃
    have hty := wf_term_set_implies_typeOf_elt hwφ₁ ht₁
    rw [← (wf_term_set_implies_typeOf_elt hwφ₂ ht₃)] at hty
    have heq := same_value_inj hw₁ hw₂ hty ht₂ ht₄
    subst heq
    have h' : Set.intersects s₁ s₂ := by
      rw [Set.intersects_iff_exists]
      exists t₁
    simp only [h', reduceCtorEq] at h
  case true =>
    rw [Set.intersects_iff_exists] at *
    replace ⟨t, h⟩ := h
    have ⟨v₁, hv₁, hv₂⟩ := set_value?_implies_in_value ih₁ t h.left
    have ⟨v₂, hv₃, hv₄⟩ := set_value?_implies_in_value ih₂ t h.right
    simp only [hv₂, Option.some.injEq] at hv₄
    subst hv₄
    exists v₁

private theorem compileApp₂_containsAny_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .containsAny t₁ t₂ εs = Except.ok t₃) :
  apply₂ .containsAny v₁ v₂ es ∼ t₃
:= by
  replace ⟨ty, hty₁, hty₂, hok⟩ := compileApp₂_containsAny_ok_implies hok
  subst hok
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  have ⟨s₁, ht₁⟩ := wfl_of_type_set_is_set (And.intro hwφ₁ hlit₁) hty₁
  have ⟨s₂, ht₂⟩ := wfl_of_type_set_is_set (And.intro hwφ₂ hlit₂) hty₂
  subst ht₁ ht₂
  replace ⟨vs₁, hv₁, ih₁⟩ := same_set_term_implies ih₁
  replace ⟨vs₂, hv₂, ih₂⟩ := same_set_term_implies ih₂
  subst hv₁ hv₂
  simp only [pe_set_intersects hlit₁ hlit₂, apply₂, ← same_ok_bool_iff]
  exact same_set_intersects hwφ₁ hwφ₂ ih₁ ih₂

theorem same_entities_ancestors_none_of_type {es : Entities} {εs : SymEntities} {e₁ e₂ : EntityUID}
  (heq : es ∼ εs)
  (hno : SymEntities.ancestorsOfType εs e₁.ty e₂.ty = none) :
  ¬ e₂ ∈ Entities.ancestorsOrEmpty es e₁
:= by
  simp only [Same.same, SameEntities] at heq
  simp only [Entities.ancestorsOrEmpty]
  split
  case h_1 d hf =>
    by_contra hc
    replace ⟨δ, heq⟩ := heq e₁ d hf
    simp only [SymEntities.ancestorsOfType, SymEntities.ancestors, Option.bind_eq_bind,
      Option.bind_eq_none_iff, Option.bind_eq_some_iff, Option.some.injEq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hno
    replace hno := hno δ heq.left
    have ha := heq.right.right.left e₂ hc
    replace ⟨_, ha, _⟩ := ha
    simp only [ha, reduceCtorEq] at hno
  case h_2 =>
    exact Set.empty_no_elts e₂

theorem same_entities_ancestors_some_of_type {es : Entities} {εs : SymEntities} {e₁ : EntityUID} {ety₂ : EntityType} {ancs : UnaryFunction}
  (heq : es ∼ εs)
  (hwf : Value.WellFormed es (Value.prim (Prim.entityUID e₁)))
  (hso : SymEntities.ancestorsOfType εs e₁.ty ety₂ = some ancs) :
  ∃ (ts : Set Term),
    app ancs (Term.prim (TermPrim.entity e₁)) = Term.set ts (TermType.entity ety₂) ∧
    (Term.set ts (TermType.entity ety₂)).isLiteral ∧
    (∀ (e₂ : EntityUID), e₂.ty = ety₂ →
      ((Term.prim (TermPrim.entity e₂) ∈ ts ↔ e₂ ∈ Entities.ancestorsOrEmpty es e₁)))
:= by
  simp only [Same.same, SameEntities] at heq
  simp only [Entities.ancestorsOrEmpty]
  split
  case h_1 d hf₁ =>
    replace ⟨δ, hf₂, heq⟩ := heq e₁ d hf₁
    replace ⟨heq, hεq⟩ := heq.right
    simp only [SymEntities.ancestorsOfType, SymEntities.ancestors, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at hso
    replace ⟨_, ⟨δ, hf₃, hso⟩, hf₄⟩ := hso
    simp [hf₂] at hf₃
    subst hf₃ hso
    replace ⟨ts, ha, hεq⟩ := hεq.left ety₂ ancs hf₄
    have hlit : (Term.set ts (TermType.entity ety₂)).isLiteral := by
      apply lit_term_set_impliedBy_lit_elts
      intro t h
      replace ⟨e, hεq, _⟩ := hεq t h
      subst hεq
      simp only [Term.isLiteral]
    exists ts
    simp only [ha, hlit, true_and]
    intro e₂ hty
    subst hty
    constructor <;> intro hin
    case mp  =>
      replace ⟨_, hεq, hin⟩ := hεq (Term.prim (TermPrim.entity e₂)) hin
      simp only [Term.prim.injEq, TermPrim.entity.injEq] at hεq
      subst hεq
      exact hin
    case mpr =>
      replace ⟨ancUF, hf₅, ⟨ts', ha', hin⟩⟩ := heq e₂ hin
      simp only [hf₄, Option.some.injEq] at hf₅ ; subst hf₅
      simp only [ha, Term.set.injEq, and_true] at ha' ; subst ha'
      exact hin
  case h_2 hf =>
    replace ⟨_, hwf⟩ := wf_value_uid_implies_exists_entity_data hwf
    simp only [hwf, reduceCtorEq] at hf

private theorem compileInₑ_eq_inₑ {es : Entities} {εs : SymEntities} {e₁ e₂ : EntityUID}
  (heq   : es ∼ εs)
  (hwf₁  : Value.WellFormed es (Value.prim (Prim.entityUID e₁)))
  (hwφ₂  : Term.WellFormed εs (Term.prim (TermPrim.entity e₂)))
  (hlit₁ : Term.isLiteral (Term.prim (TermPrim.entity e₁)))
  (hlit₂ : Term.isLiteral (Term.prim (TermPrim.entity e₂))) :
  compileInₑ (Term.prim (TermPrim.entity e₁)) (Term.prim (TermPrim.entity e₂)) (SymEntities.ancestorsOfType εs e₁.ty e₂.ty) =
  Term.prim (TermPrim.bool (inₑ e₁ e₂ es))
:= by
  rw [compileInₑ_def]
  by_cases h : e₁ = e₂
  case pos =>
    subst h
    simp only [compileInₑ.isEq, ↓reduceIte, pe_eq_same, pe_or_true_left, inₑ, beq_self_eq_true, Bool.true_or]
  case neg =>
    simp only [compileInₑ.isEq, pe_eq_lit hlit₁ hlit₂, BEq.beq, Term.prim.injEq,
      TermPrim.entity.injEq, h, decide_false, ite_self, pe_or_false_left, inₑ, Bool.false_or]
    simp only [compileInₑ.isIn]
    split
    case h_1 ancs? hs =>
      replace ⟨ts, hs, hlit, hmem⟩ := same_entities_ancestors_some_of_type heq hwf₁ hs
      specialize hmem e₂ rfl
      simp only [hs, pe_set_member hlit term_prim_is_lit, Term.prim.injEq, TermPrim.bool.injEq]
      cases h : Set.contains ts (Term.prim (TermPrim.entity e₂)) <;> rw [eq_comm]
      case false =>
        by_contra hc
        rw [Bool.not_eq_false, Set.contains_prop_bool_equiv, ← hmem, ← Set.contains_prop_bool_equiv] at hc
        simp only [hc, reduceCtorEq] at h
      case true =>
        rw [Set.contains_prop_bool_equiv, ← hmem]
        rw [Set.contains_prop_bool_equiv] at h
        exact h
    case h_2 hn =>
      simp only [Term.prim.injEq, TermPrim.bool.injEq]
      rw [eq_comm]
      by_contra hc
      simp only [Bool.not_eq_false, Set.contains_prop_bool_equiv] at hc
      have := same_entities_ancestors_none_of_type heq hn
      contradiction

private theorem term_entity_set_wfl_implies_sorted_entity_list {εs : SymEntities} {ts : List Term} {ety : EntityType}
  (hwφ  : (Term.set (Set.mk ts) (TermType.entity ety)).WellFormed εs)
  (hlit : (Term.set (Set.mk ts) (TermType.entity ety)).isLiteral) :
  ∃ (uids : List EntityUID), uids.Sorted ∧ ts = uids.map (λ uid => Term.prim (TermPrim.entity uid))
:= by
  induction ts
  case nil =>
    exists []
    simp only [List.map_nil, and_true]
    exact List.SortedBy.nil
  case cons hd tl ih =>
    have hlt := wf_term_set_implies_wf_set hwφ
    simp only [Set.wf_iff_sorted, Set.elts] at hlt
    replace hwφ := wf_term_set_cons hwφ
    replace hlit := lit_term_set_cons hlit
    replace ⟨uids, ih⟩ := ih hwφ.right.right hlit.right
    have ⟨uid, ht, hty⟩ := wfl_of_type_entity_is_entity (And.intro hwφ.left hlit.left) hwφ.right.left
    exists (uid :: uids)
    simp only [ht, ih.right, List.map_cons, List.Sorted, and_true]
    rw [eq_comm, List.Sorted] at ih
    cases tl
    case nil =>
      simp only [List.map_eq_nil_iff] at ih
      simp only [ih]
      exact List.SortedBy.cons_nil
    case cons hd' tl' =>
      cases uids <;>
      simp only [List.map_nil, and_false, List.map_cons, List.cons.injEq, reduceCtorEq] at ih
      rename_i uid' uids
      apply List.SortedBy.cons_cons
      · simp only [id_eq]
        simp only [List.Sorted] at hlt
        replace hlt := List.sortedBy_implies_head_lt_tail hlt hd'
        simp only [← ih.right.left, List.mem_cons, true_or, ht, id_eq, forall_const] at hlt
        simp only [LT.lt, Term.lt, TermPrim.lt, decide_eq_true_eq, Bool.decide_eq_true] at hlt
        simp only [LT.lt, hlt]
      · exact ih.left

private theorem term_entities_filterMap_value?_eq (uids : List EntityUID) :
  List.filterMap Term.value? (List.map (fun uid => Term.prim (TermPrim.entity uid)) uids) =
  List.map (fun uid => Value.prim (Prim.entityUID uid)) uids
:= by
  induction uids
  case nil =>
    simp only [List.map_nil, List.filterMap_nil]
  case cons hd tl ih =>
    simp only [List.map_cons, List.filterMap_cons, Term.value?, TermPrim.value?, ih]

private theorem entities_sorted_implies_values_sorted {uids : List EntityUID}
  (hsu : List.Sorted uids) :
  (List.map (fun uid => Value.prim (Prim.entityUID uid)) uids).Sorted
:= by
  simp only [List.Sorted]
  induction uids
  case nil =>
    simp only [List.map_nil]
    exact List.SortedBy.nil
  case cons hd tl ih =>
    simp only [List.map_cons]
    have htl := List.tail_sortedBy hsu
    specialize ih htl
    cases tl
    case nil =>
      simp only [List.map_nil]
      exact List.SortedBy.cons_nil
    case cons hd' tl =>
      simp only [List.map_cons] at *
      apply List.SortedBy.cons_cons _ ih
      replace hsu := List.sortedBy_implies_head_lt_tail hsu hd'
      simp only [List.mem_cons, true_or, LT.lt, id_eq, forall_const] at hsu
      simp only [LT.lt, id_eq, Value.lt, Prim.lt, hsu, decide_true]

private theorem term_entity_set_wfl_implies_value? {ts : List Term} {ety : EntityType} {vs : List Value} {uids : List EntityUID}
  (hsu  : uids.Sorted)
  (hts  : ts = uids.map (λ uid => Term.prim (TermPrim.entity uid)))
  (hvs  : Term.value? (Term.set (Set.mk ts) (TermType.entity ety)) = some (Value.set (Set.mk vs))) :
  vs = uids.map (λ uid => Value.prim (Prim.entityUID uid))
:= by
  simp only [Term.value?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Value.set.injEq] at hvs
  replace ⟨vs', hvs, hmk⟩ := hvs
  rw [List.mapM₁_eq_mapM, ← List.mapM'_eq_mapM] at hvs
  replace hvs := List.mapM'_some_eq_filterMap hvs
  subst hts
  rw [eq_comm, term_entities_filterMap_value?_eq] at hvs
  have hsrt := entities_sorted_implies_values_sorted hsu
  rw [← hvs] at hsrt
  simp only [Set.make_sorted hsrt, Set.mk.injEq] at hmk
  rw [← hmk, hvs]

private theorem entities_mapM'_asEntityUID_map_eq {uids : List EntityUID} :
  List.mapM' Value.asEntityUID (List.map (fun uid => Value.prim (Prim.entityUID uid)) uids) =
  .ok uids
:= by
  induction uids
  case nil =>
    simp only [List.map_nil, List.mapM'_nil, pure, Except.pure]
  case cons hd tl ih =>
    have h : Value.asEntityUID (Value.prim (Prim.entityUID hd)) = .ok hd := by
      simp only [Value.asEntityUID]
    simp only [List.map_cons, List.mapM'_cons, h, ih, pure, Except.pure, Except.bind_ok]

private theorem entity_set_mapOrErr_asEntityUID_eq {vs : List Value} {uids : List EntityUID}
  (hsu : uids.Sorted)
  (hvs : vs = uids.map (λ uid => Value.prim (Prim.entityUID uid))) :
  Set.mapOrErr Value.asEntityUID (Set.mk vs) Spec.Error.typeError = .ok (Set.mk uids)
:= by
  simp only [Set.mapOrErr, Set.elts, hvs, ← List.mapM'_eq_mapM, entities_mapM'_asEntityUID_map_eq, Except.ok.injEq]
  simp only [Set.make_sorted hsu]

private theorem entities_type_eq {εs : SymEntities} {ety : EntityType} {ts : List Term} {uids : List EntityUID}
  (hwφ : Term.WellFormed εs (Term.set (Set.mk ts) (TermType.entity ety)))
  (hts : ts = List.map (fun uid => Term.prim (TermPrim.entity uid)) uids) :
  ∀ uid ∈ uids, uid.ty = ety
:= by
  intro uid ht
  replace ht := @List.mem_map_of_mem _ _ _ _ (fun uid => Term.prim (TermPrim.entity uid)) ht
  simp only [← hts, Set.in_list_iff_in_mk] at ht
  replace ht := wf_term_set_implies_typeOf_elt hwφ ht
  simp only [Term.typeOf, TermPrim.typeOf, TermType.prim.injEq, TermPrimType.entity.injEq] at ht
  exact ht

private theorem compileInₛ_eq_any_inₑ_none {es : Entities} {εs : SymEntities} {ety₂ : EntityType} {e₁ : EntityUID} {uids : List EntityUID}
  (heq : es ∼ εs)
  (hty : ∀ uid ∈ uids, uid.ty = ety₂)
  (ha  : SymEntities.ancestorsOfType εs e₁.ty ety₂ = none) :
  Set.intersects (Set.mk uids) (Entities.ancestorsOrEmpty es e₁) = false
:= by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  replace ⟨e₂, ht, hc⟩ := Set.intersects_iff_exists.mp hc
  rw [← Set.in_list_iff_in_mk] at ht
  specialize hty e₂ ht
  rw [← hty] at ha
  have := same_entities_ancestors_none_of_type heq ha
  contradiction

private theorem compileInₛ_eq_any_inₑ_some {es : Entities} {εs : SymEntities} {ety₂ : EntityType} {e₁ : EntityUID} {uids : List EntityUID} {ancs : UnaryFunction}
  (heq : es ∼ εs)
  (hwf : Value.WellFormed es (Value.prim (Prim.entityUID e₁)))
  (hts : ts = List.map (fun uid => Term.prim (TermPrim.entity uid)) uids)
  (hty : ∀ uid ∈ uids, uid.ty = ety₂)
  (ha  : SymEntities.ancestorsOfType εs e₁.ty ety₂ = some ancs):
  set.intersects (Term.set (Set.mk ts) (TermType.entity ety₂)) (app ancs (Term.prim (TermPrim.entity e₁))) =
  Term.prim (TermPrim.bool (Set.intersects (Set.mk uids) (Entities.ancestorsOrEmpty es e₁)))
:= by
  have hlit : (Term.set (Set.mk ts) (TermType.entity ety₂)).isLiteral := by
    apply lit_term_set_impliedBy_lit_elts
    intro t h
    simp only [hts, ← Set.in_list_iff_in_mk, List.mem_map] at h
    replace ⟨_, _, h⟩ := h
    simp only [← h, Term.isLiteral]
  replace ⟨ts', ha, hlit', heq⟩ := same_entities_ancestors_some_of_type heq hwf ha
  simp only [ha, pe_set_intersects hlit hlit', Term.prim.injEq, TermPrim.bool.injEq]
  cases h : Set.intersects (Set.mk uids) (Entities.ancestorsOrEmpty es e₁)
  case false =>
    by_contra hc
    simp only [Bool.not_eq_false, Set.intersects_iff_exists, ← Set.in_list_iff_in_mk] at hc
    replace ⟨t, ht, hc⟩ := hc
    simp only [hts, List.mem_map] at ht
    replace ⟨e₂, ht, ht'⟩ := ht
    subst ht'
    rw [heq e₂ (hty e₂ ht)] at hc
    have h' : Set.intersects (Set.mk uids) (Entities.ancestorsOrEmpty es e₁) := by
      simp only [Set.intersects_iff_exists]
      exists e₂
    simp only [h', reduceCtorEq] at h
  case true =>
    replace ⟨e₂, h', h⟩ := Set.intersects_iff_exists.mp h
    rw [← Set.in_list_iff_in_mk] at h'
    specialize heq e₂ (hty e₂ h')
    simp only [ha, pe_set_intersects hlit hlit', Term.prim.injEq, TermPrim.bool.injEq, Set.intersects_iff_exists]
    exists (Term.prim (TermPrim.entity e₂))
    simp only [hts, Set.mem_inter_iff, ← Set.in_list_iff_in_mk, List.mem_map, Term.prim.injEq,
      TermPrim.entity.injEq, exists_eq_right, h', heq, h, and_self]

private theorem compileInₛ_eq_any_inₑ {es : Entities} {εs : SymEntities} {ety₂ : EntityType} {e₁ : EntityUID} {ts : List Term} {uids : List EntityUID}
  (heq   : es ∼ εs)
  (hwf₁  : Value.WellFormed es (Value.prim (Prim.entityUID e₁)))
  (hwφ₂  : Term.WellFormed εs (Term.set (Set.mk ts) (TermType.entity ety₂)))
  (hlit₂ : Term.isLiteral (Term.set (Set.mk ts) (TermType.entity ety₂)))
  (hts   : ts = List.map (fun uid => Term.prim (TermPrim.entity uid)) uids) :
  compileInₛ (Term.prim (TermPrim.entity e₁)) (Term.set (Set.mk ts) (TermType.entity ety₂))
      (SymEntities.ancestorsOfType εs e₁.ty ety₂) =
  Term.prim (TermPrim.bool (List.any uids (fun x => inₑ e₁ x es)))
:= by
  rw [compileInₛ_def, compileInₛ.isIn₁]
  by_cases h : e₁ ∈ uids
  case pos =>
    have ht : Term.prim (TermPrim.entity e₁) ∈ Set.mk ts := by
      simp only [hts, ← Set.in_list_iff_in_mk, List.mem_map, Term.prim.injEq, TermPrim.entity.injEq,
      exists_eq_right, h]
    have hty := wf_term_set_implies_typeOf_elt hwφ₂ ht
    rw [← Set.contains_prop_bool_equiv] at ht
    simp only [Term.typeOf, hty, ↓reduceIte, pe_set_member hlit₂ term_prim_is_lit, ht,
      pe_or_true_left, Term.prim.injEq, TermPrim.bool.injEq]
    rw [eq_comm, List.any_eq_true]
    exists e₁
    simp only [h, inₑ, beq_self_eq_true, Bool.true_or, and_self]
  case neg =>
    have ht : Set.contains (Set.mk ts) (Term.prim (TermPrim.entity e₁)) = false := by
      by_contra hc
      simp only [hts, Bool.not_eq_false, Set.contains_prop_bool_equiv, ← Set.in_list_iff_in_mk,
        List.mem_map, Term.prim.injEq, TermPrim.entity.injEq, exists_eq_right] at hc
      contradiction
    have hv : (List.any uids fun x => inₑ e₁ x es) = (Set.mk uids).intersects (es.ancestorsOrEmpty e₁) := by
      simp only [inₑ, Set.intersects, Set.elts]
      cases he : List.any uids (Set.contains (Entities.ancestorsOrEmpty es e₁))
      case false =>
        by_contra hc
        simp only [Bool.not_eq_false, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
        replace ⟨e, hc, hc'⟩ := hc
        rcases hc' with hc' | hc'
        case inl =>
          subst hc'
          contradiction
        case inr =>
          have hin : List.any uids (Set.contains (Entities.ancestorsOrEmpty es e₁)) := by
            simp only [List.any_eq_true]
            exists e
          simp only [hin, reduceCtorEq] at he
      case true =>
        simp only [List.any_eq_true] at *
        replace ⟨e, he⟩ := he
        exists e
        simp only [he, Bool.or_true, and_self]
    simp only [pe_set_member hlit₂ term_prim_is_lit, ht, ite_self, compileInₛ.isIn₂,
      pe_or_false_left, hv]
    have hty := entities_type_eq hwφ₂ hts
    split
    case h_1 ancs? ancs ha =>
      exact compileInₛ_eq_any_inₑ_some heq hwf₁ hts hty ha
    case h_2 ha =>
      simp only [compileInₛ_eq_any_inₑ_none heq hty ha]

private theorem compileApp₂_mem_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value} {es : Entities} {εs : SymEntities}
  (heq  : es ∼ εs)
  (hwf₁ : Value.WellFormed es v₁)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok  : compileApp₂ .mem t₁ t₂ εs = Except.ok t₃) :
  apply₂ .mem v₁ v₂ es ∼ t₃
:= by
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  replace ⟨ety₁, ety₂, hty₁, hok⟩ := compileApp₂_mem_ok_implies hok
  replace ⟨e₁, ht₁, hty₁⟩ := wfl_of_type_entity_is_entity (And.intro hwφ₁ hlit₁) hty₁
  subst ht₁
  rw [← hty₁] at *
  replace ih₁ := same_entity_term_implies ih₁
  subst ih₁
  rcases hok with ⟨hty₂, hok⟩ | ⟨hty₂, hok⟩ <;>
  subst hok
  case inl =>
    replace ⟨e₂, ht₂, hty₂⟩ := wfl_of_type_entity_is_entity (And.intro hwφ₂ hlit₂) hty₂
    subst ht₂
    replace ih₂ := same_entity_term_implies ih₂
    subst ih₂
    simp only [apply₂, ← hty₂, compileInₑ_eq_inₑ heq hwf₁ hwφ₂ hlit₁ hlit₂, ← same_ok_bool_iff]
  case inr =>
    replace ⟨s₂, ht₂⟩ := wfl_of_type_set_is_set (And.intro hwφ₂ hlit₂) hty₂
    subst ht₂
    replace ⟨vs, h, ih₂⟩ := same_set_term_implies ih₂
    subst h
    cases s₂ ; rename_i ts ; cases vs ; rename_i vs
    have ⟨uids, hsu, hts⟩ := term_entity_set_wfl_implies_sorted_entity_list hwφ₂ hlit₂
    have hvs := term_entity_set_wfl_implies_value? hsu hts ih₂
    simp only [apply₂, inₛ,
      entity_set_mapOrErr_asEntityUID_eq hsu hvs,
      Except.bind_ok, Set.any, Set.elts,
      compileInₛ_eq_any_inₑ heq hwf₁ hwφ₂ hlit₂ hts,
      ← same_ok_bool_iff]

private theorem compileApp₂_hasTag_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value} {es : Entities} {εs : SymEntities}
  (heq  : es ∼ εs)
  (hwf₁ : Value.WellFormed es v₁)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .hasTag t₁ t₂ εs = Except.ok t₃) :
  apply₂ .hasTag v₁ v₂ es ∼ t₃
:= by
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_hasTag_ok_implies hok
  replace hok := compileHasTag_ok_implies hok
  replace ⟨uid, ht₁, hty₁⟩ := wfl_of_type_entity_is_entity (And.intro hwφ₁ hlit₁) hty₁
  have ⟨tag, ht₂⟩ := wfl_of_type_string_is_string (And.intro hwφ₂ hlit₂) hty₂
  subst ht₁ ht₂ hty₁
  replace ih₁ := same_entity_term_implies ih₁
  replace ih₂ := same_string_term_implies ih₂
  subst ih₁ ih₂
  have ⟨d, hd⟩ := wf_value_uid_implies_exists_entity_data hwf₁
  replace ⟨δ, hδ, heq⟩ := heq uid d hd
  replace heq := heq.right.right.right
  simp only [SameTags] at heq
  simp only [apply₂, hasTag]
  rcases hok with ⟨hτs, hok⟩ | ⟨τs, hτs, hok⟩ <;>
  subst hok <;>
  simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs <;>
  replace ⟨δ', hδ', hτs⟩ := hτs <;>
  simp [hδ] at hδ' <;>
  subst hδ' <;>
  simp only [hτs] at heq
  · rw [← same_ok_bool_iff]
    simp only [Entities.tagsOrEmpty, hd, heq, Map.not_contains_of_empty]
  · simp only [Entities.tagsOrEmpty]
    split
    case _ d' hd' =>
      simp only [hd, Option.some.injEq] at hd'
      subst hd'
      cases ht : d.tags.find? tag
      case none =>
        simp only [Map.contains, ht, Option.isSome_none]
        rw [heq.right.left tag] at ht
        simp only [ht, same_ok_bool]
      case some val =>
        simp only [Map.contains, ht, Option.isSome_some]
        replace heq := heq.right.right tag val ht
        simp only [heq.left, same_ok_bool]
    case _ hd' => simp only [hd, reduceCtorEq] at hd'

private theorem compileApp₂_getTag_implies_apply₂ {t₁ t₂ t₃ : Term} {v₁ v₂ : Value} {es : Entities} {εs : SymEntities}
  (heq  : es ∼ εs)
  (hwf₁ : Value.WellFormed es v₁)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ .getTag t₁ t₂ εs = Except.ok t₃) :
  apply₂ .getTag v₁ v₂ es ∼ t₃
:= by
  have hlit₁ := same_value_implies_lit ih₁
  have hlit₂ := same_value_implies_lit ih₂
  replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
  replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
  subst hok
  replace ⟨uid, ht₁, hty₁⟩ := wfl_of_type_entity_is_entity (And.intro hwφ₁ hlit₁) hty₁
  have ⟨tag, ht₂⟩ := wfl_of_type_string_is_string (And.intro hwφ₂ hlit₂) hty₂
  subst ht₁ ht₂ hty₁
  replace ih₁ := same_entity_term_implies ih₁
  replace ih₂ := same_string_term_implies ih₂
  subst ih₁ ih₂
  have ⟨d, hd⟩ := wf_value_uid_implies_exists_entity_data hwf₁
  replace ⟨δ, hδ, heq⟩ := heq uid d hd
  replace heq := heq.right.right.right
  simp only [SameTags] at heq
  simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
  replace ⟨δ', hδ', hτs⟩ := hτs
  simp only [hδ, Option.some.injEq] at hδ'
  subst hδ'
  simp only [hτs] at heq
  simp only [apply₂, getTag, Entities.tags, Map.findOrErr, hd, Except.bind_ok]
  simp only [SymTags.getTag]
  cases ht : d.tags.find? tag <;> simp only
  case none =>
    rw [heq.right.left tag] at ht
    simp only [ht, pe_ifTrue_false]
    apply same_error_implied_by
    simp only [not_false_eq_true, reduceCtorEq]
  case some val =>
    replace heq := heq.right.right tag val ht
    simp only [Same.same, SameResults, heq.left, pe_ifTrue_true, heq.right]

private theorem compileApp₂_implies_apply₂ {op₂ : BinaryOp} {t₁ t₂ t₃ : Term} {v₁ v₂ : Value} {es : Entities} {εs : SymEntities}
  (heq  : es ∼ εs)
  (hwf₁ : Value.WellFormed es v₁)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hwφ₂ : Term.WellFormed εs t₂)
  (ih₁  : v₁ ∼ t₁)
  (ih₂  : v₂ ∼ t₂)
  (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok t₃) :
  apply₂ op₂ v₁ v₂ es ∼ t₃
:= by
  cases op₂
  case eq          => exact compileApp₂_eq_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case less        => exact compileApp₂_less_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case lessEq      => exact compileApp₂_lessEq_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case add         => exact compileApp₂_add_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case sub         => exact compileApp₂_sub_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case mul         => exact compileApp₂_mul_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case contains    => exact compileApp₂_contains_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case containsAll => exact compileApp₂_containsAll_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case containsAny => exact compileApp₂_containsAny_implies_apply₂ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case mem         => exact compileApp₂_mem_implies_apply₂ heq hwf₁ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case hasTag      => exact compileApp₂_hasTag_implies_apply₂ heq hwf₁ hwφ₁ hwφ₂ ih₁ ih₂ hok
  case getTag      => exact compileApp₂_getTag_implies_apply₂ heq hwf₁ hwφ₁ hwφ₂ ih₁ ih₂ hok

theorem compile_evaluate_binaryApp {op₂ : BinaryOp} {x₁ x₂ : Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.binaryApp op₂ x₁ x₂))
  (hwε : εnv.WellFormedFor (.binaryApp op₂ x₁ x₂))
  (hok : compile (.binaryApp op₂ x₁ x₂) εnv = .ok t)
  (ih₁ : CompileEvaluate x₁)
  (ih₂ : CompileEvaluate x₂) :
  evaluate (.binaryApp op₂ x₁ x₂) env.request env.entities ∼ t
:= by
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compile_binaryApp_ok_implies hok
  subst ht
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_binaryApp_implies hwε
  have ⟨hwf₁, hwf₂⟩ := wf_env_for_binaryApp_implies hwe
  -------
  replace ih₁ := ih₁ heq hwf₁ hwφ₁ hok₁
  replace ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok₁
  have hwo₁ := wf_option_get hwφ₁ hty₁
  -------
  replace ih₂ := ih₂ heq hwf₂ hwφ₂ hok₂
  replace ⟨hwφ₂, ty₂, hty₂⟩ := compile_wf hwφ₂ hok₂
  have hwo₂ := wf_option_get hwφ₂ hty₂
  -------
  replace hwε := hwε.left.right
  have ⟨hwφ₃, ty₃, hty₃⟩ := compileApp₂_wf hwε hwo₁.left hwo₂.left hok
  -------
  have hty := (wf_ifSome_option hwφ₂ hwφ₃ hty₃).right
  unfold evaluate
  simp_do_let (evaluate x₁ env.request env.entities)
  case error e he =>
    rw [he] at ih₁
    exact same_error_implies_ifSome_error ih₁ hty
  case ok v₁ hv₁ =>
    rw [hv₁] at ih₁
    replace ⟨t₁', ht₁, ih₁⟩ := same_ok_implies ih₁
    subst ht₁
    simp [pe_ifSome_some hty]
    simp_do_let (evaluate x₂ env.request env.entities)
    case error e he =>
      rw [he] at ih₂
      exact same_error_implies_ifSome_error ih₂ hty₃
    case ok v₂ hv₂ =>
      rw [hv₂] at ih₂
      replace ⟨t₂', ht₂, ih₂⟩ := same_ok_implies ih₂
      subst ht₂
      simp only [pe_ifSome_some hty₃]
      simp only [pe_option_get_some] at hok hwo₁ hwo₂
      replace hwf₁ := evaluate_wf hwf₁ hv₁
      exact compileApp₂_implies_apply₂ heq.right hwf₁ hwo₁.left hwo₂.left ih₁ ih₂ hok

end Cedar.Thm

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
import Cedar.Thm.SymCC.Compiler.WellTyped
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.SymCC.Term.Interpret

/-!
This file proves the compilation lemmas for `.hasAttr` and `.getAttr` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

private theorem compile_evaluate_hasAttr_record_aux
  {a : Attr} {t₂ : Term} {εs : SymEntities}
  {rty  : Map Attr TermType} {rt : Map Attr Term} {rv : Map Attr Value}
  (hwφ₂ : Term.WellFormed εs t₂ ∧ Term.typeOf t₂ = TermType.option TermType.bool)
  (ha : match Map.find? rty a with
        | some (TermType.option _) => t₂ = Term.some (isSome (record.get (Term.record rt) a))
        | some _ => t₂ = Term.some (Term.prim (TermPrim.bool true))
        | none => t₂ = Term.some (Term.prim (TermPrim.bool false)))
  (hwo  : Term.WellFormed εs (Term.record rt) ∧ Term.typeOf (Term.record rt) = TermType.record rty)
  (hlit : Term.isLiteral (Term.record rt) = true)
  (ih   : Term.value? (Term.record rt) = some (Value.record rv)) :
  (Except.ok (Value.prim (Prim.bool (Map.contains rv a))) : Spec.Result Value) ∼ t₂
:= by
  split at ha <;> subst ha
  case h_1 ty haty =>
    replace ⟨tₐ, hf, hty⟩ := typeOf_term_record_attr_value hwo.right haty
    simp only [Same.same, SameResults, SameValues, pe_record_get hf]
    replace hlit := lit_term_record_implies_lit_value hlit (Map.find?_mem_toList hf)
    replace hlit := And.intro (wf_term_record_implies hwo.left hf) hlit
    have htₐ := wfl_of_type_option_is_option hlit hty
    rcases htₐ with htₐ | ⟨t', htₐ, _⟩ <;>
    subst htₐ
    case inl =>
      replace hf := record_value?_find?_optional_none (wf_term_record_implies_wf_map hwo.left) hf ih
      simp only [pe_isSome_none, value?_bool, Map.contains, hf, Option.isSome_none]
    case inr =>
      replace ⟨vₐ, hf, _⟩ := record_value?_find?_optional_some (wf_term_record_implies_wf_map hwo.left) hf ih
      simp only [pe_isSome_some, value?_bool, Option.some.injEq, Value.prim.injEq,
        Prim.bool.injEq]
      rw [eq_comm, Map.contains_iff_some_find?]
      exists vₐ
  case h_2 aty hnopt haty =>
    replace ⟨tₐ, hf, hf'⟩ := typeOf_term_record_attr_value hwo.right haty
    subst hf'
    replace ⟨vₐ, hf, _⟩ := record_value?_find?_required (wf_term_record_implies_wf_map hwo.left) hnopt hf ih
    simp only [Same.same, SameResults, SameValues, value?_bool, Option.some.injEq,
      Value.prim.injEq, Prim.bool.injEq]
    rw [eq_comm, Map.contains_iff_some_find?]
    exists vₐ
  case h_3 heq =>
    replace heq := typeOf_term_record_attr_value_none hwo.right heq
    replace heq := record_value?_find?_none (wf_term_record_implies_wf_map hwo.left) heq ih
    simp only [Same.same, SameResults, SameValues, value?_bool, Map.contains, heq,
      Option.isSome_none]

private theorem compile_evaluate_hasAttr_record
  {a : Attr} {v₁ : Value} {es : Entities}
  {εs : SymEntities} {t₁ t₂ : Term} {ty₁ : TermType} {rty rty': Map Attr TermType}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hty₁ : Term.typeOf t₁ = TermType.option ty₁)
  (hwo : Term.WellFormed εs (option.get t₁) ∧ Term.typeOf (option.get t₁) = TermType.record rty')
  (hwφ₂: Term.WellFormed εs t₂ ∧ Term.typeOf t₂ = TermType.option TermType.bool)
  (ha : RecordHasAttr t₂ (option.get t₁) rty a)
  (ih : (Except.ok v₁ : Spec.Result Value) ∼ t₁) :
  (hasAttr v₁ a es : Spec.Result Value) ∼ ifSome t₁ t₂
:= by
  simp only [RecordHasAttr, hwo.right, TermType.record.injEq] at ha
  replace ⟨hrty, ha⟩ := ha
  rw [eq_comm] at hrty ; subst hrty
  have ht₁ := same_ok_value_implies_lit ih
  replace ht₁ := wfl_of_type_option_is_option (And.intro hwφ₁ ht₁) hty₁
  rcases ht₁ with ht₁ | ⟨t₁', ht₁', hty₁'⟩
  case inl =>
    subst ht₁
    simp only [Same.same, SameResults] at ih
  case inr =>
    subst ht₁' hty₁'
    rw [pe_ifSome_some hwφ₂.right]
    simp only [pe_option_get_some] at *
    clear hty₁ hwφ₁
    have hlit := isLiteral_some.mp (same_ok_value_implies_lit ih)
    have ht₁ := hlit
    replace ⟨rt, ht₁⟩ := wfl_of_type_record_is_record (And.intro hwo.left ht₁) hwo.right
    subst ht₁
    simp only [Same.same, SameResults] at ih
    replace ⟨rv, hv, ih⟩ := same_record_term_implies ih
    subst hv
    simp only [hasAttr, attrsOf, Except.bind_ok]
    exact compile_evaluate_hasAttr_record_aux hwφ₂ ha hwo hlit ih

private theorem compile_evaluate_attrsOrEmpty
  {es : Entities} {εs : SymEntities} {uid : EntityUID} {fₐ : UnaryFunction} {rty : Map Attr TermType}
  (heq : SameEntities es εs)
  (hwε : SymEntities.WellFormed εs)
  (hf  : SymEntities.attrs εs uid.ty = some fₐ)
  (hwo : Term.WellFormed εs (Term.prim (TermPrim.entity uid)) ∧ Term.typeOf (Term.prim (TermPrim.entity uid)) = TermType.entity uid.ty)
  (hrty : TermType.record rty = Term.typeOf (app fₐ (Term.prim (TermPrim.entity uid))))
  (hwf : Value.WellFormed es (Value.prim (Prim.entityUID uid))) :
  ∃ rt,
    app fₐ (Term.prim (TermPrim.entity uid)) = .record rt ∧
    (Term.record rt).typeOf = .record rty ∧
    (Term.record rt).WellFormedLiteral εs ∧
    Term.value? (Term.record rt) = some (Value.record (Entities.attrsOrEmpty es uid))
:= by
  have ⟨d, hwf⟩ := wf_value_uid_implies_exists_entity_data hwf
  simp only [Entities.attrsOrEmpty, hwf]
  replace ⟨δ, hδ, heq⟩ := heq uid d hwf
  have hwφ := wf_εs_implies_wf_attrs hwε hf
  simp only [SymEntities.attrs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
  replace ⟨δ', hδ', hf⟩ := hf
  simp only [hδ, Option.some.injEq] at hδ'
  subst hδ' hf
  replace heq := heq.left
  rw [← hwo.right, eq_comm] at hwφ
  have hlit := same_value_implies_lit (same_value_implies_same heq)
  have hwa := wf_app hwo.left hwφ.right.left hwφ.left
  rw [eq_comm] at hrty
  have ⟨rt, hlit'⟩ := wfl_of_type_record_is_record (And.intro hwa.left hlit) hrty
  simp only [hlit'] at *
  simp only [SameValues] at heq
  exists rt
  simp only [hrty, heq, and_true, true_and]
  exact (And.intro hwa.left hlit)

private theorem compile_evaluate_hasAttr_entity
  {a : Attr} {v₁ : Value} {es : Entities}
  {εs : SymEntities} {t₁ t₂ : Term} {fₐ : UnaryFunction}
  {ety : EntityType} {rty : Map Attr TermType}
  (heq : SameEntities es εs)
  (hwε : εs.WellFormed)
  (hwf₁ : Value.WellFormed es v₁)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hty₁ : Term.typeOf t₁ = TermType.option (.entity ety))
  (hwo  : Term.WellFormed εs (option.get t₁) ∧ Term.typeOf (option.get t₁) = .entity ety)
  (hwφ₂ : Term.WellFormed εs t₂ ∧ Term.typeOf t₂ = TermType.option TermType.bool)
  (hf : εs.attrs ety = some fₐ)
  (ha : RecordHasAttr t₂ (app fₐ (option.get t₁)) rty a)
  (ih : (Except.ok v₁ : Spec.Result Value) ∼ t₁) :
  (hasAttr v₁ a es : Spec.Result Value) ∼ ifSome t₁ t₂
:= by
  simp only [RecordHasAttr] at ha
  replace ⟨hrty, ha⟩ := ha
  rw [eq_comm] at hrty
  have ht₁ := same_ok_value_implies_lit ih
  replace ht₁ := wfl_of_type_option_is_option (And.intro hwφ₁ ht₁) hty₁
  rcases ht₁ with ht₁ | ⟨t₁', ht₁', hty₁'⟩
  case inl =>
    subst ht₁
    simp only [Same.same, SameResults] at ih
  case inr =>
    subst ht₁'
    rw [pe_ifSome_some hwφ₂.right]
    simp only [pe_option_get_some] at *
    clear hty₁ hwφ₁
    have ht₁ := isLiteral_some.mp (same_ok_value_implies_lit ih)
    replace ⟨uid, ht₁, huid⟩ := wfl_of_type_entity_is_entity (And.intro hwo.left ht₁) hwo.right
    subst ht₁ huid
    simp only [Same.same, SameResults, SameValues, value?_entity, Option.some.injEq] at ih
    subst ih
    simp only [hasAttr, attrsOf, Except.bind_ok]
    replace ⟨rt, happ, hrty, hwfl, hv⟩ := compile_evaluate_attrsOrEmpty heq hwε hf hwo hrty hwf₁
    simp only [happ] at *
    exact compile_evaluate_hasAttr_record_aux
      hwφ₂ ha (And.intro hwfl.left hrty) hwfl.right hv

theorem compile_evaluate_hasAttr {x₁ : Expr} {a : Attr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.hasAttr x₁ a))
  (hwε : εnv.WellFormedFor (.hasAttr x₁ a))
  (hok : compile (.hasAttr x₁ a) εnv = .ok t)
  (ih  : CompileEvaluate x₁) :
  evaluate (.hasAttr x₁ a) env.request env.entities ∼ t
:= by
  replace ⟨t₁, t₂, hok, hr, ht⟩ := compile_hasAttr_ok_implies hok
  subst ht
  replace hwe := wf_env_for_hasAttr_implies hwe
  replace hwε := wf_εnv_for_hasAttr_implies hwε
  have ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwε hok
  replace ih := ih heq hwe hwε hok
  replace hwε := hwε.left.right
  have hwo := wf_option_get hwφ₁ hty₁
  have hwφ₂ := compileHasAttr_wf hwε hwo.left hr
  replace ⟨t₃, rty, hr, ha⟩ := compileHasAttr_ok_implies hr
  unfold evaluate
  simp_do_let (evaluate x₁ env.request env.entities)
  case error e he =>
    rw [he] at ih
    exact same_error_implies_ifSome_error ih hwφ₂.right
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    replace hr := compileAttrsOf_ok_implies hr
    rcases hr with ⟨rty', htyₒ, ht₃⟩ | ⟨ety, fₐ, htyₒ, hf, ht₃⟩ <;>
    subst ht₃ <;>
    simp only [hwo.right] at htyₒ <;>
    subst htyₒ
    case inl =>
      exact compile_evaluate_hasAttr_record hwφ₁ hty₁ hwo hwφ₂ ha ih
    case inr =>
      have hwf₁ := evaluate_wf hwe hv₁
      exact compile_evaluate_hasAttr_entity
       heq.right hwε hwf₁ hwφ₁ hty₁ hwo hwφ₂ hf ha ih

private theorem interpret_εs_attrs {εs : SymEntities} {I : Interpretation} {ety : EntityType} {fₐ : UnaryFunction}
  (hf  : SymEntities.attrs εs ety = some fₐ) :
  SymEntities.attrs (SymEntities.interpret I εs) ety = some (fₐ.interpret I)
:= by
  simp only [SymEntities.attrs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at *
  replace ⟨d, hf, hf'⟩ := hf
  subst hf'
  exists (d.interpret I)
  constructor
  case left =>
    simp only [SymEntities.interpret]
    simp only [Map.find?_mapOnValues_some (SymEntityData.interpret I) hf]
  case right =>
    simp only [SymEntityData.interpret]

private theorem interpret_compileAttrsOf {t t₁: Term} {εs : SymEntities} {I : Interpretation}
  (hwε : εs.WellFormed)
  (hI  : Interpretation.WellFormed I εs)
  (hwt : Term.WellFormed εs t₁)
  (hok : compileAttrsOf t₁ εs = Except.ok t) :
  compileAttrsOf (t₁.interpret I) (εs.interpret I) = .ok (t.interpret I)
:= by
  simp only [compileAttrsOf]
  have hwt' := interpret_term_wf hI hwt
  simp only [hwt'.right]
  simp only [compileAttrsOf] at hok
  split <;> rename_i heq <;> simp only [heq, Except.ok.injEq, reduceCtorEq] at hok
  case h_1 ety =>
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    rename_i fₐ hf ; subst hok
    have hwf := wf_εs_implies_wf_attrs hwε hf
    simp only [← heq] at hwf ; rw [eq_comm] at hwf
    simp only [interpret_εs_attrs hf, Except.ok.injEq]
    simp only [interpret_app hI hwt hwf.left hwf.right.left]
  case h_2 =>
    simp only [hok]

private theorem interpret_compileHasAttr {t t₁: Term} {a : Attr} {εs : SymEntities} {I : Interpretation}
  (hwε : εs.WellFormed)
  (hI  : Interpretation.WellFormed I εs)
  (hwt : Term.WellFormed εs t₁)
  (hok : compileHasAttr t₁ a εs = Except.ok t) :
  compileHasAttr (t₁.interpret I) a (εs.interpret I) = .ok (t.interpret I)
:= by
  simp only [compileHasAttr]
  replace ⟨t₂, rty, hok, ht⟩ := compileHasAttr_ok_implies hok
  have hok' := interpret_compileAttrsOf hwε hI hwt hok
  simp only [hok', Except.bind_ok]
  replace ⟨hty, ht⟩ := ht
  have hwt₂ := (compileAttrsOf_wf hwε hwt hok).left
  have hwt' := interpret_term_wf hI hwt₂
  simp only [hwt'.right, hty]
  split <;>
  rename_i heq <;>
  simp only [heq] at ht <;>
  subst ht <;>
  simp only [someOf, Except.ok.injEq]
  case h_1 =>
    simp only [
      interpret_term_some,
      interpret_isSome hI (wf_record_get hwt₂ hty heq).left,
      interpret_record_get I hwt₂ hty heq]
  case h_2 | h_3 =>
    simp only [interpret_term_some, interpret_term_prim]

private theorem compileAttrsOf_ok_typeOf {t t₁ t₂ : Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hok : compileAttrsOf t₁ εs = Except.ok t) :
  ∃ t₃, compileAttrsOf t₂ εs = Except.ok t₃ ∧ t₃.typeOf = t.typeOf
:= by
  simp only [compileAttrsOf]
  replace hok := compileAttrsOf_ok_implies hok
  simp only [hty] at hok
  rcases hok with ⟨rty, hty', ht⟩ | ⟨ety, fₐ, hty', ha, ht⟩
  case inl =>
    subst ht
    simp only [hty', Except.ok.injEq, hty, exists_eq_left']
  case inr =>
    subst ht
    simp only [hty', ha, Except.ok.injEq, exists_eq_left']
    have hwf := wf_εs_implies_wf_attrs hwε ha
    have ha₁ : t₁.typeOf = fₐ.argType := by simp only [hty, hty', hwf.right.left]
    have ha₂ : t₂.typeOf = fₐ.argType := by simp only [hty', hwf.right.left]
    replace ha₁ := (wf_app hw₁ ha₁ hwf.left).right
    replace ha₂ := (wf_app hw₂ ha₂ hwf.left).right
    simp only [ha₂, ha₁]

private theorem compileHasAttr_ok_typeOf {t t₁ t₂ : Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hok : compileHasAttr t₁ a εs = Except.ok t) :
  ∃ t₃, compileHasAttr t₂ a εs = Except.ok t₃
:= by
  simp only [compileHasAttr, someOf]
  replace ⟨t₄, rty, hok, ht⟩ := compileHasAttr_ok_implies hok
  have ⟨_, hok', hty'⟩ := compileAttrsOf_ok_typeOf hwε hw₁ hw₂ hty hok
  simp_do_let (compileAttrsOf t₂ εs)
  case error hra =>
    simp only [hok', reduceCtorEq] at hra
  case ok hra =>
    simp only [hok', Except.ok.injEq] at hra ; subst hra
    simp only [hty', ht.left]
    split <;> simp only [Except.ok.injEq, exists_eq']

private theorem compileHasAttr_false_of_getAttr_error_typeOf_eq
  {t₁ t₂ : Term} {a : Attr} {εs : SymEntities} {e : SymCC.Error}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hha : compileHasAttr t₁ a εs = .ok (⊙ false))
  (hga : compileGetAttr t₁ a εs = .error e) :
  compileHasAttr t₂ a εs = .ok (⊙ false)
:= by
  replace ⟨t₄, rty, hattrs, ht⟩ := compileHasAttr_ok_implies hha
  simp only [RecordHasAttr] at ht
  have hfind : rty.find? a = .none := by
    simp only [compileGetAttr, hattrs, Except.bind_ok, ht.left] at hga
    split at hga <;> simp_all
  have ⟨t₅, hattrs', hty'⟩ := compileAttrsOf_ok_typeOf hwε hw₁ hw₂ hty hattrs
  simp only [compileHasAttr, hattrs', Except.bind_ok, hty', ht.left, hfind]

private theorem compileGetAttr_noSuchAttribute_of_error_typeOf_eq
  {t₁ t₂ : Term} {a : Attr} {εs : SymEntities} {e : SymCC.Error}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hha : compileHasAttr t₁ a εs = .ok (⊙ false))
  (hga : compileGetAttr t₁ a εs = .error e) :
  compileGetAttr t₂ a εs = .error .noSuchAttribute
:= by
  obtain ⟨t₄, rty, hattrs, ht⟩ := compileHasAttr_ok_implies hha
  simp only [RecordHasAttr] at ht
  have hfind : rty.find? a = .none := by
    simp only [compileGetAttr, hattrs, Except.bind_ok, ht.left] at hga
    split at hga <;> simp_all
  have ⟨t₅, hattrs', hty'⟩ := compileAttrsOf_ok_typeOf hwε hw₁ hw₂ hty hattrs
  simp only [compileGetAttr, hattrs', Except.bind_ok, hty', ht.left, hfind]

private theorem interpret_compileGetAttr_error_of_compileHasAttr_false
  {t₁ : Term} {a : Attr} {εs : SymEntities} {I : Interpretation} {e : SymCC.Error}
  (hwε : εs.WellFormed)
  (hI : I.WellFormed εs)
  (hwt : t₁.WellFormed εs)
  (hha : compileHasAttr t₁ a εs = .ok (⊙ false))
  (hga : compileGetAttr t₁ a εs = .error e) :
  compileGetAttr (t₁.interpret I) a (εs.interpret I) = .error .noSuchAttribute
:= by
  replace ⟨t₂, rty, hattrs, ht⟩ := compileHasAttr_ok_implies hha
  simp only [RecordHasAttr] at ht
  have hfind : rty.find? a = .none := by
    simp only [compileGetAttr, hattrs, Except.bind_ok, ht.left] at hga
    split at hga <;> simp_all
  have hattrs' := interpret_compileAttrsOf hwε hI hwt hattrs
  have hwt₂ := (compileAttrsOf_wf hwε hwt hattrs).left
  have hty₂ := (interpret_term_wf hI hwt₂).right
  simp only [compileGetAttr, hattrs', Except.bind_ok, hty₂, ht.left, hfind]

private theorem interpret_option_get_aux {εs : SymEntities} {I : Interpretation} {t : Term} {ty : TermType}
  (hI  : I.WellFormed εs)
  (hwt : t.WellFormed εs)
  (hty : t.typeOf = .option ty) :
  Term.WellFormed (SymEntities.interpret I εs) (Term.interpret I (option.get t)) ∧
  Term.WellFormed (SymEntities.interpret I εs) (option.get (Term.interpret I t)) ∧
  Term.typeOf (Term.interpret I (option.get t)) = Term.typeOf (option.get (Term.interpret I t))
:= by
  have hdom := interpret_entities_same_domain εs I
  have hI'  := wf_interpretation_same_domain hdom hI
  have hwt' := wf_term_same_domain hdom hwt
  have hwo  := wf_option_get hwt hty
  have hwo' := wf_term_same_domain hdom hwo.left
  have h₁ := interpret_term_wf hI' hwo'
  have h₂ := interpret_term_wf hI' hwt' ; rw [hty] at h₂
  replace h₂ := wf_option_get h₂.left h₂.right
  simp only [h₁, h₂, hwo.right, and_self]

-- Helper: if compileHasAttr on the interpreted option.get succeeds, then compileHasAttr on
-- option.get of the interpreted term also succeeds.
private theorem compileHasAttr_interpret_ok {εs : SymEntities} {I : Interpretation}
  {t₁ t_ha : Term} {a : Attr} {ty : TermType}
  (hI : I.WellFormed εs) (hwε : εs.WellFormed)
  (hwt : t₁.WellFormed εs) (hty : t₁.typeOf = .option ty)
  (hi : compileHasAttr ((option.get t₁).interpret I) a (εs.interpret I) = .ok (t_ha.interpret I)) :
  ∃ t', compileHasAttr (option.get (t₁.interpret I)) a (εs.interpret I) = .ok t'
:= by
  have hwε' := interpret_εntities_wf hwε hI
  have ⟨hwo₁, hwo₂, hty'⟩ := interpret_option_get_aux hI hwt hty
  exact compileHasAttr_ok_typeOf hwε' hwo₁ hwo₂ hty' hi

theorem compile_interpret_hasAttr {x₁ : Expr} {a : Attr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.hasAttr x₁ a))
  (hok : compile (.hasAttr x₁ a) εnv = .ok t)
  (ih  : CompileInterpret x₁) :
  compile (.hasAttr x₁ a) (εnv.interpret I) = .ok (t.interpret I)
:= by
  have hwε' := interpret_εntities_wf hwε.left.right hI
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_hasAttr_ok_implies hok
  subst ht
  have hwφ₁ := wf_εnv_for_hasAttr_implies hwε
  replace ih := ih hI hwφ₁ hok
  replace ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok
  have hwo := wf_option_get hwφ₁ hty₁
  replace hi := interpret_compileHasAttr hwε.left.right hI hwo.left ha
  simp only [compile, ih, Except.bind_ok]
  simp_do_let (compileHasAttr (option.get (Term.interpret I t₂)) a (SymEnv.interpret I εnv).entities) <;>
  rename_i heq <;>
  simp only [SymEnv.interpret] at heq
  case error =>
    have ⟨_, hok'⟩ := compileHasAttr_interpret_ok hI hwε.left.right hwφ₁ hty₁ hi
    simp only [hok', reduceCtorEq] at heq
  case ok t₄ =>
    have ⟨hwφ₃, hty₃⟩ := compileHasAttr_wf hwε.left.right hwo.left ha
    simp only [interpret_ifSome hI hwφ₁ hwφ₃, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁] at hi
    have hwφ₂ := interpret_term_wfl hI hwφ₁ ; rw [hty₁] at hwφ₂
    have hty₄ : Term.typeOf t₄ = TermType.option TermType.bool := by
      have hwo' := wf_option_get hwφ₂.left.left hwφ₂.right
      have hwφ₄ := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo'.left
      exact (compileHasAttr_wf hwε' hwφ₄ heq).right
    rw [← (interpret_term_wf hI hwφ₃).right] at hty₃
    exact pe_ifSome_ok_get_eq_get' I (compileHasAttr · a (SymEntities.interpret I εnv.entities))
      hwφ₂ hty₃ hty₄ hi heq

private theorem compile_evaluate_getAttr_record_aux
  {a : Attr} {t₂ : Term} {tyₐ tyₐ' : TermType} {εs : SymEntities}
  {rty  : Map Attr TermType} {rt : Map Attr Term} {rv : Map Attr Value}
  (hwφ₂ : Term.WellFormed εs t₂)
  (htyₐ : Term.typeOf t₂ = TermType.option tyₐ)
  (ha : match tyₐ' with
        | TermType.option _ => t₂ = record.get (Term.record rt) a
        | _ => t₂ = Term.some (record.get (Term.record rt) a))
  (hf : Map.find? rty a = .some tyₐ')
  (hwo  : Term.WellFormed εs (Term.record rt) ∧ Term.typeOf (Term.record rt) = TermType.record rty)
  (hlit : Term.isLiteral (Term.record rt) = true)
  (ih   : Term.value? (Term.record rt) = some (Value.record rv)) :
  Map.findOrErr rv a Error.attrDoesNotExist ∼ t₂
:= by
  split at ha <;> subst ha
  case h_1 ty tyₐ' =>
    replace ⟨tₐ, hf, hty⟩ := typeOf_term_record_attr_value hwo.right hf
    simp only [Same.same, SameResults, SameValues, pe_record_get hf, Map.findOrErr]
    replace hlit := lit_term_record_implies_lit_value hlit (Map.find?_mem_toList hf)
    replace hlit := And.intro (wf_term_record_implies hwo.left hf) hlit
    have htₐ := wfl_of_type_option_is_option hlit hty
    rcases htₐ with htₐ | ⟨t', htₐ, _⟩ <;>
    subst htₐ
    case inl =>
      replace hf := record_value?_find?_optional_none (wf_term_record_implies_wf_map hwo.left) hf ih
      simp only [hf, ne_eq, not_false_eq_true, reduceCtorEq]
    case inr =>
      replace ⟨_, hf, hf'⟩ := record_value?_find?_optional_some (wf_term_record_implies_wf_map hwo.left) hf ih
      simp only [hf, hf']
  case h_2 aty hnopt =>
    replace ⟨tₐ, hf, hf'⟩ := typeOf_term_record_attr_value hwo.right hf
    subst hf'
    replace ⟨vₐ, hf', hf''⟩ := record_value?_find?_required (wf_term_record_implies_wf_map hwo.left) hnopt hf ih
    simp only [Same.same, SameResults, Map.findOrErr, hf', pe_record_get hf, SameValues, hf'']

private theorem compile_evaluate_getAttr_record
  {a : Attr} {v₁ : Value} {es : Entities}
  {εs : SymEntities} {t₁ t₂ : Term} {ty₁ tyₐ : TermType} {rty rty': Map Attr TermType}
  (hwφ₁ : Term.WellFormed εs t₁)
  (hty₁ : Term.typeOf t₁ = TermType.option ty₁)
  (hwo  : Term.WellFormed εs (option.get t₁) ∧ Term.typeOf (option.get t₁) = TermType.record rty')
  (hwφ₂ : Term.WellFormed εs t₂)
  (htyₐ : Term.typeOf t₂ = TermType.option tyₐ)
  (ha   : RecordGetAttr t₂ (option.get t₁) rty a)
  (ih   : (Except.ok v₁ : Spec.Result Value) ∼ t₁) :
  (getAttr v₁ a es : Spec.Result Value) ∼ ifSome t₁ t₂
:= by
  simp only [RecordGetAttr, hwo.right, TermType.record.injEq] at ha
  replace ⟨hrty, ha⟩ := ha
  rw [eq_comm] at hrty ; subst hrty
  have ht₁ := same_ok_value_implies_lit ih
  replace ht₁ := wfl_of_type_option_is_option (And.intro hwφ₁ ht₁) hty₁
  rcases ht₁ with ht₁ | ⟨t₁', ht₁', hty₁'⟩
  case inl =>
    subst ht₁
    simp only [Same.same, SameResults] at ih
  case inr =>
    subst ht₁' hty₁'
    rw [pe_ifSome_some htyₐ]
    simp only [pe_option_get_some] at *
    clear hty₁ hwφ₁
    have hlit := isLiteral_some.mp (same_ok_value_implies_lit ih)
    have ht₁ := hlit
    replace ⟨rt, ht₁⟩ := wfl_of_type_record_is_record (And.intro hwo.left ht₁) hwo.right
    subst ht₁
    simp only [Same.same, SameResults] at ih
    replace ⟨rv, hv, ih⟩ := same_record_term_implies ih
    subst hv
    simp only [getAttr, attrsOf, Except.bind_ok]
    replace ⟨tyₐ', hf, ha⟩ := ha
    exact compile_evaluate_getAttr_record_aux hwφ₂ htyₐ ha hf hwo hlit ih


private theorem compile_evaluate_getAttr_entity
  {a : Attr} {v₁ : Value} {es : Entities}
  {εs : SymEntities} {t₁ t₂ : Term} {fₐ : UnaryFunction}
  {ety : EntityType} {tyₐ : TermType} {rty : Map Attr TermType}
  (heq : SameEntities es εs)
  (hwε : εs.WellFormed)
  (hwf₁ : Value.WellFormed es v₁)
  (hwφ₁ : Term.WellFormed εs t₁)
  (hty₁ : Term.typeOf t₁ = TermType.option (.entity ety))
  (hwo  : Term.WellFormed εs (option.get t₁) ∧ Term.typeOf (option.get t₁) = .entity ety)
  (hwφ₂ : Term.WellFormed εs t₂)
  (htyₐ : Term.typeOf t₂ = TermType.option tyₐ)
  (hf : εs.attrs ety = some fₐ)
  (ha : RecordGetAttr t₂ (app fₐ (option.get t₁)) rty a)
  (ih : (Except.ok v₁ : Spec.Result Value) ∼ t₁) :
  (getAttr v₁ a es : Spec.Result Value) ∼ ifSome t₁ t₂
:= by
  simp only [RecordGetAttr] at ha
  replace ⟨hrty, ha⟩ := ha
  rw [eq_comm] at hrty
  have ht₁ := same_ok_value_implies_lit ih
  replace ht₁ := wfl_of_type_option_is_option (And.intro hwφ₁ ht₁) hty₁
  rcases ht₁ with ht₁ | ⟨t₁', ht₁', hty₁'⟩
  case inl =>
    subst ht₁
    simp only [Same.same, SameResults] at ih
  case inr =>
    subst ht₁'
    rw [pe_ifSome_some htyₐ]
    simp only [pe_option_get_some] at *
    clear hty₁ hwφ₁
    have ht₁ := isLiteral_some.mp (same_ok_value_implies_lit ih)
    replace ⟨uid, ht₁, huid⟩ := wfl_of_type_entity_is_entity (And.intro hwo.left ht₁) hwo.right
    subst ht₁ huid
    simp only [Same.same, SameResults, SameValues, value?_entity, Option.some.injEq] at ih
    subst ih
    simp only [getAttr, attrsOf]
    replace ⟨rt, happ, hrty, hwfl, hv⟩ := compile_evaluate_attrsOrEmpty heq hwε hf hwo hrty hwf₁
    replace ⟨vₐ, hwf₁⟩ := wf_value_uid_implies_exists_entity_data hwf₁
    rw [Entities.attrs, Map.findOrErr]
    simp only [hwf₁, Except.bind_ok]
    simp only [Entities.attrsOrEmpty, hwf₁] at hv
    simp only [happ] at *
    replace ⟨tₐ, hf, ha⟩ := ha
    exact compile_evaluate_getAttr_record_aux
      hwφ₂ htyₐ ha hf (And.intro hwfl.left hrty) hwfl.right hv

theorem compile_evaluate_getAttr {x₁ : Expr} {a : Attr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.getAttr x₁ a))
  (hwε : εnv.WellFormedFor (.getAttr x₁ a))
  (hok : compile (.getAttr x₁ a) εnv = .ok t)
  (ih  : CompileEvaluate x₁) :
  evaluate (.getAttr x₁ a) env.request env.entities ∼ t
:= by
  replace ⟨t₁, t₂, hok, hr, ht⟩ := compile_getAttr_ok_implies hok
  subst ht
  replace hwe := wf_env_for_getAttr_implies hwe
  replace hwε := wf_εnv_for_getAttr_implies hwε
  have ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwε hok
  replace ih := ih heq hwe hwε hok
  replace hwε := hwε.left.right
  have hwo := wf_option_get hwφ₁ hty₁
  have ⟨hwφ₂, tyₐ, htyₐ⟩  := compileGetAttr_wf hwε hwo.left hr
  replace ⟨t₃, rty, hr, ha⟩ := compileGetAttr_ok_implies hr
  unfold evaluate
  simp_do_let (evaluate x₁ env.request env.entities)
  case error e he =>
    rw [he] at ih
    exact same_error_implies_ifSome_error ih htyₐ
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    replace hr := compileAttrsOf_ok_implies hr
    rcases hr with ⟨rty', htyₒ, ht₃⟩ | ⟨ety, fₐ, htyₒ, hf, ht₃⟩ <;>
    subst ht₃ <;>
    simp only [hwo.right] at htyₒ <;>
    subst htyₒ
    case inl =>
      exact compile_evaluate_getAttr_record hwφ₁ hty₁ hwo hwφ₂ htyₐ ha ih
    case inr =>
      have hwf₁ := evaluate_wf hwe hv₁
      exact compile_evaluate_getAttr_entity
       heq.right hwε hwf₁ hwφ₁ hty₁ hwo hwφ₂ htyₐ hf ha ih

private theorem interpret_compileGetAttr {t t₁: Term} {a : Attr} {εs : SymEntities} {I : Interpretation}
  (hwε : εs.WellFormed)
  (hI  : Interpretation.WellFormed I εs)
  (hwt : Term.WellFormed εs t₁)
  (hok : compileGetAttr t₁ a εs = Except.ok t) :
  compileGetAttr (t₁.interpret I) a (εs.interpret I) = .ok (t.interpret I)
:= by
  simp only [compileGetAttr]
  replace ⟨t₂, rty, hok, ht⟩ := compileGetAttr_ok_implies hok
  have hok' := interpret_compileAttrsOf hwε hI hwt hok
  simp only [hok', Except.bind_ok]
  replace ⟨hty, tyₐ, hf, ht⟩ := ht
  have hwt₂ := (compileAttrsOf_wf hwε hwt hok).left
  have hwt' := interpret_term_wf hI hwt₂
  simp only [hwt'.right, hty, hf]
  split <;>
  rename_i heq <;>
  simp only [Option.some.injEq, reduceCtorEq] at heq <;>
  subst heq <;>
  simp only [Except.ok.injEq]
  case h_1 =>
    split at ht <;>
    subst ht <;>
    simp only [interpret_record_get I hwt₂ hty hf]
  case h_2 =>
    split at ht
    case h_1 hneq =>
      simp only [TermType.option.injEq, forall_eq'] at hneq
    case h_2 =>
      subst ht
      simp only [
        someOf,
        interpret_term_some,
        interpret_record_get I hwt₂ hty hf]

private theorem compileGetAttr_ok_typeOf {t t₁ t₂ : Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hok : compileGetAttr t₁ a εs = Except.ok t) :
  ∃ t₃, compileGetAttr t₂ a εs = Except.ok t₃
:= by
  simp only [compileGetAttr, someOf]
  replace ⟨t₄, rty, hok, ht⟩ := compileGetAttr_ok_implies hok
  have ⟨_, hok', hty'⟩ := compileAttrsOf_ok_typeOf hwε hw₁ hw₂ hty hok
  simp_do_let (compileAttrsOf t₂ εs)
  case error hra =>
    simp only [hok', reduceCtorEq] at hra
  case ok hra =>
    simp only [hok', Except.ok.injEq] at hra ; subst hra
    simp only [hty', ht.left]
    split <;> simp only [Except.ok.injEq, exists_eq', reduceCtorEq]
    rename_i heq
    replace ⟨_, _, ht, _⟩ := ht
    simp only [heq, reduceCtorEq] at ht

-- Helper: if compileGetAttr on the interpreted option.get succeeds, then compileGetAttr on
-- option.get of the interpreted term also succeeds.
private theorem compileGetAttr_interpret_ok {εs : SymEntities} {I : Interpretation}
  {t₁ t_ga : Term} {a : Attr} {ty : TermType}
  (hI : I.WellFormed εs) (hwε : εs.WellFormed)
  (hwt : t₁.WellFormed εs) (hty : t₁.typeOf = .option ty)
  (hi : compileGetAttr ((option.get t₁).interpret I) a (εs.interpret I) = .ok (t_ga.interpret I)) :
  ∃ t', compileGetAttr (option.get (t₁.interpret I)) a (εs.interpret I) = .ok t'
:= by
  have hwε' := interpret_εntities_wf hwε hI
  have ⟨hwo₁, hwo₂, hty'⟩ := interpret_option_get_aux hI hwt hty
  exact compileGetAttr_ok_typeOf hwε' hwo₁ hwo₂ hty' hi

private theorem compileAttrsOf_ok_typeOf_eq {t₁ t₁' t₂ t₂' : Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hok₁ : compileAttrsOf t₁ εs = Except.ok t₁')
  (hok₂ : compileAttrsOf t₂ εs = Except.ok t₂') :
  t₁'.typeOf = t₂'.typeOf
:= by
  have h₁ := compileAttrsOf_ok_implies hok₁
  have h₂ := compileAttrsOf_ok_implies hok₂
  rcases h₁ with ⟨rty₁', h₁, h₁'⟩ | ⟨ety₁, f₁, h₁⟩ <;>
  rcases h₂ with ⟨rty₂', h₂, h₂'⟩ | ⟨ety₂, f₂, h₂⟩
  case inl.inr =>
    simp only [hty, h₂.left, reduceCtorEq] at h₁
  case inr.inl =>
    simp only [hty, h₂, false_and, reduceCtorEq] at h₁
  case inl.inl =>
    rw [eq_comm] at h₁' h₂'
    subst h₁' h₂'
    simp only [hty, h₂, TermType.record.injEq] at h₁
    subst h₁
    simp only [h₂] at hty
    simp only [hty, h₂]
  case inr.inr =>
    replace ⟨h₁, h₁', h₁''⟩ := h₁
    replace ⟨h₂, h₂', h₂''⟩ := h₂
    subst h₁'' h₂''
    simp only [hty, h₂, TermType.prim.injEq, TermPrimType.entity.injEq] at h₁
    subst h₁
    simp only [h₂', Option.some.injEq] at h₁'
    subst h₁'
    have hwf := wf_εs_implies_wf_attrs hwε h₂'
    have hwf₁ := hwf.right.left
    rw [← h₂, ← hty, eq_comm] at hwf₁
    replace hwf₁ := wf_app hw₁ hwf₁ hwf.left
    have hwf₂ := hwf.right.left
    rw [← h₂, eq_comm] at hwf₂
    replace hwf₂ := wf_app hw₂ hwf₂ hwf.left
    simp only [hwf₁.right, hwf₂.right]

private theorem compileGetAttr_ok_typeOf_eq {t t₁ t₂ t₃ : Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty : t₁.typeOf = t₂.typeOf)
  (hok₁ : compileGetAttr t₁ a εs = Except.ok t)
  (hok₂ : compileGetAttr t₂ a εs = Except.ok t₃) :
  t₃.typeOf = t.typeOf
:= by
  replace ⟨t₁', _, hok₁, ht₁⟩ := compileGetAttr_ok_implies hok₁
  replace ⟨t₂', _, hok₂, ht₂⟩ := compileGetAttr_ok_implies hok₂
  have heq := compileAttrsOf_ok_typeOf_eq hwε hw₁ hw₂ hty hok₁ hok₂
  replace ⟨heq₁, _, hf₁, ht₁⟩ := ht₁
  replace ⟨heq₂, _, hf₂, ht₂⟩ := ht₂
  replace hok₁ := wf_record_get (compileAttrsOf_wf hwε hw₁ hok₁).left heq₁ hf₁
  replace hok₂ := wf_record_get (compileAttrsOf_wf hwε hw₂ hok₂).left heq₂ hf₂
  simp only [heq, heq₂, TermType.record.injEq] at heq₁
  subst heq₁
  simp only [hf₁, Option.some.injEq] at hf₂
  subst hf₂
  split at ht₁
  all_goals {
    subst ht₁
    simp only at ht₂
    subst ht₂
    simp only [typeOf_term_some, hok₂, hok₁]
  }

theorem compile_interpret_getAttr {x₁ : Expr} {a : Attr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.getAttr x₁ a))
  (hok : compile (.getAttr x₁ a) εnv = .ok t)
  (ih  : CompileInterpret x₁) :
  compile (.getAttr x₁ a) (εnv.interpret I) = .ok (t.interpret I)
:= by
  have hwε' := interpret_εntities_wf hwε.left.right hI
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_getAttr_ok_implies hok
  subst ht
  have hwφ₁ := wf_εnv_for_getAttr_implies hwε
  replace ih := ih hI hwφ₁ hok
  replace ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok
  have hwo := wf_option_get hwφ₁ hty₁
  replace hi := interpret_compileGetAttr hwε.left.right hI hwo.left ha
  simp only [compile, ih, Except.bind_ok]
  simp_do_let (compileGetAttr (option.get (Term.interpret I t₂)) a (SymEnv.interpret I εnv).entities) <;>
  rename_i heq <;>
  simp only [SymEnv.interpret] at heq
  case error =>
    have ⟨_, hok'⟩ := compileGetAttr_interpret_ok hI hwε.left.right hwφ₁ hty₁ hi
    simp only [hok', reduceCtorEq] at heq
  case ok t₄ =>
    have ⟨hwφ₂, tyₐ, hty₂⟩ := compileGetAttr_wf hwε.left.right hwo.left ha
    simp only [interpret_ifSome hI hwφ₁ hwφ₂, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁] at hi
    have hwφ₃  := interpret_term_wfl hI hwφ₁ ; rw [hty₁] at hwφ₃
    have hty₄ : t₄.typeOf = .option tyₐ := by
      have hwo'  := wf_option_get hwφ₃.left.left hwφ₃.right
      have hwo'' := wf_option_get' hI hwφ₃.left.left hwφ₃.right
      have hwφ₄  := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo'.left
      have hwφ₄' := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo''.left
      have h := compileGetAttr_ok_typeOf_eq hwε' hwφ₄' hwφ₄ (by simp only [hwo''.right, hwo'.right]) hi heq
      simp only [interpret_term_wf hI hwφ₂] at h
      simp only [h, hty₂]
    rw [← (interpret_term_wf hI hwφ₂).right] at hty₂
    exact pe_ifSome_ok_get_eq_get' I (compileGetAttr · a (SymEntities.interpret I εnv.entities))
      hwφ₃ hty₂ hty₄ hi heq

private theorem compileExtHasAttr_none_eq {ty : TermType} {a : Attr} {rest : List Attr} {εs : SymEntities} {t : Term}
  (hwε : εs.WellFormed)
  (hwt : (Term.none ty).WellFormed εs)
  (hok : compileExtHasAttr (.none ty) (a :: rest) εs = .ok t) :
  t = .none .bool
:= by
  cases rest with
  | nil =>
    simp only [compileExtHasAttr, bind, Except.bind] at hok
    generalize hha : compileHasAttr (option.get (.none ty)) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
    have hty_ha := (compileHasAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hha).right
    simp only [Except.ok.injEq] at hok
    subst hok
    exact pe_ifSome_none hty_ha
  | cons b rest' =>
    simp only [compileExtHasAttr, bind, Except.bind] at hok
    generalize hha : compileHasAttr (option.get (.none ty)) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
    have hty_ha := (compileHasAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hha).right
    have hifs_ha_eq := pe_ifSome_none (gty := ty) hty_ha
    simp only [hifs_ha_eq] at hok
    -- Without short-circuit, go directly to compileGetAttr
    generalize hga : compileGetAttr (option.get (.none ty)) a εs = rga at hok
    cases rga with
    | error e =>
      cases e <;> simp_all
      simpa only [pure, Except.pure, Except.ok.injEq] using hok.symm
    | ok t_ga =>
    have ⟨_, ty_ga, hty_ga⟩ := compileGetAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hga
    have hifs_ga := pe_ifSome_none (gty := ty) hty_ga
    simp only [hifs_ga] at hok
    generalize hrest : compileExtHasAttr (.none ty_ga) (b :: rest') εs = rrest at hok
    cases rrest with
    | error => simp only [reduceCtorEq] at hok
    | ok t_rest =>
    have hwt_ga : (Term.none ty_ga).WellFormed εs := by
      have h := typeOf_wf_term_is_wf (compileGetAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hga).left
      rw [hty_ga] at h; cases h; exact Term.WellFormed.none_wf (by assumption)
    have hty_rest := (compileExtHasAttr_wf hwε hwt_ga ⟨_, typeOf_term_none _⟩ hrest).right
    simp only [compileAnd, typeOf_term_none, bind, Except.bind, hty_rest, ↓reduceIte,
      Except.ok.injEq] at hok
    rw [← hok]
    apply pe_ifSome_none
    have hwog := wf_option_get
      (Term.WellFormed.none_wf (εs := εs) TermType.WellFormed.bool_wf)
      (typeOf_term_none .bool)
    have hwt_rest :=
      (compileExtHasAttr_wf hwε hwt_ga ⟨_, typeOf_term_none _⟩ hrest).left
    have hwf_false : (⊙ Term.prim (TermPrim.bool false)).WellFormed εs :=
      (wf_term_some (εs := εs) wf_bool typeOf_bool).left
    have hty_ite := (wf_ite hwog.left hwt_rest hwf_false hwog.right
      (by simp [someOf, typeOf_term_some, typeOf_bool, hty_rest])).right
    simpa only [hty_rest] using hty_ite

-- Helper: from v ∼ t' and compileHasAttr t' a εs = .ok t_ha, derive hasAttr v a es ∼ t_ha
private theorem same_value_hasAttr {v : Value} {t' t_ha : Term} {a : Attr}
  {es : Entities} {εs : SymEntities}
  (heq : SameEntities es εs) (hwε : εs.WellFormed) (hwv : Value.WellFormed es v)
  (hwt : t'.WellFormed εs)
  (hha : compileHasAttr t' a εs = .ok t_ha)
  (ih' : v ∼ t') :
  (hasAttr v a es : Spec.Result Value) ∼ t_ha
:= by
  have hwφ₁ := Term.WellFormed.some_wf hwt
  have hwo := wf_option_get hwφ₁ typeOf_term_some
  have ih₁ := same_ok_some_iff.mpr ih'
  have hwφ₂ := compileHasAttr_wf hwε hwo.left hha
  replace ⟨t₃, rty, hattrs, ha⟩ := compileHasAttr_ok_implies hha
  replace hattrs := compileAttrsOf_ok_implies hattrs
  have hsame : (hasAttr v a es : Spec.Result Value) ∼ ifSome (Term.some t') t_ha := by
    rcases hattrs with ⟨rty', htyₒ, ht₃⟩ | ⟨ety, fₐ, htyₒ, hf, ht₃⟩ <;> rw [ht₃] at ha
    · exact compile_evaluate_hasAttr_record hwφ₁
        (by rw [typeOf_term_some, htyₒ]) ⟨hwo.left, htyₒ⟩ hwφ₂ ha ih₁
    · exact compile_evaluate_hasAttr_entity heq hwε hwv hwφ₁
        (by rw [typeOf_term_some, htyₒ]) ⟨hwo.left, htyₒ⟩ hwφ₂ hf ha ih₁
  rw [pe_ifSome_some hwφ₂.right] at hsame
  exact hsame

-- Helper: from v ∼ t' and compileGetAttr t' a εs = .ok t_ga, derive getAttr v a es ∼ t_ga
private theorem same_value_getAttr {v : Value} {t' t_ga : Term} {a : Attr}
  {es : Entities} {εs : SymEntities}
  (heq : SameEntities es εs) (hwε : εs.WellFormed) (hwv : Value.WellFormed es v)
  (hwt : t'.WellFormed εs)
  (hga : compileGetAttr t' a εs = .ok t_ga)
  (ih' : v ∼ t') :
  (getAttr v a es : Spec.Result Value) ∼ t_ga
:= by
  have hwφ₁ := Term.WellFormed.some_wf hwt
  have hwo := wf_option_get hwφ₁ typeOf_term_some
  have ih₁ := same_ok_some_iff.mpr ih'
  have ⟨hwφ₂, tyₐ, htyₐ⟩ := compileGetAttr_wf hwε hwo.left hga
  replace ⟨t₃, rty, hattrs, ha⟩ := compileGetAttr_ok_implies hga
  replace hattrs := compileAttrsOf_ok_implies hattrs
  have hsame : (getAttr v a es : Spec.Result Value) ∼ ifSome (Term.some t') t_ga := by
    rcases hattrs with ⟨rty', htyₒ, ht₃⟩ | ⟨ety, fₐ, htyₒ, hf, ht₃⟩ <;> rw [ht₃] at ha
    · exact compile_evaluate_getAttr_record hwφ₁
        (by rw [typeOf_term_some, htyₒ]) ⟨hwo.left, htyₒ⟩ hwφ₂ htyₐ ha ih₁
    · exact compile_evaluate_getAttr_entity heq hwε hwv hwφ₁
        (by rw [typeOf_term_some, htyₒ]) ⟨hwo.left, htyₒ⟩ hwφ₂ htyₐ hf ha ih₁
  rw [pe_ifSome_some htyₐ] at hsame
  exact hsame


private theorem getAttr_preserves_wf {v v_next : Value} {a : Attr} {es : Entities}
  (hwe : es.WellFormed)
  (hwv : Value.WellFormed es v)
  (hga : getAttr v a es = .ok v_next) :
  Value.WellFormed es v_next
:= by
  simp only [getAttr, attrsOf, Entities.attrs] at hga
  cases v with
  | prim p => cases p with
    | entityUID uid =>
      simp only [] at hga
      generalize hfind : Map.findOrErr es uid Error.entityDoesNotExist = rfind at hga
      cases rfind with
      | error => simp only [Except.bind_err, reduceCtorEq] at hga
      | ok d =>
        simp only [Except.bind_ok] at hga
        have hd : es.find? uid = .some d := by
          simp only [Map.findOrErr_ok_iff_find?_some] at hfind; exact hfind
        generalize hfa : Map.findOrErr d.attrs a Error.attrDoesNotExist = rfa at hga
        cases rfa with
        | error => simp only [reduceCtorEq] at hga
        | ok v' =>
          simp only [Except.ok.injEq] at hga; subst hga
          have hv : d.attrs.find? a = .some v' := by
            simp only [Map.findOrErr_ok_iff_find?_some] at hfa; exact hfa
          have hwf_d := (hwe.right uid d hd).left
          cases hwf_d; rename_i h₁ _; exact h₁ a v' hv
    | _ => simp only [Except.bind_err, reduceCtorEq] at hga
  | record avs =>
    simp only [Except.bind_ok] at hga
    generalize hfa : Map.findOrErr avs a Error.attrDoesNotExist = rfa at hga
    cases rfa with
    | error => simp only [reduceCtorEq] at hga
    | ok v' =>
      simp only [Except.ok.injEq] at hga; subst hga
      have hv : avs.find? a = .some v' := by
        simp only [Map.findOrErr_ok_iff_find?_some] at hfa; exact hfa
      cases hwv; rename_i h₁ _; exact h₁ a v' hv
  | set _ => simp only [Except.bind_err, reduceCtorEq] at hga
  | ext _ => simp only [Except.bind_err, reduceCtorEq] at hga

private theorem hasAttrs_loop_cons {v₁ v_next : Value} {a : Attr} {b : Attr} {rest : List Attr} {es : Entities}
  (hha : hasAttr v₁ a es = .ok (.prim (.bool true)))
  (hga : getAttr v₁ a es = .ok v_next) :
  hasAttrs.loop v₁ (a :: b :: rest) es = hasAttrs.loop v_next (b :: rest) es
:= by
  cases v₁ with
  | prim p => cases p with
    | entityUID uid =>
      simp only [hasAttr, attrsOf, Entities.attrsOrEmpty, Map.contains, Except.bind_ok,
        Except.ok.injEq] at hha
      simp only [getAttr, attrsOf, Entities.attrs] at hga
      generalize hfind : Map.findOrErr es uid Error.entityDoesNotExist = rfind at hga
      cases rfind with
      | error => simp only [Except.bind_err, reduceCtorEq] at hga
      | ok d =>
        simp only [Except.bind_ok] at hga
        have hd : es.find? uid = .some d := by
          simp only [Map.findOrErr_ok_iff_find?_some] at hfind; exact hfind
        have hfa : d.attrs.find? a = .some v_next := by
          simp only [Map.findOrErr_ok_iff_find?_some] at hga; exact hga
        simp only [hasAttrs.loop, attrsOf, Entities.attrsOrEmpty, hd, List.isEmpty_iff,
          reduceCtorEq, ↓reduceIte, hfa]
    | _ => simp only [hasAttr, attrsOf, Except.bind_err, reduceCtorEq] at hha
  | record avs =>
    simp only [getAttr, attrsOf, Except.bind_ok] at hga
    have hfa : avs.find? a = .some v_next := by
      simp only [Map.findOrErr_ok_iff_find?_some] at hga; exact hga
    simp only [hasAttrs.loop, attrsOf, List.isEmpty_iff, reduceCtorEq, ↓reduceIte, hfa]
  | set _ => simp only [hasAttr, attrsOf, Except.bind_err, reduceCtorEq] at hha
  | ext _ => simp only [hasAttr, attrsOf, Except.bind_err, reduceCtorEq] at hha


private theorem hasAttr_returns_bool {v₁ : Value} {a : Attr} {es : Entities} {v : Value}
  (hha : hasAttr v₁ a es = .ok v) : ∃ b, v = .prim (.bool b) := by
  simp only [hasAttr, attrsOf] at hha
  cases v₁ with
  | prim p => cases p with
    | entityUID _ => simp only [Except.bind_ok, Except.ok.injEq] at hha; subst hha; exact ⟨_, rfl⟩
    | _ => simp at hha
  | record _ => simp only [Except.bind_ok, Except.ok.injEq] at hha; subst hha; exact ⟨_, rfl⟩
  | set _ => simp at hha
  | ext _ => simp at hha

private theorem hasAttrs_loop_singleton_eq_hasAttr {v₁ : Value} {a : Attr} {es : Entities} :
    hasAttrs.loop v₁ [a] es = hasAttr v₁ a es := by
  simp only [hasAttrs.loop, hasAttr, attrsOf, List.isEmpty_iff]
  cases v₁ with
  | prim p => cases p with
    | entityUID uid => simp [Map.contains, Option.isSome]; cases (es.attrsOrEmpty uid).find? a <;> simp
    | _ => simp
  | record avs => simp [Map.contains, Option.isSome]; cases avs.find? a <;> simp
  | set _ => simp
  | ext _ => simp

private theorem hasAttr_true_implies_getAttr_ok {v₁ : Value} {a : Attr} {es : Entities} {e : Spec.Error}
    (hha : hasAttr v₁ a es = .ok (.prim (.bool true)))
    (hga : getAttr v₁ a es = .error e) : False := by
  simp only [hasAttr, getAttr, attrsOf, Entities.attrs, Entities.attrsOrEmpty, Map.contains] at hha hga
  cases v₁ with
  | prim p => cases p with
    | entityUID uid =>
      simp only [Except.bind_ok, Except.ok.injEq] at hha
      simp only [] at hga
      generalize hfind : Map.findOrErr es uid Error.entityDoesNotExist = rf at hga
      cases rf with
      | error =>
        simp only [Map.findOrErr] at hfind
        split at hfind
        · simp only [reduceCtorEq] at hfind
        · rename_i hfn
          have hfn' : es.find? uid = .none := by
            cases h : es.find? uid with
            | none => rfl
            | some d => exact (hfn d h).elim
          simp [hfn', Option.isSome] at hha
      | ok d =>
        simp only [Except.bind_ok] at hga
        have hd := Map.findOrErr_ok_iff_find?_some.mp hfind
        simp only [hd, Option.isSome] at hha
        simp only [Map.findOrErr] at hga
        split at hga
        · simp only [reduceCtorEq] at hga
        · rename_i hn
          cases hf : d.attrs.find? a with
          | some v => exact hn v hf
          | none => simp [hf] at hha
    | _ => simp only [Except.bind_err, reduceCtorEq] at hha
  | record avs =>
    simp only [Except.bind_ok, Except.ok.injEq] at hha
    simp only [Except.bind_ok, Map.findOrErr] at hga
    split at hga
    · simp only [reduceCtorEq] at hga
    · rename_i hn
      cases hf : avs.find? a with
      | some v => exact hn v hf
      | none => simp [hf, Option.isSome] at hha
  | set _ => simp only [Except.bind_err, reduceCtorEq] at hha
  | ext _ => simp only [Except.bind_err, reduceCtorEq] at hha

private theorem wfl_record_type_of_value {t : Term} {εs : SymEntities} {avs : Map Attr Value}
  (hwfl : t.WellFormedLiteral εs)
  (hval : t.value? = .some (.record avs)) :
  ∃ rty, t.typeOf = .record rty := by
  cases t with
  | record r => simp []
  | prim p => cases p <;> simp [Term.value?, TermPrim.value?, BitVec.int64?] at hval
              ; (try split at hval) <;> simp_all
  | set s ty =>
    simp only [Term.value?] at hval
    cases h : (s.elts.mapM₁ fun x => x.val.value?) <;> simp_all
  | _ => simp [Term.value?] at hval

private theorem wfl_entity_type_of_value {t : Term} {εs : SymEntities} {uid : EntityUID}
  (hwfl : t.WellFormedLiteral εs)
  (hval : t.value? = .some (.prim (.entityUID uid))) :
  ∃ ety, t.typeOf = .entity ety := by
  have hlit := hwfl.right
  cases t with
  | prim p => cases p with
    | entity uid' => simp []
    | bitvec =>
      simp only [Term.value?, TermPrim.value?, BitVec.int64?] at hval
      split at hval <;> simp at hval
    | _ => simp [Term.value?, TermPrim.value?] at hval
  | set s ty =>
    simp only [Term.value?] at hval
    cases h : (s.elts.mapM₁ fun x => x.val.value?) <;> simp_all
  | record r =>
    -- value? for records always returns Value.record _, never Value.prim _
    simp only [Term.value?, bind, Option.bind] at hval
    split at hval <;> simp at hval
  | _ => simp [Term.value?] at hval

private theorem hasAttrs_loop_false {v₁ : Value} {a : Attr} {rest : List Attr} {es : Entities}
  (hha : hasAttr v₁ a es = .ok (.prim (.bool false))) :
  hasAttrs.loop v₁ (a :: rest) es = .ok (.prim (.bool false)) := by
  simp only [hasAttr] at hha
  -- hha : (do let r ← attrsOf v₁ ...; .ok (r.contains a)) = .ok (.prim (.bool false))
  -- This means attrsOf v₁ ... = .ok r for some r, and r.contains a = false
  generalize hattr : attrsOf v₁ (fun uid => .ok (Entities.attrsOrEmpty es uid)) = rattr at hha
  cases rattr with
  | error => simp at hha
  | ok r =>
    simp only [Except.bind_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hha
    -- hha : r.contains a = false
    have hfind : r.find? a = .none := by
      simp only [Map.contains, Option.isSome_eq_false_iff] at hha
      exact Option.not_isSome_iff_eq_none.mp (by simp [hha])
    simp only [hasAttrs.loop, hattr, hfind]


private theorem compileHasAttr_eq_false_of_compileGetAttr_error
  {t t_ha : Term} {a : Attr} {εs : SymEntities} {e : SymCC.Error}
  (hha : compileHasAttr t a εs = .ok t_ha)
  (hga : compileGetAttr t a εs = .error e) :
  t_ha = (⊙ false)
:= by
  obtain ⟨t₂, rty, hattrs, hrecord⟩ := compileHasAttr_ok_implies hha
  simp only [RecordHasAttr] at hrecord
  simp only [compileGetAttr, hattrs, Except.bind_ok, hrecord.left] at hga
  split at hga <;> simp_all [someOf]

private theorem compile_evaluate_extHasAttr_loop
  {v₁ : Value} {t₁' : Term} {a : Attr} {l : List Attr}
  {es : Entities} {εs : SymEntities} {t : Term}
  (heq : SameEntities es εs)
  (hwε : εs.WellFormed)
  (hwe : es.WellFormed)
  (hwv : Value.WellFormed es v₁)
  (hwt : t₁'.WellFormed εs)
  (hok : compileExtHasAttr (.some t₁') (a :: l) εs = .ok t)
  (ih' : v₁ ∼ t₁') :
  hasAttrs.loop v₁ (a :: l) es ∼ t
:= by
  induction l generalizing a v₁ t₁' t with
  | nil =>
    simp only [compileExtHasAttr, bind, Except.bind] at hok
    generalize h₁ : compileHasAttr (option.get (Term.some t₁')) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
      simp only [pe_option_get_some] at h₁
      have h₂ := (compileHasAttr_wf hwε (wf_option_get (Term.WellFormed.some_wf hwt) typeOf_term_some).left h₁).right
      simp only [pe_ifSome_some h₂, Except.ok.injEq] at hok
      subst hok
      -- Goal: hasAttrs.loop v₁ [a] es ∼ t_ha
      rw [hasAttrs_loop_singleton_eq_hasAttr]
      exact same_value_hasAttr heq hwε hwv hwt h₁ ih'
  | cons b rest ih =>
    -- Unfold the compilation for the multi-attr case
    simp only [compileExtHasAttr, bind, Except.bind] at hok
    generalize h₁ : compileHasAttr (option.get (Term.some t₁')) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
    simp only [pe_option_get_some] at h₁
    have h₃ := (compileHasAttr_wf hwε (wf_option_get (Term.WellFormed.some_wf hwt) typeOf_term_some).left h₁).right
    -- key: from same_value_hasAttr, we know hasAttr v₁ a es ∼ t_ha
    have h₄ := same_value_hasAttr heq hwε hwv hwt h₁ ih'
    -- Case split on whether hasAttr succeeds or errors
    generalize h₅ : hasAttr v₁ a es = rha_v at h₄
    cases rha_v with
    | error e =>
      exfalso
      -- We know compileAttrsOf t₁' εs succeeded (from compileHasAttr succeeding)
      obtain ⟨t_attrs, rty, hattrs, _⟩ := compileHasAttr_ok_implies h₁
      have hattrs_impl := compileAttrsOf_ok_implies hattrs
      -- From v₁ ∼ t₁', we have t₁'.value? = some v₁
      have hv_same : t₁'.value? = .some v₁ := same_implies_same_value ih'
      -- hasAttr can only error if attrsOf errors, which only happens for non-record/non-entity values
      simp only [hasAttr, attrsOf] at h₅
      rcases hattrs_impl with ⟨_, hty_rec, _⟩ | ⟨ety, _, hty_ent, _, _⟩
      · -- t₁'.typeOf = record _
        -- v₁ must be a record value since v₁ ∼ t₁' and t₁' has record type
        have hlit := same_value_implies_lit ih'
        have ⟨rt, hrt⟩ := wfl_of_type_record_is_record ⟨hwt, hlit⟩ hty_rec
        subst hrt
        have ⟨rv, _, _⟩ := same_record_term_implies (same_implies_same_value ih')
        subst_vars
        simp at h₅
      · -- t₁'.typeOf = entity _
        have hlit := same_value_implies_lit ih'
        have ⟨uid, huid, _⟩ := wfl_of_type_entity_is_entity ⟨hwt, hlit⟩ hty_ent
        subst huid
        simp only [Same.same, SameValues, Term.value?, TermPrim.value?, Option.some.injEq] at ih'
        subst ih'
        simp at h₅
    | ok v_ha =>
      -- hasAttr succeeded with some value; it must be a bool
      have ⟨b_val, hb_val⟩ := hasAttr_returns_bool h₅
      subst hb_val
      have htha_eq := same_ok_bool_implies h₄; subst htha_eq
      cases b_val with
      | false =>
        -- The compiled hasAttr is statically false, so compileExtHasAttr returns it immediately.
        simp only [pe_ifSome_some h₃, pure, Except.pure, Except.ok.injEq] at hok
        subst t
        rw [hasAttrs_loop_false h₅]
        exact h₄
      | true =>
        -- hasAttr is true: recurse case
        -- hok : compileExtHasAttr (.some t₁') (a :: b :: rest) εs = .ok t
        -- t_ha = some (prim (bool true))
        -- Start fresh from hok
        have hok' := hok
        revert hok'
        simp only [pe_option_get_some, pe_ifSome_some h₃]
        intro hok'
        -- hok' is now: (compileGetAttr t₁' a εs >>= fun tGa => ...) = .ok t
        generalize hga : compileGetAttr t₁' a εs = rga at hok'
        cases rga with
        | error e =>
          have ht_ha := compileHasAttr_eq_false_of_compileGetAttr_error h₁ hga
          simp [someOf] at ht_ha
        | ok t_ga =>
        simp only [] at hok'
        have ⟨hwt_ga, _, hty_ga⟩ := compileGetAttr_wf hwε (wf_option_get (Term.WellFormed.some_wf hwt) typeOf_term_some).left hga
        -- Get the Same result for getAttr
        have hsame_ga := same_value_getAttr heq hwε hwv hwt hga ih'
        -- Since hasAttr is true, getAttr must succeed
        generalize hga_v : getAttr v₁ a es = rga_v at hsame_ga
        cases rga_v with
        | error e_ga =>
          exfalso; exact hasAttr_true_implies_getAttr_ok h₅ hga_v
        | ok v_next =>
          have ⟨t_ga', ht_ga_eq, hv_ga⟩ := same_ok_implies hsame_ga
          subst ht_ga_eq
          simp only [pe_ifSome_some hty_ga] at hok'
          -- hok' now has: match compileExtHasAttr (some t_ga') (b :: rest) εs with ...
          generalize hrest : compileExtHasAttr (Term.some t_ga') (b :: rest) εs = r_rest at hok'
          cases r_rest with
          | ok t_rest =>
            -- compileAnd (some true) (.ok t_rest) = .ok t
            have hty_some_ga : ∃ ty, (Term.some t_ga').typeOf = .option ty :=
              ⟨_, typeOf_term_some⟩
            have hty_rest := (compileExtHasAttr_wf hwε (Term.WellFormed.some_wf (wf_term_some_implies hwt_ga)) hty_some_ga hrest).right
            simp only [compileAnd, typeOf_term_some, typeOf_bool, bind, Except.bind, hty_rest,
              ↓reduceIte, pe_option_get_some, pe_ite_true, pe_ifSome_some hty_rest,
              Except.ok.injEq] at hok'
            subst hok'
            -- hasAttrs.loop v₁ (a :: b :: rest) es = hasAttrs.loop v_next (b :: rest) es
            rw [hasAttrs_loop_cons h₅ hga_v]
            have hwv_next := getAttr_preserves_wf hwe hwv hga_v
            exact ih hwv_next (wf_term_some_implies hwt_ga) hrest hv_ga
          | error => simp only [] at hok'; contradiction

theorem compile_evaluate_extHasAttr {x₁ : Expr} {a : Attr} {l : List Attr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.extHasAttr x₁ a l))
  (hwε : εnv.WellFormedFor (.extHasAttr x₁ a l))
  (hok : compile (.extHasAttr x₁ a l) εnv = .ok t)
  (ih  : CompileEvaluate x₁) :
  evaluate (.extHasAttr x₁ a l) env.request env.entities ∼ t
:= by
  unfold CompileEvaluate at ih
  rw [compile.eq_def] at hok
  simp only at hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hok₁
  replace hwe := wf_env_for_extHasAttr_implies hwe
  have hwφ₁ := wf_εnv_for_extHasAttr_implies hwε
  have ⟨hwt₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok₁
  have hce := compileExtHasAttr_wf hwε.left.right hwt₁ ⟨ty₁, hty₁⟩ hok
  replace ih := ih heq hwe hwφ₁ hok₁
  unfold evaluate
  simp_do_let (evaluate x₁ env.request env.entities)
  case error e he =>
    rw [he] at ih
    have ⟨hne, ty', ht₁⟩ := same_error_implies ih
    subst ht₁
    have ht : t = .none .bool := compileExtHasAttr_none_eq hwε.left.right hwt₁ hok
    subst ht
    exact same_error_implied_by hne
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    have ⟨t₁', ht₁, ih'⟩ := same_ok_implies ih
    subst ht₁
    exact compile_evaluate_extHasAttr_loop heq.right hwε.left.right hwe.left.right
      (evaluate_wf hwe hv₁) (wf_term_some_implies hwt₁) hok ih'



private theorem compileAnd_interpret {tl tr t : Term} {εnv : SymEnv} {I : Interpretation}
  (hI : I.WellFormed εnv.entities)
  (hwε : εnv.entities.WellFormed)
  (hwl : tl.WellFormed εnv.entities) (htyl : tl.typeOf = .option .bool)
  (hwr : tr.WellFormed εnv.entities) (htyr : tr.typeOf = .option .bool)
  (hok : compileAnd tl (.ok tr) = .ok t) :
  compileAnd (tl.interpret I) (.ok (tr.interpret I)) = .ok (t.interpret I)
:= by
  have h₁ := wf_option_get hwl htyl
  have h₂ := @wf_ite εnv.entities (option.get tl) tr (Term.some (Term.prim (TermPrim.bool false)))
    h₁.left hwr (Term.WellFormed.some_wf wf_bool)
    h₁.right (by simp only [Term.typeOf, typeOf_bool, htyr])
  have h₃ : (tl.interpret I).typeOf = .option .bool := by
    rw [(interpret_term_wf hI hwl).right]; exact htyl
  have h₄ : (tr.interpret I).typeOf = .option .bool := by
    rw [(interpret_term_wf hI hwr).right]; exact htyr
  -- Case analysis on whether tl is the false literal
  by_cases h₅ : tl = Term.some (Term.prim (TermPrim.bool false))
  case pos =>
    subst h₅
    simp only [compileAnd, Except.ok.injEq] at hok
    subst hok
    simp only [compileAnd, interpret_term_some, interpret_term_prim]
  case neg =>
    -- tl ≠ some (prim (bool false)), so compileAnd goes to h_2 branch
    have hok' : compileAnd tl (.ok tr) = .ok t := hok
    simp only [compileAnd] at hok
    split at hok
    case h_1 heq =>
      -- The split matched tl = some (prim (bool false)), contradiction with htl_false
      contradiction
    case h_2 =>
      simp only [Except.bind_ok, htyr, ↓reduceIte, Except.ok.injEq] at hok
      subst hok
      -- t = ifSome tl (ite (option.get tl) tr (⊙ false))
      -- Goal: compileAnd (tl.interpret I) (.ok (tr.interpret I)) = .ok ((ifSome tl (ite ...)).interpret I)
      simp only [someOf, interpret_ifSome hI hwl h₂.left,
        interpret_ite hI h₁.left hwr (wf_term_some wf_bool rfl).left
          h₁.right (by simp only [typeOf_term_some, typeOf_bool, htyr]),
        interpret_option_get I hwl htyl,
        interpret_term_some, interpret_term_prim]
      -- Goal: compileAnd (tl.interpret I) (.ok (tr.interpret I))
      --       = .ok (ifSome (tl.interpret I) (ite (option.get' I (tl.interpret I)) (tr.interpret I) (⊙ false)))
      simp only [compileAnd]
      split
      case h_1 heq_i =>
        -- tl.interpret I = some (prim (bool false))
        simp only [Except.ok.injEq, heq_i]
        simp only [pe_option_get'_some, pe_ite_false, pe_ifSome_some typeOf_term_some]
      case h_2 _ =>
        simp only [someOf, h₄, ↓reduceIte, Except.bind_ok, Except.ok.injEq, ExceptT.stM_eq]
        -- Goal: ifSome _ (ite (option.get _) ...) = ifSome _ (ite (option.get' I _) ...)
        -- Both sides use ifSome on a WellFormedLiteral guard of option type
        have hwfl := interpret_term_wfl hI hwl
        rw [htyl] at hwfl
        have hwε' := interpret_εntities_wf hwε hI
        have hdom := interpret_entities_same_domain εnv.entities I
        have hw_i := wf_term_same_domain hdom (interpret_term_wf hI hwl).left
        have hwr_i := wf_term_same_domain hdom (interpret_term_wf hI hwr).left
        have hog_i := wf_option_get hw_i h₃
        have hog'_raw := wf_option_get' hI (interpret_term_wf hI hwl).left h₃
        have hog'_i_wf := wf_term_same_domain hdom hog'_raw.left
        have hwf_false : (Term.some (Term.prim (TermPrim.bool false))).WellFormed (εnv.entities.interpret I) :=
          Term.WellFormed.some_wf (wf_bool (εs := εnv.entities.interpret I))
        have hty_f₁ := (wf_ite hog_i.left hwr_i hwf_false
          hog_i.right (by simp only [typeOf_term_some, typeOf_bool, h₄])).right
        have hty_f₂ := (wf_ite hog'_i_wf hwr_i hwf_false
          hog'_raw.right (by simp only [typeOf_term_some, typeOf_bool, h₄])).right
        rw [h₄] at hty_f₁ hty_f₂
        exact pe_ifSome_get_eq_get' I
          (fun x => Factory.ite x (tr.interpret I) (Term.some (Term.prim (TermPrim.bool false))))
          hwfl.left hwfl.right hty_f₁ hty_f₂
      case h_3 hty_i =>
        exfalso; simp only [h₃, imp_false, not_true_eq_false] at hty_i
    case h_3 hty =>
      -- typeOf tl ≠ .option .bool contradicts htyl
      rw [htyl] at hty; simp at hty

-- If compileHasAttr succeeds on option.get t₁ and t₁ has option type,
private theorem ifSome_none_bool (g : Term) :
  ifSome g (Term.none TermType.bool) = Term.none TermType.bool := by
  simp only [ifSome, Term.typeOf, noneOf]
  simp only [Factory.ite, Factory.ite.simplify]
  split <;> simp_all

private theorem compileAnd_none_eq {tr : Term} {εs : SymEntities}
  (hwtr : tr.WellFormed εs)
  (htyr : tr.typeOf = .option .bool) :
  compileAnd (.none .bool) (.ok tr) = .ok (.none .bool)
:= by
  simp only [compileAnd, typeOf_term_none, Except.bind_ok, htyr, ↓reduceIte]
  have hwog := wf_option_get
    (Term.WellFormed.none_wf (εs := εs) TermType.WellFormed.bool_wf)
    (typeOf_term_none .bool)
  have hwfalse : (⊙ Term.prim (TermPrim.bool false)).WellFormed εs :=
    (wf_term_some (εs := εs) wf_bool typeOf_bool).left
  have hty_ite := (wf_ite hwog.left hwtr hwfalse hwog.right
    (by simp [someOf, typeOf_term_some, typeOf_bool, htyr])).right
  simp only [Except.ok.injEq]
  exact pe_ifSome_none (hty_ite.trans htyr)

private theorem compileExtHasAttr_interpret {t₁ : Term} {attrs : List Attr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εnv.entities)
  (hwε : εnv.entities.WellFormed)
  (hw₁ : t₁.WellFormed εnv.entities) (hty₁ : ∃ ty, t₁.typeOf = .option ty)
  (hok : compileExtHasAttr t₁ attrs εnv.entities = .ok t) :
  compileExtHasAttr (t₁.interpret I) attrs (εnv.entities.interpret I) = .ok (t.interpret I)
:= by
  induction attrs generalizing t₁ t with
  | nil =>
    -- compileExtHasAttr t₁ [] εs = pure (⊙true) → t = ⊙true
    simp only [compileExtHasAttr, pure, Except.pure, Except.ok.injEq] at hok ⊢
    subst hok
    simp [interpret_term_some, interpret_term_prim]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [compileExtHasAttr, bind, Except.bind] at hok ⊢
      generalize hha : compileHasAttr (option.get t₁) a εnv.entities = rha at hok
      cases rha with
      | error => simp only [reduceCtorEq] at hok
      | ok t_ha =>
        simp only [Except.ok.injEq] at hok; subst hok
        have hwo := wf_option_get hw₁ hty₁.choose_spec
        have hi_ha := interpret_compileHasAttr hwε hI hwo.left hha
        -- Bridge option.get' vs option.get using pe_ifSome_ok_get_eq_get'
        have hwε' := interpret_εntities_wf hwε hI
        have hwt_ha := (compileHasAttr_wf hwε hwo.left hha).left
        have hty_ha := (compileHasAttr_wf hwε hwo.left hha).right
        simp_do_let (compileHasAttr (option.get (Term.interpret I t₁)) a (SymEntities.interpret I εnv.entities)) <;>
        rename_i heq
        case error =>
          have ⟨_, hok'⟩ := compileHasAttr_interpret_ok hI hwε hw₁ hty₁.choose_spec hi_ha
          simp only [hok', reduceCtorEq] at heq
        case ok t₄ =>
          simp only [interpret_ifSome hI hw₁ hwt_ha, Except.ok.injEq]
          rw [interpret_option_get I hw₁ hty₁.choose_spec] at hi_ha
          have hwφ₂ := interpret_term_wfl hI hw₁; rw [hty₁.choose_spec] at hwφ₂
          have hty₄ : t₄.typeOf = .option .bool := by
            have hwo' := wf_option_get hwφ₂.left.left hwφ₂.right
            have hwφ₄ := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo'.left
            exact (compileHasAttr_wf hwε' hwφ₄ heq).right
          rw [← (interpret_term_wf hI hwt_ha).right] at hty_ha
          exact pe_ifSome_ok_get_eq_get' I (compileHasAttr · a (SymEntities.interpret I εnv.entities))
            hwφ₂ hty_ha hty₄ hi_ha heq
    | cons b rest' =>
      -- Unfold compileExtHasAttr on both sides
      simp only [compileExtHasAttr, bind, Except.bind] at hok ⊢
      -- Extract compileHasAttr from hok
      generalize hha : compileHasAttr (option.get t₁) a εnv.entities = rha at hok
      cases rha with
      | error => simp only [reduceCtorEq] at hok
      | ok t_ha =>
      -- Extract compileGetAttr from hok
      generalize hga : compileGetAttr (option.get t₁) a εnv.entities = rga at hok
      cases rga with
      | error e =>
        have ht_ha := compileHasAttr_eq_false_of_compileGetAttr_error hha hga
        subst t_ha
        simp only [] at hok
        split at hok
        case h_1 heq =>
          simp only [pure, Except.pure, Except.ok.injEq] at hok
          subst t
          have hwo := wf_option_get hw₁ hty₁.choose_spec
          have hi_ha := interpret_compileHasAttr hwε hI hwo.left hha
          have hwε' := interpret_εntities_wf hwε hI
          have ⟨hwo_i₁, hwo_i₂, hty_i⟩ := interpret_option_get_aux hI hw₁ hty₁.choose_spec
          have hga_i := interpret_compileGetAttr_error_of_compileHasAttr_false
            hwε hI hwo.left hha hga
          simp only [interpret_someOf, interpret_term_prim] at hi_ha
          have hha_i := compileHasAttr_false_of_getAttr_error_typeOf_eq
            hwε' hwo_i₁ hwo_i₂ hty_i hi_ha hga_i
          have hwt_ha := (compileHasAttr_wf hwε hwo.left hha).left
          simp only [hha_i]
          have heq_i := congrArg (Term.interpret I) heq
          rw [interpret_ifSome hI hw₁ hwt_ha] at heq_i
          simp only [interpret_someOf, interpret_term_prim] at heq_i
          simp only [someOf] at heq heq_i ⊢
          simp only [interpret_term_some, interpret_term_prim] at heq_i
          rw [heq_i, heq]
          simp only [interpret_term_some, interpret_term_prim, pure, Except.pure]
        case h_2 =>
          cases e <;> simp_all
          simp only [pure, Except.pure, Except.ok.injEq] at hok
          subst t
          have hwo := wf_option_get hw₁ hty₁.choose_spec
          have hi_ha := interpret_compileHasAttr hwε hI hwo.left hha
          have hwε' := interpret_εntities_wf hwε hI
          have ⟨hwo_i₁, hwo_i₂, hty_i⟩ := interpret_option_get_aux hI hw₁ hty₁.choose_spec
          have hga_i := interpret_compileGetAttr_error_of_compileHasAttr_false
            hwε hI hwo.left hha hga
          simp only [interpret_someOf, interpret_term_prim] at hi_ha
          have hha_i := compileHasAttr_false_of_getAttr_error_typeOf_eq
            hwε' hwo_i₁ hwo_i₂ hty_i hi_ha hga_i
          have hga_i' := compileGetAttr_noSuchAttribute_of_error_typeOf_eq
            hwε' hwo_i₁ hwo_i₂ hty_i hi_ha hga_i
          have hwt_ha := (compileHasAttr_wf hwε hwo.left hha).left
          rw [interpret_ifSome hI hw₁ hwt_ha]
          simp only [hha_i, interpret_someOf, interpret_term_prim]
          split
          all_goals simp only [someOf, hga_i', pure, Except.pure]
      | ok t_ga =>
      -- WF setup
      have hwo := wf_option_get hw₁ hty₁.choose_spec
      have hwε' := interpret_εntities_wf hwε hI
      have hwt_ha := (compileHasAttr_wf hwε hwo.left hha).left
      have hty_ha := (compileHasAttr_wf hwε hwo.left hha).right
      have ⟨hwt_ga, tyₐ, hty_ga⟩ := compileGetAttr_wf hwε hwo.left hga
      -- Interpret compileHasAttr and compileGetAttr
      have hi_ha := interpret_compileHasAttr hwε hI hwo.left hha
      have hi_ga := interpret_compileGetAttr hwε hI hwo.left hga
      -- Bridge option.get' vs option.get for hasAttr
      simp_do_let (compileHasAttr (option.get (Term.interpret I t₁)) a (SymEntities.interpret I εnv.entities)) <;>
      rename_i heq_ha
      case error =>
        have ⟨_, hok'⟩ := compileHasAttr_interpret_ok hI hwε hw₁ hty₁.choose_spec hi_ha
        rw [hok'] at heq_ha
        simp at heq_ha
      case ok t_ha' =>
      have ⟨t_ga', heq_ga⟩ := compileGetAttr_interpret_ok hI hwε hw₁ hty₁.choose_spec hi_ga
      simp only [heq_ga]
      simp only [] at hok
      -- Now handle the recursive compileExtHasAttr on ifSome t₁ t_ga
      have hwt_next := (wf_ifSome_option hw₁ hwt_ga hty_ga).left
      have hty_next : ∃ ty, (ifSome t₁ t_ga).typeOf = .option ty :=
        ⟨_, (wf_ifSome_option hw₁ hwt_ga hty_ga).right⟩
      -- Split on original compileExtHasAttr result
      generalize hrest : compileExtHasAttr (ifSome t₁ t_ga) (b :: rest') εnv.entities = rrest at hok
      cases rrest with
      | ok t_rest =>
        -- Apply IH to get interpreted recursive result
        have hi_rest := ih hwt_next hty_next hrest
        rw [interpret_ifSome hI hw₁ hwt_ga] at hi_rest
        have hwφ₂ := interpret_term_wfl hI hw₁
        rw [hty₁.choose_spec] at hwφ₂
        have hdom := interpret_entities_same_domain εnv.entities I
        have hwo_i := wf_option_get hwφ₂.left.left hwφ₂.right
        have hwφ₄ := wf_term_same_domain hdom hwo_i.left
        have hwφ₅ := wf_term_same_domain hdom (interpret_term_wf hI hwo.left).left
        have hty_ga_i : (t_ga.interpret I).typeOf = .option tyₐ := by
          rw [(interpret_term_wf hI hwt_ga).right]
          exact hty_ga
        have hty_ga' : t_ga'.typeOf = .option tyₐ := by
          have h_eq := compileGetAttr_ok_typeOf_eq hwε' hwφ₅ hwφ₄
            (by exact (interpret_term_wf hI hwo.left).right.trans (hwo.right.trans hwo_i.right.symm)) hi_ga heq_ga
          exact h_eq.trans hty_ga_i
        -- Now rewrite hi_ga to use option.get'
        rw [interpret_option_get I hw₁ hty₁.choose_spec] at hi_ga
        have h_ifSome_ga := pe_ifSome_ok_get_eq_get' I
          (compileGetAttr · a (SymEntities.interpret I εnv.entities))
          hwφ₂ hty_ga_i hty_ga' hi_ga heq_ga
        rw [h_ifSome_ga, hi_rest]
        rw [interpret_option_get I hw₁ hty₁.choose_spec] at hi_ha
        have hty_ha_i : (t_ha.interpret I).typeOf = .option .bool := by
          rw [(interpret_term_wf hI hwt_ha).right]
          exact hty_ha
        have hty_ha' : t_ha'.typeOf = .option .bool :=
          (compileHasAttr_wf hwε' hwφ₄ heq_ha).right
        have h_ifSome_ha := pe_ifSome_ok_get_eq_get' I
          (compileHasAttr · a (SymEntities.interpret I εnv.entities))
          hwφ₂ hty_ha_i hty_ha' hi_ha heq_ha
        rw [h_ifSome_ha]
        have hwt_ifha := (wf_ifSome_option hw₁ hwt_ha hty_ha).left
        have hty_ifha := (wf_ifSome_option hw₁ hwt_ha hty_ha).right
        have hwt_rest := (compileExtHasAttr_wf hwε hwt_next hty_next hrest).left
        have hty_rest := (compileExtHasAttr_wf hwε hwt_next hty_next hrest).right
        rw [← interpret_ifSome hI hw₁ hwt_ha]
        split at hok
        case h_1 heq =>
          simp only [pure, Except.pure, Except.ok.injEq] at hok
          subst t
          rw [heq]
          simp only [interpret_term_some, interpret_term_prim, pure, Except.pure]
        case h_2 =>
          have hci := compileAnd_interpret hI hwε hwt_ifha hty_ifha hwt_rest hty_rest hok
          split
          case h_1 heq_i =>
            rw [heq_i] at hci ⊢
            simpa only [pure, Except.pure, compileAnd] using hci
          case h_2 => exact hci
      | error =>
        simp only [] at hok
        split at hok
        case h_1 heq =>
          simp only [pure, Except.pure, Except.ok.injEq] at hok
          subst t
          have hwφ₂ := interpret_term_wfl hI hw₁
          rw [hty₁.choose_spec] at hwφ₂
          have hdom := interpret_entities_same_domain εnv.entities I
          have hwo_i := wf_option_get hwφ₂.left.left hwφ₂.right
          have hwφ₄ := wf_term_same_domain hdom hwo_i.left
          rw [interpret_option_get I hw₁ hty₁.choose_spec] at hi_ha
          have hty_ha_i : (t_ha.interpret I).typeOf = .option .bool :=
            (interpret_term_wf hI hwt_ha).right.trans hty_ha
          have hty_ha' : t_ha'.typeOf = .option .bool :=
            (compileHasAttr_wf hwε' hwφ₄ heq_ha).right
          have h_ifSome_ha := pe_ifSome_ok_get_eq_get' I
            (compileHasAttr · a (SymEntities.interpret I εnv.entities))
            hwφ₂ hty_ha_i hty_ha' hi_ha heq_ha
          rw [h_ifSome_ha, ← interpret_ifSome hI hw₁ hwt_ha, heq]
          simp only [interpret_term_some, interpret_term_prim, pure, Except.pure]
        case h_2 => simp only [reduceCtorEq] at hok

theorem compile_interpret_extHasAttr {x₁ : Expr} {a : Attr} {l : List Attr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.extHasAttr x₁ a l))
  (hok : compile (.extHasAttr x₁ a l) εnv = .ok t)
  (ih  : CompileInterpret x₁) :
  compile (.extHasAttr x₁ a l) (εnv.interpret I) = .ok (t.interpret I)
:= by
  have hwφ₁ := wf_εnv_for_extHasAttr_implies hwε
  rw [compile.eq_def] at hok
  simp only at hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hok₁
  have ⟨hwt₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok₁
  have ih₁ := ih hI hwφ₁ hok₁
  simp only [compile, ih₁, Except.bind_ok]
  simp only [SymEnv.interpret]
  exact compileExtHasAttr_interpret hI hwε.left.right hwt₁ ⟨ty₁, hty₁⟩ hok

end Cedar.Thm

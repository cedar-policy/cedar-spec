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
      simp only [pe_isSome_none, bool_value?, Map.contains, hf, Option.isSome_none]
    case inr =>
      replace ⟨vₐ, hf, _⟩ := record_value?_find?_optional_some (wf_term_record_implies_wf_map hwo.left) hf ih
      simp only [pe_isSome_some, bool_value?, Option.some.injEq, Value.prim.injEq,
        Prim.bool.injEq]
      rw [eq_comm, Map.contains_iff_some_find?]
      exists vₐ
  case h_2 aty hnopt haty =>
    replace ⟨tₐ, hf, hf'⟩ := typeOf_term_record_attr_value hwo.right haty
    subst hf'
    replace ⟨vₐ, hf, _⟩ := record_value?_find?_required (wf_term_record_implies_wf_map hwo.left) hnopt hf ih
    simp only [Same.same, SameResults, SameValues, bool_value?, Option.some.injEq,
      Value.prim.injEq, Prim.bool.injEq]
    rw [eq_comm, Map.contains_iff_some_find?]
    exists vₐ
  case h_3 heq =>
    replace heq := typeOf_term_record_attr_value_none hwo.right heq
    replace heq := record_value?_find?_none (wf_term_record_implies_wf_map hwo.left) heq ih
    simp only [Same.same, SameResults, SameValues, bool_value?, Map.contains, heq,
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
    have hlit := lit_term_some_implies_lit (same_ok_value_implies_lit ih)
    have ht₁ := lit_term_some_implies_lit (same_ok_value_implies_lit ih)
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
    have ht₁ := lit_term_some_implies_lit (same_ok_value_implies_lit ih)
    replace ⟨uid, ht₁, huid⟩ := wfl_of_type_entity_is_entity (And.intro hwo.left ht₁) hwo.right
    subst ht₁ huid
    simp only [Same.same, SameResults, SameValues, entity_value?, Option.some.injEq] at ih
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
    have ⟨hwo₁, hwo₂, hty'⟩ := interpret_option_get_aux hI hwφ₁ hty₁
    have ⟨_, hok'⟩ := compileHasAttr_ok_typeOf hwε' hwo₁ hwo₂ hty' hi
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
    have hlit := lit_term_some_implies_lit (same_ok_value_implies_lit ih)
    have ht₁ := lit_term_some_implies_lit (same_ok_value_implies_lit ih)
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
    have ht₁ := lit_term_some_implies_lit (same_ok_value_implies_lit ih)
    replace ⟨uid, ht₁, huid⟩ := wfl_of_type_entity_is_entity (And.intro hwo.left ht₁) hwo.right
    subst ht₁ huid
    simp only [Same.same, SameResults, SameValues, entity_value?, Option.some.injEq] at ih
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
  case inl.intro.intro.inr =>
    simp only [hty, h₂.left, reduceCtorEq] at h₁
  case inr.intro.intro.inl =>
    simp only [hty, h₂, false_and, reduceCtorEq] at h₁
  case inl.intro.intro.inl =>
    rw [eq_comm] at h₁' h₂'
    subst h₁' h₂'
    simp only [hty, h₂, TermType.record.injEq] at h₁
    subst h₁
    simp only [h₂] at hty
    simp only [hty, h₂]
  case inr.intro.intro.inr =>
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
  replace ⟨t₁', rty₁, hok₁, ht₁⟩ := compileGetAttr_ok_implies hok₁
  replace ⟨t₂', rty₂, hok₂, ht₂⟩ := compileGetAttr_ok_implies hok₂
  have heq := compileAttrsOf_ok_typeOf_eq hwε hw₁ hw₂ hty hok₁ hok₂
  replace ⟨heq₁, tya₁, hf₁, ht₁⟩ := ht₁
  replace ⟨heq₂, tya₂, hf₂, ht₂⟩ := ht₂
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
    have ⟨hwo₁, hwo₂, hty'⟩ := interpret_option_get_aux hI hwφ₁ hty₁
    have ⟨_, hok'⟩ := compileGetAttr_ok_typeOf hwε' hwo₁ hwo₂ hty' hi
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

end Cedar.Thm

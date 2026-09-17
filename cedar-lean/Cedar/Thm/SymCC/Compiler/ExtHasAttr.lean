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

import Cedar.Thm.SymCC.Compiler.Attr

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

private theorem compileExtHasAttrRec_none_eq {ty : TermType} {a : Attr} {rest : List Attr} {εs : SymEntities} {t : Term}
  (hwε : εs.WellFormed)
  (hwt : (Term.none ty).WellFormed εs)
  (hok : compileExtHasAttrRec (.none ty) (a :: rest) εs = .ok t) :
  t = .none .bool
:= by
  cases rest with
  | nil =>
    simp only [compileExtHasAttrRec, bind, Except.bind] at hok
    generalize hha : compileHasAttr (option.get (.none ty)) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
    have hty_ha := (compileHasAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hha).right
    simp only [Except.ok.injEq] at hok
    subst hok
    exact pe_ifSome_none hty_ha
  | cons b rest' =>
    simp only [compileExtHasAttrRec, bind, Except.bind] at hok
    generalize hha : compileHasAttr (option.get (.none ty)) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
    have hty_ha := (compileHasAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hha).right
    have hifs_ha_eq := pe_ifSome_none (gty := ty) hty_ha
    simp only [hifs_ha_eq] at hok
    generalize hga : compileGetAttr (option.get (.none ty)) a εs = rga at hok
    cases rga with
    | error e =>
      cases e <;> simp_all
      simpa only [pure, Except.pure, Except.ok.injEq] using hok.symm
    | ok t_ga =>
    have ⟨_, ty_ga, hty_ga⟩ := compileGetAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hga
    have hifs_ga := pe_ifSome_none (gty := ty) hty_ga
    simp only [hifs_ga] at hok
    generalize hrest : compileExtHasAttrRec (.none ty_ga) (b :: rest') εs = rrest at hok
    cases rrest with
    | error => simp only [reduceCtorEq] at hok
    | ok t_rest =>
    have hwt_ga : (Term.none ty_ga).WellFormed εs := by
      have h := typeOf_wf_term_is_wf (compileGetAttr_wf hwε (wf_option_get hwt (typeOf_term_none ty)).left hga).left
      rw [hty_ga] at h; cases h; exact Term.WellFormed.none_wf (by assumption)
    have hty_rest := (compileExtHasAttrRec_wf hwε hwt_ga ⟨_, typeOf_term_none _⟩ hrest).right
    simp only [compileAnd, typeOf_term_none, bind, Except.bind, hty_rest, ↓reduceIte,
      Except.ok.injEq] at hok
    rw [← hok]
    apply pe_ifSome_none
    have hwog := wf_option_get
      (Term.WellFormed.none_wf (εs := εs) TermType.WellFormed.bool_wf)
      (typeOf_term_none .bool)
    have hwt_rest :=
      (compileExtHasAttrRec_wf hwε hwt_ga ⟨_, typeOf_term_none _⟩ hrest).left
    have hwf_false : (⊙ Term.prim (TermPrim.bool false)).WellFormed εs :=
      (wf_term_some (εs := εs) wf_bool typeOf_bool).left
    have hty_ite := (wf_ite hwog.left hwt_rest hwf_false hwog.right
      (by simp [someOf, typeOf_term_some, typeOf_bool, hty_rest])).right
    simpa only [hty_rest] using hty_ite

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
        simp only [hasAttrs.loop, attrsOf, Entities.attrsOrEmpty, hd, hfa]
    | _ => simp only [hasAttr, attrsOf, Except.bind_err, reduceCtorEq] at hha
  | record avs =>
    simp only [getAttr, attrsOf, Except.bind_ok] at hga
    have hfa : avs.find? a = .some v_next := by
      simp only [Map.findOrErr_ok_iff_find?_some] at hga; exact hga
    simp only [hasAttrs.loop, attrsOf, hfa]
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
  simp only [hasAttrs.loop, hasAttr, attrsOf]
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

private theorem hasAttrs_loop_false {v₁ : Value} {a : Attr} {rest : List Attr} {es : Entities}
  (hha : hasAttr v₁ a es = .ok (.prim (.bool false))) :
  hasAttrs.loop v₁ (a :: rest) es = .ok (.prim (.bool false)) := by
  simp only [hasAttr] at hha
  generalize hattr : attrsOf v₁ (fun uid => .ok (Entities.attrsOrEmpty es uid)) = rattr at hha
  cases rattr with
  | error => simp at hha
  | ok r =>
    simp only [Except.bind_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hha
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
  (hok : compileExtHasAttrRec (.some t₁') (a :: l) εs = .ok t)
  (ih' : v₁ ∼ t₁') :
  hasAttrs.loop v₁ (a :: l) es ∼ t
:= by
  induction l generalizing a v₁ t₁' t with
  | nil =>
    simp only [compileExtHasAttrRec, bind, Except.bind] at hok
    generalize h₁ : compileHasAttr (option.get (Term.some t₁')) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
      simp only [pe_option_get_some] at h₁
      have h₂ := (compileHasAttr_wf hwε (wf_option_get (Term.WellFormed.some_wf hwt) typeOf_term_some).left h₁).right
      simp only [pe_ifSome_some h₂, Except.ok.injEq] at hok
      subst hok
      rw [hasAttrs_loop_singleton_eq_hasAttr]
      exact same_value_hasAttr heq hwε hwv hwt h₁ ih'
  | cons b rest ih =>
    simp only [compileExtHasAttrRec, bind, Except.bind] at hok
    generalize h₁ : compileHasAttr (option.get (Term.some t₁')) a εs = rha at hok
    cases rha with
    | error => simp only [reduceCtorEq] at hok
    | ok t_ha =>
    simp only [pe_option_get_some] at h₁
    have h₃ := (compileHasAttr_wf hwε (wf_option_get (Term.WellFormed.some_wf hwt) typeOf_term_some).left h₁).right
    have h₄ := same_value_hasAttr heq hwε hwv hwt h₁ ih'
    generalize h₅ : hasAttr v₁ a es = rha_v at h₄
    cases rha_v with
    | error e =>
      exfalso
      obtain ⟨t_attrs, rty, hattrs, _⟩ := compileHasAttr_ok_implies h₁
      have hattrs_impl := compileAttrsOf_ok_implies hattrs
      have hv_same : t₁'.value? = .some v₁ := same_implies_same_value ih'
      simp only [hasAttr, attrsOf] at h₅
      rcases hattrs_impl with ⟨_, hty_rec, _⟩ | ⟨ety, _, hty_ent, _, _⟩
      · have hlit := same_value_implies_lit ih'
        have ⟨rt, hrt⟩ := wfl_of_type_record_is_record ⟨hwt, hlit⟩ hty_rec
        subst hrt
        have ⟨rv, _, _⟩ := same_record_term_implies (same_implies_same_value ih')
        subst_vars
        simp at h₅
      · have hlit := same_value_implies_lit ih'
        have ⟨uid, huid, _⟩ := wfl_of_type_entity_is_entity ⟨hwt, hlit⟩ hty_ent
        subst huid
        simp only [Same.same, SameValues, Term.value?, TermPrim.value?, Option.some.injEq] at ih'
        subst ih'
        simp at h₅
    | ok v_ha =>
      have ⟨b_val, hb_val⟩ := hasAttr_returns_bool h₅
      subst hb_val
      have htha_eq := same_ok_bool_implies h₄; subst htha_eq
      cases b_val with
      | false =>
        simp only [pe_ifSome_some h₃, pure, Except.pure, Except.ok.injEq] at hok
        subst t
        rw [hasAttrs_loop_false h₅]
        exact h₄
      | true =>
        have hok' := hok
        revert hok'
        simp only [pe_option_get_some, pe_ifSome_some h₃]
        intro hok'
        generalize hga : compileGetAttr t₁' a εs = rga at hok'
        cases rga with
        | error e =>
          have ht_ha := compileHasAttr_eq_false_of_compileGetAttr_error h₁ hga
          simp [someOf] at ht_ha
        | ok t_ga =>
        simp only [] at hok'
        have ⟨hwt_ga, _, hty_ga⟩ := compileGetAttr_wf hwε (wf_option_get (Term.WellFormed.some_wf hwt) typeOf_term_some).left hga
        have hsame_ga := same_value_getAttr heq hwε hwv hwt hga ih'
        generalize hga_v : getAttr v₁ a es = rga_v at hsame_ga
        cases rga_v with
        | error e_ga =>
          exfalso; exact hasAttr_true_implies_getAttr_ok h₅ hga_v
        | ok v_next =>
          have ⟨t_ga', ht_ga_eq, hv_ga⟩ := same_ok_implies hsame_ga
          subst ht_ga_eq
          simp only [pe_ifSome_some hty_ga] at hok'
          generalize hrest : compileExtHasAttrRec (Term.some t_ga') (b :: rest) εs = r_rest at hok'
          cases r_rest with
          | ok t_rest =>
            have hty_some_ga : ∃ ty, (Term.some t_ga').typeOf = .option ty :=
              ⟨_, typeOf_term_some⟩
            have hty_rest := (compileExtHasAttrRec_wf hwε (Term.WellFormed.some_wf (wf_term_some_implies hwt_ga)) hty_some_ga hrest).right
            simp only [compileAnd, typeOf_term_some, typeOf_bool, bind, Except.bind, hty_rest,
              ↓reduceIte, pe_option_get_some, pe_ite_true, pe_ifSome_some hty_rest,
              Except.ok.injEq] at hok'
            subst hok'
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
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  replace hwe := wf_env_for_extHasAttr_implies hwe
  have hwφ₁ := wf_εnv_for_extHasAttr_implies hwε
  have ⟨hwt₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok₁
  have hce := compileExtHasAttrRec_wf hwε.left.right hwt₁ ⟨ty₁, hty₁⟩ hok
  replace ih := ih heq hwe hwφ₁ hok₁
  unfold evaluate
  simp_do_let (evaluate x₁ env.request env.entities)
  case error e he =>
    rw [he] at ih
    have ⟨hne, ty', ht₁⟩ := same_error_implies ih
    subst ht₁
    have ht : t = .none .bool := compileExtHasAttrRec_none_eq hwε.left.right hwt₁ hok
    subst ht
    exact same_error_implied_by hne
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    have ⟨t₁', ht₁, ih'⟩ := same_ok_implies ih
    subst ht₁
    exact compile_evaluate_extHasAttr_loop heq.right hwε.left.right hwe.left.right
      (evaluate_wf hwe hv₁) (wf_term_some_implies hwt₁) hok ih'

private theorem compileAnd_interpret {t₁ t₂ t : Term} {εnv : SymEnv} {I : Interpretation}
  (hI : I.WellFormed εnv.entities)
  (hw₁ : t₁.WellFormed εnv.entities) (hty₁ : t₁.typeOf = .option .bool)
  (hw₂ : t₂.WellFormed εnv.entities) (hty₂ : t₂.typeOf = .option .bool)
  (hok : compileAnd t₁ (.ok t₂) = .ok t) :
  compileAnd (t₁.interpret I) (.ok (t₂.interpret I)) = .ok (t.interpret I)
:= by
  have h₁ := wf_option_get hw₁ hty₁
  have h₂ := @wf_ite εnv.entities (option.get t₁) t₂ (Term.some (Term.prim (TermPrim.bool false)))
    h₁.left hw₂ (Term.WellFormed.some_wf wf_bool)
    h₁.right (by simp only [Term.typeOf, typeOf_bool, hty₂])
  have h₃ : (t₁.interpret I).typeOf = .option .bool := by
    rw [(interpret_term_wf hI hw₁).right]; exact hty₁
  have h₄ : (t₂.interpret I).typeOf = .option .bool := by
    rw [(interpret_term_wf hI hw₂).right]; exact hty₂
  by_cases h₅ : t₁ = Term.some (Term.prim (TermPrim.bool false))
  case pos =>
    subst h₅
    simp only [compileAnd, Except.ok.injEq] at hok
    subst hok
    simp only [compileAnd, interpret_term_some, interpret_term_prim]
  case neg =>
    have hok' : compileAnd t₁ (.ok t₂) = .ok t := hok
    simp only [compileAnd] at hok
    split at hok
    case h_1 heq => contradiction
    case h_2 =>
      simp only [Except.bind_ok, hty₂, ↓reduceIte, Except.ok.injEq] at hok; subst hok
      simp only [someOf, interpret_ifSome hI hw₁ h₂.left,
        interpret_ite hI h₁.left hw₂ (wf_term_some wf_bool rfl).left
          h₁.right (by simp only [typeOf_term_some, typeOf_bool, hty₂]),
        interpret_option_get I hw₁ hty₁,
        interpret_term_some, interpret_term_prim]
      simp only [compileAnd]
      split
      case h_1 heq_i =>
        simp only [Except.ok.injEq, heq_i]
        simp only [pe_option_get'_some, pe_ite_false, pe_ifSome_some typeOf_term_some]
      case h_2 _ =>
        simp only [someOf, h₄, ↓reduceIte, Except.bind_ok, Except.ok.injEq, ExceptT.stM_eq]
        have hwfl := interpret_term_wfl hI hw₁
        rw [hty₁] at hwfl
        have h₆ := interpret_entities_same_domain εnv.entities I
        have h₇ := wf_term_same_domain h₆ (interpret_term_wf hI hw₁).left
        have h₈ := wf_term_same_domain h₆ (interpret_term_wf hI hw₂).left
        have h₉ := wf_option_get h₇ h₃
        have h₁₀ := wf_option_get' hI (interpret_term_wf hI hw₁).left h₃
        have h₁₁ := wf_term_same_domain h₆ h₁₀.left
        have h₁₂ : (Term.some (.prim (.bool false))).WellFormed (εnv.entities.interpret I) :=
          Term.WellFormed.some_wf (wf_bool (εs := εnv.entities.interpret I))
        have h₁₃ := (wf_ite h₉.left h₈ h₁₂ h₉.right
          (by simp only [typeOf_term_some, typeOf_bool, h₄])).right
        have h₁₄ := (wf_ite h₁₁ h₈ h₁₂ h₁₀.right
          (by simp only [typeOf_term_some, typeOf_bool, h₄])).right
        rw [h₄] at h₁₃ h₁₄
        exact pe_ifSome_get_eq_get' I
          (fun x => Factory.ite x (t₂.interpret I) (.some (.prim (.bool false))))
          hwfl.left hwfl.right h₁₃ h₁₄
      case h_3 hty_i =>
        exfalso; simp only [h₃, imp_false, not_true_eq_false] at hty_i
    case h_3 hty =>
      rw [hty₁] at hty; simp at hty

private theorem compileExtHasAttrRec_interpret {t₁ : Term} {attrs : List Attr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εnv.entities)
  (hwε : εnv.entities.WellFormed)
  (hw₁ : t₁.WellFormed εnv.entities) (hty₁ : ∃ ty, t₁.typeOf = .option ty)
  (hok : compileExtHasAttrRec t₁ attrs εnv.entities = .ok t) :
  compileExtHasAttrRec (t₁.interpret I) attrs (εnv.entities.interpret I) = .ok (t.interpret I)
:= by
  induction attrs generalizing t₁ t with
  | nil =>
    simp only [compileExtHasAttrRec, pure, Except.pure, Except.ok.injEq] at hok ⊢
    subst hok
    simp [interpret_term_some, interpret_term_prim]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [compileExtHasAttrRec, bind, Except.bind] at hok ⊢
      generalize h₁ : compileHasAttr (option.get t₁) a εnv.entities = rha at hok
      cases rha with
      | error => simp only [reduceCtorEq] at hok
      | ok t_ha =>
        simp only [Except.ok.injEq] at hok; subst hok
        have h₂ := wf_option_get hw₁ hty₁.choose_spec
        have h₃ := interpret_compileHasAttr hwε hI h₂.left h₁
        have h₄ := interpret_εntities_wf hwε hI
        have h₅ := (compileHasAttr_wf hwε h₂.left h₁).left
        have h₆ := (compileHasAttr_wf hwε h₂.left h₁).right
        simp_do_let (compileHasAttr (option.get (Term.interpret I t₁)) a (SymEntities.interpret I εnv.entities)) <;>
        rename_i h₇
        case error =>
          have ⟨_, hok'⟩ := compileHasAttr_interpret_ok hI hwε hw₁ hty₁.choose_spec h₃
          simp only [hok', reduceCtorEq] at h₇
        case ok t₄ =>
          simp only [interpret_ifSome hI hw₁ h₅, Except.ok.injEq]
          rw [interpret_option_get I hw₁ hty₁.choose_spec] at h₃
          have hwφ₂ := interpret_term_wfl hI hw₁; rw [hty₁.choose_spec] at hwφ₂
          have h₈ : t₄.typeOf = .option .bool := by
            have h₉ := wf_option_get hwφ₂.left.left hwφ₂.right
            have h₁₀ := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) h₉.left
            exact (compileHasAttr_wf h₄ h₁₀ h₇).right
          rw [← (interpret_term_wf hI h₅).right] at h₆
          exact pe_ifSome_ok_get_eq_get' I (compileHasAttr · a (SymEntities.interpret I εnv.entities))
            hwφ₂ h₆ h₈ h₃ h₇
    | cons b rest' =>
      simp only [compileExtHasAttrRec, bind, Except.bind] at hok ⊢
      generalize h₁ : compileHasAttr (option.get t₁) a εnv.entities = rha at hok
      cases rha with
      | error => simp only [reduceCtorEq] at hok
      | ok h₃ =>
        generalize h₂ : compileGetAttr (option.get t₁) a εnv.entities = rga at hok
        cases rga with
        | error e =>
          have h₄ := compileHasAttr_eq_false_of_compileGetAttr_error h₁ h₂
          subst h₃
          have h₅ := wf_option_get hw₁ hty₁.choose_spec
          have h₆ := interpret_compileHasAttr hwε hI h₅.left h₁
          have h₇ := interpret_εntities_wf hwε hI
          have ⟨h₈, h₉, h₁₀⟩ := interpret_option_get_aux hI hw₁ hty₁.choose_spec
          have h₁₁ := interpret_compileGetAttr_error_of_compileHasAttr_false hwε hI h₅.left h₁ h₂
          simp only [interpret_someOf, interpret_term_prim] at h₆
          have h₁₂ := compileHasAttr_false_of_getAttr_error_typeOf_eq h₇ h₈ h₉ h₁₀ h₆ h₁₁
          have h₁₃ := compileGetAttr_noSuchAttribute_of_error_typeOf_eq h₇ h₈ h₉ h₁₀ h₆ h₁₁
          have h₁₄ := (compileHasAttr_wf hwε h₅.left h₁).left
          simp only [] at hok
          split at hok
          case h_1 heq =>
            simp only [pure, Except.pure, Except.ok.injEq] at hok
            subst t
            simp only [h₁₂]
            have h₁₅ := congrArg (Term.interpret I) heq
            rw [interpret_ifSome hI hw₁ h₁₄] at h₁₅
            simp only [interpret_someOf, interpret_term_prim] at h₁₅
            simp only [someOf] at heq h₁₅ ⊢
            simp only [interpret_term_some, interpret_term_prim] at h₁₅
            rw [h₁₅, heq]
            simp only [interpret_term_some, interpret_term_prim, pure, Except.pure]
          case h_2 =>
            cases e <;> simp_all
            simp only [pure, Except.pure, Except.ok.injEq] at hok
            subst t
            rw [interpret_ifSome hI hw₁ h₁₄]
            simp only [interpret_someOf, interpret_term_prim]
            split
            all_goals simp only [someOf, pure, Except.pure]
        | ok t_ga =>
          have h₅ := wf_option_get hw₁ hty₁.choose_spec
          have h₆ := interpret_εntities_wf hwε hI
          have h₇ := (compileHasAttr_wf hwε h₅.left h₁).left
          have h₈ := (compileHasAttr_wf hwε h₅.left h₁).right
          have ⟨h₉, tyₐ, h₁₀⟩ := compileGetAttr_wf hwε h₅.left h₂
          have h₁₁ := interpret_compileHasAttr hwε hI h₅.left h₁
          have h₁₂ := interpret_compileGetAttr hwε hI h₅.left h₂
          simp_do_let (compileHasAttr (option.get (Term.interpret I t₁)) a (SymEntities.interpret I εnv.entities)) <;>
          rename_i h₁₃
          case error =>
            have ⟨_, h₁₄⟩ := compileHasAttr_interpret_ok hI hwε hw₁ hty₁.choose_spec h₁₁
            rw [h₁₄] at h₁₃
            simp at h₁₃
          case ok t_ha' =>
          have ⟨t_ga', h₁₄⟩ := compileGetAttr_interpret_ok hI hwε hw₁ hty₁.choose_spec h₁₂
          simp only [h₁₄]
          simp only [] at hok
          have h₁₅ := (wf_ifSome_option hw₁ h₉ h₁₀).left
          have h₁₆ : ∃ ty, (ifSome t₁ t_ga).typeOf = .option ty :=
            ⟨_, (wf_ifSome_option hw₁ h₉ h₁₀).right⟩
          have h₁₇ := interpret_term_wfl hI hw₁
          rw [hty₁.choose_spec] at h₁₇
          have h₁₈ := interpret_entities_same_domain εnv.entities I
          have h₁₉ := wf_option_get h₁₇.left.left h₁₇.right
          have h₂₀ := wf_term_same_domain h₁₈ h₁₉.left
          have h₂₁ := wf_term_same_domain h₁₈ (interpret_term_wf hI h₅.left).left
          have h₂₂ : (t_ga.interpret I).typeOf = .option tyₐ :=
            (interpret_term_wf hI h₉).right.trans h₁₀
          have h₂₃ : t_ga'.typeOf = .option tyₐ := by
            have h₂₄ := compileGetAttr_ok_typeOf_eq h₆ h₂₁ h₂₀
              (by exact (interpret_term_wf hI h₅.left).right.trans (h₅.right.trans h₁₉.right.symm)) h₁₂ h₁₄
            exact h₂₄.trans h₂₂
          rw [interpret_option_get I hw₁ hty₁.choose_spec] at h₁₁ h₁₂
          have h₂₄ := pe_ifSome_ok_get_eq_get' I
            (compileGetAttr · a (SymEntities.interpret I εnv.entities))
            h₁₇ h₂₂ h₂₃ h₁₂ h₁₄
          have h₂₅ : (h₃.interpret I).typeOf = .option .bool :=
            (interpret_term_wf hI h₇).right.trans h₈
          have h₂₆ : t_ha'.typeOf = .option .bool :=
            (compileHasAttr_wf h₆ h₂₀ h₁₃).right
          have h₂₇ := pe_ifSome_ok_get_eq_get' I
            (compileHasAttr · a (SymEntities.interpret I εnv.entities))
            h₁₇ h₂₅ h₂₆ h₁₁ h₁₃
          generalize h₂₈ : compileExtHasAttrRec (ifSome t₁ t_ga) (b :: rest') εnv.entities = rrest at hok
          cases rrest with
          | ok t_rest =>
            have h₂₉ := ih h₁₅ h₁₆ h₂₈
            rw [interpret_ifSome hI hw₁ h₉] at h₂₉
            rw [h₂₄, h₂₉, h₂₇]
            have h₃₀ := (wf_ifSome_option hw₁ h₇ h₈).left
            have h₃₁ := (wf_ifSome_option hw₁ h₇ h₈).right
            have h₃₂ := (compileExtHasAttrRec_wf hwε h₁₅ h₁₆ h₂₈).left
            have h₃₃ := (compileExtHasAttrRec_wf hwε h₁₅ h₁₆ h₂₈).right
            rw [← interpret_ifSome hI hw₁ h₇]
            split at hok
            case h_1 h₃₄ =>
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst t
              rw [h₃₄]
              simp only [interpret_term_some, interpret_term_prim, pure, Except.pure]
            case h_2 =>
              have h₃₄ := compileAnd_interpret hI h₃₀ h₃₁ h₃₂ h₃₃ hok
              split
              case h_1 h₃₅ =>
                rw [h₃₅] at h₃₄ ⊢
                simpa only [pure, Except.pure, compileAnd] using h₃₄
              case h_2 => exact h₃₄
          | error =>
            simp only [] at hok
            split at hok
            case h_1 h₂₉ =>
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst t
              rw [h₂₇, ← interpret_ifSome hI hw₁ h₇, h₂₉]
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
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  have ⟨hwt₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok₁
  have ih₁ := ih hI hwφ₁ hok₁
  simp only [compile, ih₁, Except.bind_ok]
  simp only [SymEnv.interpret]
  rw [compileExtHasAttr_eq_compileExtHasAttrRec]
  exact compileExtHasAttrRec_interpret hI hwε.left.right hwt₁ ⟨ty₁, hty₁⟩ hok

end Cedar.Thm

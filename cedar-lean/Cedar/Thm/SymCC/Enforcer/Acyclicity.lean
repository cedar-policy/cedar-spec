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
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.SymCC.Env.SWF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Enforcer.Util
import Cedar.Thm.SymCC.Compiler

/-!
This file proves properties of the `acyclicity` function in `Cedar/SymCC/Enforcer.lean`.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

private theorem pe_acyclicity_none {ety : EntityType} {εs : SymEntities} :
  acyclicity (.none (.entity ety)) εs = true
:= by
  simp only [acyclicity, typeOf_term_none]
  split <;> try rfl
  simp only [pe_isSome_none, pe_implies_false_left]

private theorem pe_acyclicity_some {uid : EntityUID} {εs : SymEntities} :
  acyclicity (.some (.entity uid)) εs =
  match εs.ancestorsOfType uid.ty uid.ty with
  | .some f => not (set.member (.entity uid) (app f (.entity uid)))
  | .none   => true
:= by
  simp only [acyclicity, typeOf_term_some, typeOf_term_prim_entity]
  cases εs.ancestorsOfType uid.ty uid.ty <;> simp only
  simp only [pe_isSome_some, pe_option_get_some, pe_implies_true_left]

private theorem interpret_acyclicity {t : Term} {ety : EntityType} {εs : SymEntities} {I : Interpretation} :
  εs.WellFormed →
  I.WellFormed εs →
  t.WellFormed εs →
  t.typeOf = .option (.entity ety) →
  Term.interpret I (acyclicity t εs) =
  acyclicity (t.interpret I) (εs.interpret I)
:= by
  intro hwε hI hwt hty
  have hlit := interpret_term_wfl hI hwt
  rw [hty] at hlit
  simp only [acyclicity, hty, hlit.right]
  cases hanc : εs.ancestorsOfType ety ety <;> simp only
  case none =>
    simp only [@interpret_entities_ancestorsOfType_none εs ety ety I hanc, interpret_term_prim]
  case some f =>
    simp only [@interpret_entities_ancestorsOfType_some εs ety ety I f hanc]
    have hwo := wf_option_get hwt hty
    have hwf := wf_εs_implies_wf_ancs hwε hanc
    rw [← hwo.right, eq_comm] at hwf
    have hwa := wf_app hwo.left hwf.right.left hwf.left
    rw [hwf.right.right] at hwa
    have hws := wf_set_member hwo.left hwa.left hwa.right
    have hwn := wf_not hws.left hws.right
    have hwi := wf_isSome hwt
    rw [
      interpret_implies hI hwi.left hwn.left hwi.right hwn.right,
      interpret_isSome hI hwt,
      interpret_not hI hws.left,
      interpret_set_member hwo.left hwa.left,
      interpret_app hI hwo.left hwf.left hwf.right.left,
      interpret_option_get I hwt hty]
    replace hlit := wfl_of_type_option_is_option hlit.left hlit.right
    rcases hlit with hlit | ⟨t', hlit, _⟩ <;> simp only [hlit]
    · simp only [pe_isSome_none, pe_implies_false_left]
    · simp only [pe_isSome_some, pe_option_get'_some, pe_option_get_some]

private theorem swf_implies_acyclic_entity (uid : EntityUID) {es : Entities} :
  es.StronglyWellFormed →
  ¬ uid ∈ es.ancestorsOrEmpty uid
:= by
  intro hse hin
  simp only [Entities.ancestorsOrEmpty] at hin
  cases hf : Map.find? es uid <;> simp only [hf] at hin
  case none =>
    have _ := Set.empty_no_elts uid
    contradiction
  case some d =>
    have _ := hse.right.left uid d hf
    contradiction

theorem swf_implies_interpret_acyclicity {x : Expr} {t : Term} {ety : EntityType} {env : Env} {εnv : SymEnv} {I : Interpretation}
  (heq : env ∼ SymEnv.interpret I εnv)
  (hI : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor x)
  (hse : env.StronglyWellFormedFor x)
  (hok : compile x εnv = Except.ok t)
  (hty : t.typeOf = .option (.entity ety)) :
  (acyclicity t εnv.entities).interpret I = true
:= by
  have hwt := (compile_wf hwε hok).left
  simp only [interpret_acyclicity hwε.left.right hI hwt hty]
  have ht := interpret_option_entity_term hI hwt hty
  rcases ht with ht | ⟨uid, ht, hty⟩
  · simp only [ht, pe_acyclicity_none]
  · subst hty
    simp only [ht, pe_acyclicity_some]
    split <;> try rfl
    rename_i f hanc
    have hv := compile_interpret_entity_implies_wf heq hI hwε (swf_env_for_implies_wf_for hse) hok ht
    replace ⟨ts, heq, hlit, huid⟩ := same_entities_ancestors_some_of_type heq.right hv hanc
    specialize huid uid rfl
    simp only [heq, pe_set_member hlit term_prim_is_lit]
    cases h : ts.contains (Term.prim (TermPrim.entity uid))
    · simp only [pe_not_false]
    · rw [Set.contains_prop_bool_equiv] at h
      replace huid := huid.mp h
      have _ := swf_implies_acyclic_entity uid hse.left.right
      contradiction

theorem interpret_acyclicity_implies_acyclic {t : Term} {ts : Set Term} {uid : EntityUID} {δ : SymEntityData} {f : UUF} {εnv : SymEnv} {I : Interpretation}
  (hwε : εnv.WellFormed)
  (hI  : I.WellFormed εnv.entities)
  (hwt : t.WellFormed εnv.entities)
  (hδ  : Map.find? εnv.entities uid.ty = some δ)
  (hf  : δ.ancestors.find? uid.ty = some (UnaryFunction.uuf f))
  (ht  : t.interpret I = (Term.entity uid).some)
  (heq : app ((UnaryFunction.uuf f).interpret I) (Term.entity uid) = Term.set ts (TermType.entity uid.ty))
  (ha  : Term.interpret I (acyclicity t εnv.entities) = true) :
  Term.entity uid ∉ ts
:= by
  have ⟨hwt', hty⟩ := wf_term_interpret_option_entity_implies_wf_typeOf hI hwt ht
  simp only [interpret_acyclicity hwε.right hI hwt hty, ht, pe_acyclicity_some,
    interpret_entities_ancestorsOfType_some (εs_ancestors_find?_implies_ancestorsOfType hδ hf)] at ha
  simp only [UnaryFunction.interpret] at *
  simp only [ht] at hwt'
  replace hwt' := wf_term_some_implies hwt'
  replace hwε := (hwε.right.right uid.ty δ hδ).right.right.right.left uid.ty (.uuf f) hf
  replace hI := hI.right.left f hwε.left
  have hlit := pe_app_wfl (And.intro hwt' term_prim_is_lit) hI.left
  simp only [heq] at ha hlit
  simp [pe_set_member hlit term_prim_is_lit] at ha
  cases hin : ts.contains (Term.entity uid) <;>
  simp only [hin, pe_not_true, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true] at ha
  by_contra hc
  simp [← Set.contains_prop_bool_equiv] at hc
  simp only [hc, Bool.true_eq_false] at hin

end Cedar.Thm

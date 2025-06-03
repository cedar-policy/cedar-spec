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
import Cedar.Thm.SymCC.Env.SWF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Compiler

/-!
This file contains helper lemmas that are shared by assumption proofs.
-/

namespace Cedar.Thm
open Data Spec SymCC Factory

theorem interpret_option_entity_term {εs : SymEntities} {I : Interpretation} {t : Term} {ety : EntityType}:
  I.WellFormed εs →
  t.WellFormed εs →
  t.typeOf = .option (.entity ety) →
  t.interpret I = .none (.entity ety) ∨
  ∃ uid : EntityUID, t.interpret I = .some (.entity uid) ∧ uid.ty = ety
:= by
  intro hI hwt hty
  replace ⟨hwt, htyI⟩ := interpret_term_wfl hI hwt
  rw [hty] at htyI
  have hlit := wfl_of_type_option_is_option hwt htyI
  rcases hlit with hlit | hlit
  · exact Or.inl hlit
  · replace ⟨t', hlit, hty'⟩ := hlit
    simp only [hlit, Term.some.injEq, false_or, reduceCtorEq] at *
    have hwt' : t'.WellFormedLiteral εs := And.intro (wf_term_some_implies hwt.left) (lit_term_some_implies_lit hwt.right)
    exact wfl_of_type_entity_is_entity hwt' hty'

theorem compile_interpret_entity_implies_wf {x : Expr} {t : Term} {env : Env} {εnv : SymEnv} {I : Interpretation}
  (heq : env ∼ SymEnv.interpret I εnv)
  (hI : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor x)
  (hwe : env.WellFormedFor x)
  (hok : compile x εnv = Except.ok t)
  (ht : Term.interpret I t = (Term.entity uid).some) :
  Value.WellFormed env.entities (Value.prim (Prim.entityUID uid))
:= by
  have hs := compile_bisimulation hwε hwe hI heq hok
  simp only [ht] at hs
  replace ⟨v, hv, hs⟩ := same_some_implies_ok hs
  replace hs := same_entity_term_implies hs
  subst hs
  exact evaluate_wf hwe hv

theorem wfl_entity {uid : EntityUID} {εs : SymEntities} :
  εs.isValidEntityUID uid →
  Term.WellFormedLiteral εs (Term.entity uid)
:= by
  intro h
  apply And.intro _ term_prim_is_lit
  exact Term.WellFormed.prim_wf (TermPrim.WellFormed.entity_wf h)

theorem εs_ancestors_find?_implies_ancestors {ety : EntityType} {δ : SymEntityData} {εs : SymEntities} :
  εs.find? ety = some δ →
  εs.ancestors ety = .some δ.ancestors
:= by
  intro hδ
  simp only [SymEntities.ancestors, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  exists δ

theorem εs_ancestors_find?_implies_ancestorsOfType {ety₁ ety₂ : EntityType} {δ : SymEntityData} {f : UnaryFunction} {εs : SymEntities} :
  εs.find? ety₁ = some δ →
  δ.ancestors.find? ety₂ = some f →
  εs.ancestorsOfType ety₁ ety₂ = some f
:= by
  intros hδ hf
  simp only [SymEntities.ancestorsOfType, SymEntities.ancestors, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  exists δ.ancestors
  simp only [hf, and_true]
  exists δ

theorem wf_term_interpret_option_entity_implies_wf_typeOf {t : Term} {uid : EntityUID} {εs : SymEntities} {I : Interpretation}
  (hI  : I.WellFormed εs)
  (hwt : t.WellFormed εs)
  (ht  : t.interpret I = (Term.entity uid).some) :
  (t.interpret I).WellFormed εs ∧
  t.typeOf = .option (.entity uid.ty)
:= by
  have ⟨hwt', hty'⟩ := interpret_term_wf hI hwt
  have hty := hty'
  rw [eq_comm] at hty
  simp only [ht, Term.typeOf, TermPrim.typeOf] at hty
  simp only [hwt', hty, and_self]

end Cedar.Thm

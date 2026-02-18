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
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Enforcer.Util
import Cedar.Thm.SymCC.Compiler

/-!
This file proves properties of the `transitivity` function in `Cedar/SymCC/Enforcer.lean`.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

private def transitivity.core (t₁ t₂ : Term) (ety₁ ety₂ : EntityType) (εs : SymEntities) : Term :=
  match εs.ancestorsOfType ety₁ ety₂, εs.ancestors ety₂ with
  | .some f₁₂, .some anc₂ =>
    let t₁' := option.get t₁
    let t₂' := option.get t₂
    implies (transitivity.isAncestor t₁ t₂ t₂' t₁' f₁₂) (transitivity.areAncestors εs t₂' anc₂ t₁' ety₁)
  | _, _ => true

private theorem transitivity_option_entity_implies {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} :
  t₁.typeOf = .option (.entity ety₁) →
  t₂.typeOf = .option (.entity ety₂) →
  transitivity t₁ t₂ εs =
  (if t₁ = t₂ then Term.bool true else transitivity.core t₁ t₂ ety₁ ety₂ εs)
:= by
  intro hty₁ hty₂
  split <;>
  rename_i h <;>
  simp only [transitivity, h, ↓reduceIte, hty₁, hty₂]
  cases h₁ : εs.ancestorsOfType ety₁ ety₂ <;>
  cases h₂ : εs.ancestors ety₂ <;>
  simp only [transitivity.core, h₁, h₂]

private theorem pe_transitivity_isAncestor_none_left {t₂ t₁' t₂' : Term} {ety₁ : EntityType} {f : UnaryFunction} :
  transitivity.isAncestor (.none (.entity ety₁)) t₂ t₁' t₂' f = false
:= by
  simp only [transitivity.isAncestor, pe_isSome_none, pe_and_false_left]

private theorem pe_transitivity_isAncestor_none_right {t₁ t₁' t₂' : Term} {ety₂ : EntityType} {f : UnaryFunction} :
  transitivity.isAncestor t₁ (.none (.entity ety₂)) t₁' t₂' f = false
:= by
  simp only [transitivity.isAncestor, pe_isSome_none, pe_and_false_right, pe_and_false_left]

private theorem pe_transitivity_isAncestor_some_some {uid₁ uid₂ : EntityUID} {f : UnaryFunction} :
  transitivity.isAncestor (Term.entity uid₁).some (Term.entity uid₂).some (.entity uid₂) (.entity uid₁) f =
  set.member (.entity uid₂) (app f (.entity uid₁))
:= by
  simp only [transitivity.isAncestor, pe_isSome_some, pe_and_true_left]

private theorem pe_transitivity_core_none_left {t₂ : Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} :
  transitivity.core (.none (.entity ety₁)) t₂ ety₁ ety₂ εs = true
:= by
  simp only [transitivity.core]
  split <;> try rfl
  simp only [pe_transitivity_isAncestor_none_left, pe_implies_false_left]

private theorem pe_transitivity_core_none_right {t₁ : Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} :
  transitivity.core t₁ (.none (.entity ety₂)) ety₁ ety₂ εs = true
:= by
  simp only [transitivity.core]
  split <;> try rfl
  simp only [pe_transitivity_isAncestor_none_right, pe_implies_false_left]

private theorem wf_app_anc {t₁ : Term} {ety₁ ety₂ : EntityType} {f₁₂ : UnaryFunction} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hwt₁ : Term.WellFormed εs t₁)
  (hty₁ : t₁.typeOf = TermType.entity ety₁)
  (hf₁₂ : εs.ancestorsOfType ety₁ ety₂ = some f₁₂) :
  (app f₁₂ t₁).WellFormed εs ∧ (app f₁₂ t₁).typeOf = .set (.entity ety₂)
:= by
  have hwf  := wf_εs_implies_wf_ancs hwε hf₁₂
  rw [← hty₁, eq_comm] at hwf
  have hwfa := wf_app hwt₁ hwf.right.left hwf.left
  rw [hwf.right.right] at hwfa
  exact hwfa

private theorem wf_transitivity_isAncestor {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {f₁₂ : UnaryFunction} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hwt₁ : Term.WellFormed εs t₁)
  (hwt₂ : Term.WellFormed εs t₂)
  (hty₁ : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂ : t₂.typeOf = (TermType.entity ety₂).option)
  (hf₁₂ : εs.ancestorsOfType ety₁ ety₂ = some f₁₂) :
  (transitivity.isAncestor t₁ t₂ (option.get t₂) (option.get t₁) f₁₂).WellFormed εs ∧
  (transitivity.isAncestor t₁ t₂ (option.get t₂) (option.get t₁) f₁₂).typeOf = .bool
:= by
  simp only [transitivity.isAncestor]
  have hwi₁ := wf_isSome hwt₁
  have hwi₂ := wf_isSome hwt₂
  have hwa₁ := wf_and hwi₁.left hwi₂.left hwi₁.right hwi₂.right
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwo₂ := wf_option_get hwt₂ hty₂
  have hwfa := wf_app_anc hwε hwo₁.left hwo₁.right hf₁₂
  rw [← hwo₂.right] at hwfa
  have hws  := wf_set_member hwo₂.left hwfa.left hwfa.right
  exact wf_and hwa₁.left hws.left hwa₁.right hws.right

private theorem wf_foldl_and {α} {xs : List α} {f : α → Term} {init : Term} {εs : SymEntities} :
  (∀ x ∈ xs, (f x).WellFormed εs ∧ (f x).typeOf = .bool) →
  init.WellFormed εs →
  init.typeOf = .bool →
  (xs.foldl (λ acc x => Factory.and acc (f x)) init).WellFormed εs ∧
  (xs.foldl (λ acc x => Factory.and acc (f x)) init).typeOf = .bool
:= by
  intro hwf hwi hty
  induction xs generalizing init
  case nil =>
    simp only [List.foldl_nil, hwi, hty, and_self]
  case cons xhd xtl ih =>
    simp only [List.foldl_cons]
    have hwh := hwf xhd (by simp only [List.mem_cons, true_or])
    replace hwh := wf_and hwi hwh.left hty hwh.right
    apply ih _ hwh.left hwh.right
    intro x hin
    apply hwf
    simp only [List.mem_cons, hin, or_true]

private theorem mem_ancestors_implies_ancestorsOfType {ety₁ ety₂ : EntityType} {ancs : Map EntityType UnaryFunction} {f : UnaryFunction} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hanc : εs.ancestors ety₁ = some ancs)
  (hin : (ety₂, f) ∈ ancs.toList) :
  εs.ancestorsOfType ety₁ ety₂ = some f
:= by
  simp only [SymEntities.ancestorsOfType, Option.bind_eq_bind, Option.bind_eq_some_iff]
  exists ancs
  simp only [hanc, true_and]
  simp only [SymEntities.ancestors, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hanc
  replace ⟨δ, hf, hanc⟩ := hanc
  subst hanc
  replace hwε := (hwε.right ety₁ δ hf).right.right.right.right.left
  exact (Map.in_list_iff_find?_some hwε).mp hin

private theorem wf_transitivity_areAncestorsOfType {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {f₂₃ : UnaryFunction} {εs : SymEntities}
  (hwε   : εs.WellFormed)
  (hwt₁  : Term.WellFormed εs t₁)
  (hwt₂  : Term.WellFormed εs t₂)
  (hty₁  : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂  : t₂.typeOf = (TermType.entity ety₂).option)
  (hf₂₃  : εs.ancestorsOfType ety₂ ety₃ = some f₂₃) :
  (transitivity.areAncestorsOfType εs (option.get t₂) f₂₃ ety₃ (option.get t₁) ety₁).WellFormed εs ∧
  (transitivity.areAncestorsOfType εs (option.get t₂) f₂₃ ety₃ (option.get t₁) ety₁).typeOf = .bool
:= by
  simp only [transitivity.areAncestorsOfType]
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwo₂ := wf_option_get hwt₂ hty₂
  have hw₂₃ := wf_app_anc hwε hwo₂.left hwo₂.right hf₂₃
  cases hanc₁ : εs.ancestorsOfType ety₁ ety₃ <;> simp only
  case none =>
    exact wf_set_isEmpty hw₂₃.left hw₂₃.right
  case some f₁₃ =>
    have hw₁₃ := wf_app_anc hwε hwo₁.left hwo₁.right hanc₁
    exact wf_set_subset hw₂₃.left hw₁₃.left hw₂₃.right hw₁₃.right

private theorem wf_transitivity_areAncestors {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {ancs₂ : Map EntityType UnaryFunction} {εs : SymEntities}
  (hwε   : εs.WellFormed)
  (hwt₁  : Term.WellFormed εs t₁)
  (hwt₂  : Term.WellFormed εs t₂)
  (hty₁  : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂  : t₂.typeOf = (TermType.entity ety₂).option)
  (hanc₂ : εs.ancestors ety₂ = some ancs₂) :
  (transitivity.areAncestors εs (option.get t₂) ancs₂ (option.get t₁) ety₁).WellFormed εs ∧
  (transitivity.areAncestors εs (option.get t₂) ancs₂ (option.get t₁) ety₁).typeOf = TermType.bool
:= by
  simp only [transitivity.areAncestors]
  apply wf_foldl_and _ wf_bool typeOf_bool
  intro (ety₃, f₂₃) hin
  have hf₂₃ := mem_ancestors_implies_ancestorsOfType hwε hanc₂ hin
  exact wf_transitivity_areAncestorsOfType hwε hwt₁ hwt₂ hty₁ hty₂ hf₂₃

private theorem interpret_app_anc {t₁ : Term} {ety₁ ety₂ : EntityType} {f₁₂ : UnaryFunction} {εs : SymEntities} {I : Interpretation}
  (hwε  : εs.WellFormed)
  (hI   : I.WellFormed εs)
  (hwt₁ : Term.WellFormed εs t₁)
  (hty₁ : t₁.typeOf = TermType.entity ety₁)
  (hf₁₂ : εs.ancestorsOfType ety₁ ety₂ = some f₁₂) :
  (app f₁₂ t₁).interpret I = app (f₁₂.interpret I) (t₁.interpret I)
:= by
  have hwf  := wf_εs_implies_wf_ancs hwε hf₁₂
  rw [← hty₁, eq_comm] at hwf
  simp only [interpret_app hI hwt₁ hwf.left hwf.right.left]

private theorem interpret_transitivity_isAncestor {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {f₁₂ : UnaryFunction} {εs : SymEntities}  {I : Interpretation}
  (hwε  : εs.WellFormed)
  (hI   : I.WellFormed εs)
  (hwt₁ : Term.WellFormed εs t₁)
  (hwt₂ : Term.WellFormed εs t₂)
  (hty₁ : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂ : t₂.typeOf = (TermType.entity ety₂).option)
  (hf₁₂ : εs.ancestorsOfType ety₁ ety₂ = some f₁₂) :
  (transitivity.isAncestor t₁ t₂ (option.get t₂) (option.get t₁) f₁₂).interpret I =
  transitivity.isAncestor (t₁.interpret I) (t₂.interpret I)
    (option.get' I (t₂.interpret I)) (option.get' I (t₁.interpret I))
    (f₁₂.interpret I)
:= by
  have hwi₁ := wf_isSome hwt₁
  have hwi₂ := wf_isSome hwt₂
  have hwa₁ := wf_and hwi₁.left hwi₂.left hwi₁.right hwi₂.right
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwo₂ := wf_option_get hwt₂ hty₂
  have hwfa := wf_app_anc hwε hwo₁.left hwo₁.right hf₁₂
  rw [← hwo₂.right] at hwfa
  have hws  := wf_set_member hwo₂.left hwfa.left hwfa.right
  simp only [
    transitivity.isAncestor,
    interpret_and hI hwa₁.left hws.left hwa₁.right hws.right,
    interpret_and hI hwi₁.left hwi₂.left hwi₁.right hwi₂.right,
    interpret_isSome hI hwt₁, interpret_isSome hI hwt₂,
    interpret_set_member hwo₂.left hwfa.left,
    interpret_option_get I hwt₂ hty₂,
    interpret_app_anc hwε hI hwo₁.left hwo₁.right hf₁₂,
    interpret_option_get I hwt₁ hty₁]

private theorem interpret_foldl_and {α} {xs : List α} (f : α → Term) {init : Term} {εs : SymEntities} {I : Interpretation} :
  I.WellFormed εs →
  (∀ x ∈ xs, (f x).WellFormed εs ∧ (f x).typeOf = .bool) →
  init.WellFormed εs →
  init.typeOf = .bool →
  (xs.foldl (λ acc x => Factory.and acc (f x)) init).interpret I =
  (xs.foldl (λ acc x => Factory.and acc ((f x).interpret I)) (init.interpret I))
:= by
  intro hI hwf hwi hty
  induction xs generalizing init
  case nil =>
    simp only [List.foldl_nil]
  case cons xhd xtl ih =>
    simp only [List.foldl_cons]
    have hwh := hwf xhd (by simp only [List.mem_cons, true_or])
    have hwa := wf_and hwi hwh.left hty hwh.right
    rw [ih _ hwa.left hwa.right]
    · simp only [interpret_and hI hwi hwh.left hty hwh.right]
    · intro x hin
      apply hwf
      simp only [List.mem_cons, hin, or_true]

private theorem interpret_transitivity_areAncestorsOfType {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {f₂₃ : UnaryFunction} {εs : SymEntities} {I : Interpretation}
  (hwε   : εs.WellFormed)
  (hI    : I.WellFormed εs)
  (hwt₁  : Term.WellFormed εs t₁)
  (hwt₂  : Term.WellFormed εs t₂)
  (hty₁  : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂  : t₂.typeOf = (TermType.entity ety₂).option)
  (hf₂₃  : εs.ancestorsOfType ety₂ ety₃ = some f₂₃) :
  (transitivity.areAncestorsOfType εs (option.get t₂) f₂₃ ety₃ (option.get t₁) ety₁).interpret I =
  transitivity.areAncestorsOfType (εs.interpret I) (option.get' I (t₂.interpret I))
    (f₂₃.interpret I) ety₃ (option.get' I (t₁.interpret I)) ety₁
:= by
  simp only [transitivity.areAncestorsOfType]
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwo₂ := wf_option_get hwt₂ hty₂
  have hw₂₃ := wf_app_anc hwε hwo₂.left hwo₂.right hf₂₃
  cases hanc₁ : εs.ancestorsOfType ety₁ ety₃ <;> simp only
  case none =>
    simp only [
      interpret_entities_ancestorsOfType_none hanc₁,
      interpret_set_isEmpty hI hw₂₃.left hw₂₃.right,
      interpret_app_anc hwε hI hwo₂.left hwo₂.right hf₂₃,
      interpret_option_get I hwt₂ hty₂]
  case some f₁₃ =>
    have hw₁₃ := wf_app_anc hwε hwo₁.left hwo₁.right hanc₁
    simp only [
      interpret_entities_ancestorsOfType_some hanc₁,
      interpret_set_subset hw₂₃.left hw₁₃.left,
      interpret_app_anc hwε hI hwo₂.left hwo₂.right hf₂₃,
      interpret_app_anc hwε hI hwo₁.left hwo₁.right hanc₁,
      interpret_option_get I hwt₁ hty₁,
      interpret_option_get I hwt₂ hty₂]

private theorem interpret_transitivity_areAncestors {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {ancs₂ : Map EntityType UnaryFunction} {εs : SymEntities}  {I : Interpretation}
  (hwε   : εs.WellFormed)
  (hI    : I.WellFormed εs)
  (hwt₁  : Term.WellFormed εs t₁)
  (hwt₂  : Term.WellFormed εs t₂)
  (hty₁  : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂  : t₂.typeOf = (TermType.entity ety₂).option)
  (hanc₂ : εs.ancestors ety₂ = some ancs₂) :
  (transitivity.areAncestors εs (option.get t₂) ancs₂ (option.get t₁) ety₁).interpret I =
  transitivity.areAncestors (εs.interpret I)
    (option.get' I (t₂.interpret I)) (Map.mapOnValues (UnaryFunction.interpret I) ancs₂) (option.get' I (t₁.interpret I)) ety₁
:= by
  let f := λ x : EntityType × UnaryFunction => transitivity.areAncestorsOfType εs (option.get t₂) x.snd x.fst (option.get t₁) ety₁
  have hwa : ∀ (x : EntityType × UnaryFunction), x ∈ ancs₂.1 → Term.WellFormed εs (f x) ∧ (f x).typeOf = TermType.bool := by
    intro (ety₃, f₂₃) hin
    have hf₂₃ := mem_ancestors_implies_ancestorsOfType hwε hanc₂ hin
    exact wf_transitivity_areAncestorsOfType hwε hwt₁ hwt₂ hty₁ hty₂ hf₂₃
  simp only [transitivity.areAncestors, Map.toList, interpret_foldl_and f hI hwa wf_bool typeOf_bool,
    Map.mapOnValues, List.foldl_map, f, interpret_term_prim]
  apply List.foldl_congr
  intro _ _ hin
  have hf₂₃ := mem_ancestors_implies_ancestorsOfType hwε hanc₂ hin
  simp only [interpret_transitivity_areAncestorsOfType hwε hI hwt₁ hwt₂ hty₁ hty₂ hf₂₃]

private theorem interpret_transitivity_core {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {εs : SymEntities} {I : Interpretation}
  (hwε  : εs.WellFormed)
  (hI   : I.WellFormed εs)
  (hwt₁ : Term.WellFormed εs t₁)
  (hwt₂ : Term.WellFormed εs t₂)
  (hty₁ : t₁.typeOf = (TermType.entity ety₁).option)
  (hty₂ : t₂.typeOf = (TermType.entity ety₂).option) :
  (transitivity.core t₁ t₂ ety₁ ety₂ εs).interpret I =
  transitivity.core (t₁.interpret I) (t₂.interpret I) ety₁ ety₂ (εs.interpret I)
:= by
  simp only [transitivity.core]
  cases hanc₁ : εs.ancestorsOfType ety₁ ety₂
  case none =>
    simp only [interpret_entities_ancestorsOfType_none hanc₁, interpret_term_prim]
  case some f₁₂ =>
    cases hanc₂ : εs.ancestors ety₂
    case none =>
      simp only [interpret_term_prim, interpret_entities_ancestors_none I hanc₂,
        imp_self, implies_true, reduceCtorEq]
    case some ancs₂ =>
      have hanc₁' := @interpret_entities_ancestorsOfType_some _ _ _ I _ hanc₁
      have hanc₂' := interpret_entities_ancestors_some I hanc₂
      simp only [hanc₁', hanc₂']
      have hwa₁ := wf_transitivity_isAncestor hwε hwt₁ hwt₂ hty₁ hty₂ hanc₁
      have hwa₂ := wf_transitivity_areAncestors hwε hwt₁ hwt₂ hty₁ hty₂ hanc₂
      simp only [
        interpret_implies hI hwa₁.left hwa₂.left hwa₁.right hwa₂.right,
        interpret_transitivity_isAncestor hwε hI hwt₁ hwt₂ hty₁ hty₂ hanc₁,
        interpret_transitivity_areAncestors hwε hI hwt₁ hwt₂ hty₁ hty₂ hanc₂]
      have ht₁ := interpret_option_entity_term hI hwt₁ hty₁
      have ht₂ := interpret_option_entity_term hI hwt₂ hty₂
      rcases ht₁ with ht₁ | ⟨_, ht₁, _⟩
      · simp only [ht₁, pe_transitivity_isAncestor_none_left, pe_implies_false_left]
      · rcases ht₂ with ht₂ | ⟨_, ht₂, _⟩
        · simp only [ht₂, pe_transitivity_isAncestor_none_right, pe_implies_false_left]
        · simp only [ht₁, ht₂, pe_option_get'_some, pe_option_get_some]

private theorem pe_foldl_and_not_true_implies {α} (xs : List α) (f : α → Term) {t : Term} :
  t ≠ true →
  xs.foldl (λ acc x => Factory.and acc (f x)) t ≠ true
:= by
  intro hnt
  induction xs generalizing t
  case nil =>
    simp only [List.foldl_nil, ne_eq, hnt, not_false_eq_true]
  case cons xhd xtl ih =>
    simp only [List.foldl_cons, ne_eq]
    apply ih
    by_contra ht
    replace ht := (pe_and_true_iff_true.mp ht).left
    contradiction

private theorem pe_foldl_and_true_iff {α} {xs : List α} {f : α → Term} :
  xs.foldl (λ acc x => Factory.and acc (f x)) true = true ↔
  ∀ x ∈ xs, f x = true
:= by
  induction xs
  case nil =>
    simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true]
  case cons xhd xtl ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro hf
      simp [pe_and_true_left] at hf
      cases ht : decide ((f xhd) = true) <;>
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at ht
      case false =>
        have _ := pe_foldl_and_not_true_implies xtl f ht
        contradiction
      case true =>
        simp only [ht, true_and] at *
        intro x hx
        exact ih.mp hf x hx
    · intro ⟨hhd, htl⟩
      simp only [hhd, pe_and_true_left, ih]
      intro x hx
      exact htl x hx

private theorem swf_implies_entity_transitive {uid₁ uid₂ uid₃ : EntityUID} {es : Entities}
  (hse  : es.StronglyWellFormed)
  (hin₁ : uid₂ ∈ es.ancestorsOrEmpty uid₁)
  (hin₂ : uid₃ ∈ es.ancestorsOrEmpty uid₂) :
  uid₃ ∈ es.ancestorsOrEmpty uid₁
:= by
  simp only [Entities.ancestorsOrEmpty] at *
  cases hf₁ : Map.find? es uid₁ <;> simp only [hf₁] at hin₁
  case none =>
    have _ := Set.empty_no_elts uid₂
    contradiction
  case some d₁ =>
    cases hf₂ : Map.find? es uid₂ <;> simp only [hf₂] at hin₂
    case none =>
      have _ := Set.empty_no_elts uid₃
      contradiction
    case some d₂ =>
      simp only
      have htr := hse.right.right uid₁ d₁ uid₂ d₂ hf₁ hf₂ hin₁
      exact Set.mem_subset_mem hin₂ htr

private theorem wfl_ancestors_implies_wfl_term_entity {uid  : EntityUID} {ety : EntityType} {f : UnaryFunction} {t : Term} {ts : Set Term} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hwt  : Term.WellFormed εs (Term.entity uid))
  (hanc : εs.ancestorsOfType uid.ty ety = some f)
  (heq  : app f (Term.prim (TermPrim.entity uid)) = Term.set ts (TermType.entity ety))
  (hlit : (Term.set ts (TermType.entity ety)).isLiteral = true)
  (hin  : t ∈ ts) :
  Term.WellFormedLiteral εs t ∧ t.typeOf = TermType.entity ety
:= by
  replace hlit₃ := lit_term_set_implies_lit_elt hlit hin
  have hws := wf_app_anc hwε hwt (by simp only [Term.typeOf, TermPrim.typeOf]) hanc
  simp only [heq] at hws
  have hwt₃ := wf_term_set_implies_wf_elt hws.left hin
  have hty₃ := wf_term_set_implies_typeOf_elt hws.left hin
  exact And.intro (And.intro hwt₃ hlit₃) hty₃

private theorem swf_implies_transitivity_areAncestorsOfType
  {uid₁ uid₂ : EntityUID} {ety₃ : EntityType} {f₂₃ : UnaryFunction} {εs : SymEntities} {es : Entities}
  (heq  : es ∼ εs)
  (hwε  : εs.WellFormed)
  (hse  : es.StronglyWellFormed)
  (hwt₂ : (Term.entity uid₂).WellFormed εs)
  (hv₁   : Value.WellFormed es (Value.prim (Prim.entityUID uid₁)))
  (hv₂   : Value.WellFormed es (Value.prim (Prim.entityUID uid₂)))
  (hanc₂ : εs.ancestorsOfType uid₂.ty ety₃ = some f₂₃)
  (hin₂  : uid₂ ∈ es.ancestorsOrEmpty uid₁) :
  transitivity.areAncestorsOfType εs (.entity uid₂) f₂₃ ety₃ (.entity uid₁) uid₁.ty = true
:= by
  simp only [transitivity.areAncestorsOfType]
  have ⟨ts₂, heq₂, hlit₂, hmem₂⟩ := same_entities_ancestors_some_of_type heq hv₂ hanc₂
  simp only [heq₂]
  cases hanc₁ : εs.ancestorsOfType uid₁.ty ety₃ <;> simp only
  case none =>
    simp only [pe_set_isEmpty, Set.empty_iff_not_exists, Term.prim.injEq, TermPrim.bool.injEq]
    by_contra hin₃
    replace ⟨t₃, hin₃⟩ := hin₃
    have ⟨hwt₃, hty₃⟩ := wfl_ancestors_implies_wfl_term_entity hwε hwt₂ hanc₂ heq₂ hlit₂ hin₃
    replace ⟨uid₃, heq₃, hty₃⟩ := wfl_of_type_entity_is_entity hwt₃ hty₃
    subst heq₃ hty₃
    specialize hmem₂ uid₃ rfl
    replace hmem₂ := hmem₂.mp hin₃
    have hmem₁ := same_entities_ancestors_none_of_type heq hanc₁
    have _ := swf_implies_entity_transitive hse hin₂ hmem₂
    contradiction
  case some f₁₃ =>
    have ⟨ts₁, heq₁, hlit₁, hmem₁⟩ := same_entities_ancestors_some_of_type heq hv₁ hanc₁
    simp only [heq₁, pe_set_subset hlit₂ hlit₁, Term.prim.injEq, TermPrim.bool.injEq]
    have hsub : ts₂ ⊆ ts₁ ↔ ts₂.subset ts₁ = true := by simp only [Subset]
    simp only [← hsub, Set.subset_def]
    intro t₃ hin₃
    replace ⟨hwt₃, hty₃⟩ := wfl_ancestors_implies_wfl_term_entity hwε hwt₂ hanc₂ heq₂ hlit₂ hin₃
    replace ⟨uid₃, heq₃, hty₃⟩ := wfl_of_type_entity_is_entity hwt₃ hty₃
    subst heq₃ hty₃
    specialize hmem₁ uid₃ rfl
    specialize hmem₂ uid₃ rfl
    replace hin₃ := hmem₂.mp hin₃
    simp only [hmem₁, swf_implies_entity_transitive hse hin₂ hin₃]

theorem swf_implies_interpret_transitivity {x₁ x₂ : Expr} {t₁ t₂ : Term} {ety₁ ety₂ : EntityType} {env : Env} {εnv : SymEnv} {I : Interpretation}
  (heq : env ∼ SymEnv.interpret I εnv)
  (hI : I.WellFormed εnv.entities)
  (hwε₁ : εnv.WellFormedFor x₁)
  (hwε₂ : εnv.WellFormedFor x₂)
  (hse₁ : env.StronglyWellFormedFor x₁)
  (hse₂ : env.StronglyWellFormedFor x₂)
  (hok₁ : compile x₁ εnv = Except.ok t₁)
  (hok₂ : compile x₂ εnv = Except.ok t₂)
  (hty₁ : t₁.typeOf = .option (.entity ety₁))
  (hty₂ : t₂.typeOf = .option (.entity ety₂)) :
  (transitivity t₁ t₂ εnv.entities).interpret I = true
:= by
  have hwt₁ := (compile_wf hwε₁ hok₁).left
  have hwt₂ := (compile_wf hwε₂ hok₂).left
  simp only [transitivity_option_entity_implies hty₁ hty₂]
  split <;> try simp only [interpret_term_prim]
  simp only [interpret_transitivity_core hwε₁.left.right hI hwt₁ hwt₂ hty₁ hty₂]
  have ht₁ := interpret_option_entity_term hI hwt₁ hty₁
  have ht₂ := interpret_option_entity_term hI hwt₂ hty₂
  rcases ht₁ with ht₁ | ⟨uid₁, ht₁, hty₁⟩
  · simp only [ht₁, pe_transitivity_core_none_left]
  · rcases ht₂ with ht₂ | ⟨uid₂, ht₂, hty₂⟩
    · simp only [ht₂, pe_transitivity_core_none_right]
    · subst hty₁ hty₂
      simp only [ht₁, ht₂]
      have hv₁ := compile_interpret_entity_implies_wf heq hI hwε₁ (swf_env_for_implies_wf_for hse₁) hok₁ ht₁
      have hv₂ := compile_interpret_entity_implies_wf heq hI hwε₂ (swf_env_for_implies_wf_for hse₂) hok₂ ht₂
      clear hty₁ hty₂ hok₁ hok₂
      simp only [transitivity.core]
      split <;> try rfl
      rename_i f₁₂ anc₂ hanc₁ hanc₂
      simp only [transitivity.isAncestor, pe_isSome_some, pe_and_true_left, pe_option_get_some]
      replace ⟨ts₁, heq₁, hlit₁, hanc₁⟩ := same_entities_ancestors_some_of_type heq.right hv₁ hanc₁
      specialize hanc₁ uid₂ rfl
      simp only [heq₁, pe_set_member hlit₁ term_prim_is_lit]
      cases hmem : ts₁.contains (Term.prim (TermPrim.entity uid₂)) <;>
      simp only [pe_implies_false_left, pe_implies_true_left]
      replace hmem := hanc₁.mp (Set.contains_prop_bool_equiv.mp hmem)
      clear heq₁ hlit₁ hanc₁ ts₁ f₁₂
      simp only [transitivity.areAncestors, pe_foldl_and_true_iff]
      intro (ety₃, f₂₃) hin
      replace hwε₂ := (interpret_εnv_wf_for_expr hwε₂ hI).left.right
      replace hanc₂ := mem_ancestors_implies_ancestorsOfType hwε₂ hanc₂ hin
      have hdom := interpret_entities_same_domain εnv.entities I
      replace hwt₁ := wf_term_same_domain hdom (interpret_term_wf hI hwt₁).left
      replace hwt₂ := wf_term_same_domain hdom (interpret_term_wf hI hwt₂).left
      simp only [ht₁, ht₂] at hwt₁ hwt₂
      replace hwt₂ := wf_term_some_implies hwt₂
      exact swf_implies_transitivity_areAncestorsOfType
        heq.right hwε₂ hse₂.left.right hwt₂ hv₁ hv₂ hanc₂ hmem

private theorem wf_ancs_implies_wfl_app_interpret_ancs {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities} {ancTy : EntityType} {ancUF : UnaryFunction} {I : Interpretation}
  (hεs : εs.WellFormed)
  (hI  : I.WellFormed εs)
  (hδ  : εs.find? uid.ty = some δ)
  (hf  : δ.ancestors.find? ancTy = some ancUF)
  (hwt : (Term.entity uid).WellFormed εs) :
  (app (ancUF.interpret I) (Term.entity uid)).WellFormedLiteral εs ∧
  (app (ancUF.interpret I) (Term.entity uid)).typeOf = .set (.entity ancTy)
:= by
  have hwf := (hεs.right uid.ty δ hδ).right.right.right.left ancTy ancUF hf
  rw [eq_comm, ← typeOf_term_prim_entity] at hwf
  simp only [Term.WellFormedLiteral, ← hwf.right.right]
  cases ancUF
  case udf ancUF =>
    simp only [ UnaryFunction.interpret,
      wf_app hwt hwf.right.left hwf.left,
      pe_app_wfl (And.intro hwt term_prim_is_lit) hwf.left, and_self]
  case uuf ancUF =>
    simp only [UnaryFunction.interpret]
    have hwf' := hI.right.left ancUF hwf.left
    simp only [Interpretation.WellFormed.WellFormedUUFInterpretation] at hwf'
    simp only [UnaryFunction.argType, UnaryFunction.outType] at hwf
    simp only [← hwf.right.left] at hwf'
    simp only [pe_app_wfl (And.intro hwt term_prim_is_lit) hwf'.left, and_true,
      UnaryFunction.outType, hwf'.right.right]
    have htyᵢ : (I.funs ancUF).arg = (UnaryFunction.udf (I.funs ancUF)).argType := by simp only [UnaryFunction.argType]
    have htyₒ : (I.funs ancUF).out = (UnaryFunction.udf (I.funs ancUF)).outType := by simp only [UnaryFunction.outType]
    rw [htyᵢ] at hwf'
    simp only [wf_app hwt hwf'.right.left hwf'.left, htyₒ, and_self]


private theorem interpret_entities_ancestorsOfType_some_implies {εs : SymEntities} {ety ancTy : EntityType} {I : Interpretation} {f' : UnaryFunction} :
  (εs.interpret I).ancestorsOfType ety ancTy = .some f' →
  ∃ δ f,
    εs.find? ety = some δ ∧
    δ.ancestors.find? ancTy = some f ∧
    f.interpret I = f'
:= by
  intro heq
  simp only [SymEntities.ancestorsOfType, SymEntities.ancestors, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at heq
  replace ⟨ancs, ⟨δ', hδ, heq⟩, hf⟩ := heq
  subst heq
  simp only [SymEntities.interpret, ← Map.find?_mapOnValues, Option.map_eq_some_iff] at hδ
  replace ⟨δ, hδ, hf'⟩ := hδ
  subst hf'
  simp only [SymEntityData.interpret, ← Map.find?_mapOnValues, Option.map_eq_some_iff] at hf
  replace ⟨f, hf, heq⟩ := hf
  exists δ, f

theorem interpret_transitivity_implies_transitive
  {uid₁ uid₂ uid₃ : EntityUID} {t₁ t₂ : Term} {ts₁₂ ts₂₃ : Set Term}
  {δ₁ δ₂ : SymEntityData} {f₁₂ f₂₃ : UUF} {εnv : SymEnv} {I : Interpretation}
  (hwε  : εnv.WellFormed)
  (hI   : I.WellFormed εnv.entities)
  (hwt₁ : t₁.WellFormed εnv.entities)
  (hwt₂ : t₂.WellFormed εnv.entities)
  (ht₁  : t₁.interpret I = (Term.entity uid₁).some)
  (ht₂  : t₂.interpret I = (Term.entity uid₂).some)
  (hδ₁  : εnv.entities.find? uid₁.ty = some δ₁)
  (hf₁  : δ₁.ancestors.find? uid₂.ty = some (UnaryFunction.uuf f₁₂))
  (heq₁ : app ((UnaryFunction.uuf f₁₂).interpret I) (.entity uid₁) = .set ts₁₂ (.entity uid₂.ty))
  (hin₁ : Term.entity uid₂ ∈ ts₁₂)
  (hδ₂  : εnv.entities.find? uid₂.ty = some δ₂)
  (hf₂  : δ₂.ancestors.find? uid₃.ty = some (UnaryFunction.uuf f₂₃))
  (heq₂ : app ((UnaryFunction.uuf f₂₃).interpret I) (.entity uid₂) = .set ts₂₃ (.entity uid₃.ty))
  (hin₂ : Term.entity uid₃ ∈ ts₂₃)
  (htr  : (transitivity t₁ t₂ εnv.entities).interpret I = true) :
  ∃ f₁₃ ts₁₃,
    δ₁.ancestors.find? uid₃.ty = some f₁₃ ∧
    app (f₁₃.interpret I) (.entity uid₁) = .set ts₁₃ (.entity uid₃.ty) ∧
    Term.entity uid₃ ∈ ts₁₃
:= by
  have ⟨hwt₁', hty₁⟩ := wf_term_interpret_option_entity_implies_wf_typeOf hI hwt₁ ht₁
  have ⟨hwt₂', hty₂⟩ := wf_term_interpret_option_entity_implies_wf_typeOf hI hwt₂ ht₂
  simp only [transitivity_option_entity_implies hty₁ hty₂] at htr
  split at htr
  case isTrue heq =>
    subst heq
    simp only [ht₁, Term.some.injEq, Term.prim.injEq, TermPrim.entity.injEq] at ht₂
    subst ht₂
    simp only [hδ₁, Option.some.injEq] at hδ₂
    subst hδ₂
    exists (.uuf f₂₃), ts₂₃
  case isFalse =>
    simp only [interpret_transitivity_core hwε.right hI hwt₁ hwt₂ hty₁ hty₂, ht₁, ht₂] at htr
    simp only [transitivity.core,
      interpret_entities_ancestorsOfType_some (εs_ancestors_find?_implies_ancestorsOfType hδ₁ hf₁),
      interpret_entities_ancestors_some I (εs_ancestors_find?_implies_ancestors hδ₂),
      pe_option_get_some, pe_transitivity_isAncestor_some_some, heq₁] at htr
    simp only [ht₁] at hwt₁'
    replace hwt₁' := wf_term_some_implies hwt₁'
    have hwl₁₂ := wf_ancs_implies_wfl_app_interpret_ancs hwε.right hI hδ₁ hf₁ hwt₁'
    simp only [heq₁] at hwl₁₂
    rw [← Set.contains_prop_bool_equiv] at hin₁
    simp only [pe_set_member hwl₁₂.left.right term_prim_is_lit, hin₁, pe_implies_true_left] at htr
    simp only [transitivity.areAncestors, Map.toList, Map.mapOnValues, pe_foldl_and_true_iff,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at htr
    specialize htr (uid₃.ty, .uuf f₂₃) (Map.find?_mem_toList hf₂)
    simp only [transitivity.areAncestorsOfType] at htr
    split at htr
    · rename_i f₁₃' heq
      replace ⟨_, f₁₃, hδ₁', hf₃, heq'⟩ := interpret_entities_ancestorsOfType_some_implies heq
      subst heq'
      simp only [hδ₁, Option.some.injEq] at hδ₁'
      subst hδ₁'
      simp only [ht₂] at hwt₂'
      replace hwt₂' := wf_term_some_implies hwt₂'
      have hwl₂₃ := wf_ancs_implies_wfl_app_interpret_ancs hwε.right hI hδ₂ hf₂ hwt₂'
      simp only [heq₂] at hwl₂₃ htr
      have hwl₁₃ := wf_ancs_implies_wfl_app_interpret_ancs hwε.right hI hδ₁ hf₃ hwt₁'
      have ⟨ts₁₃, hts⟩ := wfl_of_type_set_is_set hwl₁₃.left hwl₁₃.right
      simp only [hts] at hwl₁₃ htr
      simp only [pe_set_subset hwl₂₃.left.right hwl₁₃.left.right, Term.prim.injEq, TermPrim.bool.injEq] at htr
      replace htr : ts₂₃ ⊆ ts₁₃ := by simp only [Subset, htr]
      simp only [Set.subset_def] at htr
      specialize htr uid₃ hin₂
      exists f₁₃, ts₁₃
    · simp only [heq₂, pe_set_isEmpty, Set.isEmpty, Term.prim.injEq, TermPrim.bool.injEq, beq_iff_eq] at htr
      subst htr
      simp only [Set.empty_no_elts] at hin₂

end Cedar.Thm

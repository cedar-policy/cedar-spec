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

import Cedar.Partial.Evaluator
import Cedar.Partial.Value
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Evaluate.Record

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr Error Expr Result)

/--
  `Partial.bindAttr` on concrete arguments is the same as `Spec.bindAttr` on
  those arguments
-/
theorem bindAttr_on_concrete_eqv_concrete {a : Attr} {res : Result Spec.Value} :
  Partial.bindAttr a (res.map Partial.Value.value) = (Spec.bindAttr a res).map λ (k, v) => (k, Partial.Value.value v)
:= by
  unfold Partial.bindAttr Spec.bindAttr
  cases res <;> simp [Except.map]

/--
  `List.mapM_pmap_subtype` specialized for a particular setting involving pairs
  and `Spec.bindAttr`
-/
private theorem mapM_pmap_subtype_spec_bindAttr
  {p : (Attr × β) → Prop}
  (f : β → Result Spec.Value)
  (pairs: List (Attr × β))
  (h : ∀ pair ∈ pairs, p pair) :
  List.mapM (λ x : {pair : (Attr × β) // p pair} => Spec.bindAttr x.val.fst (f x.val.snd)) (List.pmap Subtype.mk pairs h) =
  pairs.mapM (λ x => Spec.bindAttr x.fst (f x.snd))
:= by
  rw [←List.mapM'_eq_mapM]
  induction pairs <;> simp [*]

/--
  `List.mapM_pmap_subtype` specialized for a particular setting involving pairs
  and `Partial.bindAttr`
-/
private theorem mapM_pmap_subtype_partial_bindAttr
  {p : (Attr × β) → Prop}
  (f : β → Result Partial.Value)
  (pairs: List (Attr × β))
  (h : ∀ pair ∈ pairs, p pair) :
  List.mapM (λ x : {pair : (Attr × β) // p pair} => Partial.bindAttr x.val.fst (f x.val.snd)) (List.pmap Subtype.mk pairs h) =
  pairs.mapM (λ x => Partial.bindAttr x.fst (f x.snd))
:= by
  rw [←List.mapM'_eq_mapM]
  induction pairs <;> simp [*]

/--
  `List.mapM₂_eq_mapM` specialized for a particular setting involving pairs and
  `Spec.bindAttr`
-/
private theorem mapM₂_eq_mapM_spec_bindAttr [SizeOf β]
  (f : β → Result Spec.Value)
  (attrs : List (Attr × β)) :
  attrs.mapM₂
    (λ x : {x : Attr × β // sizeOf x.snd < 1 + sizeOf attrs} => match x with
      | ⟨(a, b), _⟩ => Spec.bindAttr a (f b)
    ) =
  attrs.mapM λ (a, b) => Spec.bindAttr a (f b)
:= by
  simp [List.mapM₂, List.attach₂, mapM_pmap_subtype_spec_bindAttr]

/--
  `List.mapM₂_eq_mapM` specialized for a particular setting involving pairs and
  `Partial.bindAttr`
-/
private theorem mapM₂_eq_mapM_partial_bindAttr [SizeOf β]
  (f : β → Result Partial.Value)
  (attrs : List (Attr × β)) :
  attrs.mapM₂
    (λ x : {x : Attr × β // sizeOf x.snd < 1 + sizeOf attrs} => match x with
      | ⟨(a, b), _⟩ => Partial.bindAttr a (f b)
    ) =
  attrs.mapM λ (a, b) => Partial.bindAttr a (f b)
:= by
  simp [List.mapM₂, List.attach₂, mapM_pmap_subtype_partial_bindAttr]

/--
  Inductive argument that, for an `Expr.record` with concrete request/entities,
  partial evaluation and concrete evaluation give the same output
-/
theorem on_concrete_eqv_concrete_eval {attrs : List (Attr × Expr)} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ kv ∈ attrs, PartialEvalEquivConcreteEval kv.snd request entities) →
  PartialEvalEquivConcreteEval (Expr.record attrs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp only
  rw [mapM₂_eq_mapM_spec_bindAttr (Spec.evaluate · request entities)]
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · request entities)]
  induction attrs
  case nil => simp [Except.map, pure, Except.pure]
  case cons kv tl ih =>
    specialize ih (by
      intro kv' h₁
      exact ih₁ kv' (List.mem_cons_of_mem kv h₁)
    )
    cases h₁ : Spec.bindAttr kv.fst (Spec.evaluate kv.snd request entities)
    <;> cases h₂ : Partial.bindAttr kv.fst (Partial.evaluate kv.snd request entities)
    <;> cases h₃ : Spec.evaluate kv.snd request entities
    <;> simp only [h₁, h₂, List.mapM_cons, Except.bind_err, Except.bind_ok, bind_assoc, pure_bind, Option.pure_def, Option.bind_eq_bind, List.map_cons, List.mapM_cons]
    <;> simp only [ih₁ kv, Except.map, true_or, List.mem_cons] at h₂
    <;> simp only [h₃, Spec.bindAttr, Partial.bindAttr, Except.bind_ok, Except.bind_err, Except.error.injEq, Except.ok.injEq] at h₁ h₂
    case error.error.error e₁ e₂ e₃ =>
      simp only [Except.map, Except.error.injEq]
      subst h₁ h₂
      rfl
    case ok.ok.ok val' pval val =>
      subst h₁ h₂
      simp only [Option.some_bind]
      -- the remaning goal is just a statement about `tl`, not `kv` itself
      -- so we can dispatch it using `ih`
      generalize h₃ : (tl.mapM λ x => Partial.bindAttr x.fst (Partial.evaluate x.snd request entities)) = pres at *
      generalize h₄ : (tl.mapM λ x => Spec.bindAttr x.fst (Spec.evaluate x.snd request entities)) = sres at *
      cases pres <;> cases sres
      <;> simp only [Except.map, List.mem_cons, forall_eq_or_imp, Except.bind_ok, Except.bind_err, Except.error.injEq] at *
      case error.error e₁ e₂ => exact ih
      case ok.error pvals e => split at ih <;> simp at ih
      case ok.ok pvals vals =>
        split at ih <;> simp only [Except.ok.injEq, Partial.Value.value.injEq,
          Spec.Value.record.injEq] at ih
        case h_1 vals' h₂ =>
          simp only [h₂, Option.some_bind, Except.ok.injEq, Partial.Value.value.injEq,
            Spec.Value.record.injEq]
          exact Map.make_cons ih

/--
  Inductive argument that if partial-evaluating an `Expr.record` produces
  `ok` with some value, that value is well-formed
-/
theorem partial_eval_wf {attrs: List (Attr × Expr)} {request : Partial.Request} {entities : Partial.Entities}
  (ih : ∀ kv ∈ attrs, EvaluatesToWellFormed kv.snd request entities) :
  EvaluatesToWellFormed (Expr.record attrs) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · request entities)]
  cases hkv : attrs.mapM (λ kv => match kv with | (k, v) => Partial.bindAttr k (Partial.evaluate v request entities))
  <;> simp only [Except.bind_ok, Except.bind_err, false_implies, implies_true]
  case ok pvals =>
    replace hkv := List.mapM_ok_implies_all_from_ok hkv
    split <;> simp only [Except.ok.injEq, forall_eq']
    · simp only [Partial.Value.WellFormed, Spec.Value.WellFormed]
      rename_i vs h₂
      apply And.intro (Map.make_wf vs)
      intro kv h₃
      replace h₃ := Map.make_mem_list_mem h₃
      replace ⟨(k', pval'), h₄, h₂⟩ := List.mapM_some_implies_all_from_some h₂ kv h₃
      split at h₂ <;> simp at h₂ <;> subst h₂
      replace ⟨(k, v), h₅, hkv⟩ := hkv (k', pval') h₄
      rename_i v' h₆
      simp at h₆ ; subst h₆
      simp [Partial.bindAttr] at hkv
      cases h₇ : Partial.evaluate v request entities <;> simp [h₇] at hkv
      case ok pval' =>
        replace ⟨hkv, hkv'⟩ := hkv
        subst k' pval'
        simpa [Partial.Value.WellFormed] using ih (k, v) h₅ (.value v') h₇
    · simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]

/--
  If partial-evaluating an `Expr.record` produces `ok` with a concrete
  value, then so would partial-evaluating any of the values it contains
-/
theorem evals_to_concrete_then_vals_eval_to_concrete {attrs : List (Attr × Expr)} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Expr.record attrs) request entities →
  ∀ kv ∈ attrs, EvaluatesToConcrete kv.snd request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁ (k, x) h₂
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · request entities)] at h₁
  cases h₃ : attrs.mapM (λ kv => match kv with | (k, v) => Partial.bindAttr k (Partial.evaluate v request entities))
  <;> simp only [h₃, Except.bind_ok, Except.bind_err] at h₁
  case ok pvals =>
    replace ⟨(k', pval), h₃, h₄⟩ := List.mapM_ok_implies_all_ok h₃ (k, x) h₂
    split at h₁ <;> simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₁
    subst h₁
    rename_i vs h₁
    replace ⟨(k'', v), _, h₁⟩ := List.mapM_some_implies_all_some h₁ (k', pval) h₃
    split at h₁ <;> simp only [Option.some.injEq, Prod.mk.injEq] at h₁
    replace ⟨h₁, h₁'⟩ := h₁ ; rename_i v' h₅ ; subst k'' v'
    simp only at h₅ ; subst pval
    simp only [Partial.bindAttr] at h₄
    cases h₅ : Partial.evaluate x request entities
    <;> simp only [h₅, Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq] at h₄
    case ok pval =>
      replace ⟨h₄, h₄'⟩ := h₄ ; subst k' pval
      exists v

/--
  Lemma:

  Inductive argument that if `mapM` on a list of attrs produces `.ok` with a
  list of concrete vals, then it produces the same list of concrete vals after
  any substitution of unknowns
-/
theorem mapM_subst_snd_preserves_evaluation_to_values {attrs : List (Attr × Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ kv ∈ attrs, SubstPreservesEvaluationToConcrete kv.snd req req' entities subsmap) :
  req.subst subsmap = some req' →
  ∀ (pvals : List (Attr × Partial.Value)),
    attrs.mapM (λ kv => do .ok (kv.fst, (← Partial.evaluate kv.snd req entities))) = .ok pvals →
    IsAllConcrete (pvals.map Prod.snd) →
    attrs.mapM (λ kv => do .ok (kv.fst, (← Partial.evaluate kv.snd req' (entities.subst subsmap)))) = .ok pvals
:= by
  intro h_req pvals h₁ h₂
  cases attrs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.mapM_nil, pure, Except.pure,
      Except.ok.injEq, List.map_nil] at *
    exact h₁
  case cons hd tl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.mapM_cons, pure, Except.pure, bind_assoc,
      Except.bind_ok, List.map_cons] at *
    have ⟨ih_hd, ih_tl⟩ := ih ; clear ih
    have (khd, xhd) := hd ; clear hd
    simp only at *
    cases h₃ : Partial.evaluate xhd req entities
    <;> simp only [h₃, Except.bind_err, Except.bind_ok] at h₁
    case ok hd_pval =>
      unfold IsAllConcrete at h₂
      replace ⟨vs, h₂⟩ := h₂
      replace ⟨h₂, h₂'⟩ := And.intro (List.mapM_some_implies_all_some h₂) (List.mapM_some_implies_all_from_some h₂)
      cases h₅ : tl.mapM (λ kv => do let v ← Partial.evaluate kv.snd req entities ; .ok (kv.fst, v))
      <;> simp only [h₅, Except.bind_ok, Except.ok.injEq, Except.bind_err] at h₁
      case ok tl_pvals =>
        subst h₁
        cases h₄ : Partial.evaluate xhd req' (entities.subst subsmap)
        <;> simp only [Except.bind_err, Except.bind_ok]
        case error e =>
          replace ⟨v, _, h₂⟩ := h₂ hd_pval (by simp)
          cases hd_pval <;> simp only [Option.some.injEq] at h₂
          case value v' =>
            subst v'
            unfold SubstPreservesEvaluationToConcrete at ih_hd
            simp only [ih_hd h_req v h₃] at h₄
        case ok hd'_pval =>
          have ih₂ := mapM_subst_snd_preserves_evaluation_to_values ih_tl h_req tl_pvals h₅ (by
            unfold IsAllConcrete
            apply List.all_some_implies_mapM_some
            intro tl_pval h₆
            replace ⟨v, _, h₂⟩ := h₂ tl_pval (by simp [h₆])
            exists v
          )
          simp only [ih₂, Except.bind_ok, Except.ok.injEq, List.cons.injEq, Prod.mk.injEq,
            true_and, and_true]
          cases hd_pval <;> simp only [List.map_cons, List.mem_cons, List.mem_map, forall_eq_or_imp,
            and_false, false_and, exists_const, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
            Option.some.injEq] at h₂
          case value hd_val =>
            unfold SubstPreservesEvaluationToConcrete at ih_hd
            simp only [ih_hd h_req hd_val h₃, Except.ok.injEq] at h₄
            exact h₄.symm

/-- Helper lemma proved by induction -/
private theorem mapM_pairs_snd {pvals : List (Attr × Partial.Value)} {pairs : List (Attr × Spec.Value)}:
  pvals.mapM (λ kv => match kv.snd with
      | .value v => some (kv.fst, v)
      | .residual _ => none)
    = some pairs →
  pvals.mapM (λ kv => match kv.snd with
      | .value v => some v
      | .residual _ => none)
    = some (pairs.map Prod.snd)
:= by
  intro h₁
  cases pvals <;> simp only [List.mapM_nil, List.mapM_cons, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at *
  case nil => subst h₁ ; simp only [List.map_nil]
  case cons hd tl =>
    have (khd, vhd) := hd ; clear hd
    simp only at *
    replace ⟨(khd', vhd'), h₁, h₂⟩ := h₁
    cases vhd <;> simp only [Option.some.injEq, Prod.mk.injEq, exists_eq_left'] at *
    replace ⟨h₁, h₁'⟩ := h₁ ; subst khd' vhd' ; rename_i vhd
    replace ⟨tl', h₂, h₃⟩ := h₂
    subst h₃
    exists (tl'.map Prod.snd)
    simp only [List.map_cons, and_true]
    exact mapM_pairs_snd h₂

/--
  Inductive argument that if partial-evaluation of an `Expr.record`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {attrs : List (Attr × Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ kv ∈ attrs, SubstPreservesEvaluationToConcrete kv.snd req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Expr.record attrs) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete
  unfold Partial.evaluate
  intro h_req v
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req entities)]
  cases h₁ : attrs.mapM (λ kv => match kv with | (k, v) => Partial.bindAttr k (Partial.evaluate v req entities))
  <;> simp only [Except.bind_err, Except.bind_ok, Bool.not_eq_true', false_implies]
  case ok pvals =>
    split <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, false_implies]
    rename_i avs h₂
    -- avs are the concrete values produced by evaluating the record values pre-subst
    intro h ; subst h
    rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req' (entities.subst subsmap))]
    simp only [Partial.bindAttr] at *
    rw [mapM_subst_snd_preserves_evaluation_to_values ih h_req pvals h₁ (by
      unfold IsAllConcrete
      exists (avs.map Prod.snd)
      simp only [List.mapM_map]
      exact mapM_pairs_snd h₂
    )]
    simp only [Except.bind_ok, h₂]

/--
  Inductive argument that if partial-evaluation of an `Expr.record`
  returns an error, then it also returns an error (not necessarily the same error)
  after any substitution of unknowns
-/
theorem subst_preserves_errors {attrs : List (Attr × Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ kv ∈ attrs, SubstPreservesEvaluationToError kv.snd req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.record attrs) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  simp only [Partial.evaluate]
  intro h_req e
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req entities)]
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req' (entities.subst subsmap))]
  cases hattrs : attrs.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)
  case error e' =>
    simp only [Except.bind_err, Except.error.injEq, List.mapM_map]
    intro _ ; subst e'
    replace ⟨(k, x), hx, hattrs⟩ := List.mapM_error_implies_exists_error hattrs
    simp only [Partial.bindAttr, do_error] at hattrs
    replace ⟨e', ih⟩ := ih (k, x) hx h_req e hattrs
    have ⟨e'', h₁⟩ := List.element_error_implies_mapM_error hx (f := λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req' (entities.subst subsmap))) (by
      simp only [Partial.bindAttr, do_error]
      exact ih
    )
    simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
  case ok pvals =>
    simp only [Except.bind_ok]
    intro h₁
    split at h₁ <;> simp at h₁

end Cedar.Thm.Partial.Evaluation.Evaluate.Record

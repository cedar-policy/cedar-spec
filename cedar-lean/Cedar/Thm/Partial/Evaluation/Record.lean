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
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Record

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr Error Result)

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
  Inductive argument that partial evaluating a concrete `Partial.Expr.record`
  expression gives the same output as concrete-evaluating the `Spec.Expr.record`
  with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {attrs : List (Attr × Spec.Expr)} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ kv ∈ attrs, PartialEvalEquivConcreteEval kv.snd request entities) →
  PartialEvalEquivConcreteEval (Spec.Expr.record attrs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only
  rw [List.map_attach₂_snd Spec.Expr.asPartialExpr]
  rw [mapM₂_eq_mapM_spec_bindAttr (Spec.evaluate · request entities)]
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · request entities)]
  simp only [List.mapM_map]
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
      generalize h₃ : (tl.mapM λ x => Partial.bindAttr x.fst (Partial.evaluate x.snd.asPartialExpr request entities)) = pres at *
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
  Inductive argument that if partial-evaluating a `Partial.Expr.record` produces
  `ok` with some value, that value is well-formed
-/
theorem partial_eval_wf {attrs: List (Attr × Partial.Expr)} {request : Partial.Request} {entities : Partial.Entities}
  (ih : ∀ kv ∈ attrs, EvaluatesToWellFormed kv.snd request entities) :
  EvaluatesToWellFormed (Partial.Expr.record attrs) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · request entities)]
  cases hkv : attrs.mapM (λ kv => match kv with | (k, v) => Partial.bindAttr k (Partial.evaluate v request entities))
  <;> simp [hkv]
  case ok pvals =>
    replace hkv := List.mapM_ok_implies_all_from_ok hkv
    simp [Partial.Value.WellFormed]
    split <;> simp <;> simp [Spec.Value.WellFormed]
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

private theorem mapM_Option_on_snd_preserves_sortedBy_fst [LT α] [DecidableLT α] [StrictLT α] {abs : List (α × β)} {f : β → Option γ} :
  abs.SortedBy Prod.fst →
  abs.mapM (λ (a, b) => do some (a, ← f b)) = some ags →
  ags.SortedBy Prod.fst
:= by
  intro h₁ h₂
  replace h₂ := List.mapM_some_eq_filterMap h₂
  subst h₂
  apply List.filterMap_sortedBy _ h₁
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, implies_true]

private theorem mapM_Except_on_snd_preserves_sortedBy_fst [LT α] [DecidableLT α] [StrictLT α] {abs: List (α × β)} {f : β → Except ε γ} :
  abs.SortedBy Prod.fst →
  abs.mapM (λ (a, b) => do .ok (a, ← f b)) = .ok ags →
  ags.SortedBy Prod.fst
:= by
  intro h₁ h₂
  replace h₂ := List.mapM_ok_eq_filterMap h₂
  subst h₂
  apply List.filterMap_sortedBy _ h₁
  intro (a, b) (a', g)
  split <;> rename_i h₂ <;> split at h₂ <;> rename_i h₃
  <;> simp only [Prod.mk.injEq] at h₃ <;> replace ⟨h₃, h₃'⟩ := h₃ <;> subst h₃ h₃'
  · simp only [Option.some.injEq]
    cases hb : f b <;> simp only [hb, Except.bind_err, Except.bind_ok, Except.ok.injEq] at h₂
    subst h₂
    simp only [Prod.mk.injEq, and_imp]
    intro _ ; subst a' ; simp only [implies_true]
  · simp only [false_implies]

/--
  Inductive argument that partial evaluation of a `Spec.Value.record` always
  succeeds and returns the same value
-/
theorem eval_spec_value (m : Map Attr Spec.Value) (request : Partial.Request) (entities : Partial.Entities)
  (wf_m : m.WellFormed)
  (ih : ∀ v ∈ m.values, Partial.evaluate v.asPartialExpr request entities = .ok (.value v)) :
  Partial.evaluate (Spec.Value.record m).asPartialExpr request entities = .ok (.value (.record m))
:= by
  unfold Partial.evaluate Spec.Value.asPartialExpr
  simp only
  rw [List.map_attach₃_snd]
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · request entities)]
  rw [List.mapM_map]
  cases h₁ : m.kvs.mapM (λ kv => match match kv with | (k, v) => (k, v.asPartialExpr) with | (k, v) => Partial.bindAttr k (Partial.evaluate v request entities)) <;> simp
  case error e =>
    replace ⟨(k, v), h₁, h₂⟩ := List.mapM_error_implies_exists_error h₁
    specialize ih v (Map.in_list_in_values h₁)
    simp [ih, Partial.bindAttr] at h₂
  case ok pvals =>
    -- m is the input map. pvals is the output list of (attr, pval) pairs.
    simp [Partial.bindAttr] at h₁
    have h_sorted : pvals.SortedBy Prod.fst := by
      apply mapM_Except_on_snd_preserves_sortedBy_fst (Map.wf_iff_sorted.mp wf_m) (f := λ v => Partial.evaluate v.asPartialExpr request entities)
      unfold Map.toList
      rw [← h₁]
    replace ⟨h₁, h₁'⟩ := And.intro (List.mapM_ok_implies_all_ok h₁) (List.mapM_ok_implies_all_from_ok h₁)
    conv at h₁' => intro pval h ; simp
    split <;> simp
    · -- pvals has no residuals
      rename_i avs h₂
      -- avs is the output list of (attr, value) pairs
      have h_sorted' : avs.SortedBy Prod.fst := by
        apply mapM_Option_on_snd_preserves_sortedBy_fst h_sorted (f := λ v => match v with | .value v => some v | .residual _ => none)
        rw [← h₂] ; clear h₂
        apply List.mapM_congr
        intro (k, v)
        cases v <;> simp
      replace ⟨h₂, h₂'⟩ := And.intro (List.mapM_some_implies_all_some h₂) (List.mapM_some_implies_all_from_some h₂)
      apply (Map.eq_iff_kvs_equiv (Map.make_wf avs) wf_m).mp
      simp [List.Equiv, List.subset_def]
      constructor <;> intro kv h₃
      · replace ⟨(k, pval), h₂', h₄⟩ := h₂' kv (Map.make_mem_list_mem h₃)
        cases pval <;> simp at h₄
        case value v =>
          subst kv
          replace ⟨(k', v'), h₁', h₄⟩ := h₁' (k, .value v) h₂'
          specialize ih v' (Map.in_list_in_values h₁')
          simp [ih, Partial.bindAttr] at h₄
          replace ⟨h₄, h₄'⟩ := h₄
          subst k' v'
          exact h₁'
      · replace ⟨(k, pval), h₁, h₄⟩ := h₁ kv h₃
        have ⟨k', v⟩ := kv ; clear kv
        specialize ih v (Map.in_list_in_values h₃)
        replace ⟨(k'', v'), h₂, h₅⟩ := h₂ (k, pval) h₁
        cases pval <;> simp at h₅
        case value v'' =>
          replace ⟨h₅, h₅'⟩ := h₅
          subst k'' v''
          simp [ih, Partial.bindAttr] at h₄
          replace ⟨h₄, h₄'⟩ := h₄
          subst k' v'
          exact Map.mem_list_mem_make h_sorted' h₂
    · -- pvals has a residual
      rename_i h₂
      replace ⟨(k, pval), h₂, h₃⟩ := List.mapM_none_iff_exists_none.mp h₂
      cases pval <;> simp at h₃
      case residual r =>
        replace ⟨(k', v), h₁', h₄⟩ := h₁' (k, .residual r) h₂
        specialize ih v (Map.in_list_in_values h₁')
        simp [ih] at h₄

/--
  If partial-evaluating a `Partial.Expr.record` produces `ok` with a concrete
  value, then so would partial-evaluating any of the values it contains
-/
theorem evals_to_concrete_then_vals_eval_to_concrete {attrs : List (Attr × Partial.Expr)} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.record attrs) request entities →
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
theorem mapM_subst_snd_preserves_evaluation_to_values {attrs : List (Attr × Partial.Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ kv ∈ attrs, SubstPreservesEvaluationToConcrete kv.snd req req' entities subsmap) :
  req.subst subsmap = some req' →
  ∀ (pvals : List (Attr × Partial.Value)),
    attrs.mapM (λ kv => do let v ← Partial.evaluate kv.snd req entities ; .ok (kv.fst, v)) = .ok pvals →
    IsAllConcrete (pvals.map Prod.snd) →
    (attrs.map (λ kv => (kv.fst, kv.snd.subst subsmap))).mapM (λ kv => do let v ← Partial.evaluate kv.snd req' (entities.subst subsmap) ; .ok (kv.fst, v)) = .ok pvals
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
        cases h₄ : Partial.evaluate (xhd.subst subsmap) req' (entities.subst subsmap)
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
  Inductive argument that if partial-evaluation of a `Partial.Expr.record`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {attrs : List (Attr × Partial.Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ kv ∈ attrs, SubstPreservesEvaluationToConcrete kv.snd req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.record attrs) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete
  unfold Partial.evaluate Spec.Value.asBool
  intro h_req v
  rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req entities)]
  cases h₁ : attrs.mapM (λ kv => match kv with | (k, v) => Partial.bindAttr k (Partial.evaluate v req entities))
  <;> simp only [Except.bind_err, Except.bind_ok, Bool.not_eq_true', false_implies]
  case ok pvals =>
    split <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, false_implies]
    rename_i avs h₂
    -- avs are the concrete values produced by evaluating the record values pre-subst
    intro h ; subst h
    unfold Partial.Expr.subst
    rw [List.map_attach₂_snd]
    simp only
    rw [mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req' (entities.subst subsmap))]
    simp only [Partial.bindAttr] at *
    rw [mapM_subst_snd_preserves_evaluation_to_values ih h_req pvals h₁ (by
      unfold IsAllConcrete
      exists (avs.map Prod.snd)
      simp only [List.mapM_map]
      exact mapM_pairs_snd h₂
    )]
    simp only [Except.bind_ok, h₂]

end Cedar.Thm.Partial.Evaluation.Record

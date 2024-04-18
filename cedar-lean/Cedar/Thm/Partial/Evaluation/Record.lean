/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.Basic
import Cedar.Thm.Utils

namespace Cedar.Thm.Partial.Evaluation.Record

open Cedar.Data
open Cedar.Spec (Attr Error Result)
open Except

/--
  helper lemma: any subexpression of x is a subexpression of any record containing x
-/
theorem value_subexpression {x₁ x₂ : Partial.Expr} {attrs : List (Attr × Partial.Expr)} :
  x₁ ∈ attrs.map Prod.snd → x₂ ∈ x₁.subexpressions → x₂ ∈ (Partial.Expr.record attrs).subexpressions
:= by
  intro h₁ h₂
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right
  have h₃ := List.mem_map_of_mem Partial.Expr.subexpressions h₁
  rw [List.map_map] at h₃
  apply List.mem_join_of_mem h₃ h₂

/--
  helper lemma: if any component of a `record` contains an unknown, the whole
  expression does
-/
theorem value_unknown {x : Partial.Expr} {attrs : List (Attr × Partial.Expr)} :
  x ∈ attrs.map Prod.snd → x.containsUnknown → (Partial.Expr.record attrs).containsUnknown
:= by
  unfold Partial.Expr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁ h₂
  replace ⟨subx, h₂⟩ := h₂
  exists subx
  constructor
  case left => apply value_subexpression h₁ h₂.left
  case right => exact h₂.right

/--
  `Partial.bindAttr` on concrete arguments is the same as `Spec.bindAttr` on
  those arguments
-/
theorem Partial.bindAttr_on_concrete_eqv_bindAttr {a : Attr} {res : Result Spec.Value} :
  Partial.bindAttr a (res.map Partial.Value.value) = (Spec.bindAttr a res).map λ (k, v) => (k, Partial.Value.value v)
:= by
  unfold Partial.bindAttr Spec.bindAttr
  cases res <;> simp [Except.map]

/--
  `List.mapM_pmap_subtype` specialized for a particular setting involving pairs
-/
theorem mapM_pmap_subtype_snd
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
-/
theorem mapM_pmap_subtype_snd'
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
  `List.mapM₂_eq_mapM` specialized for a particular setting involving pairs
-/
theorem mapM₂_eq_mapM_specialized [SizeOf β]
  (f : β → Result Spec.Value)
  (attrs : List (Attr × β)) :
  attrs.mapM₂
    (λ x : {x : Attr × β // sizeOf x.snd < 1 + sizeOf attrs} => match x with
      | ⟨(a, b), _⟩ => Spec.bindAttr a (f b)
    ) =
  attrs.mapM λ (a, b) => Spec.bindAttr a (f b)
:= by
  simp [List.mapM₂, List.attach₂, mapM_pmap_subtype_snd]

/--
  `List.mapM₂_eq_mapM` specialized for a particular setting involving pairs
-/
theorem mapM₂_eq_mapM_specialized' [SizeOf β]
  (f : β → Result Partial.Value)
  (attrs : List (Attr × β)) :
  attrs.mapM₂
    (λ x : {x : Attr × β // sizeOf x.snd < 1 + sizeOf attrs} => match x with
      | ⟨(a, b), _⟩ => Partial.bindAttr a (f b)
    ) =
  attrs.mapM λ (a, b) => Partial.bindAttr a (f b)
:= by
  simp [List.mapM₂, List.attach₂, mapM_pmap_subtype_snd']

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.record`
  expression gives the same output as concrete-evaluating the `Spec.Expr.record`
  with the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {attrs : List (Attr × Spec.Expr)} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ kv ∈ attrs, Partial.evaluate kv.snd request entities = (Spec.evaluate kv.snd request entities).map Partial.Value.value) →
  Partial.evaluate (Partial.Expr.record (attrs.map₁ λ ⟨(k, v), _⟩ => (k, v.asPartialExpr))) request entities = (Spec.evaluate (Spec.Expr.record attrs) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  rw [List.map₁_eq_map_snd Spec.Expr.asPartialExpr attrs]
  rw [mapM₂_eq_mapM_specialized (Spec.evaluate · request entities) attrs]
  rw [mapM₂_eq_mapM_specialized' (Partial.evaluate · request entities) _]
  induction attrs
  case nil => simp [Except.map, pure, Except.pure]
  case cons kv attrs' h_ind =>
    specialize h_ind (by
      intro kv' h₁
      apply ih₁ kv' (List.mem_cons_of_mem kv h₁)
    )
    cases h₁ : Spec.bindAttr kv.fst (Spec.evaluate kv.snd request entities)
    <;> cases h₂ : Partial.bindAttr kv.fst (Partial.evaluate kv.snd request entities)
    <;> cases h₃ : Spec.evaluate kv.snd request entities
    <;> simp [h₁, h₂]
    <;> simp [ih₁ kv, Except.map, pure, Except.pure] at h₂
    <;> simp [h₃, Spec.bindAttr, Partial.bindAttr] at h₁ h₂
    case error.error.error e₁ e₂ e₃ =>
      simp [Except.map, pure, Except.pure]
      subst h₁ h₂
      rfl
    case ok.ok.ok val' pval val =>
      subst h₁ h₂
      simp [List.mapM_map]
      simp [List.mapM_map] at h_ind
      -- the remaning goal is just a statement about `attrs'`, not `kv` itself
      -- so we can dispatch it using `h_ind`
      generalize h₃ : (attrs'.mapM λ x => Partial.bindAttr x.fst (Partial.evaluate x.snd.asPartialExpr request entities)) = pres at *
      generalize h₄ : (attrs'.mapM λ x => Spec.bindAttr x.fst (Spec.evaluate x.snd request entities)) = sres at *
      cases pres <;> cases sres <;> simp [Except.map, pure, Except.pure] at *
      case error.error e₁ e₂ => exact h_ind
      case ok.error pvals e =>
        -- here, partial evaluation of `attrs'` produced `ok` (h₃), while concrete
        -- evaluation of `attrs'` produced `error` (h₄).
        -- this contradicts `h_ind`.
        exfalso
        split at h_ind <;> simp at h_ind
      case ok.ok pvals vals =>
        -- here, partial evaluation of `xs'` produced `ok pvals` (h₃), while
        -- concrete evaluation of `xs'` produced `ok vals` (h₄), and we need to
        -- show a particular relationship between `pvals` and `vals` using `h_ind`.
        split at h_ind <;> simp at h_ind
        case h_1 vals' h₂ =>
          simp [h₂]
          exact Map.make_cons h_ind

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.set`
-/
theorem residuals_contain_unknowns {attrs : List (Attr × Partial.Expr)} {request : Partial.Request} {entities : Partial.Entities} :
  (∀ kv ∈ attrs, @Partial.Expr.ResidualsContainUnknowns kv.snd request entities) →
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.record attrs) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns
  intro ih₁ r h₁
  -- the entire record evaluated to `.residual r`. we must show that `r` contains
  -- an unknown
  unfold Partial.evaluate at h₁
  rw [mapM₂_eq_mapM_specialized' (Partial.evaluate · request entities) attrs] at h₁
  cases h₂ : (attrs.mapM λ x => match x with | (k, v) => Partial.bindAttr k (Partial.evaluate v request entities))
  <;> simp [h₂] at h₁
  case ok pvals =>
    split at h₁ <;> simp at h₁
    -- naturally, the residual `r` which the record evaluated to, is itself a `.record`
    -- with elements `pvals.map Partial.Value.asPartialExpr`
    all_goals subst h₁
    -- so now we have to show that `(.record (pvals.map Partial.Value.asPartialExpr))`
    -- contains an unknown
    case h_2 h₃ =>
      -- in this case, some element of the record evaluated to a residual
      rw [mapM_none_iff_f_none_on_some_element] at h₃
      replace ⟨(a, pval), h₃, h₄⟩ := h₃
      split at h₄ <;> simp at h₄
      case h_2 r h₅ =>
        -- `.residual r` is the residual we got when evaluating some element of
        -- the record
        simp at h₅ ; subst h₅
        apply value_unknown (x := r)
        case _ =>
          simp [List.mem_map]
          exists (a, .residual r)
        case _ =>
          have ⟨(a', x), h₆, h₇⟩ := mem_mapM_ok h₂ h₃
          -- `x` is the record value which evaluated to `.residual r`
          simp [Partial.bindAttr] at h₇
          cases h₈ : Partial.evaluate x request entities
          all_goals simp [h₈] at h₇
          replace ⟨h₇, h₅⟩ := h₇
          subst a' h₅
          exact ih₁ (a, x) h₆ r h₈

end Cedar.Thm.Partial.Evaluation.Record

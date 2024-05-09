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
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.Record

open Cedar.Data
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
  rw [List.mapM_map]
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
    <;> simp only [h₁, h₂, List.mapM_cons, bind_assoc]
    <;> csimp
    <;> simp only [ih₁ kv, Except.map, true_or, List.mem_cons] at h₂
    <;> simp only [h₃, Spec.bindAttr, Partial.bindAttr] at h₁ h₂
    <;> csimp at h₁ h₂
    case error.error.error e₁ e₂ e₃ =>
      simp only [Except.map, Except.error.injEq]
      subst h₁ h₂
      rfl
    case ok.ok.ok val' pval val =>
      subst h₁ h₂
      csimp
      -- the remaning goal is just a statement about `tl`, not `kv` itself
      -- so we can dispatch it using `ih`
      generalize h₃ : (tl.mapM λ x => Partial.bindAttr x.fst (Partial.evaluate x.snd.asPartialExpr request entities)) = pres at *
      generalize h₄ : (tl.mapM λ x => Spec.bindAttr x.fst (Spec.evaluate x.snd request entities)) = sres at *
      unfold Except.map at *
      cases pres <;> cases sres <;> csimp at *
      case error.error e₁ e₂ => exact ih
      case ok.error pvals e => split at ih <;> csimp at ih
      case ok.ok pvals vals =>
        split at ih
        <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq] at ih
        case h_1 vals' h₂ =>
          simp only [h₂, Option.some_bind, Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
          exact Map.make_cons ih

end Cedar.Thm.Partial.Evaluation.Record

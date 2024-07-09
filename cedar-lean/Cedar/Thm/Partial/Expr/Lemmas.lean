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

import Cedar.Partial.Expr
import Cedar.Thm.Data.List
import Cedar.Spec
import Cedar.Thm.Data.Applicative

namespace Cedar.Partial.Thm.Expr


/--
  `List.mapM_pmap_subtype` specialized for a particular setting involving attribute pairs
-/
private theorem mapM_pmap_subtype_partial_attr
  {p : (Spec.Attr × β) → Prop}
  (f : β → Option Spec.Expr)
  (pairs: List (Spec.Attr × β))
  (h : ∀ pair ∈ pairs, p pair) :
  List.mapM (λ x : {pair : (Spec.Attr × β) // p pair} =>
    Option.map (λ e => (x.val.fst, e)) (f x.val.snd)) (List.pmap Subtype.mk pairs h) =
  pairs.mapM (λ x => Option.map (λ e => (x.fst, e)) (f x.snd))
:= by
  rw [←List.mapM'_eq_mapM]
  induction pairs <;> simp [*]

/--
  `List.map_pmap_subtype` specialized for a particular setting involving attribute pairs
-/
private theorem map_pmap_subtype_attr
  {p : (Spec.Attr × β) → Prop}
  (f : β → Partial.Expr)
  (pairs : List (Spec.Attr × β))
  (h : ∀ pair ∈ pairs, p pair) :
  List.map (λ x : {pair : (Spec.Attr × β) // p pair} => (x.val.fst, f x.val.snd)) (List.pmap Subtype.mk pairs h) =
  pairs.map (λ x => (x.fst, f x.snd))
  := by
  induction pairs <;> simp [*]


/--
  `List.mapM₂_eq_mapM` specialized for a particular setting involving attribute pairs
-/
private theorem mapM₂_eq_mapM_partial_attr [SizeOf β]
  (f : β → Option Spec.Expr)
  (attrs : List (Spec.Attr × β)) :
  attrs.mapM₂
    (λ x : {x : Spec.Attr × β // sizeOf x.snd < 1 + sizeOf attrs} => match x with
      | ⟨(a, b), _⟩ => Option.map (λ e => (a, e)) (f b)
    ) =
  attrs.mapM λ (a, b) => Option.map (λ e => (a, e)) (f b)
:= by
  simp [List.mapM₂, List.attach₂, mapM_pmap_subtype_partial_attr]

/--
  `List.mapM₂_eq_mapM` specialized for a particular setting involving attribute pairs
-/
private theorem map_attach_eq_map_attr [SizeOf β]
  (f : β → Partial.Expr)
  (attrs : List (Spec.Attr × β)) :
  List.map
    (λ x : {x : Spec.Attr × β // sizeOf x.snd < 1 + sizeOf attrs} => match x with
      | ⟨(a,b), _ ⟩ => (a, f b)
    ) (List.attach₂ attrs) =
  List.map (λ (a,b) => (a, f b)) attrs
  := by
  simp [List.map, List.attach₂, map_pmap_subtype_attr]

/--
  Tactic for proving roundtrip property for binary operation nodes
-/
local macro "binary_node" roundtrip:ident : tactic => do
  `(tactic | (
    rename_i lhs rhs h
    unfold Partial.Expr.asSpec at ( h )
    cases h_lhs : Partial.Expr.asSpec lhs
    case _ =>
      rw [h_lhs] at ( h )
      simp only [Option.map_eq_map, Option.map_none'] at ( h )
      rw [applicative_none] at ( h )
      contradiction
      rfl
    case _ lhs' =>
      cases h_rhs : Partial.Expr.asSpec rhs
      case _ =>
        rw [h_rhs] at ( h )
        simp only [Option.map_eq_map] at ( h )
        rw [applicative_of_none] at ( h )
        contradiction
        rfl
      case _ rhs' =>
        have ih_lhs : lhs'.asPartialExpr = ( lhs ) := $roundtrip lhs lhs'  h_lhs
        have ih_rhs : rhs'.asPartialExpr = ( rhs ) := $roundtrip rhs rhs' h_rhs
        rw [h_lhs] at ( h )
        rw [h_rhs] at ( h )
        simp only [Option.map_eq_map, Option.map_some'] at ( h )
        rw [applicative_step] at ( h )
        injection ( h )
        rename_i h
        rw [← h]
        unfold Spec.Expr.asPartialExpr
        rw [ih_lhs]
        rw [ih_rhs]
  ))

/--
  Tactic for proving roundtrip property for unary op
-/
local macro "unary_simple" h:ident arg:ident roundtrip:ident : tactic => do
  `(tactic |  (
    unfold Partial.Expr.asSpec at ( $h )
    cases h_arg : Partial.Expr.asSpec $arg
    case _ =>
      rw [h_arg] at ( $h )
      simp at ( $h )

    case _ arg' =>
      rw [h_arg] at ( $h )
      simp at ( $h )
      have ih : arg'.asPartialExpr = $arg := $roundtrip $arg arg' h_arg
      rw [← $h]
      unfold Spec.Expr.asPartialExpr
      rw [ih]
  ))

/--
  Tactic for proving roundtrip property for get/has attr
-/
local macro "attr" roundtrip:ident : tactic => do
    `(tactic | (
    rename_i arg a h
    unfold Partial.Expr.asSpec at ( h )
    cases h_arg : Partial.Expr.asSpec arg
    case _ =>
      rw [h_arg] at ( h )
      simp at ( h )
      rw [applicative_none] at ( h )
      simp at ( h )
      rw [applicative_none] at ( h )
      contradiction
    case _ arg' =>
      rw [h_arg] at ( h )
      simp at ( h )
      have ih : arg'.asPartialExpr = arg := $roundtrip arg arg' h_arg
      rw [applicative_step] at ( h )
      injection ( h )
      rename_i h
      rw [← h]
      unfold Spec.Expr.asPartialExpr
      rw [ih]))


theorem roundtrip₁ (pe : Partial.Expr) (e : Spec.Expr) :
  (pe.asSpec = some e) →
  e.asPartialExpr = pe
  := by
  intros h
  cases pe
    <;> (try (attr roundtrip₁))
    <;> (try (binary_node roundtrip₁))
    <;> try (unfold Partial.Expr.asSpec at h
            <;> injection h
            <;> rename_i h
            <;> rw [← h]
            <;> unfold Spec.Expr.asPartialExpr
            <;> rfl)
  case ite cond cons alt =>
    unfold Partial.Expr.asSpec at h
    cases h_cond : cond.asSpec <;> rw [h_cond] at h
    case none =>
      simp only [Option.map_eq_map, Option.map_none'] at h
      rw [applicative_none] at h
      ·
        contradiction
      ·
        apply applicative_none
        rfl
    case some cond' =>
      cases h_cons : cons.asSpec  <;> rw [h_cons ] at h
      case none =>
        simp only [Option.map_eq_map, Option.map_some'] at h
        have inner : ((some (Spec.Expr.ite cond')) <*> none) = none := by
          apply applicative_of_none
          rfl
        rw [inner] at h
        rw [applicative_none] at h
        contradiction
        rfl
      case some cons' =>
        cases h_alt : alt.asSpec <;> rw [h_alt] at h
        case none =>
          simp at h
          rw [applicative_of_none] at h
          contradiction
          rfl
        case some alt' =>
          have ih_cond : cond'.asPartialExpr = cond := roundtrip₁ cond cond' h_cond
          have ih_cons : cons'.asPartialExpr = cons := roundtrip₁ cons cons' h_cons
          have ih_alt : alt'.asPartialExpr = alt := roundtrip₁ alt alt' h_alt
          simp only [Option.map_eq_map, Option.map_some'] at h
          have inner₁ : (some (Spec.Expr.ite cond')) <*> (some cons') = some (Spec.Expr.ite cond' cons') := by
            apply applicative_some
            repeat rfl
          rw [inner₁] at h
          have inner₂ : (some (Spec.Expr.ite cond' cons')) <*> (some alt') = some (Spec.Expr.ite cond' cons' alt') := by
            apply applicative_some
            repeat rfl
          rw [inner₂] at h
          injection h
          rename_i h
          rw [← h]
          unfold Spec.Expr.asPartialExpr
          rw [ih_cond]
          rw [ih_cons]
          rw [ih_alt]
  case unaryApp o arg =>
    unary_simple h arg roundtrip₁
  case set members =>
    have inner : ∀ (es : List Partial.Expr) (es' : List Spec.Expr),
      sizeOf es < sizeOf (Partial.Expr.set members) →
      List.mapM Partial.Expr.asSpec es = some es' →
      List.map Spec.Expr.asPartialExpr es' = es
      := by
        intros es
        induction es
        case nil =>
          intros es' _  h₂
          simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h₂
          rw [← h₂]
          simp
        case cons head tail ih =>
          intros es' h₁ h₂
          simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
            Option.some.injEq] at h₂
          have ⟨ head', h_head, tail', h_tail, h_eq ⟩ := h₂
          rw [← h_eq]
          simp only [List.map_cons, List.cons.injEq]
          apply And.intro
          case _ =>
            exact roundtrip₁ head head' h_head
          case _ =>
            apply ih <;> try assumption
            simp only [Partial.Expr.set.sizeOf_spec]
            simp only [List.cons.sizeOf_spec, Partial.Expr.set.sizeOf_spec] at h₁
            omega
    unfold Partial.Expr.asSpec at h
    rw [List.mapM₁_eq_mapM] at h
    simp only [Option.map_eq_map, Option.map_eq_some'] at h
    have ⟨ members', h₁ , h₂ ⟩ := h
    rw [← h₂]
    unfold Spec.Expr.asPartialExpr
    rw [List.map₁_eq_map]

    have sizeH : sizeOf members < sizeOf (Partial.Expr.set members) := by
      simp only [Partial.Expr.set.sizeOf_spec]
      omega
    rw [inner]
    repeat assumption
  case record attrs =>
    have inner : ∀ (es : List (Spec.Attr × Partial.Expr)) (es' : List (Spec.Attr × Spec.Expr)),
      sizeOf es < sizeOf (Partial.Expr.record attrs) →
      List.mapM (λ pair => Option.map (λ e => (pair.fst, e)) pair.snd.asSpec) es = some es' →
      List.map (λ pair => (pair.fst, pair.snd.asPartialExpr)) es' = es := by
      intros es
      induction es
      case _ =>
        intros es _ h₂
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h₂
        rw [← h₂]
        simp only [List.map_nil]
      case cons head tail ih =>
        intros es h₁ h₂
        simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
          Option.map_eq_some', Option.some.injEq] at h₂
        have ⟨ head', h_head, tail', h_tail, h_eq ⟩ := h₂
        rw [← h_eq]
        simp only [List.map_cons, List.cons.injEq]
        apply And.intro
        ·
          have ⟨ e', h_head₁, h_head₂ ⟩ := h_head
          rw [← h_head₂]
          simp only
          have eq : Spec.Expr.asPartialExpr e' = head.snd := roundtrip₁ head.snd e' h_head₁
          rw [eq]
        ·
          apply ih
          simp only [List.cons.sizeOf_spec, Partial.Expr.record.sizeOf_spec] at h₁
          simp only [Partial.Expr.record.sizeOf_spec]
          omega
          assumption
    unfold Partial.Expr.asSpec at h
    simp only [Option.map_eq_map, Option.map_eq_some'] at h
    have ⟨ attrs', h₁, h₂ ⟩ := h
    rw [← h₂]
    unfold Spec.Expr.asPartialExpr

    rw [mapM₂_eq_mapM_partial_attr] at h₁
    rw [map_attach_eq_map_attr]
    have size_h : sizeOf attrs < sizeOf (Partial.Expr.record attrs) := by
      simp only [Partial.Expr.record.sizeOf_spec]
      omega
    rw [inner]
    repeat assumption
  case call xfn args =>
    have inner : ∀ (es : List Partial.Expr) (es' : List Spec.Expr),
      sizeOf es < sizeOf (Partial.Expr.call xfn args) →
      List.mapM Partial.Expr.asSpec es = some es' →
      List.map Spec.Expr.asPartialExpr es' = es
      := by
        intros es
        induction es
        case nil =>
          intros es' _ h₂
          simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h₂
          rw [← h₂]
          simp
        case cons head tail ih =>
          intros es' h₁ h₂
          simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
            Option.some.injEq] at h₂
          have ⟨ head', h_head, tail', h_tail, h_eq ⟩ := h₂
          rw [← h_eq]
          simp only [List.map_cons, List.cons.injEq]
          apply And.intro
          case _ =>
            exact roundtrip₁ head head' h_head
          case _ =>
            apply ih <;> try assumption
            simp only [Partial.Expr.call.sizeOf_spec]
            simp only [List.cons.sizeOf_spec, Partial.Expr.call.sizeOf_spec] at h₁
            omega
    unfold Partial.Expr.asSpec at h
    rw [List.mapM₁_eq_mapM] at h
    simp only [Option.map_eq_map, Option.map_eq_some'] at h
    have ⟨ members', h₁ , h₂ ⟩ := h
    rw [← h₂]
    unfold Spec.Expr.asPartialExpr
    rw [List.map₁_eq_map]

    have sizeH : sizeOf args < sizeOf (Partial.Expr.call xfn args) := by
      simp only [Partial.Expr.call.sizeOf_spec]
      omega
    rw [inner]
    repeat assumption
termination_by sizeOf pe
decreasing_by
  all_goals (try (simp_wf <;> (try rename_i a _ _ _ _ _ _ <;> rw [a]) <;> (try (rename_i a _ _ _ _ _ _ _ <;> rw [a])) <;> (try (rename_i a _ _ _) <;> rw [a]) <;> simp <;> omega))
  case _ =>
    simp_wf
    rename_i f _ _ _
    rw [f]
    simp only [Partial.Expr.set.sizeOf_spec]
    simp at h₁
    omega
  case _ =>
    simp_wf
    simp only [List.cons.sizeOf_spec, Partial.Expr.record.sizeOf_spec] at h₁
    rename_i f g _ _
    rw [f]
    simp only [Partial.Expr.record.sizeOf_spec]
    have size_step : sizeOf g.snd < sizeOf g := by
      cases g
      case _ =>
        simp only [Prod.mk.sizeOf_spec]
        omega
    omega
  case _ =>
    simp_wf
    rename_i f _ _ _
    rw [f]
    simp only [Partial.Expr.call.sizeOf_spec]
    simp at h₁
    omega


/-
  Creates an inductive hypothesis for the given expression
-/
local macro "roundtrip₂_recurse" r:ident e:ident : tactic => do
  `(tactic| (
    have ih : Expr.asSpec (Spec.Expr.asPartialExpr $e) = some $e := by
      apply $r
      rfl
    rw [ih]
  ))

/-
  Domain-specific combination of simps and rfl, repeated
-/
local macro "slam" : tactic => do
  `(tactic |(
    simp only [Option.map_eq_map, Option.map_some']
    repeat rw [applicative_some]
    repeat rfl
  ))

/-
  Solves binary ops goals for roundtrip₂
-/
local macro "binop₂" r:ident : tactic => do
  `(tactic | (
    rename_i lhs rhs
    roundtrip₂_recurse $r lhs
    roundtrip₂_recurse $r rhs
    slam
  ))

/-
  Simplify a bunch then call omega
-/
local macro "somega" : tactic => do
  `(tactic | (
    simp only [
      List.cons.sizeOf_spec,
      Spec.Expr.record.sizeOf_spec,
      Spec.Expr.call.sizeOf_spec,
      Spec.Expr.set.sizeOf_spec]
    omega
  ))

/--
  A theorem for mapM specialized to option
-/
private theorem mapM_option_cons
  (a : α)
  (as : List α)
  (b : β)
  (bs : List β)
  (f : α → Option β) :
  f a = some b →
  List.mapM f as = some bs  →
  List.mapM f (a :: as) = some (b :: bs) := by
  intros h₁ h₂
  simp
  apply And.intro <;> assumption

theorem roundtrip₂ (e : Spec.Expr) (pe : Partial.Expr) :
  e.asPartialExpr = pe →
  (pe.asSpec = some e) := by
  cases e  <;> intros h
    <;> (try (simp only [Spec.Expr.asPartialExpr] at h <;> rw [← h] <;> simp only [Expr.asSpec]))
    <;> (try (rename_i lhs rhs <;> roundtrip₂_recurse roundtrip₂ lhs <;> roundtrip₂_recurse roundtrip₂ rhs <;> slam))
    <;> (try (rename_i a _ <;> roundtrip₂_recurse roundtrip₂ a <;> slam))
    <;> try (repeat rfl)
  case ite cond cons alt =>
    roundtrip₂_recurse roundtrip₂ cond
    slam
  case unaryApp =>
    rename_i e
    roundtrip₂_recurse roundtrip₂ e
    slam
  case set members =>
    have inner : ∀ (es : List Spec.Expr) (es' : List Partial.Expr),
      sizeOf es < sizeOf (Spec.Expr.set members) →
      List.map Spec.Expr.asPartialExpr es = es' →
      List.mapM Partial.Expr.asSpec es' = some es := by
        intros es
        induction es <;> intros es' h₁ h₂
        case nil =>
          simp only [List.map_nil] at h₂
          rw [← h₂]
          simp only [List.mapM_nil, Option.pure_def]
        case cons head tail ih =>
          cases es'
          case nil =>
            simp only [List.map_cons] at h₂
          case cons head' tail' =>
            simp only [List.map_cons, List.cons.injEq] at h₂
            have ⟨h_head, h_tails ⟩ := h₂
            rw [mapM_option_cons]
            apply roundtrip₂
            assumption
            apply ih
            simp only [List.cons.sizeOf_spec, Spec.Expr.set.sizeOf_spec] at h₁
            somega
            assumption
    rw [List.mapM₁_eq_mapM]
    rw [List.map₁_eq_map]
    rw [inner]
    simp only [Option.map_eq_map, Option.map_some', Option.some.injEq, Spec.Expr.set.injEq]
    rfl
    somega
    rfl
  case record attrs =>
    simp only [Option.map_eq_map, Option.map_eq_some', Spec.Expr.record.injEq, exists_eq_right]
    rw [mapM₂_eq_mapM_partial_attr]
    rw [map_attach_eq_map_attr]
    have inner : ∀ (as: List (Spec.Attr × Spec.Expr)) (pas: List (Spec.Attr × Partial.Expr)),
      sizeOf as < sizeOf (Spec.Expr.record attrs) →
      List.map (λ (name,expr) => (name, expr.asPartialExpr)) as = pas →
      List.mapM (λ (name,expr) => Option.map (λ e => (name,e)) expr.asSpec) pas = some as
      := by
      intros as
      induction as <;> intros pas h₁ h₂
      case nil =>
        simp only [List.map_nil] at h₂
        rw [← h₂]
        simp
      case cons head tail ih =>
        simp only [List.map_cons] at h₂
        simp only
        cases pas
        case nil =>
          simp at h₂
        case cons head' tail' =>
          simp only [List.cons.injEq] at h₂
          have ⟨ h₂₁, h₂₂ ⟩ := h₂
          rw [mapM_option_cons]
          simp only [Option.map_eq_some']
          exists head.snd
          apply And.intro
          case _ => {
            apply roundtrip₂
            rw [← h₂₁]
          }
          case _ => {
            rw [← h₂₁]
          }
          case _ => {
            apply ih
            simp only [List.cons.sizeOf_spec, Spec.Expr.record.sizeOf_spec] at h₁
            somega
            assumption
          }
    rw [inner]
    somega
    rfl
  case call xfn args =>
    have inner : ∀ (es : List Spec.Expr) (es' : List Partial.Expr),
      sizeOf es < sizeOf (Spec.Expr.call xfn args) →
      List.map Spec.Expr.asPartialExpr es = es' →
      List.mapM Partial.Expr.asSpec es' = some es := by
        intros es
        induction es <;> intros es' h₁ h₂
        case nil =>
          simp only [List.map_nil] at h₂
          rw [← h₂]
          simp only [List.mapM_nil, Option.pure_def]
        case cons head tail ih =>
          cases es'
          case nil =>
            simp only [List.map_cons] at h₂
          case cons head' tail' =>
            simp only [List.map_cons, List.cons.injEq] at h₂
            have ⟨h_head, h_tails ⟩ := h₂
            rw [mapM_option_cons]
            apply roundtrip₂
            assumption
            apply ih
            simp only [List.cons.sizeOf_spec, Spec.Expr.call.sizeOf_spec] at h₁
            somega
            assumption
    rw [List.mapM₁_eq_mapM]
    rw [List.map₁_eq_map]
    rw [inner]
    simp only [Option.map_eq_map, Option.map_some', Option.some.injEq, Spec.Expr.set.injEq]
    rfl
    somega
    rfl
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (try (simp only [List.cons.sizeOf_spec, Spec.Expr.set.sizeOf_spec, Spec.Expr.call.sizeOf_spec] at h₁ <;> omega))
  case _ =>
    simp only [List.cons.sizeOf_spec, Spec.Expr.record.sizeOf_spec] at h₁
    rename_i head' tail' _ h_eq' head as _
    have size_step : sizeOf head'.snd  < sizeOf head' := by
      cases head'
      case _ =>
        simp only [Prod.mk.sizeOf_spec]
        omega
    omega

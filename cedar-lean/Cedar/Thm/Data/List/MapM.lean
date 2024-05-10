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

import Cedar.Data.List
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List.Forall

namespace List

open Cedar.Data

/-! ### mapM, mapM', and mapM₁ -/

/--
  `mapM` with a function that always produces `pure`
-/
theorem mapM_pure {α β} [Monad m] [LawfulMonad m] {f : α → β} {xs : List α} :
  xs.mapM ((λ a => pure (f a)) : α → m β) = pure (xs.map f)
:= by
  induction xs
  case nil => simp only [mapM_nil, map_nil]
  case cons hd tl ih => simp [ih]

theorem mapM_some {xs : List α} :
  xs.mapM some = some xs
:= by
  -- Probably could be proved as a corollary of `mapM_pure`, but I couldn't
  -- easily get that to work, and the direct inductive proof is very short
  induction xs
  case nil => simp only [mapM_nil, Option.pure_def]
  case cons hd tl ih => simp [ih]

theorem mapM_map {α β γ} [Monad m] [LawfulMonad m] {f : α → β} {g : β → m γ} {xs : List α} :
  List.mapM g (xs.map f) = xs.mapM λ x => g (f x)
:= by
  induction xs
  case nil => simp only [map_nil, mapM_nil]
  case cons hd tl ih => simp [ih]

theorem mapM_pmap_subtype [Monad m] [LawfulMonad m]
  {p : α → Prop}
  (f : α → m β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.mapM (λ x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.mapM f as
:= by
  rw [←List.mapM'_eq_mapM]
  induction as <;> simp [*]

theorem mapM₁_eq_mapM [Monad m] [LawfulMonad m]
  (f : α → m β)
  (as : List α) :
  List.mapM₁ as (λ x : { x // x ∈ as } => f x.val) =
  List.mapM f as
:= by
  simp [mapM₁, attach, mapM_pmap_subtype]

theorem mapM_implies_nil {f : α → Except β γ} {as : List α}
  (h₁ : List.mapM f as = Except.ok []) :
  as = []
:= by
  rw [←List.mapM'_eq_mapM] at h₁
  cases as
  case nil => rfl
  case cons hd tl =>
    simp only [List.mapM'] at h₁
    cases h₂ : f hd <;> simp only [h₂, Except.bind_err, Except.bind_ok] at h₁
    cases h₃ : List.mapM' f tl <;>
    simp [h₃, pure, Except.pure] at h₁

theorem mapM_head_tail {α β γ} {f : α → Except β γ} {x : α} {xs : List α} {y : γ} {ys : List γ} :
  (List.mapM f (x :: xs)) = Except.ok (y :: ys) →
  (List.mapM f xs) = Except.ok ys
:= by
  simp only [← mapM'_eq_mapM, mapM'_cons]
  cases h₁ : f x <;>
  simp only [h₁, Except.bind_ok, Except.bind_err, false_implies]
  cases h₂ : mapM' f xs <;>
  simp [h₂, pure, Except.pure]

theorem mapM'_ok_iff_forall₂ {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .ok ys ↔
  List.Forall₂ (λ x y => f x = .ok y) xs ys
:= by
  constructor
  case mp =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [mapM'_nil, pure, Except.pure, Except.ok.injEq] at h₁
      subst h₁
      exact List.Forall₂.nil
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Except.pure] at h₁
      cases h₂ : f xhd <;>
      simp only [h₂, Except.bind_err, Except.bind_ok] at h₁
      rename_i yhd
      cases h₃ : mapM' f xtl <;>
      simp only [h₃, Except.bind_err, Except.bind_ok] at h₁
      rename_i ytl
      simp only [Except.ok.injEq] at h₁
      subst h₁
      exact List.Forall₂.cons h₂ (ih h₃)
  case mpr =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [forall₂_nil_left_iff] at h₁
      simp only [mapM'_nil, pure, Except.pure, h₁]
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Except.pure]
      replace ⟨yhd, ytl, h₁, h₃, h₄⟩ := forall₂_cons_left_iff.mp h₁
      subst ys
      cases h₂ : f xhd
      case error e => simp [h₁] at h₂
      case ok y' =>
        simp only [h₁, Except.ok.injEq] at h₂
        subst y'
        specialize @ih ytl h₃
        simp only [ih, Except.bind_err, Except.bind_ok]

theorem mapM_ok_iff_forall₂ {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM f xs = .ok ys ↔
  List.Forall₂ (λ x y => f x = .ok y) xs ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_iff_forall₂

/--
  Note that the converse is not true:
  counterexample `xs` is `[1]`, `ys` is `[1, 2]`, `f` is `Except.ok`

  But for a limited converse, see `all_ok_implies_mapM'_ok`
-/
theorem mapM'_ok_implies_all_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .ok ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
:= by
  intro h
  exact forall₂_implies_all_left (mapM'_ok_iff_forall₂.mp h)

theorem mapM_ok_implies_all_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM f xs = .ok ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_implies_all_ok

theorem all_ok_implies_mapM'_ok {α β γ} {f : α → Except γ β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = .ok y) →
  ∃ ys, List.mapM' f xs = .ok ys
:= by
  intro h₁
  induction xs
  case nil => exists []
  case cons xhd xtl ih =>
    simp only [mem_cons, forall_eq_or_imp] at h₁
    replace ⟨⟨yhd, h₁⟩, h₂⟩ := h₁
    replace ⟨ytl, ih⟩ := ih h₂
    exists yhd :: ytl
    simp [h₁, ih, pure, Except.pure]

theorem all_ok_implies_mapM_ok {α β γ} {f : α → Except γ β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = .ok y) →
  ∃ ys, List.mapM f xs = .ok ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact all_ok_implies_mapM'_ok

/--
  Note that the converse is not true:
  counterexample `ys` is `[1]`, `xs` is `[1, 2]`, `f` is `Except.ok`

  But for a limited converse, see `all_from_ok_implies_mapM'_ok`
-/
theorem mapM'_ok_implies_all_from_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .ok ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
:= by
  intro h
  exact forall₂_implies_all_right (mapM'_ok_iff_forall₂.mp h)

theorem mapM_ok_implies_all_from_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM f xs = .ok ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_implies_all_from_ok

theorem all_from_ok_implies_mapM'_ok {α β γ} {f : α → Except γ β} {ys : List β} :
  (∀ y ∈ ys, ∃ x, f x = .ok y) →
  ∃ xs, List.mapM' f xs = .ok ys
:= by
  intro h₁
  induction ys
  case nil => exists []
  case cons yhd ytl ih =>
    simp only [mem_cons, forall_eq_or_imp] at h₁
    replace ⟨⟨xhd, h₁⟩, h₂⟩ := h₁
    replace ⟨xtl, ih⟩ := ih h₂
    exists xhd :: xtl
    simp [h₁, ih, pure, Except.pure]

theorem all_from_ok_implies_mapM_ok {α β γ} {f : α → Except γ β} {ys : List β} :
  (∀ y ∈ ys, ∃ x, f x = .ok y) →
  ∃ xs, List.mapM f xs = .ok ys
:= by
  intro h
  have ⟨xs, h₂⟩ := all_from_ok_implies_mapM'_ok h
  rw [List.mapM'_eq_mapM] at h₂
  exists xs

/--
  The converse is not true:
  counterexample `xs` is `[1, 2]` and `f` is `Except.error`.
  In that case, `f 2 = .error 2` but `xs.mapM' f = .error 1`.
-/
theorem mapM'_error_implies_exists_error {α β γ} {f : α → Except γ β} {xs : List α} {e : γ} :
  List.mapM' f xs = .error e → ∃ x ∈ xs, f x = .error e
:= by
  intro h₁
  cases xs
  case nil =>
    simp only [mapM'_nil, pure, Except.pure] at h₁
  case cons xhd xtl =>
    simp only [mapM'_cons] at h₁
    cases h₂ : f xhd <;>
    simp only [h₂, Except.bind_ok, Except.bind_err, Except.error.injEq] at h₁
    case error =>
      subst h₁
      exists xhd
      simp only [mem_cons, true_or, h₂, and_self]
    case ok =>
      cases h₃ : mapM' f xtl <;>
      simp only [h₃, Except.bind_ok, Except.bind_err, Except.error.injEq, pure, Except.pure] at h₁
      subst h₁
      replace h₃ := mapM'_error_implies_exists_error h₃
      replace ⟨x, h₃⟩ := h₃
      exists x
      simp only [mem_cons, h₃, or_true, and_self]

theorem mapM_error_implies_exists_error {α β γ} {f : α → Except γ β} {xs : List α} {e : γ} :
  List.mapM f xs = .error e → ∃ x ∈ xs, f x = .error e
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_error_implies_exists_error

theorem mapM'_some_iff_forall₂ {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys ↔
  List.Forall₂ (λ x y => f x = .some y) xs ys
:= by
  constructor
  case mp =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [mapM'_nil, pure, Option.some.injEq] at h₁
      subst h₁
      exact List.Forall₂.nil
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h₁
      replace ⟨yhd, h₁, ytl, h₂, h₃⟩ := h₁
      subst h₃
      exact List.Forall₂.cons h₁ (ih h₂)
  case mpr =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [forall₂_nil_left_iff] at h₁
      simp only [mapM'_nil, pure, Except.pure, h₁]
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Except.pure]
      replace ⟨yhd, ytl, h₁, h₃, h₄⟩ := forall₂_cons_left_iff.mp h₁
      subst ys
      cases h₂ : f xhd
      case none => simp [h₁] at h₂
      case some y' =>
        simp only [h₁, Option.some.injEq] at h₂
        subst y'
        simp [@ih ytl h₃]

theorem mapM_some_iff_forall₂ {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys ↔
  List.Forall₂ (λ x y => f x = .some y) xs ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_iff_forall₂

/--
  Note that the converse is not true:
  counterexample `xs` is `[1]`, `ys` is `[1, 2]`, `f` is `Option.some`
-/
theorem mapM'_some_implies_all_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .some y
:= by
  intro h
  exact forall₂_implies_all_left (mapM'_some_iff_forall₂.mp h)

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .some y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_implies_all_some

/--
  Note that the converse is not true:
  counterexample `ys` is `[1]`, `xs` is `[1, 2]`, `f` is `Option.some`
-/
theorem mapM'_some_implies_all_from_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .some y
:= by
  intro h
  exact forall₂_implies_all_right (mapM'_some_iff_forall₂.mp h)

theorem mapM_some_implies_all_from_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .some y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_implies_all_from_some

theorem mapM'_none_iff_exists_none {α β} {f : α → Option β} {xs : List α} :
  List.mapM' f xs = none ↔ ∃ x ∈ xs, f x = none
:= by
  constructor
  case mp =>
    intro h₁
    cases xs
    case nil => simp at h₁
    case cons xhd xtl =>
      cases h₂ : f xhd <;> simp only [h₂, mem_cons, exists_eq_or_imp, true_or, false_or]
      case some yhd =>
        simp only [mapM'_cons, h₂, Option.pure_def, Option.bind_eq_bind, Option.bind_some_fun,
          Option.bind_eq_none] at h₁
        apply mapM'_none_iff_exists_none.mp
        by_contra h₃
        rw [← ne_eq] at h₃
        replace ⟨ytl, h₃⟩ := Option.ne_none_iff_exists'.mp h₃
        exact h₁ ytl h₃
  case mpr =>
    intro h₁
    replace ⟨x, h₁, h₂⟩ := h₁
    cases xs <;> simp only [mem_cons, not_mem_nil] at h₁
    case cons xhd xtl =>
      simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none]
      intro yhd h₃ ytl h₄
      rcases h₁ with h₁ | h₁
      · subst h₁ ; simp [h₂] at h₃
      · replace h₄ := mapM'_some_implies_all_some h₄
        replace ⟨y, _, h₅⟩ := h₄ x h₁
        simp [h₂] at h₅

theorem mapM_none_iff_exists_none {α β} {f : α → Option β} {xs : List α} :
  List.mapM f xs = none ↔ ∃ x ∈ xs, f x = none
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_none_iff_exists_none

theorem mapM'_some_eq_filterMap {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys →
  List.filterMap f xs = ys
:= by
  intro h
  induction xs generalizing ys
  case nil =>
    simp only [mapM'_nil, Option.pure_def, Option.some.injEq, filterMap_nil] at *
    exact h
  case cons hd tl ih =>
    simp only [filterMap_cons]
    simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
      Option.some.injEq] at h
    replace ⟨hd', h, tl', hm, hys⟩ := h
    subst hys
    simp only [h, cons.injEq, true_and]
    exact ih hm

theorem mapM_some_eq_filterMap {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys →
  List.filterMap f xs = ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_eq_filterMap

end List

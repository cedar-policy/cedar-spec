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

import Cedar.Thm.Data.List.Basic

/-!

# Properties of Lists

This file contains useful lemmas about standard list functions and
our custom variations on these.
-/

namespace List

/-! ### any -/

theorem any_of_mem {f : α → Bool} {x : α} {xs : List α}
  (h₁ : x ∈ xs)
  (h₂ : f x) :
  any xs f = true
:= by
  cases xs <;> simp only [mem_cons, not_mem_nil] at h₁
  case cons hd tl =>
    simp only [any_cons, Bool.or_eq_true, any_eq_true]
    rcases h₁ with h₁ | h₁
    subst h₁
    simp only [h₂, true_or]
    apply Or.inr
    exists x

/-! ### all -/

/--
  Copied from Mathlib. We can delete this if it gets added to Batteries.
-/
theorem all_pmap_subtype
  {p : α → Prop}
  (f : α → Bool)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.all (List.pmap Subtype.mk as h) (λ x : { a : α // p a } => f x.val)
    =
    List.all as f
:= by
  induction as <;> simp [*]

/-! ### map and map₁ -/

/--
  Copied from Mathlib. We can delete this if it gets added to Batteries.
-/
theorem map_congr {f g : α → β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]

/--
  Copied from Mathlib. We can delete this if it gets added to Batteries.
-/
theorem map_pmap_subtype
  {p : α → Prop}
  (f : α → β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.map (λ x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.map f as
:= by
  induction as <;> simp [*]

/--
  Not actually a special case of `map_pmap_subtype` -- you can use this in
  places you can't use `map_pmap_subtype` because the LHS function (being
  mapped) doesn't fit the `map_pmap_subtype` form but does fit this form (where
  the application of `f` is not the outermost AST node of the function,
  basically)
-/
theorem map_pmap_subtype_snd
  {p : (α × β) → Prop}
  (f : β → γ)
  (xs : List (α × β))
  (h : ∀ pair ∈ xs, p pair)
  : List.map (λ x : { pair : (α × β) // p pair } => (x.val.fst, f x.val.snd)) (List.pmap Subtype.mk xs h)
    =
    xs.map λ pair => (pair.fst, f pair.snd)
:= by
  induction xs <;> simp [*]

theorem attach_def {as : List α} :
  as.attach = pmap Subtype.mk as λ _ => id
:= by
  simp [attach, attachWith]

theorem map₁_eq_map (f : α → β) (as : List α) :
  as.map₁ (λ x : {x // x ∈ as} => f x.val) =
  as.map f
:= by
  simp [map₁, attach_def, map_pmap_subtype]


theorem map_attach₂ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : (α × β) → γ) :
  xs.attach₂.map (λ x : { x : α × β // sizeOf x.snd < 1 + sizeOf xs } => f x.1) =
  xs.map f
:= by
  simp [attach₂, map_pmap_subtype]

/--
  Not actually a special case of `map_attach₂` -- you can use this in places you
  can't use `map_attach₂` because the LHS function (being mapped) doesn't fit
  the `map_attach₂` form but does fit this form (where the application of `f` is
  not the outermost AST node of the function, basically)
-/
theorem map_attach₂_snd {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : β → γ) :
  xs.attach₂.map (λ x : {x : α × β // sizeOf x.snd < 1 + sizeOf xs } => match x with | ⟨(a, b), _⟩ => (a, f b)) =
  xs.map λ (a, b) => (a, f b)
:= by
  simp [attach₂, map_pmap_subtype_snd]

/--
  same as `map_attach₂_snd` but for `attach₃`
-/
theorem map_attach₃_snd [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : β → γ) :
  xs.attach₃.map (λ x : {x : α × β // sizeOf x.snd < 1 + (1 + sizeOf xs) } => match x with | ⟨(a, b), _⟩ => (a, f b)) =
  xs.map λ (a, b) => (a, f b)
:= by
  simp [attach₃, map_pmap_subtype_snd]

/-! ### Forall₂ -/

/--
  Copied from Mathlib
-/
theorem forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

/--
  Copied from Mathlib
-/
theorem forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

/--
  Copied from Mathlib
-/
theorem Forall₂.imp (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim

/--
  Copied from Mathlib
-/
theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

/--
  Copied from Mathlib
-/
theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

theorem forall₂_singleton_right_iff {α β} {R : α → β → Prop} {xs : List α} {y : β} :
  Forall₂ R xs [y] ↔ ∃ x, R x y ∧ xs = [x]
:= by
  constructor <;> intro h
  case mp =>
    have ⟨xhd, xtl, hx, h, hxs⟩ := forall₂_cons_right_iff.mp h
    rw [forall₂_nil_right_iff] at h
    subst h hxs
    exists xhd
  case mpr =>
    replace ⟨x, h, hxs⟩ := h
    subst hxs
    exact Forall₂.cons h Forall₂.nil

theorem forall₂_pair_right_iff {α β} {R : α → β → Prop} {xs : List α} {y₁ y₂ : β} :
  Forall₂ R xs [y₁, y₂] ↔ ∃ x₁ x₂, R x₁ y₁ ∧ R x₂ y₂ ∧ xs = [x₁, x₂]
:= by
  constructor <;> intro h
  case mp =>
    have ⟨x₁, xtl₁, _, h, _⟩ := forall₂_cons_right_iff.mp h
    have ⟨x₂, xtl₂, _, h, _⟩ := forall₂_cons_right_iff.mp h
    rw [forall₂_nil_right_iff] at h
    subst xtl₂ xtl₁
    exists x₁, x₂
  case mpr =>
    replace ⟨x₁, x₂, h₁, h₂, hxs⟩ := h
    subst xs
    exact Forall₂.cons h₁ (Forall₂.cons h₂ Forall₂.nil)

/--
  Note the converse is not true:
  counterexample `R` is `=`, `xs` is `[1]`, `ys` is `[1, 2]`
-/
theorem forall₂_implies_all_left {α β} {R : α → β → Prop} {xs : List α} {ys : List β} :
  List.Forall₂ R xs ys →
  ∀ x ∈ xs, ∃ y ∈ ys, R x y
:= by
  intro h
  induction h
  case nil =>
    simp only [not_mem_nil, false_and, exists_false, imp_self, implies_true]
  case cons xhd yhd xtl ytl hhd _ ih =>
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with hx | hx
    · subst hx
      exists yhd
      simp only [mem_cons, true_or, hhd, and_self]
    · have ⟨y, ih⟩ := ih x hx
      exists y
      simp only [mem_cons, ih, or_true, and_self]

theorem forall₂_implies_all_right {α β} {R : α → β → Prop} {xs : List α} {ys : List β} :
  List.Forall₂ R xs ys →
  ∀ y ∈ ys, ∃ x ∈ xs, R x y
:= by
  intro h
  induction h
  case nil =>
    simp only [not_mem_nil, false_and, exists_false, imp_self, implies_true]
  case cons xhd yhd xtl ytl hhd _ ih =>
    intro y hy
    simp only [mem_cons] at hy
    rcases hy with hy | hy
    · subst hy
      exists xhd
      simp only [mem_cons, true_or, hhd, and_self]
    · have ⟨x, ih⟩ := ih y hy
      exists x
      simp only [mem_cons, ih, or_true, and_self]

theorem forall₂_iff_map_eq {α β γ} {f : α → γ} {g : β → γ} {xs : List α} {ys : List β} :
  List.Forall₂ (λ x y => f x = g y) xs ys ↔
  xs.map f = ys.map g
:= by
  constructor <;> intro h
  case mp =>
    induction h <;> simp only [map_nil, map_cons, cons.injEq]
    constructor <;> assumption
  case mpr =>
    induction ys generalizing xs <;>
    simp only [map_nil, map_eq_nil, map_cons] at h
    case nil =>
      subst h
      simp only [Forall₂.nil]
    case cons yhd ytl ih =>
      cases xs <;> simp only [map_nil, map_cons, cons.injEq] at h
      rename_i xhd xtl
      rw [forall₂_cons_right_iff]
      exists xhd, xtl
      simp only [h.left, ih h.right, and_self]

theorem forall₂_fun_subset_implies {R : α → β → Prop} {xs xs' : List α} {ys ys' : List β} :
  List.Forall₂ R xs ys →
  List.Forall₂ R xs' ys' →
  (∀ {x y y'}, R x y → R x y' → y = y') →
  xs ⊆ xs' →
  ys ⊆ ys'
:= by
  intro ha ha' hf heqv
  intro y hy
  replace ⟨x, hx, hr⟩ := List.forall₂_implies_all_right ha y hy
  replace heqv := heqv hx
  replace ⟨y', hy', hr'⟩ := List.forall₂_implies_all_left ha' x heqv
  replace hf := hf hr hr'
  subst hf
  exact hy'


/--
The converse (ys ≡ ys' → xs ≡ xs') doesn't hold without requiring R to be
injective (as well as functional).
-/
theorem forall₂_fun_equiv_implies {R : α → β → Prop} {xs xs' : List α} {ys ys' : List β} :
  List.Forall₂ R xs ys →
  List.Forall₂ R xs' ys' →
  (∀ {x y y'}, R x y → R x y' → y = y') →
  xs ≡ xs' →
  ys ≡ ys'
:= by
  intro ha ha' hf heqv
  simp only [Equiv] at *
  replace ⟨heqv, heqv'⟩ := heqv
  constructor
  · exact forall₂_fun_subset_implies ha ha' hf heqv
  · exact forall₂_fun_subset_implies ha' ha hf heqv'

/-! ### mapM, mapM', mapM₁, and mapM₂ -/

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
  simp [mapM₁, attach_def, mapM_pmap_subtype]

theorem mapM₂_eq_mapM [Monad m] [LawfulMonad m]
  (f : (α × β) → m γ)
  (as : List (α × β)) :
  List.mapM₂ as (λ x : { x // sizeOf x.snd < 1 + sizeOf as } => f x.val) =
  List.mapM f as
:= by
  simp [mapM₂, attach₂, mapM_pmap_subtype]

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
        specialize ih h₃
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

  But for a limited converse, see `element_error_implies_mapM_error`
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

/--
  If applying `f` to any of `xs` produces an error, then `xs.mapM' f` must also
  produce an error (not necessarily the same error)

  Limited converse of `mapM'_error_implies_exists_error`
-/
theorem element_error_implies_mapM'_error {x : α} {xs : List α} {f : α → Except ε β} {e : ε} :
  x ∈ xs →
  f x = .error e →
  ∃ e', xs.mapM' f = .error e'
:= by
  intro h₁ h₂
  cases h₃ : xs.mapM' f <;> simp
  case ok pvals =>
    replace ⟨pval, _, h₃⟩ := mapM'_ok_implies_all_ok h₃ x h₁
    simp [h₂] at h₃

theorem element_error_implies_mapM_error {x : α} {xs : List α} {f : α → Except ε β} {e : ε} :
  x ∈ xs →
  f x = .error e →
  ∃ e', xs.mapM f = .error e'
:= by
  rw [← List.mapM'_eq_mapM]
  exact element_error_implies_mapM'_error

theorem mapM'_ok_eq_filterMap {α β} {f : α → Except ε β} {xs : List α} {ys : List β} :
  xs.mapM' f = .ok ys →
  xs.filterMap (λ x => match f x with | .ok y => some y | .error _ => none) = ys
:= by
  intro h
  induction xs generalizing ys
  case nil =>
    simpa [mapM'_nil, pure, Except.pure] using h
  case cons hd tl ih =>
    simp only [filterMap_cons]
    simp only [mapM'_cons, pure, Except.pure] at h
    cases h₂ : f hd <;> simp only [h₂, Except.bind_ok, Except.bind_err] at h
    case ok hd' =>
      simp only
      cases h₃ : tl.mapM' f <;> simp only [h₃, Except.bind_ok, Except.bind_err, Except.ok.injEq] at h
      case ok tl' =>
        subst ys
        simp only [ih h₃]

theorem mapM_ok_eq_filterMap {α β} {f : α → Except ε β} {xs : List α} {ys : List β} :
  xs.mapM f = .ok ys →
  xs.filterMap (λ x => match f x with | .ok y => some y | .error _ => none) = ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_eq_filterMap

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
        simp [ih h₃]

theorem mapM_some_iff_forall₂ {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys ↔
  List.Forall₂ (λ x y => f x = .some y) xs ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_iff_forall₂

/--
  Note that the converse is not true:
  counterexample `xs` is `[1]`, `ys` is `[1, 2]`, `f` is `Option.some`

  But for a limited converse, see `all_some_implies_mapM'_some`
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

theorem all_some_implies_mapM'_some {α β} {f : α → Option β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = some y) →
  ∃ ys, List.mapM' f xs = some ys
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

theorem all_some_implies_mapM_some {α β} {f : α → Option β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = some y) →
  ∃ ys, List.mapM f xs = some ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact all_some_implies_mapM'_some

/--
  Note that the converse is not true:
  counterexample `ys` is `[1]`, `xs` is `[1, 2]`, `f` is `Option.some`

  But for a limited converse, see `all_from_some_implies_mapM'_some`
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

theorem all_from_some_implies_mapM'_some {α β} {f : α → Option β} {ys : List β} :
  (∀ y ∈ ys, ∃ x, f x = some y) →
  ∃ xs, List.mapM' f xs = some ys
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

theorem all_from_some_implies_mapM_some {α β} {f : α → Option β} {ys : List β} :
  (∀ y ∈ ys, ∃ x, f x = some y) →
  ∃ xs, List.mapM f xs = some ys
:= by
  intro h
  have ⟨xs, h₂⟩ := all_from_some_implies_mapM'_some h
  rw [List.mapM'_eq_mapM] at h₂
  exists xs

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

theorem mapM'_some_subset {f : α → Option β} {xs xs' : List α} {ys : List β} :
  xs.mapM' f = some ys →
  xs' ⊆ xs →
  ∃ ys', xs'.mapM' f = some ys'
:= by
  intro hm heqv
  rw [List.mapM'_some_iff_forall₂] at hm
  replace hm := List.forall₂_implies_all_left hm
  induction xs'
  case nil =>
    simp only [mapM'_nil, Option.pure_def, Option.some.injEq, exists_eq']
  case cons xhd' xtl' ih =>
    simp only [cons_subset] at heqv
    replace ⟨ytl', ih⟩ := ih heqv.right
    replace ⟨yhd', _, hm⟩ := hm xhd' heqv.left
    simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
      Option.some.injEq]
    exists (yhd' :: ytl'), yhd'
    simp only [hm, ih, Option.some.injEq, cons.injEq, true_and, exists_eq_right, and_self]

theorem mapM_some_subset {f : α → Option β} {xs xs' : List α} {ys : List β} :
  xs.mapM f = some ys →
  xs' ⊆ xs →
  ∃ ys', xs'.mapM f = some ys'
:= by
  simp only [← mapM'_eq_mapM]
  exact mapM'_some_subset

/--
  our own variant of map_congr, for mapM'
-/
theorem mapM'_congr [Monad m] [LawfulMonad m] {f g : α → m β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → mapM' f l = mapM' g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [mapM', mapM', h₁, mapM'_congr h₂]

/--
  our own variant of map_congr, for mapM
-/
theorem mapM_congr [Monad m] [LawfulMonad m] {f g : α → m β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → mapM f l = mapM g l
:= by
  intro l
  rw [← mapM'_eq_mapM, ← mapM'_eq_mapM]
  exact mapM'_congr

/-! ### foldl -/

theorem foldl_pmap_subtype
  {p : α → Prop}
  (f : β → α → β)
  (as : List α)
  (init : β)
  (h : ∀ a, a ∈ as → p a) :
  List.foldl (λ b (x : { a : α // p a }) => f b x.val) init (List.pmap Subtype.mk as h)
  =
  List.foldl f init as
:= by
  induction as generalizing init
  case nil => simp only [pmap, foldl_nil]
  case cons ih => apply ih

/-! ### foldlM -/

theorem foldlM_of_assoc_some (f : α → α → Option α) (x₀ x₁ x₂ x₃ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = some x₂)
  (h₃ : List.foldlM f x₂ xs = some x₃):
  (do let y ← List.foldlM f x₁ xs ; f x₀ y) = some x₃
:= by
  cases xs
  case nil =>
    simp only [Option.bind_eq_bind, List.foldlM, pure, Option.some.injEq, Option.bind_some_fun] at *
    subst h₃; exact h₂
  case cons hd tl =>
    simp only [Option.bind_eq_bind, List.foldlM, Option.bind_eq_some] at *
    cases h₄ : f x₂ hd <;> simp only [h₄, false_and, exists_false, Option.some.injEq, exists_eq_left'] at h₃
    case some x₄ =>
    have h₅ := h₁ x₀ x₁ hd
    simp only [h₂, h₄, Option.some_bind] at h₅
    cases h₆ : f x₁ hd <;> simp only [h₆, Option.some_bind, Option.none_bind] at h₅
    case some x₅ =>
    have h₇ := List.foldlM_of_assoc_some f x₂ hd x₄ x₃ tl h₁ h₄ h₃
    cases h₈ : List.foldlM f hd tl <;> simp only [h₈, Option.bind_some_fun, Option.bind_none_fun] at h₇
    case some x₆ =>
    rw [eq_comm] at h₅
    cases h₉ : List.foldlM f x₅ tl <;> simp only [h₉, Option.some.injEq, exists_eq_left', false_and, exists_false]
    case none =>
      have h₁₀ := List.foldlM_of_assoc_some f x₀ x₅ x₄ x₃ tl h₁ h₅ h₃
      simp [h₉] at h₁₀
    case some x₇ =>
      have h₁₀ := List.foldlM_of_assoc_some f x₁ hd x₅ x₇ tl h₁ h₆ h₉
      simp only [h₈, Option.bind_some_fun] at h₁₀
      specialize h₁ x₀ x₁ x₆
      simp only [h₂, h₁₀, Option.some_bind] at h₁
      simp [←h₁, h₇]

theorem foldlM_of_assoc_none' (f : α → α → Option α) (x₀ x₁ x₂ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = none)
  (h₃ : List.foldlM f x₁ xs = some x₂):
  f x₀ x₂ = none
:= by
  cases xs
  case nil =>
    simp only [foldlM_nil, pure, Option.some.injEq] at h₃ ; subst h₃; exact h₂
  case cons hd tl =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_some] at h₃
    cases h₄ : f x₁ hd <;> simp only [h₄, false_and, exists_false, Option.some.injEq, exists_eq_left'] at h₃
    case some x₃ =>
    have h₅ := List.foldlM_of_assoc_some f x₁ hd x₃ x₂ tl h₁ h₄ h₃
    cases h₆ : List.foldlM f hd tl <;> simp only [h₆, Option.bind_some_fun, Option.bind_none_fun] at h₅
    case some x₄ =>
    specialize h₁ x₀ x₁ x₄
    simp only [h₂, h₅, Option.bind_none_fun, Option.bind_some_fun] at h₁
    simp [h₁]

theorem foldlM_of_assoc_none (f : α → α → Option α) (x₀ x₁ x₂ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = some x₂)
  (h₃ : List.foldlM f x₂ xs = none):
  (do let y ← List.foldlM f x₁ xs ; f x₀ y) = none
:= by
  cases xs
  case nil => simp [List.foldlM] at h₃
  case cons hd tl =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_none, Option.bind_eq_some,
      forall_exists_index, and_imp]
    cases h₄ : f x₁ hd <;> simp only [false_implies, implies_true, Option.some.injEq, forall_eq']
    case some x₃ =>
    cases h₅ : List.foldlM f x₃ tl <;> simp only [false_implies, implies_true, Option.some.injEq, forall_eq']
    case some x₄ =>
    have h₆ := List.foldlM_of_assoc_some f x₁ hd x₃ x₄ tl h₁ h₄ h₅
    cases h₇ : List.foldlM f hd tl <;> simp only [h₇, Option.bind_some_fun, Option.bind_none_fun] at h₆
    case some x₅ =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_none] at h₃
    cases h₈ : f x₂ hd <;> simp only [h₈, false_implies, implies_true, Option.some.injEq, forall_eq'] at h₃
    case none =>
      have h₉ := List.foldlM_of_assoc_none' f x₂ hd x₅ tl h₁ h₈ h₇
      have h₁₀ := h₁ x₀ x₁ x₅
      simp only [h₂, h₆, Option.bind_some_fun] at h₁₀
      simp [←h₁₀, h₉]
    case some x₆ =>
      have h₉ := List.foldlM_of_assoc_none f x₂ hd x₆ tl h₁ h₈ h₃
      simp only [h₇, Option.bind_some_fun] at h₉
      have h₁₀ := h₁ x₀ x₁ x₅
      simp only [h₂, h₆, Option.bind_some_fun] at h₁₀
      simp [←h₁₀, h₉]

theorem foldlM_of_assoc (f : α → α → Option α) (x₀ x₁ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄) ) :
  List.foldlM f x₀ (x₁ :: xs) =
  (do let y ← List.foldlM f x₁ xs ; f x₀ y)
:= by
  simp only [List.foldlM, Option.bind_eq_bind]
  cases h₂ : f x₀ x₁ <;> simp only [Option.some_bind, Option.none_bind]
  case none =>
    induction xs generalizing x₁
    case nil => simp [h₂]
    case cons hd tl ih =>
      simp only [List.foldlM, Option.bind_eq_bind]
      cases h₃ : f x₁ hd <;> simp only [Option.some_bind, Option.none_bind]
      case some x₂ =>
      apply ih x₂
      specialize h₁ x₀ x₁ hd
      simp only [h₂, h₃, Option.bind_some_fun, Option.bind_none_fun] at h₁
      rw [eq_comm] at h₁ ; exact h₁
  case some x₂ =>
    rw [eq_comm]
    cases h₃ : List.foldlM f x₂ xs
    case none =>
      exact List.foldlM_of_assoc_none f x₀ x₁ x₂ xs h₁ h₂ h₃
    case some x₃ =>
      exact List.foldlM_of_assoc_some f x₀ x₁ x₂ x₃ xs h₁ h₂ h₃

/-! ### find? -/

theorem find?_pair_map {α β γ} [BEq α] (f : β → γ) (xs : List (α × β)) (k : α)  :
  Option.map (λ x => (x.fst, f x.snd)) (List.find? (λ x => x.fst == k) xs)  =
  List.find? (λ x => x.fst == k) (List.map (λ x => (x.fst, f x.snd)) xs)
:= by
  induction xs
  case nil => simp only [find?_nil, Option.map_none', map_nil]
  case cons hd tl ih =>
    cases h₁ : hd.fst == k <;> simp only [map_cons]
    case false =>
      rw [Bool.eq_false_iff, ne_eq] at h₁
      have h₂ := @List.find?_cons_of_neg _
        (λ (x : α × β) => x.fst == k) hd tl h₁
      have h₃ := @List.find?_cons_of_neg _
        (λ (x : α × γ) => x.fst == k) (hd.fst, f hd.snd)
        (map (λ x => (x.fst, f x.snd)) tl)
      simp only [h₁, not_false_eq_true, forall_const] at h₃
      simp only [h₂, h₃]
      exact ih
    case true =>
      have h₂ := @List.find?_cons_of_pos _
        (λ (x : α × β) => x.fst == k) hd tl h₁
      have h₃ := @List.find?_cons_of_pos _
        (λ (x : α × γ) => x.fst == k) (hd.fst, f hd.snd)
        (map (λ x => (x.fst, f x.snd)) tl)
      simp only [h₁, forall_const] at h₃
      simp [h₂, h₃]

theorem find?_fst_map_implies_find? {α β γ} [BEq α] {f : β → γ} {xs : List (α × β)} {k : α} {fx : α × γ}:
  List.find? (λ x => x.fst == k) (List.map (Prod.map id f) xs) = .some fx  →
  ∃ x, xs.find? (λ x => x.fst == k) = .some x ∧ fx = Prod.map id f x
:= by
  intro h
  induction xs
  case nil => simp at h
  case cons hd tl ih =>
    simp only [map_cons, find?_cons] at h
    split at h <;> rename_i heq
    · exists hd
      simp only [Option.some.injEq] at h
      simp only [h, and_true]
      simp only [Prod.map, id_eq] at heq
      simp only [find?_cons, heq]
    · replace ⟨x, ih⟩ := ih h
      exists x
      simp only [Prod.map, id_eq] at heq
      simp [find?_cons, heq, ih]

theorem not_find?_some_iff_find?_none {α} {p : α → Bool} {xs : List α} :
  (∀ x ∈ xs, ¬xs.find? p = .some x) ↔ xs.find? p = .none
:= by
  rw [List.find?_eq_none]
  constructor
  case mp =>
    intro h x hx
    induction xs generalizing x
    case nil =>
      simp only [not_mem_nil] at hx
    case cons hd tl ih =>
      simp only [mem_cons] at hx
      rcases hx with hx | hx
      case inl =>
        by_contra hc
        subst hx
        specialize h x
        simp only [mem_cons, true_or, true_implies] at h
        simp only [find?_cons, hc, not_true_eq_false] at h
      case inr =>
        apply ih _ _ hx
        intro y hy
        simp only [mem_cons, forall_eq_or_imp] at h
        replace ⟨hnf, h⟩ := h
        specialize h y hy
        simp only [find?_cons] at h hnf
        split at h
        · rename_i heq
          simp only [heq, not_true_eq_false] at hnf
        · exact h
  case mpr =>
    intro h x hx
    by_contra hc
    replace hc := List.find?_some hc
    specialize h x hx
    contradiction


/-! ### filterMap -/

/--
  our own variant of map_congr, for filterMap
-/
theorem filterMap_congr {f g : α → Option β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → filterMap f l = filterMap g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [filterMap, filterMap, h₁, filterMap_congr h₂]

theorem filterMap_empty_iff_all_none {f : α → Option β} {xs : List α} :
  xs.filterMap f = [] ↔ ∀ x ∈ xs, f x = none
:= by
  constructor
  case mp =>
    induction xs
    case nil =>
      simp only [filterMap_nil, not_mem_nil, false_implies, implies_true, imp_self]
    case cons hd tl ih =>
      intro h₁ a h₂
      simp only [List.filterMap_cons] at h₁
      split at h₁ <;> rename_i h₃
      · rcases (List.mem_cons.mp h₂) with h₄ | h₄
        · subst h₄ ; assumption
        · apply ih h₁ a ; assumption
      · simp only at h₁
  case mpr =>
    intro h₁
    induction xs
    case nil => simp only [filterMap_nil]
    case cons hd tl ih =>
      simp only [List.filterMap_cons]
      split
      case h_1 =>
        apply ih ; clear ih
        intro a h₂
        apply h₁ a
        exact List.mem_cons_of_mem hd h₂
      case h_2 b h₂ =>
        exfalso
        specialize h₁ hd
        simp only [mem_cons, true_or, forall_const] at h₁
        simp [h₁] at h₂

theorem filterMap_nonempty_iff_exists_some {f : α → Option β} {xs : List α} :
  xs.filterMap f ≠ [] ↔ ∃ x ∈ xs, (f x).isSome
:= by
  constructor
  case mp =>
    intro h₁
    replace ⟨b, h₁⟩ := List.exists_mem_of_ne_nil (xs.filterMap f) h₁
    replace ⟨x, h₁⟩ := (List.mem_filterMap f xs).mp h₁
    exists x
    simp [h₁, Option.isSome]
  case mpr =>
    intro h₁ h₂
    rw [filterMap_empty_iff_all_none] at h₂
    replace ⟨x, h₁, h₃⟩ := h₁
    specialize h₂ x h₁
    simp [h₂, Option.isSome] at h₃

theorem f_implies_g_then_subset {f g : α → Option β} {xs : List α} :
  (∀ a b, f a = some b → g a = some b) →
  xs.filterMap f ⊆ xs.filterMap g
:= by
  intro h₁
  simp only [subset_def, mem_filterMap, forall_exists_index, and_imp]
  intro b a h₂ h₃
  exists a
  apply And.intro h₂
  exact h₁ a b h₃

end List

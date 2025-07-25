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
  simp only [map₁, attach_def, map_pmap_subtype]


theorem map_attach₂ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : (α × β) → γ) :
  xs.attach₂.map (λ x : { x : α × β // sizeOf x.snd < 1 + sizeOf xs } => f x.1) =
  xs.map f
:= by
  simp only [attach₂, map_pmap_subtype]

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
    simp only [map_nil, map_eq_nil_iff, map_cons] at h
    case nil =>
      subst h
      simp only [Forall₂.nil]
    case cons yhd ytl ih =>
      cases xs <;> simp only [map_nil, map_cons, cons.injEq, reduceCtorEq] at h
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

theorem map_preserves_forall₂
  {f : α → α'}
  {g : β → β'}
  {p₁ : α → β → Prop}
  {p₂ : α' → β' → Prop}
  {xs : List α} {ys : List β}
  (h : ∀ x y, p₁ x y → p₂ (f x) (g y))
  (hforall₂ : List.Forall₂ p₁ xs ys) :
  List.Forall₂ p₂ (xs.map f) (ys.map g)
:= by
  induction hforall₂
  case nil => simp
  case cons =>
    simp only [List.map]
    constructor
    apply h
    assumption
    assumption

theorem forall₂_swap
  {R : α → β → Prop} {xs : List α} {ys : List β}
  (hforall₂ : List.Forall₂ (λ y x => R x y) ys xs) :
  List.Forall₂ R xs ys
:= by
  induction hforall₂
  case nil => simp
  case cons =>
    constructor
    assumption
    assumption

/--
Applying `mapM` on the RHS list of `Forall₂`
leads to new `Forall₂` relation if certain
conditions are met.
-/
theorem forall₂_compose_mapM_right
  {l₁ : List α} {l₂ : List β} {l₃ : List γ}
  {R₁ : α → β → Prop}
  {R₂ : α → γ → Prop}
  {f : β → Option γ}
  (h : List.Forall₂ R₁ l₁ l₂)
  (hmapM : List.mapM f l₂ = .some l₃)
  (hf : ∀ a b, R₁ a b → ∃ c, f b = .some c ∧ R₂ a c) :
  List.Forall₂ R₂ l₁ l₃
:= by
  induction h generalizing l₃ with
  | nil =>
    simp at hmapM
    simp [hmapM]
  | cons hhd htl ih =>
    rename_i hd₁ hd₂ tl₁ tl₂
    have ⟨c, hc, hrc⟩ := hf hd₁ hd₂ hhd
    simp only [
      List.mapM_cons, hc, Option.pure_def,
      Option.bind_eq_bind,
      Option.bind_some_fun,
    ] at hmapM
    simp only [bind, Option.bind] at hmapM
    split at hmapM
    contradiction
    rename_i mapM_tl hmapM_tl
    simp only [Option.some.injEq] at hmapM
    simp only [←hmapM]
    constructor
    · exact hrc
    · specialize ih hmapM_tl
      exact ih

theorem forall₂_eq_implies_filterMap
  {l₁ : List α} {l₂ : List β} {p : α → β → Prop}
  {f : α → Option β}
  (h : List.Forall₂ p l₁ l₂)
  (hp : ∀ a b, p a b → f a = .some b) :
  l₁.filterMap f = l₂
:= by
  induction h with
  | nil => simp
  | cons hhd htl ih =>
    rename_i hd₁ hd₂ tl₁ tl₂
    simp only [List.filterMap]
    have := hp hd₁ hd₂ hhd
    simp only [this, ih]

/-! ### mapM, mapM', mapM₁, and mapM₂ -/

theorem mapM_some {xs : List α} :
  xs.mapM some = some xs
:= by
  -- Probably could be proved as a corollary of `mapM_pure`, but I couldn't
  -- easily get that to work, and the direct inductive proof is very short
  induction xs
  case nil => simp only [mapM_nil, Option.pure_def]
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
  simp only [mapM₁, attach_def, mapM_pmap_subtype]

theorem mapM₂_eq_mapM [Monad m] [LawfulMonad m] [SizeOf α] [SizeOf β]
  (f : (α × β) → m γ)
  (as : List (α × β)) :
  List.mapM₂ as (λ x : { x // sizeOf x.snd < 1 + sizeOf as } => f x.val) =
  List.mapM f as
:= by
  simp only [mapM₂, attach₂, mapM_pmap_subtype]

theorem mapM₃_eq_mapM [Monad m] [LawfulMonad m] [SizeOf α] [SizeOf β]
  (f : (α × β) → m γ)
  (as : List (α × β)) :
  List.mapM₃ as (λ x : { x // sizeOf x.snd < 1 + (1 + sizeOf as) } => f x.val) =
  List.mapM f as
:= by
  simp only [mapM₃, attach₃, mapM_pmap_subtype]

theorem mapM_implies_nil {f : α → Except β γ} {as : List α}
  (h₁ : List.mapM f as = Except.ok []) :
  as = []
:= by
  rw [←List.mapM'_eq_mapM] at h₁
  cases as
  case nil => rfl
  case cons hd tl =>
    simp only [List.mapM'] at h₁
    cases h₂ : f hd <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₁
    cases h₃ : List.mapM' f tl <;>
    simp [h₃, pure, Except.pure] at h₁

theorem mapM_head_tail {α β γ} {f : α → Except β γ} {x : α} {xs : List α} {y : γ} {ys : List γ} :
  (List.mapM f (x :: xs)) = Except.ok (y :: ys) →
  (List.mapM f xs) = Except.ok ys
:= by
  simp only [← mapM'_eq_mapM, mapM'_cons]
  cases h₁ : f x <;>
  simp only [h₁, Except.bind_ok, Except.bind_err, false_implies, reduceCtorEq]
  cases h₂ : mapM' f xs <;>
  simp [h₂, pure, Except.pure]

theorem not_mem_implies_not_mem_mapM_key_id {α β : Type} {ks : List α} {kvs : List (α × β)} {fn : α → Option β} {k: α}
  (hm : ks.mapM (λ k => do (k, ←fn k)) = some kvs)
  (hl : k ∉ ks) :
  ∀ v, (k, v) ∉ kvs
:= by
  intro v hl'
  cases ks
  case nil =>
    have : kvs = [] := by simpa using hm
    subst kvs
    cases hl'
  case cons head tail =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at hm
    cases hm₁ : fn head <;> simp only [hm₁, Option.bind_none, Option.bind_some, reduceCtorEq] at hm
    cases hm₂ : (tail.mapM (λ k => (fn k).bind λ v => some (k, v))) <;> simp only [hm₂, Option.bind_none, Option.bind_some, Option.some.injEq, reduceCtorEq] at hm
    subst kvs
    cases hl'
    case head =>
      exact hl (List.Mem.head _)
    case tail tail' ht' =>
      replace hl : k ∉ tail := (hl $ List.Mem.tail _ ·)
      exact not_mem_implies_not_mem_mapM_key_id  hm₂ hl _ ht'

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
      cases mapM' f xtl
      · simp only [reduceCtorEq] at h₁
      · simp only [reduceCtorEq] at h₁
      · rename_i yhd
        replace ⟨ytl, h₁, h₃⟩ := do_ok_eq_ok.mp h₁
        subst h₃
        exact List.Forall₂.cons h₂ (ih h₁)
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
Introduces `forall₂` through the input output relation
of a `f` through `List.mapM`. This is slightly stronger
than the forward direction of `mapM_ok_iff_forall₂`
since it allowed an extra `x ∈ xs` condition in `h`.
-/
theorem mapM_implies_forall₂
  {f : α → Except ε β}
  {p : α → β → Prop}
  {xs : List α} {ys : List β}
  (h : ∀ x y, x ∈ xs → f x = .ok y → p x y)
  (hmapM : List.mapM f xs = .ok ys) :
  List.Forall₂ p xs ys
:= by
  induction xs generalizing ys
  case nil =>
    simp only [mapM, mapM.loop, pure, Except.pure, reverse_nil, Except.ok.injEq, nil_eq] at hmapM
    simp [hmapM]
  case cons xhd xtl ih =>
    simp only [mapM_cons, Bind.bind, Except.bind, pure, Except.pure] at hmapM
    split at hmapM
    contradiction
    split at hmapM
    contradiction
    simp only [Except.ok.injEq] at hmapM
    simp only [← hmapM, forall₂_cons]
    constructor
    · apply h
      simp only [mem_cons, true_or]
      assumption
    · apply ih
      intros
      apply h
      simp only [mem_cons, or_true, *]
      assumption
      assumption

/--
Same as `mapM_implies_forall₂` but for `Option`
-/
theorem mapM_implies_forall₂_option
  {f : α → Option β}
  {p : α → β → Prop}
  {xs : List α} {ys : List β}
  (h : ∀ x y, x ∈ xs → f x = .some y → p x y)
  (hmapM : List.mapM f xs = .some ys) :
  List.Forall₂ p xs ys
:= by
  induction xs generalizing ys
  case nil =>
    simp only [mapM, mapM.loop, pure, Option.pure_def, reverse_nil, Option.some.injEq, nil_eq] at hmapM
    simp [hmapM]
  case cons xhd xtl ih =>
    simp only [mapM_cons, bind, Option.bind, pure] at hmapM
    split at hmapM
    contradiction
    simp only at hmapM
    split at hmapM
    contradiction
    simp only [Option.some.injEq] at hmapM
    simp only [← hmapM, forall₂_cons]
    constructor
    · apply h
      simp only [mem_cons, true_or]
      assumption
    · apply ih
      intros
      apply h
      simp only [mem_cons, or_true, *]
      assumption
      assumption

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
    simp only [mapM'_nil, pure, Except.pure, reduceCtorEq] at h₁
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
      simp only [h₃, Except.bind_ok, Except.bind_err, Except.error.injEq, pure, Except.pure, reduceCtorEq] at h₁
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
    cases h₂ : f hd <;> simp only [h₂, Except.bind_ok, Except.bind_err, reduceCtorEq] at h
    case ok hd' =>
      simp only
      cases h₃ : tl.mapM' f <;> simp only [h₃, Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h
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
      simp only [mapM'_cons, pure, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
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
      cases h₂ : f xhd <;> simp only [h₂, mem_cons, exists_eq_or_imp, true_or, false_or, reduceCtorEq]
      case some yhd =>
        simp only [mapM'_cons, h₂, Option.pure_def, Option.bind_eq_bind, Option.bind_some_fun,
          Option.bind_eq_none_iff, reduceCtorEq] at h₁
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
      simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff]
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
    simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
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
    simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
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

theorem forall₂_implies_mapM_eq {α₁ α₂ β ε} {xs : List α₁} {ys : List α₂} (f : α₁ → Except ε β) (g : α₂ → Except ε β):
  List.Forall₂ (fun x y => f x = g y) xs ys →
  List.mapM f xs =
  List.mapM g ys
:= by
  intro h
  cases h
  case nil => simp only [List.mapM_nil]
  case cons h₁ h₂ =>
    simp only [List.mapM_cons, h₁, forall₂_implies_mapM_eq f g h₂, bind_pure_comp]

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

theorem foldl_congr {f g : β → α → β} {init : β} {l : List α} :
  (∀ b x, x ∈ l → f b x = g b x) → foldl f init l = foldl g init l
:= by
  intro h
  induction l generalizing init
  case nil =>
    simp only [not_mem_nil, false_implies, implies_true, foldl_nil, imp_self]
  case cons lhd ltl ih =>
    simp only [mem_cons, forall_eq_or_imp, foldl_cons,
      h init lhd (by simp only [mem_cons, true_or])]
    apply ih
    intro b x hin
    apply h b x
    simp only [mem_cons, hin, or_true]

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
    simp only [Option.bind_eq_bind, List.foldlM, Option.bind_eq_some_iff] at *
    cases h₄ : f x₂ hd <;> simp only [h₄, false_and, exists_false, Option.some.injEq, exists_eq_left', reduceCtorEq] at h₃
    case some x₄ =>
    have h₅ := h₁ x₀ x₁ hd
    simp only [h₂, h₄, Option.bind_some] at h₅
    cases h₆ : f x₁ hd <;> simp only [h₆, Option.bind_some, Option.bind_none, reduceCtorEq] at h₅
    case some x₅ =>
    have h₇ := List.foldlM_of_assoc_some f x₂ hd x₄ x₃ tl h₁ h₄ h₃
    cases h₈ : List.foldlM f hd tl <;> simp only [h₈, Option.bind_some_fun, Option.bind_none_fun, reduceCtorEq] at h₇
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
      simp only [h₂, h₁₀, Option.bind_some] at h₁
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
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h₃
    cases h₄ : f x₁ hd <;> simp only [h₄, false_and, exists_false, Option.some.injEq, exists_eq_left', reduceCtorEq] at h₃
    case some x₃ =>
    have h₅ := List.foldlM_of_assoc_some f x₁ hd x₃ x₂ tl h₁ h₄ h₃
    cases h₆ : List.foldlM f hd tl <;> simp only [h₆, Option.bind_some_fun, Option.bind_none_fun, reduceCtorEq] at h₅
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
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_none_iff, Option.bind_eq_some_iff,
      forall_exists_index, and_imp]
    cases h₄ : f x₁ hd <;> simp only [false_implies, implies_true, Option.some.injEq, forall_eq', reduceCtorEq]
    case some x₃ =>
    cases h₅ : List.foldlM f x₃ tl <;> simp only [false_implies, implies_true, Option.some.injEq, forall_eq', reduceCtorEq]
    case some x₄ =>
    have h₆ := List.foldlM_of_assoc_some f x₁ hd x₃ x₄ tl h₁ h₄ h₅
    cases h₇ : List.foldlM f hd tl <;> simp only [h₇, Option.bind_some_fun, Option.bind_none_fun, reduceCtorEq] at h₆
    case some x₅ =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_none_iff] at h₃
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
  cases h₂ : f x₀ x₁ <;> simp only [Option.bind_some, Option.bind_none]
  case none =>
    induction xs generalizing x₁
    case nil => simp [h₂]
    case cons hd tl ih =>
      simp only [List.foldlM, Option.bind_eq_bind]
      cases h₃ : f x₁ hd <;> simp only [Option.bind_some, Option.bind_none]
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
  case nil => simp only [find?_nil, Option.map_none, map_nil]
  case cons hd tl ih =>
    cases h₁ : hd.fst == k <;> simp only [map_cons]
    case false =>
      rw [Bool.eq_false_iff, ne_eq] at h₁
      have h₂ := @List.find?_cons_of_neg _
        (λ (x : α × β) => x.fst == k) hd tl h₁
      have h₃ := @List.find?_cons_of_neg _
        (λ (x : α × γ) => x.fst == k) (hd.fst, f hd.snd)
        (map (λ x => (x.fst, f x.snd)) tl)
      simp only [h₁, not_false_eq_true, forall_const, reduceCtorEq] at h₃
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

theorem find?_implies_find?_fst_map
  {α β γ} [BEq α] [ReflBEq α]
  {l : List (α × β)}
  {k : α} {v : β}
  {f : α → β → γ}
  (h : List.find? (λ x => x.fst == k) l = some (k, v)) :
  List.find? (λ x => x.fst == k) (l.map λ (k, v) => (k, f k v)) = some (k, f k v)
:= by
  induction l
  case nil => simp only [find?_nil, reduceCtorEq] at h
  case cons head tail ih =>
    simp only [find?_cons_eq_some, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    cases h
    case _ h => simp [h]
    case _ h =>
      specialize ih h.2
      simp only [List.map]
      simp only [List.find?]
      simp [ih, h]

theorem find?_implies_append_find?
  {a b : List α}
  {v : α}
  {f : α → Bool}
  (h : List.find? f a = some v) :
  List.find? f (a ++ b) = some v
:= by
  simp [List.find?_append, h]

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
      · simp only [reduceCtorEq] at h₁
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
    replace ⟨x, h₁⟩ := List.mem_filterMap.mp h₁
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

/-! ### forM and mapM -/

theorem mapM_forM {α β : Type} (f : α → Except β PUnit) (xs : List α) (ys : List PUnit) :
  xs.mapM f = Except.ok ys → xs.forM f = Except.ok ()
:= by
  intro h₀
  induction xs generalizing ys with
  | nil => simp only [forM_eq_forM, forM_nil]; rfl
  | cons xh xt ih =>
    simp only [forM_eq_forM, forM_cons]
    cases h₁ : f xh with
    | error =>
      simp only [List.mapM_cons] at h₀
      rw [h₁] at h₀
      simp only [Except.bind_err, reduceCtorEq] at h₀
    | ok =>
        simp only [List.mapM_cons, pure, Except.pure] at h₀
        cases h₁ : f xh <;>
        simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₀
        rename_i yh
        cases h₂ : List.mapM f xt <;>
        simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₀
        rename_i yt
        simp only [Except.ok.injEq] at h₀
        subst h₀
        simp only [Except.bind_ok]
        apply ih yt
        assumption

theorem forM_mapM {α β : Type} (f : α → Except β PUnit) (xs : List α) :
  xs.forM f = Except.ok () → ∃ ys, xs.mapM f = Except.ok ys
:= by
  intro h₁
  rw [← List.mapM'_eq_mapM]
  induction xs
  case nil =>
    simp only [List.mapM'_nil, pure, Except.pure, Except.ok.injEq]
    exists []
  case cons xh xt ih =>
    cases h₂ : f xh with
    | error =>
      simp only [List.mapM'_cons, pure, Except.pure]
      simp only [forM_eq_forM, forM_cons] at h₁
      rw [h₂] at h₁
      simp only [Except.bind_err, reduceCtorEq] at h₁
    | ok y' =>
      simp only [forM_eq_forM, forM_cons] at h₁
      rw [h₂] at h₁
      simp only [Except.bind_ok] at h₁
      simp only [List.mapM'_cons, pure, Except.pure]
      rw [h₂]
      have ⟨ys, h₃⟩ := ih h₁
      rw [h₃]
      simp only [Except.bind_ok]
      exists (y' :: ys)


theorem forM_ok_implies_all_ok {α β : Type} (xs : List α) (f : α → Except β Unit) :
  xs.forM f = Except.ok () → (∀ x ∈ xs, f x = Except.ok ())
:= by
  intro h₀ x xin
  obtain ⟨ys, h₁⟩ := forM_mapM f xs h₀
  have h₂ := List.mapM_ok_implies_all_ok h₁ x
  obtain ⟨_, _, h₅⟩ := h₂ xin
  exact h₅

theorem forM_ok_implies_all_ok' {α β : Type} {xs : List α} {f : α → Except β Unit} :
  xs.forM f = Except.ok () → (∀ x ∈ xs, f x = Except.ok ())
:= forM_ok_implies_all_ok xs f

/-! ### removeAll -/

theorem removeAll_singleton_cons_of_neq [DecidableEq α] (x y : α) (xs : List α) :
  x ≠ y → (x :: xs).removeAll [y] = x :: (xs.removeAll [y])
:= by
  intro _
  simp only [removeAll, elem_eq_mem, mem_singleton, filter_cons, Bool.not_eq_true',
    decide_eq_false_iff_not, ite_not, ite_eq_right_iff]
  intro _
  contradiction

theorem removeAll_singleton_cons_of_eq [DecidableEq α] (x : α) (xs : List α) :
  (x :: xs).removeAll [x] = xs.removeAll [x]
:= by
  simp only [removeAll, elem_eq_mem, mem_singleton, decide_true, Bool.not_true, Bool.false_eq_true,
    not_false_eq_true, filter_cons_of_neg]

theorem mem_removeAll_singleton_of_eq [DecidableEq α] (x : α) (xs : List α) :
  x ∉ xs.removeAll [x]
:= by
  simp only [removeAll, elem_eq_mem, mem_singleton]
  by_contra h
  simp only [mem_filter, decide_true, Bool.not_true, Bool.false_eq_true, and_false] at h

theorem removeAll_singleton_equiv [DecidableEq α] (x : α) (xs : List α) :
  x :: xs ≡ x :: (xs.removeAll [x])
:= by
  induction xs
  case nil =>
    simp only [removeAll, filter_nil, Equiv.refl]
  case cons xhd xtl ih =>
    cases h : decide (x = xhd)
    case false =>
      simp only [decide_eq_false_iff_not] at h
      rw [eq_comm] at h
      rw [removeAll_singleton_cons_of_neq _ _ _ h]
      apply List.Equiv.trans (List.swap_cons_cons_equiv _ _ _)
      apply List.Equiv.symm
      apply List.Equiv.trans (List.swap_cons_cons_equiv _ _ _)
      apply List.Equiv.symm
      exact List.cons_equiv_cons _ _ _ ih
    case true =>
      simp only [decide_eq_true_eq] at h
      subst h
      simp only [removeAll_singleton_cons_of_eq]
      exact List.Equiv.trans (dup_head_equiv x xtl) ih

theorem length_removeAll_le {α : Type u_1} [BEq α] (xs ys : List α) :
  (xs.removeAll ys).length ≤ xs.length
:= by
  simp only [removeAll]
  have _ := List.length_filter_le (fun x => !elem x ys) xs
  omega

/- #### Mem -/

theorem mem_pmap_subtype
  {p : α → Prop}
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  (a : α)
  (ha : p a) :
  ⟨a, ha⟩ ∈ (List.pmap Subtype.mk as h) ↔
  a ∈ as
:= by
  induction as <;> simp [*]

theorem find?_compose {α β} (f : α → β) (p₁ : β → Bool) (p₂ : α → Bool) {xs : List α} :
  (∀ x, (p₁ ∘ f) x = p₂ x) →
  List.find? (p₁ ∘ f) xs = List.find? p₂ xs
:= by
  induction xs
  case nil => simp only [Function.comp_apply, find?_nil, implies_true]
  case cons head tail h =>
    intro hₐ
    simp [find?]
    split <;> split
    case _ => rfl
    case _ heq₁ _ heq₂ =>
      specialize hₐ head
      simp only [Function.comp_apply, heq₁, heq₂, Bool.true_eq_false] at hₐ
    case _ heq₁ _ heq₂ =>
      specialize hₐ head
      simp only [Function.comp_apply, heq₁, heq₂, Bool.false_eq_true] at hₐ
    case _ => exact h hₐ

theorem mem_implies_mem_eraseDups
  [BEq α] [LawfulBEq α]
  {xs : List α} {x : α}
  (hmem : x ∈ xs) :
  x ∈ xs.eraseDups
:= by
  cases xs with
  | nil => contradiction
  | cons hd tl =>
    simp only [List.eraseDups_cons, List.mem_cons]
    simp only [List.mem_cons] at hmem
    cases hx : x == hd
    · simp only [beq_eq_false_iff_ne, ne_eq] at hx
      apply Or.inr
      simp only [hx, false_or] at hmem
      apply mem_implies_mem_eraseDups
      apply List.mem_filter.mpr
      simp only [hmem, true_and]
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
      exact hx
    · apply Or.inl
      simp only [beq_iff_eq] at hx
      exact hx
termination_by xs.length
decreasing_by
  calc
    (List.filter (fun b => !b == hd) tl).length <= tl.length := by
      apply List.length_filter_le
    _ < xs.length := by
      simp [*]

theorem mem_eraseDups_implies_mem
  [BEq α] [LawfulBEq α]
  {xs : List α} {x : α}
  (hmem : x ∈ xs.eraseDups) :
  x ∈ xs
:= by
  cases xs with
  | nil => contradiction
  | cons hd tl =>
    simp only [eraseDups_cons, mem_cons] at hmem
    simp only [mem_cons]
    cases hmem with
    | inl h => exact Or.inl h
    | inr h =>
      apply Or.inr
      have := mem_eraseDups_implies_mem h
      have := List.mem_filter.mp this
      exact this.1
termination_by xs.length
decreasing_by
  calc
    (List.filter (fun b => !b == hd) tl).length <= tl.length := by
      apply List.length_filter_le
    _ < xs.length := by
      simp [*]

theorem mem_iff_mem_eraseDups
  [BEq α] [LawfulBEq α]
  {xs : List α} {x : α} :
  x ∈ xs ↔ x ∈ xs.eraseDups
:= by
  constructor
  · apply mem_implies_mem_eraseDups
  · apply mem_eraseDups_implies_mem

/-- `mapM` preserves `SortedBy` if the keys are preserved -/
theorem mapM_preserves_SortedBy
  [LT γ]
  {l₁ : List α} {l₂ : List β}
  {f : α → Option β}
  {k₁ : α → γ}
  {k₂ : β → γ}
  (hsorted : List.SortedBy k₁ l₁)
  (hmapM : l₁.mapM f = .some l₂)
  (hkey : ∀ a b, f a = .some b → k₁ a = k₂ b) :
  List.SortedBy k₂ l₂
:= by
  have := List.mapM_some_iff_forall₂.mp hmapM
  induction this with
  | nil => constructor
  | cons hhd hrst ih =>
    rename_i hd₁ hd₂ tl₁ tl₂
    have hrst' := List.mapM_some_iff_forall₂.mpr hrst
    cases tl₂ with
    | nil => constructor
    | cons hd₂' tl₂' =>
      constructor
      · cases hrst with | cons h =>
        rename_i hd₁' _ _
        simp only [
          ←hkey _ _ hhd,
          ←hkey _ _ h
        ]
        cases hsorted
        assumption
      · apply ih
        · cases hsorted
          · constructor
          · assumption
        · exact hrst'

theorem map_restricted_id
  {l : List α}
  {f : α → α}
  (hf : ∀ x ∈ l, f x = x) :
  l.map f = l
:= by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply hf x
      simp
    · apply ih
      intros x hmem_x
      apply hf
      simp [hmem_x]

theorem findSome?_unique
  [BEq α] [LawfulBEq α]
  {l : List α} {x : α} {y : β}
  {f : α → Option β}
  (hfind : x ∈ l)
  (hf : ∀ x', (∃ y', f x' = .some y') → x' = x)
  (hx : f x = .some y) :
  l.findSome? f = .some y
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.findSome?]
    simp only [List.mem_cons] at hfind
    cases hfind with
    | inl hfind =>
      simp only [←hfind, hx]
    | inr hfind =>
      split
      · rename_i v' hhd
        simp only [←hx, ←hhd]
        congr
        apply hf
        exists v'
      · exact ih hfind

theorem find?_unique_entry
  {l : List α}
  {f : α → Bool}
  {v : α}
  (hf : ∀ x ∈ l, f x → x = v)
  (hmem : v ∈ l)
  (hv : f v) :
  List.find? f l = .some v
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.find?]
    cases hmem with
    | inl hmem =>
      simp only [hmem] at hv
      simp only [hv, hmem]
    | inr hmem =>
      split
      · rename_i h
        have := hf hd
        simp only [List.mem_cons, true_or, forall_const] at this
        specialize this h
        simp [this]
      · apply ih
        · intros x hmem_x_tl
          have : x ∈ hd :: tl := by simp [hmem_x_tl]
          exact hf x this
        · exact hmem

theorem find?_stronger_pred
  {l : List α} {v : α}
  {f : α → Bool}
  {g : α → Bool}
  (hfind : List.find? f l = .some v)
  (hg : ∀ x ∈ l, g x → f x)
  (hv : g v) :
  List.find? g l = .some v
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?]
    cases h : g hd with
    | false =>
      simp only [List.find?] at hfind
      apply ih
      · split at hfind
        · simp only [Option.some.injEq] at hfind
          simp only [hfind, hv] at h
          contradiction
        · exact hfind
      · intros x hmem_x h
        apply hg
        · simp [hmem_x]
        · exact h
    | true =>
      simp only [Option.some.injEq]
      have := hg hd List.mem_cons_self h
      simp only [List.find?] at hfind
      simp only [this, Option.some.injEq] at hfind
      exact hfind

theorem mem_implies_find?
  {l : List α} {k : α} {f : α → Bool}
  (hmem : k ∈ l)
  (hk : f k)
  (hf : ∀ k', f k' → k' = k) :
  List.find? f l = .some k
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.find?_cons_eq_some, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases hmem with
    | inl hmem =>
      apply Or.inl
      simp [←hmem, hk]
    | inr hmem =>
      cases hhd : f hd with
      | true =>
        apply Or.inl
        simp [hhd, hf hd hhd]
      | false =>
        apply Or.inr
        simp only [true_and]
        exact ih hmem

theorem filterMap_eq_filterMap
  {l₁ : List α} {l₂ : List β}
  {p : α → β → Prop} {f₁ : α → Option γ} {f₂ : β → Option γ}
  (h : List.Forall₂ p l₁ l₂)
  (hp : ∀ a b, p a b → f₁ a = f₂ b) :
  l₁.filterMap f₁ = l₂.filterMap f₂
:= by
  induction h with
  | nil => simp
  | cons hhd htl ih =>
    rename_i a b hmem_a hmem_b
    simp only [List.filterMap_cons]
    have heq := hp a b hhd
    simp only [heq]
    split
    · exact ih
    · simp only [cons.injEq, true_and]
      exact ih

end List

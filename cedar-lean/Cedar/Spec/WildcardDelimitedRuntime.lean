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

module

import Std.Data.HashMap

/-!
Ghost-counter variant of `Cedar.Spec.WildcardDelimited` used to prove the
`steps ≤ 3 · (text.length + 1) · (pattern.length + 1)` runtime bound.
The DP is identical to the un-instrumented version apart from a step
counter in the state.
-/

namespace Cedar.Spec.Runtime

open Std (HashMap)

public inductive DelimPatElem where
  | multiStar
  | star
  | justChar (c : Char)
deriving Repr, DecidableEq, Inhabited

public abbrev DelimPattern := List DelimPatElem

public def matchesDelimited (text : List Char) (pattern : DelimPattern) (delim : Char) : Bool :=
  match text, pattern with
  | [],      []              => true
  | [],      (.multiStar :: ps) => matchesDelimited [] ps delim
  | [],      (.star      :: ps) => matchesDelimited [] ps delim
  | [],      (.justChar _ :: _) => false
  | _ :: _,  []              => false
  | c :: cs, (.multiStar :: ps) =>
      matchesDelimited (c :: cs) ps delim ||
      matchesDelimited cs (.multiStar :: ps) delim
  | c :: cs, (.star :: ps) =>
      matchesDelimited (c :: cs) ps delim ||
      (c != delim && matchesDelimited cs (.star :: ps) delim)
  | c :: cs, (.justChar k :: ps) =>
      c == k && matchesDelimited cs ps delim
termination_by text.length + pattern.length
decreasing_by
  all_goals (simp_wf ; try omega)

abbrev DelimCache := HashMap (Nat × Nat) Bool

abbrev DelimState := DelimCache × Nat

abbrev DelimStateM (α) := StateM DelimState α

def bumpSteps : DelimStateM Unit :=
  modifyGet fun s => ((), (s.1, s.2 + 1))

def wildcardMatchDelimitedIdx
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length)
    (delim : Char) : DelimStateM Bool := do
  bumpSteps
  if let .some b := (← get).1.get? (i, j) then
    return b
  let mut r := false
  if h₃ : j = pattern.length then
    r := i = text.length
  else if h₄ : i = text.length then
    match hd : pattern.get ⟨j, by omega⟩ with
    | .multiStar | .star =>
        r ← wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
    | .justChar _ => r := false
  else
    match hd : pattern.get ⟨j, by omega⟩ with
    | .multiStar =>
        r := (← wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim) ||
             (← wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim)
    | .star =>
        let c := text.get ⟨i, by omega⟩
        r := (← wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim) ||
             (c != delim &&
              (← wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim))
    | .justChar k =>
        let c := text.get ⟨i, by omega⟩
        r := c == k &&
             (← wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim)
  modifyGet λ s => (r, (s.1.insert (i, j) r, s.2))
termination_by
  (text.length - i) + (pattern.length - j)
decreasing_by
  all_goals { simp_wf ; omega }

public def wildcardMatchDelimited (text : String) (pattern : DelimPattern) (delim : Char) : Bool :=
  (wildcardMatchDelimitedIdx text.toList pattern 0 0 (by simp) (by simp) delim ({}, 0)).1

public def wildcardMatchDelimitedSteps (text : String) (pattern : DelimPattern)
    (delim : Char) : Nat :=
  (wildcardMatchDelimitedIdx text.toList pattern 0 0 (by simp) (by simp) delim ({}, 0)).2.2

set_option linter.unusedSimpArgs false in
theorem steps_monotone
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (delim : Char)
    (state : DelimState) :
    state.2 ≤
      (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim state).2.2 := by
  induction i, j, h₁, h₂ using wildcardMatchDelimitedIdx.induct text pattern
      generalizing state with
  | _ i j h₁ h₂ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    rw [wildcardMatchDelimitedIdx.eq_def]
    simp only [bumpSteps, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
               modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
    rcases hget : state.1.get? (i, j) with _ | b
    ·
      simp only [hget]
      by_cases hj : j = pattern.length
      · subst hj
        simp only [↓reduceDIte]
        show state.snd ≤ state.snd + 1
        omega
      · rw [dif_neg hj]
        have hjlt : j < pattern.length := Nat.lt_of_le_of_ne h₂ hj
        by_cases hi : i = text.length
        · subst hi
          simp only [↓reduceDIte]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih := ih1 hj (state.1, state.2 + 1)
            show state.snd ≤
              (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd.snd
            omega
          | .star =>
            have ih := ih2 hj (state.1, state.2 + 1)
            show state.snd ≤
              (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd.snd
            omega
          | .justChar _ =>
            show state.snd ≤ state.snd + 1
            omega
        · rw [dif_neg hi]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih_j := ih3 hj hi (state.1, state.2 + 1)
            have ih_i := ih4 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            show state.snd ≤
              (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).snd.snd
            omega
          | .star =>
            have ih_j := ih5 hj hi (state.1, state.2 + 1)
            have ih_i := ih6 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            show state.snd ≤
              (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).snd.snd
            omega
          | .justChar k =>
            have ih := ih7 hj hi (state.1, state.2 + 1)
            show state.snd ≤
              (wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim
                (state.1, state.2 + 1)).snd.snd
            omega
    ·
      show state.snd ≤ state.snd + 1
      omega

set_option linter.unusedSimpArgs false in
theorem cache_size_monotone
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (delim : Char)
    (state : DelimState) :
    state.1.size ≤
      (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim state).2.1.size := by
  induction i, j, h₁, h₂ using wildcardMatchDelimitedIdx.induct text pattern
      generalizing state with
  | _ i j h₁ h₂ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    rw [wildcardMatchDelimitedIdx.eq_def]
    simp only [bumpSteps, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
               modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
    rcases hget : state.1.get? (i, j) with _ | b
    ·
      simp only [hget]
      by_cases hj : j = pattern.length
      · subst hj
        simp only [↓reduceDIte]
        show state.1.size ≤ (state.1.insert (i, pattern.length) (decide (i = text.length))).size
        exact Std.HashMap.size_le_size_insert
      · rw [dif_neg hj]
        have hjlt : j < pattern.length := Nat.lt_of_le_of_ne h₂ hj
        by_cases hi : i = text.length
        · subst hi
          simp only [↓reduceDIte]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih := ih1 hj (state.1, state.2 + 1)
            show state.1.size ≤
              ((wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd.1.insert (text.length, j) _).size
            exact Nat.le_trans ih Std.HashMap.size_le_size_insert
          | .star =>
            have ih := ih2 hj (state.1, state.2 + 1)
            show state.1.size ≤
              ((wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd.1.insert (text.length, j) _).size
            exact Nat.le_trans ih Std.HashMap.size_le_size_insert
          | .justChar _ =>
            show state.1.size ≤ (state.1.insert (text.length, j) false).size
            exact Std.HashMap.size_le_size_insert
        · rw [dif_neg hi]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih_j := ih3 hj hi (state.1, state.2 + 1)
            have ih_i := ih4 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            show state.1.size ≤
              ((wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).snd.1.insert (i, j) _).size
            exact Nat.le_trans (Nat.le_trans ih_j ih_i) Std.HashMap.size_le_size_insert
          | .star =>
            have ih_j := ih5 hj hi (state.1, state.2 + 1)
            have ih_i := ih6 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            show state.1.size ≤
              ((wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).snd.1.insert (i, j) _).size
            exact Nat.le_trans (Nat.le_trans ih_j ih_i) Std.HashMap.size_le_size_insert
          | .justChar k =>
            have ih := ih7 hj hi (state.1, state.2 + 1)
            show state.1.size ≤
              ((wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim
                (state.1, state.2 + 1)).snd.1.insert (i, j) _).size
            exact Nat.le_trans ih Std.HashMap.size_le_size_insert
    ·
      show state.1.size ≤ state.1.size
      exact Nat.le_refl _

private def CacheKeysBounded
    (text : List Char) (pattern : DelimPattern) (cache : DelimCache) : Prop :=
  ∀ k l, cache.contains (k, l) → k ≤ text.length ∧ l ≤ pattern.length

private theorem CacheKeysBounded.insert
    {text : List Char} {pattern : DelimPattern} {cache : DelimCache}
    (h : CacheKeysBounded text pattern cache)
    {k l : Nat} {v : Bool}
    (hkl : k ≤ text.length ∧ l ≤ pattern.length) :
    CacheKeysBounded text pattern (cache.insert (k, l) v) := by
  intro k' l' hc
  rw [Std.HashMap.contains_insert] at hc
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.or_eq_true] at hc
  rcases hc with ⟨hk, hl⟩ | hc'
  · subst hk; subst hl; exact hkl
  · exact h k' l' hc'

private theorem flatMap_range_length (n m : Nat) :
    ((List.range (n + 1)).flatMap
        (fun i => (List.range (m + 1)).map (fun j => (i, j)))).length
      = (n + 1) * (m + 1) := by
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append]
    simp [ih, Nat.succ_mul]

private theorem CacheKeysBounded.size_le
    {text : List Char} {pattern : DelimPattern} {cache : DelimCache}
    (h : CacheKeysBounded text pattern cache) :
    cache.size ≤ (text.length + 1) * (pattern.length + 1) := by
  rw [← Std.HashMap.length_keys]
  have hnodup : cache.keys.Nodup := by
    have hd := Std.HashMap.distinct_keys (m := cache)
    exact List.Pairwise.imp (by intro a b hab; simp at hab; simpa using hab) hd
  have hsub : cache.keys ⊆
      (List.range (text.length + 1)).flatMap
        (fun i => (List.range (pattern.length + 1)).map (fun j => (i, j))) := by
    intro ⟨k, l⟩ hmem
    simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    rw [Std.HashMap.mem_keys] at hmem
    have hc : cache.contains (k, l) := hmem
    obtain ⟨hk, hl⟩ := h k l hc
    exact ⟨k, Nat.lt_add_one_iff.mpr hk, l, Nat.lt_add_one_iff.mpr hl, rfl, rfl⟩
  calc cache.keys.length
      ≤ _ := hnodup.length_le_of_subset hsub
    _ = (text.length + 1) * (pattern.length + 1) :=
        flatMap_range_length text.length pattern.length

private theorem wildcardMatchDelimitedIdx_preserves_bounded
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (delim : Char) :
    ∀ (state : DelimState), CacheKeysBounded text pattern state.1 →
      CacheKeysBounded text pattern
        (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim state).2.1 := by
  induction i, j, h₁, h₂ using wildcardMatchDelimitedIdx.induct text pattern with
  | _ i j h₁ h₂ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    intro state hcache
    rw [wildcardMatchDelimitedIdx.eq_def]
    simp only [bumpSteps, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
               modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
    have hcache' : CacheKeysBounded text pattern (state.1, state.2 + 1).1 := hcache
    rcases hget : state.1.get? (i, j) with _ | b
    · simp only [hget]
      by_cases hj : j = pattern.length
      · subst hj
        simp only [↓reduceDIte]
        show CacheKeysBounded text pattern
          (state.1.insert (i, pattern.length) (decide (i = text.length)))
        exact hcache.insert ⟨h₁, Nat.le_refl _⟩
      · rw [dif_neg hj]
        have hjlt : j < pattern.length := Nat.lt_of_le_of_ne h₂ hj
        by_cases hi : i = text.length
        · subst hi
          simp only [↓reduceDIte]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih := ih1 hj (state.1, state.2 + 1) hcache'
            show CacheKeysBounded text pattern
              ((wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd.1.insert (text.length, j) _)
            exact ih.insert ⟨Nat.le_refl _, Nat.le_of_lt hjlt⟩
          | .star =>
            have ih := ih2 hj (state.1, state.2 + 1) hcache'
            show CacheKeysBounded text pattern
              ((wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd.1.insert (text.length, j) _)
            exact ih.insert ⟨Nat.le_refl _, Nat.le_of_lt hjlt⟩
          | .justChar _ =>
            show CacheKeysBounded text pattern
              (state.1.insert (text.length, j) false)
            exact hcache.insert ⟨Nat.le_refl _, Nat.le_of_lt hjlt⟩
        · rw [dif_neg hi]
          have hilt : i < text.length := Nat.lt_of_le_of_ne h₁ hi
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih_j := ih3 hj hi (state.1, state.2 + 1) hcache'
            have ih_i := ih4 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2 ih_j
            show CacheKeysBounded text pattern
              ((wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).snd.1.insert (i, j) _)
            exact ih_i.insert ⟨Nat.le_of_lt hilt, Nat.le_of_lt hjlt⟩
          | .star =>
            have ih_j := ih5 hj hi (state.1, state.2 + 1) hcache'
            have ih_i := ih6 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2 ih_j
            show CacheKeysBounded text pattern
              ((wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).snd.1.insert (i, j) _)
            exact ih_i.insert ⟨Nat.le_of_lt hilt, Nat.le_of_lt hjlt⟩
          | .justChar k =>
            have ih := ih7 hj hi (state.1, state.2 + 1) hcache'
            show CacheKeysBounded text pattern
              ((wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim
                (state.1, state.2 + 1)).snd.1.insert (i, j) _)
            exact ih.insert ⟨Nat.le_of_lt hilt, Nat.le_of_lt hjlt⟩
    · simp only [StateT.pure, pure]
      exact hcache

theorem cache_size_le
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (delim : Char)
    (state : DelimState)
    (hcache_bound : ∀ k l, state.1.contains (k, l) →
      k ≤ text.length ∧ l ≤ pattern.length) :
    (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim state).2.1.size ≤
      (text.length + 1) * (pattern.length + 1) :=
  (wildcardMatchDelimitedIdx_preserves_bounded text pattern i j h₁ h₂ delim state
    hcache_bound).size_le

set_option linter.unusedSimpArgs false in
private theorem wildcardMatchDelimitedIdx_preserves_absent
    (text : List Char) (pattern : DelimPattern) (i' j' : Nat)
    (h₁' : i' ≤ text.length) (h₂' : j' ≤ pattern.length) (delim : Char) :
    ∀ (state : DelimState) (i j : Nat),
      ¬ state.1.contains (i, j) →
      (i < i' ∨ j < j') →
      ¬ (wildcardMatchDelimitedIdx text pattern i' j' h₁' h₂' delim state).2.1.contains (i, j) := by
  induction i', j', h₁', h₂' using wildcardMatchDelimitedIdx.induct text pattern with
  | _ i' j' h₁' h₂' ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    intros state i j habsent hbound
    rw [wildcardMatchDelimitedIdx.eq_def]
    simp only [bumpSteps, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
               modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
    have habsent' : ¬ (state.1, state.2 + 1).1.contains (i, j) := habsent
    have hne : (i', j') ≠ (i, j) := by
      intro heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      omega
    rcases hget : state.1.get? (i', j') with _ | b
    · simp only [hget]
      by_cases hj : j' = pattern.length
      · subst hj
        simp only [↓reduceDIte]
        show ¬ (state.1.insert (i', pattern.length) _).contains (i, j)
        rw [Std.HashMap.contains_insert]
        simp only [beq_iff_eq, Bool.or_eq_true, not_or]
        exact ⟨fun heq => hne heq, habsent⟩
      · rw [dif_neg hj]
        have hjlt : j' < pattern.length := Nat.lt_of_le_of_ne h₂' hj
        by_cases hi : i' = text.length
        · subst hi
          simp only [↓reduceDIte]
          match hd : pattern.get ⟨j', hjlt⟩ with
          | .multiStar =>
            have hbound' : i < text.length ∨ j < j' + 1 := by
              rcases hbound with h | h
              · exact Or.inl h
              · exact Or.inr (Nat.lt_succ_of_lt h)
            have ih := ih1 hj (state.1, state.2 + 1) i j habsent' hbound'
            show ¬ ((wildcardMatchDelimitedIdx text pattern text.length (j' + 1) h₁' (by omega) delim
              (state.1, state.2 + 1)).snd.1.insert (text.length, j') _).contains (i, j)
            rw [Std.HashMap.contains_insert]
            simp only [beq_iff_eq, Bool.or_eq_true, not_or]
            exact ⟨fun heq => hne heq, ih⟩
          | .star =>
            have hbound' : i < text.length ∨ j < j' + 1 := by
              rcases hbound with h | h
              · exact Or.inl h
              · exact Or.inr (Nat.lt_succ_of_lt h)
            have ih := ih2 hj (state.1, state.2 + 1) i j habsent' hbound'
            show ¬ ((wildcardMatchDelimitedIdx text pattern text.length (j' + 1) h₁' (by omega) delim
              (state.1, state.2 + 1)).snd.1.insert (text.length, j') _).contains (i, j)
            rw [Std.HashMap.contains_insert]
            simp only [beq_iff_eq, Bool.or_eq_true, not_or]
            exact ⟨fun heq => hne heq, ih⟩
          | .justChar _ =>
            show ¬ (state.1.insert (text.length, j') false).contains (i, j)
            rw [Std.HashMap.contains_insert]
            simp only [beq_iff_eq, Bool.or_eq_true, not_or]
            exact ⟨fun heq => hne heq, habsent⟩
        · rw [dif_neg hi]
          match hd : pattern.get ⟨j', hjlt⟩ with
          | .multiStar =>
            have hbound_j : i < i' ∨ j < j' + 1 := by
              rcases hbound with h | h
              · exact Or.inl h
              · exact Or.inr (Nat.lt_succ_of_lt h)
            have hbound_i : i < i' + 1 ∨ j < j' := by
              rcases hbound with h | h
              · exact Or.inl (Nat.lt_succ_of_lt h)
              · exact Or.inr h
            have ih_j := ih3 hj hi (state.1, state.2 + 1) i j habsent' hbound_j
            have ih_i := ih4 hi
              (wildcardMatchDelimitedIdx text pattern i' (j'+1) h₁' (by omega) delim
                (state.1, state.2 + 1)).2 i j ih_j hbound_i
            show ¬ ((wildcardMatchDelimitedIdx text pattern (i' + 1) j' (by omega) h₂' delim
              (wildcardMatchDelimitedIdx text pattern i' (j' + 1) h₁' (by omega) delim
                (state.1, state.2 + 1)).snd).snd.1.insert (i', j') _).contains (i, j)
            rw [Std.HashMap.contains_insert]
            simp only [beq_iff_eq, Bool.or_eq_true, not_or]
            exact ⟨fun heq => hne heq, ih_i⟩
          | .star =>
            have hbound_j : i < i' ∨ j < j' + 1 := by
              rcases hbound with h | h
              · exact Or.inl h
              · exact Or.inr (Nat.lt_succ_of_lt h)
            have hbound_i : i < i' + 1 ∨ j < j' := by
              rcases hbound with h | h
              · exact Or.inl (Nat.lt_succ_of_lt h)
              · exact Or.inr h
            have ih_j := ih5 hj hi (state.1, state.2 + 1) i j habsent' hbound_j
            have ih_i := ih6 hi
              (wildcardMatchDelimitedIdx text pattern i' (j'+1) h₁' (by omega) delim
                (state.1, state.2 + 1)).2 i j ih_j hbound_i
            show ¬ ((wildcardMatchDelimitedIdx text pattern (i' + 1) j' (by omega) h₂' delim
              (wildcardMatchDelimitedIdx text pattern i' (j' + 1) h₁' (by omega) delim
                (state.1, state.2 + 1)).snd).snd.1.insert (i', j') _).contains (i, j)
            rw [Std.HashMap.contains_insert]
            simp only [beq_iff_eq, Bool.or_eq_true, not_or]
            exact ⟨fun heq => hne heq, ih_i⟩
          | .justChar k =>
            have hbound' : i < i' + 1 ∨ j < j' + 1 := by
              rcases hbound with h | h
              · exact Or.inl (Nat.lt_succ_of_lt h)
              · exact Or.inr (Nat.lt_succ_of_lt h)
            have ih := ih7 hj hi (state.1, state.2 + 1) i j habsent' hbound'
            show ¬ ((wildcardMatchDelimitedIdx text pattern (i' + 1) (j' + 1) (by omega) (by omega) delim
              (state.1, state.2 + 1)).snd.1.insert (i', j') _).contains (i, j)
            rw [Std.HashMap.contains_insert]
            simp only [beq_iff_eq, Bool.or_eq_true, not_or]
            exact ⟨fun heq => hne heq, ih⟩
    · simp only [StateT.pure, pure]
      exact habsent

set_option linter.unusedSimpArgs false in
theorem steps_le_growth
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (delim : Char)
    (state : DelimState) :
    (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim state).2.2 ≤
      state.2 + 3 * ((wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim state).2.1.size
                     - state.1.size) + 1 := by
  induction i, j, h₁, h₂ using wildcardMatchDelimitedIdx.induct text pattern
      generalizing state with
  | _ i j h₁ h₂ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    rw [wildcardMatchDelimitedIdx.eq_def]
    simp only [bumpSteps, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
               modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
    rcases hget : state.1.get? (i, j) with _ | b
    ·
      simp only [hget]
      have habsent : ¬ state.1.contains (i, j) := by
        rw [Std.HashMap.contains_eq_isSome_getElem?]
        simp [show state.1[(i, j)]? = none from hget]
      have habsent_mem : (i, j) ∉ state.1 := by
        rw [Std.HashMap.mem_iff_contains]; exact habsent
      by_cases hj : j = pattern.length
      · subst hj
        simp only [↓reduceDIte]
        show state.snd + 1 ≤ state.snd + 3 * ((state.1.insert (i, pattern.length)
          (decide (i = text.length))).size - state.1.size) + 1
        rw [Std.HashMap.size_insert]
        have hnin : ¬ (i, pattern.length) ∈ state.1 := habsent
        simp only [hnin, if_false]
        omega
      · rw [dif_neg hj]
        have hjlt : j < pattern.length := Nat.lt_of_le_of_ne h₂ hj
        by_cases hi : i = text.length
        · subst hi
          simp only [↓reduceDIte]
          have habsent_intermediate_multiStar :
              ¬ (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2.1.contains (text.length, j) := by
            apply wildcardMatchDelimitedIdx_preserves_absent
            · exact habsent
            · exact Or.inr (Nat.lt_succ_self _)
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih := ih1 hj (state.1, state.2 + 1)
            have hmono_c := cache_size_monotone text pattern text.length (j + 1) h₁ (by omega) delim
              (state.1, state.2 + 1)
            show (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2.2 ≤
              state.2 + 3 * (((wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2.1.insert (text.length, j) _).size - state.1.size) + 1
            rw [Std.HashMap.size_insert]
            have hnin : ¬ (text.length, j) ∈ (wildcardMatchDelimitedIdx text pattern text.length
              (j + 1) h₁ (by omega) delim (state.1, state.2 + 1)).2.1 :=
                habsent_intermediate_multiStar
            simp only [hnin, if_false]
            simp only at ih hmono_c
            omega
          | .star =>
            have habsent_intermediate :
                ¬ (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).2.1.contains (text.length, j) := by
              apply wildcardMatchDelimitedIdx_preserves_absent
              · exact habsent
              · exact Or.inr (Nat.lt_succ_self _)
            have hnin : ¬ (text.length, j) ∈ (wildcardMatchDelimitedIdx text pattern text.length
              (j + 1) h₁ (by omega) delim (state.1, state.2 + 1)).2.1 := by
              rw [Std.HashMap.mem_iff_contains]; exact habsent_intermediate
            have ih := ih2 hj (state.1, state.2 + 1)
            have hmono_c := cache_size_monotone text pattern text.length (j + 1) h₁ (by omega) delim
              (state.1, state.2 + 1)
            show (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2.2 ≤
              state.2 + 3 * (((wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2.1.insert (text.length, j) _).size - state.1.size) + 1
            rw [Std.HashMap.size_insert, if_neg hnin]
            simp only at ih hmono_c
            omega
          | .justChar _ =>
            show state.snd + 1 ≤ state.snd + 3 * ((state.1.insert (text.length, j) false).size
              - state.1.size) + 1
            rw [Std.HashMap.size_insert]
            have hnin : ¬ (text.length, j) ∈ state.1 := habsent
            simp only [hnin, if_false]
            omega
        · rw [dif_neg hi]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have habsent_after_j :
                ¬ (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).2.1.contains (i, j) := by
              apply wildcardMatchDelimitedIdx_preserves_absent
              · exact habsent
              · exact Or.inr (Nat.lt_succ_self _)
            have habsent_after_ji :
                ¬ (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                  (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                    (state.1, state.2 + 1)).2).2.1.contains (i, j) := by
              apply wildcardMatchDelimitedIdx_preserves_absent
              · exact habsent_after_j
              · exact Or.inl (Nat.lt_succ_self _)
            have ih_j := ih3 hj hi (state.1, state.2 + 1)
            have ih_i := ih4 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            have hmono_c_j := cache_size_monotone text pattern i (j + 1) h₁ (by omega) delim
              (state.1, state.2 + 1)
            have hmono_c_i := cache_size_monotone text pattern (i + 1) j (by omega) h₂ delim
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            have hnin : ¬ (i, j) ∈ (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
              (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd).2.1 := by
              rw [Std.HashMap.mem_iff_contains]; exact habsent_after_ji
            show (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).2.2 ≤
              state.2 + 3 * (((wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).2.1.insert (i, j) _).size - state.1.size) + 1
            rw [Std.HashMap.size_insert, if_neg hnin]
            simp only at ih_j ih_i hmono_c_j hmono_c_i
            omega
          | .star =>
            have habsent_after_j :
                ¬ (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).2.1.contains (i, j) := by
              apply wildcardMatchDelimitedIdx_preserves_absent
              · exact habsent
              · exact Or.inr (Nat.lt_succ_self _)
            have habsent_after_ji :
                ¬ (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                  (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                    (state.1, state.2 + 1)).2).2.1.contains (i, j) := by
              apply wildcardMatchDelimitedIdx_preserves_absent
              · exact habsent_after_j
              · exact Or.inl (Nat.lt_succ_self _)
            have ih_j := ih5 hj hi (state.1, state.2 + 1)
            have ih_i := ih6 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            have hmono_c_j := cache_size_monotone text pattern i (j + 1) h₁ (by omega) delim
              (state.1, state.2 + 1)
            have hmono_c_i := cache_size_monotone text pattern (i + 1) j (by omega) h₂ delim
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim
                (state.1, state.2 + 1)).2
            have hnin : ¬ (i, j) ∈ (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
              (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                (state.1, state.2 + 1)).snd).2.1 := by
              rw [Std.HashMap.mem_iff_contains]; exact habsent_after_ji
            show (wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).2.2 ≤
              state.2 + 3 * (((wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim
                (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
                  (state.1, state.2 + 1)).snd).2.1.insert (i, j) _).size - state.1.size) + 1
            rw [Std.HashMap.size_insert, if_neg hnin]
            simp only at ih_j ih_i hmono_c_j hmono_c_i
            omega
          | .justChar k =>
            have habsent_after :
                ¬ (wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim
                  (state.1, state.2 + 1)).2.1.contains (i, j) := by
              apply wildcardMatchDelimitedIdx_preserves_absent
              · exact habsent
              · exact Or.inl (Nat.lt_succ_self _)
            have hnin : ¬ (i, j) ∈ (wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega)
              (by omega) delim (state.1, state.2 + 1)).2.1 := by
              rw [Std.HashMap.mem_iff_contains]; exact habsent_after
            have ih := ih7 hj hi (state.1, state.2 + 1)
            have hmono_c := cache_size_monotone text pattern (i + 1) (j + 1) (by omega) (by omega) delim
              (state.1, state.2 + 1)
            show (wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim
                (state.1, state.2 + 1)).2.2 ≤
              state.2 + 3 * (((wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim
                (state.1, state.2 + 1)).2.1.insert (i, j) _).size - state.1.size) + 1
            rw [Std.HashMap.size_insert, if_neg hnin]
            simp only at ih hmono_c
            omega
    ·
      simp only [StateT.pure, pure]
      show state.snd + 1 ≤ state.snd + 3 * (state.1.size - state.1.size) + 1
      omega

public theorem wildcardMatchDelimited_steps_le
    (text : String) (pattern : DelimPattern) (delim : Char) :
    wildcardMatchDelimitedSteps text pattern delim ≤
      3 * (text.toList.length + 1) * (pattern.length + 1) + 1 := by
  unfold wildcardMatchDelimitedSteps
  have hgrowth := steps_le_growth text.toList pattern 0 0 (by simp) (by simp) delim ({}, 0)
  have hcache := cache_size_le text.toList pattern 0 0 (by simp) (by simp) delim ({}, 0) (by simp)
  simp at hgrowth
  have hcombine : (wildcardMatchDelimitedIdx text.toList pattern 0 0 (by simp) (by simp) delim (∅, 0)).2.2 ≤
      3 * ((text.toList.length + 1) * (pattern.length + 1)) + 1 :=
    Nat.le_trans hgrowth (Nat.add_le_add_right (Nat.mul_le_mul_left _ hcache) _)
  calc (wildcardMatchDelimitedIdx text.toList pattern 0 0 (by simp) (by simp) delim ({}, 0)).2.2
      ≤ 3 * ((text.toList.length + 1) * (pattern.length + 1)) + 1 := hcombine
    _ = 3 * (text.toList.length + 1) * (pattern.length + 1) + 1 := by
        rw [Nat.mul_assoc]

end Cedar.Spec.Runtime

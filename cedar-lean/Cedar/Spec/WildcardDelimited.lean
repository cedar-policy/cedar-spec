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
# Delimiter-aware wildcard matching

This file specifies and implements `wildcardMatchDelimited`, the matching
function for `like(pattern, delimiter)`.  Pattern elements are:

- `DelimPatElem.multiStar` (`**`)  — matches any sequence of characters,
  including the delimiter.  Equivalent to `.*` in a regular expression.
- `DelimPatElem.star`      (`*`)   — matches any sequence of characters that
  does **not** include the delimiter.  Equivalent to `[^d]*`.
- `DelimPatElem.justChar c`        — matches the single character `c`
  (including the delimiter itself when it appears as a literal in the pattern).

The file contains:
1. The type `DelimPatElem` and `DelimPattern`.
2. `matchesDelimited` — a clean recursive specification (no memoization).
3. `wildcardMatchDelimitedIdx` — a memoized DP implementation.
4. `wildcardMatchDelimited` — the public entry point.
5. A correctness statement `wildcardMatchDelimited_correct` establishing that
   the memoized DP agrees with `matchesDelimited` on every input.
-/

namespace Cedar.Spec

open Std (HashMap)

-- ---------------------------------------------------------------------------
-- 1.  Types
-- ---------------------------------------------------------------------------

/-- A pattern element for delimiter-aware `like`. -/
public inductive DelimPatElem where
  | multiStar              -- `**` : matches any chars, including the delimiter
  | star                   -- `*`  : matches any chars except the delimiter
  | justChar (c : Char)    -- literal character
deriving Repr, DecidableEq, Inhabited

public abbrev DelimPattern := List DelimPatElem

/-- Ordering on `DelimPatElem`, mirroring the pattern used by `PatElem.lt`
    in `Cedar.Spec.Wildcard`.  Order: `multiStar` < `star` < `justChar c` for
    every `c`, then by `c` within `justChar`. -/
public def DelimPatElem.lt : DelimPatElem → DelimPatElem → Bool
  | .justChar c₁, .justChar c₂ => c₁ < c₂
  | .multiStar, .star           => true
  | .multiStar, .justChar _     => true
  | .star, .justChar _          => true
  | _, _                        => false

public instance : LT DelimPatElem where
  lt := fun x y => DelimPatElem.lt x y

public instance DelimPatElem.decLt (x y : DelimPatElem) : Decidable (x < y) :=
  if h : DelimPatElem.lt x y then isTrue h else isFalse h

-- ---------------------------------------------------------------------------
-- 2.  Recursive specification (no memoisation)
-- ---------------------------------------------------------------------------

/--
`matchesDelimited text pattern delim` is `true` iff `text` is a member of the
language described by `pattern` when `delim` is the separator character.

This function is the **specification**; it is not efficient.  The DP
`wildcardMatchDelimitedIdx` below implements the same relation.

Termination: on every recursive call, either the text shrinks by one or the
pattern shrinks by one; the sum decreases.
-/
public def matchesDelimited (text : List Char) (pattern : DelimPattern) (delim : Char) : Bool :=
  match text, pattern with
  -- Both exhausted: match.
  | [],      []              => true
  -- Text exhausted, pattern non-empty: only wildcards (of either kind) can
  -- still match the empty remainder.
  | [],      (.multiStar :: ps) => matchesDelimited [] ps delim
  | [],      (.star      :: ps) => matchesDelimited [] ps delim
  | [],      (.justChar _ :: _) => false
  -- Pattern exhausted but text non-empty: no match.
  | _ :: _,  []              => false
  -- `**`: matches zero more chars (advance pattern) or one more char of any
  -- kind (advance text, keep `**`).
  | c :: cs, (.multiStar :: ps) =>
      matchesDelimited (c :: cs) ps delim ||
      matchesDelimited cs (.multiStar :: ps) delim
  -- `*`: matches zero more chars (advance pattern) or one non-delimiter char
  -- (advance text, keep `*`).
  | c :: cs, (.star :: ps) =>
      matchesDelimited (c :: cs) ps delim ||
      (c != delim && matchesDelimited cs (.star :: ps) delim)
  -- Literal: must match exactly.
  | c :: cs, (.justChar k :: ps) =>
      c == k && matchesDelimited cs ps delim
termination_by text.length + pattern.length
decreasing_by
  all_goals (simp_wf ; try omega)

-- ---------------------------------------------------------------------------
-- 3.  Memoized DP implementation
-- ---------------------------------------------------------------------------

abbrev DelimCache := HashMap (Nat × Nat) Bool

abbrev DelimCacheM (α) := StateM DelimCache α

/--
`wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim` returns `true` iff
`text[i:]` matches `pattern[j:]` with delimiter `delim`.

The implementation uses the same memoised DP structure as `wildcardMatchIdx`
in `Cedar.Spec.Wildcard`, extended with `multiStar` and delimiter-aware `star`.

**Complexity.** Each `(i, j)` cell of the memo table is computed at most
once (subsequent visits hit the cache).  Each computation does O(1) work
plus a constant number of recursive calls to strictly-smaller cells.
Therefore the total work is O(|text| × |pattern|), matching the current
undelimited implementation.
-/
def wildcardMatchDelimitedIdx
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length)
    (delim : Char) : DelimCacheM Bool := do
  -- Cache lookup
  if let .some b := (← get).get? (i, j) then
    return b
  let mut r := false
  if h₃ : j = pattern.length then
    -- Pattern exhausted: match iff text exhausted too.
    r := i = text.length
  else if h₄ : i = text.length then
    -- Text exhausted: only wildcards can still succeed.
    match hd : pattern.get ⟨j, by omega⟩ with
    | .multiStar | .star =>
        r ← wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim
    | .justChar _ => r := false
  else
    -- Both non-exhausted.
    match hd : pattern.get ⟨j, by omega⟩ with
    | .multiStar =>
        -- `**`: advance pattern (consume nothing) OR advance text (consume any char).
        r := (← wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim) ||
             (← wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim)
    | .star =>
        -- `*`: advance pattern (consume nothing) OR advance text only if not delimiter.
        let c := text.get ⟨i, by omega⟩
        r := (← wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ (by omega) delim) ||
             (c != delim &&
              (← wildcardMatchDelimitedIdx text pattern (i + 1) j (by omega) h₂ delim))
    | .justChar k =>
        -- Literal: must match exactly.
        let c := text.get ⟨i, by omega⟩
        r := c == k &&
             (← wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) (by omega) (by omega) delim)
  modifyGet λ cache => (r, cache.insert (i, j) r)
termination_by
  (text.length - i) + (pattern.length - j)
decreasing_by
  all_goals { simp_wf ; omega }

/-- Public entry point. -/
public def wildcardMatchDelimited (text : String) (pattern : DelimPattern) (delim : Char) : Bool :=
  wildcardMatchDelimitedIdx text.toList pattern 0 0 (by simp) (by simp) delim |>.run' {}

-- ---------------------------------------------------------------------------
-- 4.  Correctness proof
-- ---------------------------------------------------------------------------

/-- Invariant on the memo cache: every entry in `cache` records the correct
    value of `matchesDelimited` for the corresponding suffix pair. -/
private def CacheCorrect
    (text : List Char) (pattern : DelimPattern) (delim : Char)
    (cache : DelimCache) : Prop :=
  ∀ k l b, cache.get? (k, l) = some b →
    b = matchesDelimited (text.drop k) (pattern.drop l) delim

private theorem cacheCorrect_empty
    (text : List Char) (pattern : DelimPattern) (delim : Char) :
    CacheCorrect text pattern delim ∅ := by
  intro k l b hget
  simp at hget

private theorem cacheCorrect_insert
    {text : List Char} {pattern : DelimPattern} {delim : Char}
    {cache : DelimCache} (h : CacheCorrect text pattern delim cache)
    {i j : Nat} {b : Bool}
    (hb : b = matchesDelimited (text.drop i) (pattern.drop j) delim) :
    CacheCorrect text pattern delim (cache.insert (i, j) b) := by
  intro k l b' hget
  rw [Std.HashMap.get?_insert] at hget
  by_cases hk : ((i, j) == (k, l)) = true
  · simp [hk] at hget
    have hkl : (i, j) = (k, l) := by
      simpa [beq_iff_eq] using hk
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkl
    rw [← hget]; exact hb
  · simp [hk] at hget
    exact h k l b' hget

-- Helper simp lemmas for reducing `StateM` computations on `Id`.
private theorem StateT_pure_apply_bool {σ : Type} (a : Bool) (s : σ) :
    (StateT.pure a : StateM σ Bool) s = (a, s) := rfl

private theorem StateT_bind_apply_bool {σ : Type} (m : StateM σ Bool) (f : Bool → StateM σ Bool)
    (s : σ) :
    (StateT.bind m f : StateM σ Bool) s = f (m s).1 (m s).2 := rfl

private theorem StateT_modifyGet_apply_bool {σ : Type} (f : σ → Bool × σ) (s : σ) :
    (StateT.modifyGet f : StateM σ Bool) s = f s := rfl

private theorem run'_eq_fst {σ α : Type} (m : StateM σ α) (s : σ) :
    m.run' s = (m s).1 := rfl

-- Unfolding `matchesDelimited` on drop-suffixes.
private theorem matchesDelimited_drop_empty_pattern
    (text : List Char) (i : Nat) (h₁ : i ≤ text.length) (delim : Char) :
    matchesDelimited (text.drop i) [] delim = decide (i = text.length) := by
  by_cases hi : i = text.length
  · rw [hi, List.drop_length]
    simp [matchesDelimited]
  · have hlt : i < text.length := Nat.lt_of_le_of_ne h₁ hi
    rw [List.drop_eq_getElem_cons hlt]
    unfold matchesDelimited
    simp [hi]

-- Drop cons form for pattern.
private theorem pattern_drop_cons (pattern : DelimPattern) (j : Nat)
    (hj : j < pattern.length) :
    pattern.drop j = pattern.get ⟨j, hj⟩ :: pattern.drop (j+1) := by
  have := List.drop_eq_getElem_cons hj
  simpa using this

-- Drop cons form for text.
private theorem text_drop_cons (text : List Char) (i : Nat)
    (hi : i < text.length) :
    text.drop i = text.get ⟨i, hi⟩ :: text.drop (i+1) := by
  have := List.drop_eq_getElem_cons hi
  simpa using this

-- Text-exhausted matchesDelimited on cons pattern with multiStar/star/justChar heads.
private theorem matchesDelimited_empty_multiStar (pattern : DelimPattern) (delim : Char) :
    matchesDelimited [] (DelimPatElem.multiStar :: pattern) delim =
    matchesDelimited [] pattern delim := by
  simp [matchesDelimited]

private theorem matchesDelimited_empty_star (pattern : DelimPattern) (delim : Char) :
    matchesDelimited [] (DelimPatElem.star :: pattern) delim =
    matchesDelimited [] pattern delim := by
  simp [matchesDelimited]

private theorem matchesDelimited_empty_justChar (c : Char) (pattern : DelimPattern) (delim : Char) :
    matchesDelimited [] (DelimPatElem.justChar c :: pattern) delim = false := by
  simp [matchesDelimited]

private theorem matchesDelimited_cons_multiStar
    (c : Char) (cs : List Char) (pattern : DelimPattern) (delim : Char) :
    matchesDelimited (c :: cs) (DelimPatElem.multiStar :: pattern) delim =
    (matchesDelimited (c :: cs) pattern delim ||
     matchesDelimited cs (DelimPatElem.multiStar :: pattern) delim) := by
  simp [matchesDelimited]

private theorem matchesDelimited_cons_star
    (c : Char) (cs : List Char) (pattern : DelimPattern) (delim : Char) :
    matchesDelimited (c :: cs) (DelimPatElem.star :: pattern) delim =
    (matchesDelimited (c :: cs) pattern delim ||
     (c != delim && matchesDelimited cs (DelimPatElem.star :: pattern) delim)) := by
  simp [matchesDelimited]

private theorem matchesDelimited_cons_justChar
    (c : Char) (cs : List Char) (k : Char) (pattern : DelimPattern) (delim : Char) :
    matchesDelimited (c :: cs) (DelimPatElem.justChar k :: pattern) delim =
    (c == k && matchesDelimited cs pattern delim) := by
  simp [matchesDelimited]

/-- Auxiliary correctness lemma with an explicit correct cache. Returns both the
    correctness of the value and the preservation of the cache invariant. -/
private theorem wildcardMatchDelimitedIdx_run_correct
    (text : List Char) (pattern : DelimPattern) (delim : Char)
    (i j : Nat) (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length)
    (cache : DelimCache) (hcache : CacheCorrect text pattern delim cache) :
    (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim cache).1 =
      matchesDelimited (text.drop i) (pattern.drop j) delim ∧
    CacheCorrect text pattern delim
      (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim cache).2 := by
  induction i, j, h₁, h₂ using wildcardMatchDelimitedIdx.induct text pattern
      generalizing cache with
  | _ i j h₁ h₂ ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
    rw [wildcardMatchDelimitedIdx.eq_def]
    -- Reduce the outer state-monad plumbing and case on the cache lookup.
    rcases hget : cache.get? (i, j) with _ | b
    all_goals simp only [bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
                          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind, hget]
    · -- Cache miss branch.
      by_cases hj : j = pattern.length
      · -- Pattern exhausted.
        subst hj
        simp only [↓reduceDIte]
        refine ⟨?_, ?_⟩
        · rw [List.drop_length]
          exact (matchesDelimited_drop_empty_pattern text i h₁ delim).symm
        · apply cacheCorrect_insert hcache
          rw [List.drop_length]
          exact (matchesDelimited_drop_empty_pattern text i h₁ delim).symm
      · rw [dif_neg hj]
        have hjlt : j < pattern.length := Nat.lt_of_le_of_ne h₂ hj
        rw [pattern_drop_cons pattern j hjlt]
        by_cases hi : i = text.length
        · -- Text exhausted.
          subst hi
          rw [List.drop_length]
          simp only [↓reduceDIte]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih := ih1 hj cache hcache
            refine ⟨?_, ?_⟩
            · show (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ _ delim cache).1 = _
              rw [matchesDelimited_empty_multiStar, ih.1, List.drop_length]
            · apply cacheCorrect_insert ih.2
              show (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ _ delim cache).1 = _
              rw [ih.1, List.drop_length, pattern_drop_cons pattern j hjlt, hd,
                  matchesDelimited_empty_multiStar]
          | .star =>
            have ih := ih2 hj cache hcache
            refine ⟨?_, ?_⟩
            · show (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ _ delim cache).1 = _
              rw [matchesDelimited_empty_star, ih.1, List.drop_length]
            · apply cacheCorrect_insert ih.2
              show (wildcardMatchDelimitedIdx text pattern text.length (j + 1) h₁ _ delim cache).1 = _
              rw [ih.1, List.drop_length, pattern_drop_cons pattern j hjlt, hd,
                  matchesDelimited_empty_star]
          | .justChar k =>
            refine ⟨?_, ?_⟩
            · show false = _
              rw [matchesDelimited_empty_justChar]
            · apply cacheCorrect_insert hcache
              rw [List.drop_length, pattern_drop_cons pattern j hjlt, hd,
                  matchesDelimited_empty_justChar]
        · rw [dif_neg hi]
          have hilt : i < text.length := Nat.lt_of_le_of_ne h₁ hi
          rw [text_drop_cons text i hilt]
          match hd : pattern.get ⟨j, hjlt⟩ with
          | .multiStar =>
            have ih_j := ih3 hj hi cache hcache
            have ih_i := ih4 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim cache).2 ih_j.2
            refine ⟨?_, ?_⟩
            · show ((wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).1 ||
                    (wildcardMatchDelimitedIdx text pattern (i + 1) j _ h₂ delim
                      (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).2).1) = _
              rw [matchesDelimited_cons_multiStar, ih_j.1, ih_i.1,
                  ← text_drop_cons text i hilt, pattern_drop_cons pattern j hjlt, hd]
            · apply cacheCorrect_insert ih_i.2
              show ((wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).1 ||
                    (wildcardMatchDelimitedIdx text pattern (i + 1) j _ h₂ delim
                      (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).2).1) = _
              rw [ih_j.1, ih_i.1, pattern_drop_cons pattern j hjlt, hd,
                  text_drop_cons text i hilt, matchesDelimited_cons_multiStar]
          | .star =>
            have ih_j := ih5 hj hi cache hcache
            have ih_i := ih6 hi
              (wildcardMatchDelimitedIdx text pattern i (j+1) h₁ (by omega) delim cache).2 ih_j.2
            refine ⟨?_, ?_⟩
            · show ((wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).1 ||
                    text.get ⟨i, hilt⟩ != delim &&
                    (wildcardMatchDelimitedIdx text pattern (i + 1) j _ h₂ delim
                      (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).2).1) = _
              rw [matchesDelimited_cons_star, ih_j.1, ih_i.1,
                  ← text_drop_cons text i hilt, pattern_drop_cons pattern j hjlt, hd]
            · apply cacheCorrect_insert ih_i.2
              show ((wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).1 ||
                    text.get ⟨i, hilt⟩ != delim &&
                    (wildcardMatchDelimitedIdx text pattern (i + 1) j _ h₂ delim
                      (wildcardMatchDelimitedIdx text pattern i (j + 1) h₁ _ delim cache).2).1) = _
              rw [ih_j.1, ih_i.1, pattern_drop_cons pattern j hjlt, hd,
                  text_drop_cons text i hilt, matchesDelimited_cons_star]
          | .justChar k =>
            have ih := ih7 hj hi cache hcache
            refine ⟨?_, ?_⟩
            · show (text.get ⟨i, hilt⟩ == k &&
                    (wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) _ _ delim cache).1) = _
              rw [matchesDelimited_cons_justChar, ih.1]
            · apply cacheCorrect_insert ih.2
              show (text.get ⟨i, hilt⟩ == k &&
                    (wildcardMatchDelimitedIdx text pattern (i + 1) (j + 1) _ _ delim cache).1) = _
              rw [ih.1, pattern_drop_cons pattern j hjlt, hd,
                  text_drop_cons text i hilt, matchesDelimited_cons_justChar]
    · -- Cache hit.
      exact ⟨hcache i j b hget, hcache⟩

private theorem wildcardMatchDelimitedIdx_correct_aux
    (text : List Char) (pattern : DelimPattern) (i j : Nat)
    (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (delim : Char)
    (cache : DelimCache) (hcache : CacheCorrect text pattern delim cache) :
    (wildcardMatchDelimitedIdx text pattern i j h₁ h₂ delim).run' cache =
    matchesDelimited (text.drop i) (pattern.drop j) delim := by
  have := wildcardMatchDelimitedIdx_run_correct text pattern delim i j h₁ h₂ cache hcache
  exact this.1

theorem wildcardMatchDelimited_correct
    (text : String) (pattern : DelimPattern) (delim : Char) :
    wildcardMatchDelimited text pattern delim =
    matchesDelimited text.toList pattern delim := by
  unfold wildcardMatchDelimited
  have := wildcardMatchDelimitedIdx_correct_aux
    text.toList pattern 0 0 (by simp) (by simp) delim ∅
    (cacheCorrect_empty _ _ _)
  simpa using this

end Cedar.Spec

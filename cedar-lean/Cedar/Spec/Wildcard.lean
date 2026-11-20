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

namespace Cedar.Spec

open Std (HashMap)

public inductive PatElem where
  | star
  | justChar (c : Char)
deriving Repr, DecidableEq, Inhabited

public instance : Coe Char PatElem where
  coe c := .justChar c

public def PatElem.lt : PatElem → PatElem → Bool
  | .justChar c₁, .justChar c₂ => c₁ < c₂
  | .star, .justChar _         => true
  | _, _                       => false

public instance : LT PatElem where
  lt := fun x y => PatElem.lt x y

public instance PatElem.decLt (x y : PatElem) : Decidable (x < y) :=
  if  h : PatElem.lt x y then isTrue h else isFalse h

public abbrev Pattern := List PatElem

/--
Reference semantics of `like`: `*` matches any (possibly empty) sequence of
characters. This takes exponential time and is only used in proofs.
-/
public def wildcardMatchSpec : List Char → Pattern → Bool
  | [],      []                => true
  | [],      .star :: ps       => wildcardMatchSpec [] ps
  | [],      .justChar _ :: _  => false
  | _ :: _,  []                => false
  | c :: cs, .star :: ps       => wildcardMatchSpec (c :: cs) ps || wildcardMatchSpec cs (.star :: ps)
  | c :: cs, .justChar k :: ps => c == k && wildcardMatchSpec cs ps

/-! ## Memoized matcher -/

def charMatch (textChar : Char) : PatElem → Bool
  | .justChar c => textChar == c
  | _           => false

def wildcard : PatElem → Bool
  | .star => true
  | _     => false

abbrev Cache := HashMap (Nat × Nat) Bool

abbrev CacheM (α) := StateM Cache α

def wildcardMatchIdx (text : List Char) (pattern : Pattern) (i j : Nat)
  (h₁ : i ≤ text.length)
  (h₂ : j ≤ pattern.length) : CacheM Bool
:= do
  if let .some b := (← get).get? (i, j) then
    return b
  let mut r := false
  if h₃ : j = pattern.length then
    r := i = text.length
  else if h₄ : i = text.length then
    r := wildcard (pattern.get ⟨j, (by omega)⟩) &&
         (← wildcardMatchIdx text pattern i (j + 1) h₁ (by omega))
  else if wildcard (pattern.get ⟨j, (by omega)⟩) then
    r := (← wildcardMatchIdx text pattern i (j + 1) h₁ (by omega)) ||
         (← wildcardMatchIdx text pattern (i + 1) j (by omega) h₂)
  else
    r := charMatch (text.get ⟨i, (by omega)⟩) (pattern.get ⟨j, (by omega)⟩) &&
         (← wildcardMatchIdx text pattern (i + 1) (j + 1) (by omega) (by omega))
  modifyGet λ cache => (r, cache.insert (i, j) r)
termination_by
  (text.length - i) + (pattern.length - j)
decreasing_by
  all_goals { simp_wf ; omega }

/--
The `like` matcher used by the evaluator: a memoized version of
`wildcardMatchSpec`. See `wildcardMatch_eq_spec`.
-/
public def wildcardMatch (text : String) (pattern : Pattern) : Bool :=
  wildcardMatchIdx text.toList pattern 0 0 (by simp) (by simp) |>.run' {}

/-! ## Greedy matcher

A model of Rust's `Pattern::wildcard_match` (`cedar-policy-core/src/ast/pattern.rs`):
a two-pointer loop that, on a mismatch, backtracks only to the most recent `*`.
-/

/--
Loop state: text index `i`, pattern index `j`, and `star = some (star_idx, tmp_idx)`
once `contains_star` is set.
-/
public structure GreedyState where
  i : Nat
  j : Nat
  star : Option (Nat × Nat)

/-- Result of one loop iteration: return a value, or continue from a new state. -/
public inductive GreedyStep where
  | done (b : Bool)
  | next (st : GreedyState)

/-- The Rust `while` condition: `i < text_len && (!contains_star || star_idx != pattern_len - 1)`. -/
public def greedyLoopCond (T : Array Char) (P : Array PatElem) (st : GreedyState) : Bool :=
  st.i < T.size &&
    (match st.star with
     | none         => true
     | some (sj, _) => sj != P.size - 1)

/-- The `else if contains_star` / `else` branches of the loop body. -/
public def greedyBacktrack (st : GreedyState) : GreedyStep :=
  match st.star with
  | some (sj, si) => .next ⟨si + 1, sj + 1, some (sj, si + 1)⟩
  | none          => .done false

/-- The trailing `while j < pattern_len && pattern[j].is_wildcard() { j += 1 }` loop. -/
public def skipStars (P : Array PatElem) (j : Nat) : Nat :=
  if h : j < P.size then
    if wildcard P[j] then skipStars P (j + 1) else j
  else j
termination_by P.size - j

/--
One iteration of the Rust `while` loop. Once the loop condition fails, the
result is `j == pattern_len` after skipping trailing `*`s.
-/
public def greedyStep (T : Array Char) (P : Array PatElem) (st : GreedyState) : GreedyStep :=
  if greedyLoopCond T P st then
    match P[st.j]? with
    | some .star         => .next ⟨st.i, st.j + 1, some (st.j, st.i)⟩
    | some (.justChar c) =>
      if T[st.i]? == some c then .next ⟨st.i + 1, st.j + 1, st.star⟩
      else greedyBacktrack st
    | none               => greedyBacktrack st
  else
    .done (skipStars P st.j == P.size)

def greedyMeasure (T : Array Char) (P : Array PatElem) (st : GreedyState) : Nat × Nat :=
  ((match st.star with
    | none         => T.size + 2
    | some (_, si) => T.size + 1 - min si st.i),
   (T.size - st.i) + (P.size - st.j))

theorem greedyStep_decreases {T : Array Char} {P : Array PatElem} {st st' : GreedyState}
    (h : greedyStep T P st = .next st') :
    Prod.Lex (· < ·) (· < ·) (greedyMeasure T P st') (greedyMeasure T P st) := by
  obtain ⟨i, j, star⟩ := st
  unfold greedyStep greedyBacktrack at h
  split at h
  · rename_i hc
    simp only [greedyLoopCond, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hi := hc.1
    apply Prod.lex_def.mpr
    split at h
    · rename_i hj
      have := (Array.getElem?_eq_some_iff.mp hj).1
      cases h
      rcases star with _ | ⟨sj, si⟩ <;> simp only [greedyMeasure, and_true] at * <;> omega
    · rename_i c hj
      have := (Array.getElem?_eq_some_iff.mp hj).1
      split at h
      · cases h
        rcases star with _ | ⟨sj, si⟩ <;> simp only [greedyMeasure, true_and, and_true] at * <;> omega
      · rcases star with _ | ⟨sj, si⟩ <;> simp only [reduceCtorEq, GreedyStep.next.injEq] at h
        cases h
        simp only [greedyMeasure] at *; omega
    · rcases star with _ | ⟨sj, si⟩ <;> simp only [reduceCtorEq, GreedyStep.next.injEq] at h
      cases h
      simp only [greedyMeasure] at *; omega
  · cases h

/-- Run the greedy loop from `st` until it returns. -/
public def greedyRun (T : Array Char) (P : Array PatElem) (st : GreedyState) : Bool :=
  match _h : greedyStep T P st with
  | .done b   => b
  | .next st' => greedyRun T P st'
termination_by greedyMeasure T P st
decreasing_by exact greedyStep_decreases _h

/-- Model of `Pattern::wildcard_match` on arrays. -/
public def greedyMatch (T : Array Char) (P : Array PatElem) : Bool :=
  if P.isEmpty then T.isEmpty
  else greedyRun T P ⟨0, 0, none⟩

/--
Greedy `like` matcher on strings. It agrees with `wildcardMatch` (see
`wildcardMatchGreedy_eq_wildcardMatch`) but does not need a memo table, and
runs in `O(text.length * pattern.length)` time (see `greedyMatch_steps`).
-/
public def wildcardMatchGreedy (text : String) (pattern : Pattern) : Bool :=
  greedyMatch text.toList.toArray pattern.toArray

end Cedar.Spec

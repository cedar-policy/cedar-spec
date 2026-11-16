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

public import Cedar.Spec.Wildcard
import all Cedar.Spec.Wildcard

/-!
This file proves that the memoized `like` matcher `wildcardMatch` and the
greedy matcher `wildcardMatchGreedy` both agree with `wildcardMatchSpec`.
-/

namespace Cedar.Spec

/-! ## Facts about `wildcardMatchSpec` on suffixes -/

/-- `wildcardMatchSpec` on the suffixes starting at text index `i` and pattern index `j`. -/
abbrev MS (T : List Char) (P : Pattern) (i j : Nat) : Bool :=
  wildcardMatchSpec (T.drop i) (P.drop j)

theorem spec_nil (ps : Pattern) : wildcardMatchSpec [] ps = ps.all wildcard := by
  induction ps with
  | nil => simp [wildcardMatchSpec]
  | cons e ps ih => cases e <;> simp [wildcardMatchSpec, ih, wildcard]

theorem spec_cons_nil (c : Char) (cs : List Char) :
    wildcardMatchSpec (c :: cs) [] = false := by simp [wildcardMatchSpec]

theorem spec_cons_star (c : Char) (cs : List Char) (ps : Pattern) :
    wildcardMatchSpec (c :: cs) (.star :: ps) =
    (wildcardMatchSpec (c :: cs) ps || wildcardMatchSpec cs (.star :: ps)) := by
  simp [wildcardMatchSpec]

theorem spec_cons_char (c : Char) (cs : List Char) (k : Char) (ps : Pattern) :
    wildcardMatchSpec (c :: cs) (.justChar k :: ps) = (c == k && wildcardMatchSpec cs ps) := by
  simp [wildcardMatchSpec]

theorem drop_of_getElem? {α} {l : List α} {j : Nat} {e : α} (h : l[j]? = some e) :
    l.drop j = e :: l.drop (j + 1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hj, he]

theorem MS_end (T : List Char) (P : Pattern) (i : Nat) :
    MS T P i P.length = decide (T.length ≤ i) := by
  unfold MS
  rw [List.drop_length]
  by_cases hi : i < T.length
  · rw [List.drop_eq_getElem_cons hi, spec_cons_nil]
    simp; omega
  · rw [List.drop_eq_nil_of_le (by omega)]
    simp [wildcardMatchSpec]; omega

theorem MS_end_text (T : List Char) (P : Pattern) (j : Nat) :
    MS T P T.length j = (P.drop j).all wildcard := by
  unfold MS
  rw [List.drop_length, spec_nil]

theorem MS_char {T : List Char} {P : Pattern} {i j : Nat} {c : Char}
    (h : P[j]? = some (.justChar c)) :
    MS T P i j = (T[i]? == some c && MS T P (i + 1) (j + 1)) := by
  unfold MS
  rw [drop_of_getElem? h]
  by_cases hi : i < T.length
  · rw [List.drop_eq_getElem_cons hi, List.getElem?_eq_getElem hi, spec_cons_char]
    simp
  · rw [List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega)]
    simp [wildcardMatchSpec]

theorem MS_star_step {T : List Char} {P : Pattern} {i j : Nat}
    (h : P[j]? = some .star) (hi : i < T.length) :
    MS T P i j = (MS T P i (j + 1) || MS T P (i + 1) j) := by
  unfold MS
  rw [drop_of_getElem? h, List.drop_eq_getElem_cons hi, spec_cons_star]

/-- Some `k ≥ i` satisfies `M` iff `i` does or some `k > i` does. -/
theorem exists_ge_iff {M : Nat → Bool} {i n : Nat} (hi : i ≤ n) :
    ((M i = true ∨ ∃ k, i < k ∧ k ≤ n ∧ M k = true) ↔
      ∃ k, i ≤ k ∧ k ≤ n ∧ M k = true) := by
  constructor
  · rintro (hm | ⟨k, hk1, hk2, hm⟩)
    · exact ⟨i, Nat.le_refl _, hi, hm⟩
    · exact ⟨k, by omega, hk2, hm⟩
  · rintro ⟨k, hk1, hk2, hm⟩
    by_cases hk : k = i
    · subst hk; exact Or.inl hm
    · exact Or.inr ⟨k, by omega, hk2, hm⟩

theorem MS_star {T : List Char} {P : Pattern} {j : Nat}
    (h : P[j]? = some .star) (i : Nat) (hi : i ≤ T.length) :
    MS T P i j = true ↔ ∃ k, i ≤ k ∧ k ≤ T.length ∧ MS T P k (j + 1) = true := by
  induction hd : T.length - i generalizing i with
  | zero =>
    have hi' : i = T.length := by omega
    subst hi'
    unfold MS
    rw [drop_of_getElem? h, List.drop_length]
    simp only [wildcardMatchSpec]
    constructor
    · intro hm
      exact ⟨T.length, Nat.le_refl _, Nat.le_refl _, by rw [List.drop_length]; exact hm⟩
    · rintro ⟨k, hk1, hk2, hm⟩
      have : k = T.length := by omega
      subst this; rw [List.drop_length] at hm; exact hm
  | succ d ih =>
    have hlt : i < T.length := by omega
    rw [MS_star_step h hlt, Bool.or_eq_true, ih (i + 1) (by omega) (by omega)]
    exact exists_ge_iff (M := fun k => MS T P k (j + 1)) hi

/-- If a suffix starting with `*` matches from text index `q`, it matches from any `i ≤ q`. -/
theorem MS_star_mono {T : List Char} {P : Pattern} {j : Nat}
    (h : P[j]? = some .star) {i q : Nat} (hiq : i ≤ q) (hq : q ≤ T.length)
    (hm : MS T P q j = true) : MS T P i j = true := by
  obtain ⟨k, hk1, hk2, hk⟩ := (MS_star h q hq).mp hm
  exact (MS_star h i (by omega)).mpr ⟨k, by omega, hk2, hk⟩

/-- `P[b..b+L)` consists of literal characters. -/
def LitSeg (P : Pattern) (b L : Nat) : Prop :=
  ∀ t, t < L → ∃ c, P[b + t]? = some (.justChar c)

/-- `P[b..b+L)` consists of literal characters equal to `T[k..k+L)`. -/
def LitMatch (T : List Char) (P : Pattern) (k b L : Nat) : Prop :=
  ∀ t, t < L → ∃ c, P[b + t]? = some (.justChar c) ∧ T[k + t]? = some c

theorem lit_forward {T : List Char} {P : Pattern} :
    ∀ (L k b : Nat), LitSeg P b L → MS T P k b = true →
      LitMatch T P k b L ∧ MS T P (k + L) (b + L) = true
  | 0, k, b, _, hm => ⟨fun t ht => by omega, hm⟩
  | L + 1, k, b, hl, hm => by
    obtain ⟨c, hc⟩ := hl 0 (by omega)
    simp only [Nat.add_zero] at hc
    rw [MS_char hc] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    have hl' : LitSeg P (b + 1) L := fun t ht => by
      obtain ⟨c', hc'⟩ := hl (t + 1) (by omega)
      exact ⟨c', by rw [← hc']; congr 1; omega⟩
    obtain ⟨hlm, hm'⟩ := lit_forward L (k + 1) (b + 1) hl' hm.2
    refine ⟨?_, by
      rw [show k + (L + 1) = k + 1 + L by omega, show b + (L + 1) = b + 1 + L by omega]
      exact hm'⟩
    intro t ht
    cases t with
    | zero => exact ⟨c, hc, by simpa using hm.1⟩
    | succ t =>
      obtain ⟨c', h1, h2⟩ := hlm t (by omega)
      exact ⟨c', by rw [← h1]; congr 1; omega, by rw [← h2]; congr 1; omega⟩

theorem LitMatch.le {T : List Char} {P : Pattern} {k b L : Nat}
    (h : LitMatch T P k b L) (hL : 0 < L) : k + L ≤ T.length := by
  obtain ⟨c, _, h2⟩ := h (L - 1) (by omega)
  have := (List.getElem?_eq_some_iff.mp h2).1
  omega

/-! ## Correctness of the greedy matcher -/

section Greedy

variable {T : List Char} {P : Pattern}

theorem skipStars_eq (P : Pattern) (j : Nat) (hj : j ≤ P.length) :
    (skipStars P.toArray j == P.toArray.size) = (P.drop j).all wildcard := by
  induction hd : P.length - j generalizing j with
  | zero =>
    have : j = P.length := by omega
    subst this
    rw [skipStars]; simp
  | succ d ih =>
    have hlt : j < P.length := by omega
    rw [skipStars, List.drop_eq_getElem_cons hlt]
    simp only [List.size_toArray, hlt, ↓reduceDIte, List.getElem_toArray, List.all_cons]
    by_cases hw : wildcard P[j] = true
    · simp only [hw, ↓reduceIte, Bool.true_and]
      simpa using ih (j + 1) (by omega) (by omega)
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, Bool.false_and, beq_eq_false_iff_ne, ne_eq]
      omega

/--
Invariant of the greedy loop. If the last `*` seen is at pattern index `sj`
and the current attempt resumes the text after it at index `si`, then
`P[sj+1..j)` consists of `i - si` literals.
-/
def GInv (T : List Char) (P : Pattern) (st : GreedyState) : Prop :=
  st.i ≤ T.length ∧ st.j ≤ P.length ∧
  ∀ sj si, st.star = some (sj, si) →
    sj < st.j ∧ P[sj]? = some .star ∧ si ≤ st.i ∧ st.i - si = st.j - (sj + 1) ∧
    LitSeg P (sj + 1) (st.i - si)

/-- Matches not yet tried by the loop: the last `*` extends to some text index `k > si`. -/
def GAlt (T : List Char) (P : Pattern) : Option (Nat × Nat) → Prop
  | none          => False
  | some (sj, si) => ∃ k, si < k ∧ k ≤ T.length ∧ MS T P k (sj + 1) = true

/-- The value the loop computes from `st` (see `greedyRun_correct`). -/
def GVal (T : List Char) (P : Pattern) (st : GreedyState) : Prop :=
  MS T P st.i st.j = true ∨ GAlt T P st.star


/-- If the last `*` can extend to `k > si`, then `j` matches from a text index past `i`. -/
theorem alt_shift {st : GreedyState} (hinv : GInv T P st) {sj si k : Nat}
    (hs : st.star = some (sj, si)) (hk1 : si < k) (hk2 : k ≤ T.length)
    (hm : MS T P k (sj + 1) = true) :
    st.i < k + (st.i - si) ∧ k + (st.i - si) ≤ T.length ∧
      MS T P (k + (st.i - si)) st.j = true := by
  obtain ⟨_, _, hs'⟩ := hinv
  obtain ⟨h1, _, h3, h4, h5⟩ := hs' sj si hs
  obtain ⟨hlm, hm'⟩ := lit_forward (st.i - si) k (sj + 1) h5 hm
  rw [show sj + 1 + (st.i - si) = st.j by omega] at hm'
  refine ⟨by omega, ?_, hm'⟩
  by_cases hL : st.i - si = 0
  · omega
  · exact hlm.le (by omega)

theorem GInv.backtrack {i j sj si : Nat} {star : Option (Nat × Nat)}
    (hinv : GInv T P ⟨i, j, star⟩) (hstar : star = some (sj, si)) (hi : i < T.length) :
    GInv T P ⟨si + 1, sj + 1, some (sj, si + 1)⟩ := by
  dsimp only [GInv] at hinv ⊢
  obtain ⟨_, _, hs⟩ := hinv
  obtain ⟨h1, h2, h3, _, _⟩ := hs sj si hstar
  refine ⟨by omega, by omega, ?_⟩
  intro sj' si' he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨by simp, h2, by simp, by simp, fun t ht => by simp at ht⟩

theorem greedyStep_next {st st' : GreedyState} (hinv : GInv T P st)
    (h : greedyStep T.toArray P.toArray st = .next st') :
    GInv T P st' ∧ (GVal T P st' ↔ GVal T P st) := by
  obtain ⟨i, j, star⟩ := st
  have hinv0 := hinv
  dsimp only [GInv] at hinv
  obtain ⟨hi, hj, hs⟩ := hinv
  have hc : greedyLoopCond T.toArray P.toArray ⟨i, j, star⟩ = true := by
    cases hc : greedyLoopCond T.toArray P.toArray ⟨i, j, star⟩
    · simp [greedyStep, hc] at h
    · rfl
  have hin : i < T.length := by
    simp only [greedyLoopCond, Bool.and_eq_true, decide_eq_true_eq] at hc; simpa using hc.1
  -- the backtracking branch, shared by a literal mismatch and the end of the pattern
  have hback : MS T P i j = false →
      greedyBacktrack ⟨i, j, star⟩ = .next st' →
      GInv T P st' ∧ (GVal T P st' ↔ GVal T P ⟨i, j, star⟩) := by
    intro hm0 hb
    rcases star with _ | ⟨sj, si⟩
    · simp [greedyBacktrack] at hb
    · simp only [greedyBacktrack, GreedyStep.next.injEq] at hb
      subst hb
      obtain ⟨_, _, h3, _, _⟩ := hs sj si rfl
      refine ⟨hinv0.backtrack rfl hin, ?_⟩
      simp only [GVal, GAlt, hm0, Bool.false_eq_true, false_or]
      exact exists_ge_iff (M := fun k => MS T P k (sj + 1)) (i := si + 1) (by omega)
  rcases hpj : P[j]? with _ | _ | c
  · -- end of pattern
    have hjl : j = P.length := by
      have := List.getElem?_eq_none_iff.mp hpj; omega
    simp only [greedyStep, hc, ↓reduceIte, List.getElem?_toArray, hpj] at h
    apply hback _ h
    rw [hjl, MS_end]; simp; omega
  · -- `*`
    have hjl := (List.getElem?_eq_some_iff.mp hpj).1
    simp only [greedyStep, hc, ↓reduceIte, List.getElem?_toArray, hpj,
      GreedyStep.next.injEq] at h
    subst h
    refine ⟨⟨by simp; omega, by simp; omega, ?_⟩, ?_⟩
    · intro sj si he
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨by simp, hpj, by simp, by simp, fun t ht => by simp at ht⟩
    · simp only [GVal, GAlt]
      rw [exists_ge_iff (M := fun k => MS T P k (j + 1)) hi, ← MS_star hpj i hi]
      constructor
      · exact Or.inl
      · rintro (hm | hm)
        · exact hm
        · rcases star with _ | ⟨sj, si⟩
          · exact hm.elim
          · obtain ⟨k, hk1, hk2, hk⟩ := hm
            obtain ⟨_, hq, hm'⟩ := alt_shift hinv0 rfl hk1 hk2 hk
            exact MS_star_mono hpj (by simp at *; omega) hq hm'
  · -- literal
    have hjl := (List.getElem?_eq_some_iff.mp hpj).1
    by_cases htc : (T[i]? == some c) = true
    · simp only [greedyStep, hc, ↓reduceIte, List.getElem?_toArray, hpj, htc,
        GreedyStep.next.injEq] at h
      subst h
      refine ⟨⟨by simp; omega, by simp; omega, ?_⟩, ?_⟩
      · intro sj si he
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs sj si he
        refine ⟨by simp; omega, h2, by simp; omega, by simp; omega, ?_⟩
        intro t ht
        simp only at ht
        by_cases htl : t < i - si
        · exact h5 t htl
        · exact ⟨c, by rw [show sj + 1 + t = j by omega]; exact hpj⟩
      · simp only [GVal]
        rw [MS_char hpj (i := i), htc]
        simp
    · simp only [greedyStep, hc, ↓reduceIte, List.getElem?_toArray, hpj, htc] at h
      apply hback _ h
      rw [MS_char hpj]; simp [htc]

theorem greedyStep_done {st : GreedyState} {b : Bool} (hinv : GInv T P st)
    (h : greedyStep T.toArray P.toArray st = .done b) :
    (b = true ↔ GVal T P st) := by
  obtain ⟨i, j, star⟩ := st
  have hinv0 := hinv
  dsimp only [GInv] at hinv
  obtain ⟨hi, hj, hs⟩ := hinv
  by_cases hc : greedyLoopCond T.toArray P.toArray ⟨i, j, star⟩ = true
  · have hin : i < T.length := by
      simp only [greedyLoopCond, Bool.and_eq_true, decide_eq_true_eq] at hc; simpa using hc.1
    have hback : MS T P i j = false →
        greedyBacktrack ⟨i, j, star⟩ = .done b → (b = true ↔ GVal T P ⟨i, j, star⟩) := by
      intro hm0 hb
      rcases star with _ | ⟨sj, si⟩
      · simp only [greedyBacktrack, GreedyStep.done.injEq] at hb
        subst hb
        simp [GVal, GAlt, hm0]
      · simp [greedyBacktrack] at hb
    rcases hpj : P[j]? with _ | _ | c
    · have hjl : j = P.length := by
        have := List.getElem?_eq_none_iff.mp hpj; omega
      simp only [greedyStep, hc, ↓reduceIte, List.getElem?_toArray, hpj] at h
      apply hback _ h
      rw [hjl, MS_end]; simp; omega
    · simp [greedyStep, hc, hpj] at h
    · by_cases htc : (T[i]? == some c) = true
      · simp [greedyStep, hc, hpj, htc] at h
      · simp only [greedyStep, hc, ↓reduceIte, List.getElem?_toArray, hpj, htc] at h
        apply hback _ h
        rw [MS_char hpj]; simp [htc]
  · simp only [greedyStep, hc, Bool.false_eq_true, ↓reduceIte, GreedyStep.done.injEq] at h
    subst h
    rw [skipStars_eq P j hj]
    simp only [greedyLoopCond, Bool.and_eq_true, decide_eq_true_eq, not_and,
      List.size_toArray] at hc
    by_cases hin : i < T.length
    · have hc' := hc hin
      rcases star with _ | ⟨sj, si⟩
      · simp at hc'
      · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc'
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs sj si rfl
        have hsj := (List.getElem?_eq_some_iff.mp h2).1
        have hjl : j = P.length := by omega
        subst hjl
        simp only [List.drop_length, List.all_nil, true_iff]
        refine Or.inr ⟨T.length, by omega, Nat.le_refl _, ?_⟩
        rw [show sj + 1 = P.length by omega, MS_end]
        simp
    · have hin' : i = T.length := by omega
      subst hin'
      rw [← MS_end_text T P j]
      simp only [GVal]
      constructor
      · exact Or.inl
      · rintro (hm | hm)
        · exact hm
        · rcases star with _ | ⟨sj, si⟩
          · exact hm.elim
          · obtain ⟨k, hk1, hk2, hk⟩ := hm
            obtain ⟨hlt, hle, _⟩ := alt_shift hinv0 rfl hk1 hk2 hk
            simp at hlt hle; omega

theorem greedyRun_correct (st : GreedyState) (hinv : GInv T P st) :
    greedyRun T.toArray P.toArray st = true ↔ GVal T P st := by
  rw [greedyRun]
  split
  · next b h => exact greedyStep_done hinv h
  · next st' h =>
    obtain ⟨hinv', hval⟩ := greedyStep_next hinv h
    rw [greedyRun_correct st' hinv']
    exact hval
termination_by greedyMeasure T.toArray P.toArray st
decreasing_by all_goals (apply greedyStep_decreases; assumption)

end Greedy

public theorem greedyMatch_eq_spec (text : List Char) (pattern : Pattern) :
    greedyMatch text.toArray pattern.toArray = wildcardMatchSpec text pattern := by
  unfold greedyMatch
  split
  · rename_i he
    simp only [List.isEmpty_toArray, List.isEmpty_iff] at he
    subst he
    cases text <;> simp [wildcardMatchSpec]
  · apply Bool.eq_iff_iff.mpr
    have hinv : GInv text pattern ⟨0, 0, none⟩ := ⟨by simp, by simp, by simp⟩
    rw [greedyRun_correct _ hinv]
    simp [GVal, GAlt, MS]

public theorem wildcardMatchGreedy_eq_spec (text : String) (pattern : Pattern) :
    wildcardMatchGreedy text pattern = wildcardMatchSpec text.toList pattern :=
  greedyMatch_eq_spec text.toList pattern

/-! ## Correctness of the memoized matcher -/

section DP

open Std (HashMap)

def CacheCorrect (T : List Char) (P : Pattern) (cache : Cache) : Prop :=
  ∀ k l b, cache.get? (k, l) = some b → b = MS T P k l

theorem cacheCorrect_insert {T : List Char} {P : Pattern}
    {cache : Cache} (h : CacheCorrect T P cache) {i j : Nat} {b : Bool}
    (hb : b = MS T P i j) :
    CacheCorrect T P (cache.insert (i, j) b) := by
  intro k l b' hget
  rw [Std.HashMap.get?_insert] at hget
  by_cases hk : ((i, j) == (k, l)) = true
  · simp only [hk, ↓reduceIte] at hget
    simp only [beq_iff_eq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Option.some.injEq] at hget
    rw [← hget]; exact hb
  · simp only [hk] at hget
    exact h k l b' hget

theorem stateM_bind_run {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    StateT.bind x f s = f (x s).1 (x s).2 := rfl

theorem stateM_modifyGet_run {σ α : Type} (g : σ → α × σ) (s : σ) :
    (StateT.modifyGet g s : Id (α × σ)) = g s := rfl

theorem MS_star_end (T : List Char) (P : Pattern) (j : Nat) (hj : j < P.length) :
    MS T P T.length j = (wildcard P[j] && MS T P T.length (j + 1)) := by
  rw [MS_end_text, MS_end_text, List.drop_eq_getElem_cons hj, List.all_cons]

theorem MS_wild {T : List Char} {P : Pattern} {i j : Nat}
    (hi : i < T.length) (hj : j < P.length) (hw : wildcard P[j] = true) :
    MS T P i j = (MS T P i (j + 1) || MS T P (i + 1) j) := by
  have hpj : P[j]? = some P[j] := List.getElem?_eq_getElem hj
  generalize P[j] = e at hpj hw
  cases e with
  | star => exact MS_star_step hpj hi
  | justChar c => simp [wildcard] at hw

theorem MS_nonwild {T : List Char} {P : Pattern} {i j : Nat}
    (hi : i < T.length) (hj : j < P.length) (hw : ¬ wildcard P[j] = true) :
    MS T P i j = (charMatch T[i] P[j] && MS T P (i + 1) (j + 1)) := by
  have hpj : P[j]? = some P[j] := List.getElem?_eq_getElem hj
  generalize P[j] = e at hpj hw
  cases e with
  | star => simp [wildcard] at hw
  | justChar c =>
    rw [MS_char hpj, List.getElem?_eq_getElem hi]
    simp [charMatch]

theorem wildcardMatchIdx_run_correct (T : List Char) (P : Pattern)
    (i j : Nat) (h₁ : i ≤ T.length) (h₂ : j ≤ P.length)
    (cache : Cache) (hc : CacheCorrect T P cache) :
    (wildcardMatchIdx T P i j h₁ h₂ cache).1 = MS T P i j ∧
    CacheCorrect T P (wildcardMatchIdx T P i j h₁ h₂ cache).2 := by
  induction i, j, h₁, h₂ using wildcardMatchIdx.induct T P generalizing cache with
  | _ i j h₁ h₂ ih1 ih2 ih3 ih4 =>
    rw [wildcardMatchIdx.eq_def]
    rcases hget : cache.get? (i, j) with _ | b
    all_goals simp only [bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
                          modifyGet, MonadStateOf.modifyGet, StateT.bind, hget]
    · split
      · rename_i h₃
        have e : decide (i = T.length) = MS T P i j := by
          rw [h₃, MS_end]; simp; omega
        rw [stateM_modifyGet_run]
        exact ⟨e, cacheCorrect_insert hc e⟩
      · rename_i h₃
        split
        · rename_i h₄
          obtain ⟨e1, c1⟩ := ih1 h₃ cache hc
          rw [stateM_bind_run, stateM_modifyGet_run]
          have e : (wildcard (P.get ⟨j, by omega⟩) &&
              (wildcardMatchIdx T P i (j + 1) h₁ (by omega) cache).1) = MS T P i j := by
            rw [e1, h₄, MS_star_end T P j (by omega)]; rfl
          exact ⟨e, cacheCorrect_insert c1 e⟩
        · rename_i h₄
          split
          · rename_i hw
            obtain ⟨e1, c1⟩ := ih2 h₃ h₄ cache hc
            obtain ⟨e2, c2⟩ := ih3 h₄ _ c1
            rw [stateM_bind_run, stateM_bind_run, stateM_modifyGet_run]
            have e : ((wildcardMatchIdx T P i (j + 1) h₁ (by omega) cache).1 ||
                (wildcardMatchIdx T P (i + 1) j (by omega) h₂
                  (wildcardMatchIdx T P i (j + 1) h₁ (by omega) cache).2).1) =
                MS T P i j := by
              rw [e1, e2, MS_wild (i := i) (j := j) (by omega) (by omega) hw]
            exact ⟨e, cacheCorrect_insert c2 e⟩
          · rename_i hw
            obtain ⟨e1, c1⟩ := ih4 h₃ h₄ cache hc
            rw [stateM_bind_run, stateM_modifyGet_run]
            have e : (charMatch (T.get ⟨i, by omega⟩) (P.get ⟨j, by omega⟩) &&
                (wildcardMatchIdx T P (i + 1) (j + 1) (by omega) (by omega) cache).1) =
                MS T P i j := by
              rw [e1, MS_nonwild (i := i) (j := j) (by omega) (by omega) hw]; rfl
            exact ⟨e, cacheCorrect_insert c1 e⟩
    · exact ⟨hc i j b hget, hc⟩

end DP

public theorem wildcardMatch_eq_spec (text : String) (pattern : Pattern) :
    wildcardMatch text pattern = wildcardMatchSpec text.toList pattern := by
  unfold wildcardMatch
  have := (wildcardMatchIdx_run_correct text.toList pattern 0 0 (by simp) (by simp) {}
    (fun k l b h => by simp at h)).1
  simp only [StateT.run', MS, List.drop_zero] at this ⊢
  exact this

public theorem wildcardMatchGreedy_eq_wildcardMatch (text : String) (pattern : Pattern) :
    wildcardMatchGreedy text pattern = wildcardMatch text pattern := by
  rw [wildcardMatchGreedy_eq_spec, wildcardMatch_eq_spec]

/-! ## Running time of the greedy matcher -/

section Steps

/-- The number of iterations of the greedy loop from `st`, including the one that returns. -/
public def greedySteps (T : Array Char) (P : Array PatElem) (st : GreedyState) : Nat :=
  match _h : greedyStep T P st with
  | .done _   => 1
  | .next st' => greedySteps T P st' + 1
termination_by greedyMeasure T P st
decreasing_by exact greedyStep_decreases _h

/-- Bounds on the loop indices that hold throughout the greedy loop. -/
def GBounds (T : Array Char) (P : Array PatElem) (st : GreedyState) : Prop :=
  st.i ≤ T.size ∧ st.j ≤ P.size ∧
  ∀ sj si, st.star = some (sj, si) → sj < st.j ∧ si ≤ st.i

/-- The text index where the last `*` started matching, or `i` if there is no `*` yet. -/
def lastStart (st : GreedyState) : Nat :=
  match st.star with
  | none         => st.i
  | some (_, si) => si

/--
Every iteration either moves `lastStart` forward, or keeps it and moves `j`
forward. This bounds the number of iterations by `(T.size + 1) * (P.size + 1)`.
-/
def greedyPotential (T : Array Char) (P : Array PatElem) (st : GreedyState) : Nat :=
  (T.size - lastStart st) * (P.size + 1) + (P.size - st.j)

theorem potential_lt {n m a a' j j' : Nat} (haa : a ≤ a') (ha' : a' ≤ n) (hj' : j' ≤ m)
    (h : a < a' ∨ j < j') :
    (n - a') * (m + 1) + (m - j') < (n - a) * (m + 1) + (m - j) := by
  rcases h with h | h
  · have : (n - a' + 1) * (m + 1) ≤ (n - a) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    omega
  · have : (n - a') * (m + 1) ≤ (n - a) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    omega

theorem greedyStep_potential {T : Array Char} {P : Array PatElem} {st st' : GreedyState}
    (hb : GBounds T P st) (h : greedyStep T P st = .next st') :
    GBounds T P st' ∧ greedyPotential T P st' < greedyPotential T P st := by
  obtain ⟨i, j, star⟩ := st
  obtain ⟨hi, hj, hs⟩ := hb
  simp only at hi hj hs
  unfold greedyStep at h
  split at h
  · rename_i hc
    simp only [greedyLoopCond, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hin : i < T.size := hc.1
    -- the backtracking branch, shared by a literal mismatch and the end of the pattern
    have hback : greedyBacktrack ⟨i, j, star⟩ = .next st' →
        GBounds T P st' ∧ greedyPotential T P st' < greedyPotential T P ⟨i, j, star⟩ := by
      intro hb
      rcases star with _ | ⟨sj, si⟩
      · simp [greedyBacktrack] at hb
      · simp only [greedyBacktrack, GreedyStep.next.injEq] at hb
        subst hb
        obtain ⟨h1, h2⟩ := hs sj si rfl
        refine ⟨⟨by simp; omega, by simp; omega, ?_⟩, ?_⟩
        · intro sj' si' he
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp
        · simp only [greedyPotential, lastStart]
          exact potential_lt (by omega) (by omega) (by omega) (.inl (by omega))
    split at h
    · rename_i hpj
      have hjl : j < P.size := (Array.getElem?_eq_some_iff.mp hpj).1
      simp only [GreedyStep.next.injEq] at h
      subst h
      refine ⟨⟨by simp; omega, by simp; omega, ?_⟩, ?_⟩
      · intro sj' si' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp
      · rcases star with _ | ⟨sj, si⟩
        · exact potential_lt (by simp [lastStart]) (by simp [lastStart]; omega) (by simp; omega)
            (.inr (by simp))
        · exact potential_lt (by simp [lastStart]; exact (hs sj si rfl).2)
            (by simp [lastStart]; omega) (by simp; omega) (.inr (by simp))
    · rename_i c hpj
      have hjl : j < P.size := (Array.getElem?_eq_some_iff.mp hpj).1
      split at h
      · simp only [GreedyStep.next.injEq] at h
        subst h
        refine ⟨⟨by simp; omega, by simp; omega, ?_⟩, ?_⟩
        · intro sj' si' he
          obtain ⟨h1, h2⟩ := hs sj' si' he
          simp only; omega
        · rcases star with _ | ⟨sj, si⟩
          · exact potential_lt (by simp [lastStart]) (by simp [lastStart]; omega) (by simp; omega)
              (.inl (by simp [lastStart]))
          · have := (hs sj si rfl).2
            exact potential_lt (by simp [lastStart]) (by simp [lastStart]; omega) (by simp; omega)
              (.inr (by simp))
      · exact hback h
    · exact hback h
  · cases h

theorem greedySteps_le {T : Array Char} {P : Array PatElem} {st : GreedyState}
    (hb : GBounds T P st) : greedySteps T P st ≤ greedyPotential T P st + 1 := by
  rw [greedySteps]
  split
  · omega
  · next st' h =>
    obtain ⟨hb', hlt⟩ := greedyStep_potential hb h
    have := greedySteps_le hb'
    omega
termination_by greedyMeasure T P st
decreasing_by all_goals (apply greedyStep_decreases; assumption)

end Steps

/--
The greedy loop runs at most `(T.size + 1) * (P.size + 1)` iterations. Each
iteration does a constant amount of work, except the last one, which may also
skip up to `P.size` trailing `*`s.
-/
public theorem greedyMatch_steps (T : Array Char) (P : Array PatElem) :
    greedySteps T P ⟨0, 0, none⟩ ≤ (T.size + 1) * (P.size + 1) := by
  have := greedySteps_le (T := T) (P := P) (st := ⟨0, 0, none⟩) ⟨by simp, by simp, by simp⟩
  simp only [greedyPotential, lastStart, Nat.sub_zero] at this
  rw [Nat.succ_mul]
  omega

end Cedar.Spec

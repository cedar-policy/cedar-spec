import Cedar.Spec.Ext.Decimal
import Cedar.Thm.Data.String

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

def IsWfStr (s : String) : Prop :=
 ∃ left right,
    s.splitToList (· = '.') = [left, right] ∧
    left ≠ "-" ∧
    0 < right.length ∧
    right.length ≤ DECIMAL_DIGITS ∧
    (toInt?' left).isSome ∧
    (toNat?' right).isSome

def computeValue (s : String) : Int :=
  match s.splitToList (· = '.') with
  | [left, right] =>
    let rlen := right.length
    match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        let i  := if !left.startsWith "-" then l' + r' else l' - r'
        i
      | _, _ => 0
  | _ => 0

/-- `toString d` splits into concrete parts whose parse-relevant properties are known: -/
theorem toString_split (d : Decimal) :
    let leftPart := (if d < 0 then "-" else "") ++ toString (d.natAbs / Nat.pow 10 4)
    let rightNat := d.natAbs % Nat.pow 10 4
    let rightPart :=
      if rightNat < 10 then "000" ++ toString rightNat
      else if rightNat < 100 then "00" ++ toString rightNat
      else if rightNat < 1000 then "0" ++ toString rightNat
      else toString rightNat
    (toString d).splitToList (· = '.') = [leftPart, rightPart] ∧
    rightPart.length = 4 ∧
    toInt?' leftPart = some (if d < 0 then -(↑(d.natAbs / Nat.pow 10 4) : Int)
      else (↑(d.natAbs / Nat.pow 10 4) : Int)) ∧
    toNat?' rightPart = some rightNat ∧
    (!leftPart.startsWith "-") = !(d < 0) := by
  intro leftPart rightNat rightPart
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- splitToList
    have h_left_no_dot : ∀ c ∈ leftPart.toList,
        (fun x : Char => decide (x = '.')) c = false := by
      intro c hc; simp only [leftPart, String.toList_append] at hc
      simp only [decide_eq_false_iff_not]; intro heq
      cases List.mem_append.mp hc with
      | inl h =>
        split at h
        · simp at h; rw [h] at heq; exact absurd heq (by decide)
        · simp at h
      | inr h => exact absurd (repr_no_dot _ c h) (by simp [heq])
    have h_right_no_dot : ∀ c ∈ rightPart.toList,
        (fun x : Char => decide (x = '.')) c = false := by
      intro c hc; simp only [rightPart] at hc
      split at hc
      · exact zeros_repr_no_dot "000" _ (by simp) c hc
      · split at hc
        · exact zeros_repr_no_dot "00" _ (by simp) c hc
        · split at hc
          · exact zeros_repr_no_dot "0" _ (by simp) c hc
          · exact repr_no_dot _ c hc
    have h_toString : toString d = leftPart ++ String.singleton '.' ++ rightPart := by
      show leftPart ++ (if rightNat < 10 then ".000" ++ toString rightNat
        else if rightNat < 100 then ".00" ++ toString rightNat
        else if rightNat < 1000 then ".0" ++ toString rightNat
        else "." ++ toString rightNat) = leftPart ++ String.singleton '.' ++ rightPart
      simp only [rightPart, String.append_assoc]; congr 1
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · rfl
    rw [h_toString]
    exact splitToList_eq leftPart rightPart _ '.' (by rfl) h_left_no_dot h_right_no_dot
  · -- rightPart.length = 4
    simp only [rightPart, rightNat]
    split
    · have : ("000" : String).length = 3 := by rfl
      have : (d.natAbs % Nat.pow 10 4).repr.length = 1 := by
        rw [Nat.repr_eq_ofList_toDigits, String.length_ofList, Nat.toDigits,
          show d.natAbs % Nat.pow 10 4 + 1 = Nat.succ (d.natAbs % Nat.pow 10 4) from rfl,
          Nat.toDigitsCore.eq_def]
        simp [show d.natAbs % Nat.pow 10 4 / 10 = 0 from by omega]
      simp [*]
    · split
      · have : ("00" : String).length = 2 := by rfl
        have : (d.natAbs % Nat.pow 10 4).repr.length = 2 := by
          rw [Nat.repr_eq_ofList_toDigits, String.length_ofList, Nat.toDigits,
            show d.natAbs % Nat.pow 10 4 + 1 = Nat.succ (d.natAbs % Nat.pow 10 4) from rfl,
            Nat.toDigitsCore.eq_def]
          simp only [show d.natAbs % Nat.pow 10 4 / 10 ≠ 0 from by omega]
          rw [show d.natAbs % Nat.pow 10 4 = Nat.succ (d.natAbs % Nat.pow 10 4 - 1) from by omega,
            Nat.toDigitsCore.eq_def]
          simp [show (d.natAbs % Nat.pow 10 4 - 1).succ / 10 / 10 = 0 from by omega]
        simp [*]
      · split
        · have : ("0" : String).length = 1 := by rfl
          have : (d.natAbs % Nat.pow 10 4).repr.length = 3 := by
            rw [Nat.repr_eq_ofList_toDigits, String.length_ofList, Nat.toDigits,
              show d.natAbs % Nat.pow 10 4 + 1 = Nat.succ (d.natAbs % Nat.pow 10 4) from rfl,
              Nat.toDigitsCore.eq_def]
            simp only [show d.natAbs % Nat.pow 10 4 / 10 ≠ 0 from by omega]
            rw [show d.natAbs % Nat.pow 10 4 = Nat.succ (d.natAbs % Nat.pow 10 4 - 1) from by omega,
              Nat.toDigitsCore.eq_def]
            simp only [show (d.natAbs % Nat.pow 10 4 - 1).succ / 10 / 10 ≠ 0 from by omega, ↓reduceIte]
            rw [show (d.natAbs % Nat.pow 10 4 - 1) = Nat.succ (d.natAbs % Nat.pow 10 4 - 2) from by omega,
              Nat.toDigitsCore.eq_def]
            simp [show (d.natAbs % Nat.pow 10 4 - 2).succ.succ / 10 / 10 / 10 = 0 from by omega]
          simp [*]
        · have : (d.natAbs % Nat.pow 10 4).repr.length = 4 := by
            rw [Nat.repr_eq_ofList_toDigits, String.length_ofList, Nat.toDigits,
              show d.natAbs % Nat.pow 10 4 + 1 = Nat.succ (d.natAbs % Nat.pow 10 4) from rfl,
              Nat.toDigitsCore.eq_def]
            simp only [show d.natAbs % Nat.pow 10 4 / 10 ≠ 0 from by omega]
            rw [show d.natAbs % Nat.pow 10 4 = Nat.succ (d.natAbs % Nat.pow 10 4 - 1) from by omega,
              Nat.toDigitsCore.eq_def]
            simp only [show (d.natAbs % Nat.pow 10 4 - 1).succ / 10 / 10 ≠ 0 from by omega]
            rw [show (d.natAbs % Nat.pow 10 4 - 1) = Nat.succ (d.natAbs % Nat.pow 10 4 - 2) from by omega,
              Nat.toDigitsCore.eq_def]
            simp only [show (d.natAbs % Nat.pow 10 4 - 2).succ.succ / 10 / 10 / 10 ≠ 0 from by omega]
            rw [show (d.natAbs % Nat.pow 10 4 - 2) = Nat.succ (d.natAbs % Nat.pow 10 4 - 3) from by omega,
              Nat.toDigitsCore.eq_def]
            simp [show (d.natAbs % Nat.pow 10 4 - 3).succ.succ.succ / 10 / 10 / 10 / 10 = 0 from
              by simp; omega]
          simp [*]
  · -- toInt?' leftPart = some (...)
    simp only [leftPart, toInt?']
    split <;> simp
  · -- toNat?' rightPart = some rightNat
    simp only [rightPart, rightNat, toNat?']
    have hno_us : ∀ (pad : String) (n : Nat), (∀ c ∈ pad.toList, c = '0') →
        (pad ++ toString n).contains '_' = false := by
      intro pad n hz
      have h : ¬ ('_' ∈ (pad ++ toString n).toList) := by
        rw [String.toList_append]
        intro h
        cases List.mem_append.mp h with
        | inl h => exact absurd (hz '_' h) (by decide)
        | inr h =>
          rw [Nat.toString_eq_repr, Nat.toList_repr] at h
          exact Nat.underscore_not_in_toDigits h
      simpa [String.contains] using h
    split
    · -- "000" ++ toString n, n < 10
      rename_i h
      rw [hno_us "000" _ (by simp)]
      simp [String.toNat?, String.Slice.toNat?]
      simp [toDigits_foldl_roundtrip _]
      simp [String.isNat_iff]
      refine ⟨?_, ?_, ?_⟩
      · -- ∀ c ∈ list, c.isDigit ∨ c = '_'
        intro c hc
        left
        apply Nat.isDigit_of_mem_toDigits _ _ hc <;> omega
      · -- ¬ ['_', '_'] <:+: list
        intro ⟨s, t, ht⟩
        have hmem : '_' ∈ ('0' :: '0' :: '0' :: Nat.toDigits 10 (d.natAbs % 10000)) := by
          rw [← ht]; simp [List.mem_append, List.mem_cons]
        simp [List.mem_cons] at hmem
      · -- getLast? ≠ some '_'
        intro h
        have hne : ('0' :: Nat.toDigits 10 (d.natAbs % 10000)) ≠ [] := List.cons_ne_nil _ _
        rw [List.getLast?_eq_some_getLast hne] at h
        have hmem := List.getLast_mem hne
        injection h with h; rw [h] at hmem
        simp [List.mem_cons] at hmem
    · split
      · -- "00" ++ toString n, 10 ≤ n < 100
        rename_i h2 h1
        rw [hno_us "00" _ (by simp)]
        simp [String.toNat?, String.Slice.toNat?]
        simp[toDigits_foldl_roundtrip _]
        simp [String.isNat_iff]; refine ⟨?_, ?_, ?_⟩
        · intro c hc;
          left
          apply Nat.isDigit_of_mem_toDigits _ _ hc <;> omega
        · intro ⟨s, t, ht⟩
          have : '_' ∈ ('0' :: '0' :: Nat.toDigits 10 (d.natAbs % 10000)) := by
            rw [← ht]; simp [List.mem_append, List.mem_cons]
          simp [List.mem_cons] at this
        · intro h
          have hne : ('0' :: Nat.toDigits 10 (d.natAbs % 10000)) ≠ [] := List.cons_ne_nil _ _
          rw [List.getLast?_eq_some_getLast hne] at h
          have hmem := List.getLast_mem hne
          injection h with h; rw [h] at hmem
          simp [List.mem_cons] at hmem
      · split
        · -- "0" ++ toString n, 100 ≤ n < 1000
          rename_i h3 h2 h1
          rw [hno_us "0" _ (by simp)]
          simp [String.toNat?, String.Slice.toNat?]
          simp [toDigits_foldl_roundtrip _]
          simp [String.isNat_iff]; refine ⟨?_, ?_, ?_⟩
          · intro c hc
            left
            apply Nat.isDigit_of_mem_toDigits _ _ hc <;> omega
          · intro ⟨s, t, ht⟩
            have : '_' ∈ ('0' :: Nat.toDigits 10 (d.natAbs % 10000)) := by
              rw [← ht]; simp [List.mem_append, List.mem_cons]
            simp [List.mem_cons] at this
          · intro h
            have hne : ('0' :: Nat.toDigits 10 (d.natAbs % 10000)) ≠ [] := List.cons_ne_nil _ _
            rw [List.getLast?_eq_some_getLast hne] at h
            have hmem := List.getLast_mem hne
            injection h with h; rw [h] at hmem
            simp [List.mem_cons] at hmem
        · -- toString n, 1000 ≤ n < 10000
          rename_i h3 h2 h1
          have hc : (toString (d.natAbs % Nat.pow 10 4)).contains '_' = false := by
            have h := hno_us "" (d.natAbs % Nat.pow 10 4) (by simp)
            rwa [String.empty_append] at h
          simp only [hc]
          simp [String.toNat?, String.Slice.toNat?]
          exact toDigits_foldl_roundtrip _
  · -- (!leftPart.startsWith "-") = !(d < 0)
    simp [leftPart]
    by_cases hd : d < 0
    · simp [hd]
    · simp [hd]
      intro h
      have hmem : '-' ∈ Nat.toDigits 10 (d.natAbs / 10000) :=
        List.IsPrefix.subset h (List.Mem.head _)
      exact absurd (Nat.isDigit_of_mem_toDigits (by omega) (by omega) hmem) (by decide)

/-- The string produced by `toString d` is well-formed for parsing. -/
theorem toString_isWfStr (d : Decimal) : IsWfStr (toString d) := by
  obtain ⟨h_split, h_rlen, h_lint, h_rnat, _⟩ := toString_split d
  refine ⟨_, _, h_split, ?_, ?_, ?_, ?_, ?_⟩
  · -- leftPart ≠ "-"
    intro h; by_cases hd : d < 0
    · simp [hd] at h
    · simp [hd] at h
      have hdigits : ∀ c ∈ (d.natAbs / 10000).repr.toList, c.isDigit = true := by
        intro c hc
        have hc' : c ∈ Nat.toDigits 10 (d.natAbs / 10000) := by
          rwa [Nat.repr_eq_ofList_toDigits, String.toList_ofList] at hc
        exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc'
      rw [h] at hdigits; exact absurd (hdigits '-' (by simp)) (by decide)
  · -- 0 < rightPart.length
    rw [h_rlen]; omega
  · -- rightPart.length ≤ DECIMAL_DIGITS
    rw [h_rlen]; simp [DECIMAL_DIGITS]
  · -- (toInt?' leftPart).isSome
    rw [h_lint]; simp
  · -- (toNat?' rightPart).isSome
    rw [h_rnat]; simp

/-- If a string is well-formed, `parse` succeeds and reconstructs the value. -/
theorem parse_of_isWfStr (s : String) (d : Decimal)
    (hwf : IsWfStr s) (hval : computeValue s = d.toInt) :
    Decimal.parse s = some d := by
  obtain ⟨left, right, h_split, h_ne, h_rpos, h_rle, h_lint, h_rnat⟩ := hwf
  unfold Decimal.parse
  rw [h_split]
  split
  · rename_i heq; exact absurd ((List.cons.inj heq).1) h_ne
  · rename_i _ _ _ heq; simp at heq; obtain ⟨hl', hr'⟩ := heq; subst hl'; subst hr'
    simp only [show 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS from ⟨h_rpos, h_rle⟩]
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h_lint
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_rnat
    simp only [hl, hr, Decimal.decimal?]
    have hval' : (if !left.startsWith "-"
        then l * Int.pow 10 DECIMAL_DIGITS + ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length)
        else l * Int.pow 10 DECIMAL_DIGITS - ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length))
        = d.toInt := by
      simpa only [computeValue, h_split, hl, hr] using hval
    rw [hval']
    exact Int64.ofInt?_toInt d
  · rename_i h; exact (h left right rfl).elim

/-- The `computeValue` of `toString d` equals `d.toInt`. -/
theorem computeValue_toString (d : Decimal) : computeValue (toString d) = d.toInt := by
  obtain ⟨h_split, h_rlen, h_lint, h_rnat, h_starts⟩ := toString_split d
  simp only [computeValue, h_split, h_lint, h_rnat, h_rlen, h_starts, DECIMAL_DIGITS]
  simp only [show Nat.pow 10 4 = 10000 from rfl, show (4 : Nat) - 4 = 0 from rfl,
    show Int.pow 10 4 = (10000 : Int) from rfl,
    show Int.pow 10 0 = (1 : Int) from rfl, Int.mul_one]
  simp (config := { decide := true }) only [Int64.natAbs]
  by_cases hd : d < 0
  · simp only [hd, ↓reduceIte, decide_true, Bool.not_true, Bool.false_eq_true]
    -- Goal: -↑(n/10000) * 10000 - ↑(n%10000) = d.toInt
    have h1 := Int.natAbs_eq d.toInt
    have h3 : -(↑(d.toInt.natAbs / 10000) : Int) * 10000 - ↑(d.toInt.natAbs % 10000) =
        -↑d.toInt.natAbs := by
      have := Nat.div_add_mod d.toInt.natAbs 10000; omega
    simp_all
    apply Eq.symm (Int.eq_neg_natAbs_of_nonpos (by
      rw [Int64.lt_def_toInt] at hd
      have : (0 : Int64).toInt = 0 := by rfl
      omega))
  · simp only [hd, ↓reduceIte, decide_false, Bool.not_false]
    have hge : d.toInt ≥ 0 := by
      simp only [Int64.lt_def_toInt] at hd
      have : (0 : Int64).toInt = 0 := by rfl
      omega
    have h3 : (↑(d.toInt.natAbs / 10000) : Int) * 10000 + ↑(d.toInt.natAbs % 10000) =
        ↑d.toInt.natAbs := by
      have := Nat.div_add_mod d.toInt.natAbs 10000; omega
    rw [h3, Int.natAbs_of_nonneg hge]

/-- Roundtrip: `Decimal.parse (toString d) = some d`. -/
theorem parse_toString_roundtrip (d : Decimal) :
    Decimal.parse (toString d) = some d :=
  parse_of_isWfStr (toString d) d (toString_isWfStr d) (computeValue_toString d)

/-- `parse` fails iff the string is malformed or its value overflows `Int64`. -/
theorem parse_eq_none_iff (s : String) :
    Decimal.parse s = none ↔ ¬ IsWfStr s ∨
    computeValue s < Int64.MIN ∨ computeValue s > Int64.MAX := by
  constructor
  · -- → direction: parse s = none implies malformed or overflow
    intro h
    by_cases hwf : IsWfStr s
    · -- s is well-formed, so it must be overflow
      right
      obtain ⟨left, right, h_split, h_ne, h_rpos, h_rle, h_lint, h_rnat⟩ := hwf
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h_lint
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_rnat
      -- parse returned none despite well-formedness → decimal? returned none → overflow
      unfold Decimal.parse at h
      rw [h_split] at h
      simp only [show 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS from ⟨h_rpos, h_rle⟩,
        hl, hr, Decimal.decimal?, ite_true, and_true] at h
      -- h : Int64.ofInt? (if ... then ... + ... else ... - ...) = none
      have hcv : computeValue s = (if !left.startsWith "-"
          then l * Int.pow 10 DECIMAL_DIGITS + ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length)
          else l * Int.pow 10 DECIMAL_DIGITS - ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length)) := by
        simp only [computeValue, h_split, hl, hr]
      rw [hcv]
      exact Int64.ofInt?_none_iff.mpr h
    · left; exact hwf
  · -- ← direction: malformed or overflow implies parse s = none
    intro h
    rcases h with h | h
    · -- ¬ IsWfStr s → parse s = none
      by_contra hne
      have ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
      exact absurd (parse_some_isWfStr s d hd) h
    · -- overflow → parse s = none
      -- If s is not well-formed, parse = none trivially
      by_cases hwf : IsWfStr s
      · -- s is well-formed but overflows
        obtain ⟨left, right, h_split, h_ne, h_rpos, h_rle, h_lint, h_rnat⟩ := hwf
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h_lint
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_rnat
        unfold Decimal.parse
        rw [h_split]
        simp only [show 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS from ⟨h_rpos, h_rle⟩,
          hl, hr, Decimal.decimal?, ite_true, and_true]
        -- Goal: Int64.ofInt? (if ... then ... else ...) = none
        -- We know computeValue s is out of range, and computeValue s = this expression
        have hcv : computeValue s = (if !left.startsWith "-"
            then l * Int.pow 10 DECIMAL_DIGITS + ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length)
            else l * Int.pow 10 DECIMAL_DIGITS - ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length)) := by
          simp only [computeValue, h_split, hl, hr]
        rw [← hcv]
        exact Int64.ofInt?_none_iff.mp h
      · -- s is not well-formed → parse = none (same as the other branch)
        by_contra hne
        have ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
        exact absurd (parse_some_isWfStr s d hd) hwf

where
  parse_some_isWfStr (s : String) (d : Decimal) (h : Decimal.parse s = some d) : IsWfStr s := by
    unfold Decimal.parse at h
    split at h
    · exact absurd h (by simp)
    · rename_i left right h_ne h_split
      split at h
      · rename_i l r heq_l heq_r
        have h_len : 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS := by
          by_contra hc; simp [hc] at h
        exact ⟨left, right, h_split, h_ne, h_len.1, h_len.2,
          by rw [heq_l]; rfl, by rw [heq_r]; rfl⟩
      · simp at h
    · simp at h

end Cedar.Thm.Decimal

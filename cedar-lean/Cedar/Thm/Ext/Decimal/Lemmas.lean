module

public import Cedar.Thm.Ext.Decimal.Grammar

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.Decimal.Grammar
import all Init.Data.Nat.ToString
import all Init.Data.String.Search
import all Init.Data.String.Slice

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

/-- Prepending zero characters to a natural number's string representation does not change
    the value accepted by `toNat?'`. -/
private theorem zeroPad_toNat? (pad : String) (n : Nat)
    (hp : ∀ c ∈ pad.toList, c = '0') :
    toNat?' (pad ++ toString n) = some n := by
  simp only [toNat?']
  have hno_us : (pad ++ toString n).contains '_' = false := by
    have h : ¬ ('_' ∈ (pad ++ toString n).toList) := by
      rw [String.toList_append]
      intro h
      cases List.mem_append.mp h with
      | inl h => exact absurd (hp '_' h) (by decide)
      | inr h =>
        rw [Nat.toString_eq_repr, Nat.toList_repr] at h
        exact Nat.underscore_not_in_toDigits h
    simpa [String.contains] using h
  rw [hno_us]
  simp [String.toNat?, String.Slice.toNat?]
  simp [String.isNat_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc
      cases hc with
      | inl h =>
        left
        rw [hp c h]
        rfl
      | inr h =>
        left
        exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) h
    · intro hsub
      rcases hsub with ⟨s, t, ht⟩
      have hmem : '_' ∈ pad.toList ++ Nat.toDigits 10 n := by
        rw [← ht]
        simp [List.mem_append, List.mem_cons]
      cases List.mem_append.mp hmem with
      | inl h => exact absurd (hp '_' h) (by decide)
      | inr h => exact Nat.underscore_not_in_toDigits h
    · refine ⟨?_, ?_⟩
      · intro hhead
        cases hlist : pad.toList with
        | nil => simp [hlist] at hhead
        | cons c cs =>
          have hc : c = '0' := hp c (by rw [hlist]; exact List.Mem.head _)
          simp [hlist] at hhead
          rw [hhead] at hc
          exact absurd hc (by decide)
      · intro _ hhead
        have hmem : '_' ∈ Nat.toDigits 10 n := by
          cases hlist : Nat.toDigits 10 n with
          | nil => simp [hlist] at hhead
          | cons c cs =>
            simp [hlist] at hhead
            rw [← hhead]
            exact List.Mem.head _
        exact Nat.underscore_not_in_toDigits hmem
    · intro hlast
      have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
      rw [List.getLast?_eq_some_getLast hne] at hlast
      have hmem := List.getLast_mem hne
      injection hlast with hlast
      rw [hlast] at hmem
      exact Nat.underscore_not_in_toDigits hmem
  · have hpad_fold : ∀ l, (∀ c ∈ l, c = '0') →
        List.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - 48)) 0 l = 0 := by
      intro l hz
      induction l with
      | nil => rfl
      | cons c cs ih =>
        have hc : c = '0' := hz c (List.Mem.head _)
        have hcs : ∀ x ∈ cs, x = '0' := fun x hx => hz x (List.Mem.tail _ hx)
        simp [List.foldl, hc, ih hcs]
    rw [hpad_fold pad.toList hp]
    exact toDigits_foldl_roundtrip n

/-- Decomposes `toString d` into its left (integer) and right (fractional) parts, establishing
    their split structure, right-part length, parsability, and sign behavior. -/
private theorem toString_split (d : Decimal) :
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
    simp only [rightPart, rightNat]
    split
    · -- "000" ++ toString n, n < 10
      exact zeroPad_toNat? "000" _ (by simp)
    · split
      · -- "00" ++ toString n, 10 ≤ n < 100
        exact zeroPad_toNat? "00" _ (by simp)
      · split
        · -- "0" ++ toString n, 100 ≤ n < 1000
          exact zeroPad_toNat? "0" _ (by simp)
        · -- toString n, 1000 ≤ n < 10000
          have hpad : ∀ c ∈ ("".toList), c = '0' := by simp
          have hempty : "" ++ toString (d.natAbs % Nat.pow 10 4) =
              toString (d.natAbs % Nat.pow 10 4) := String.empty_append
          rw [← hempty]
          exact zeroPad_toNat? "" (d.natAbs % Nat.pow 10 4) hpad
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

/-- The canonical string representation of a decimal encodes the same integer value. -/
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

end Cedar.Thm.Decimal

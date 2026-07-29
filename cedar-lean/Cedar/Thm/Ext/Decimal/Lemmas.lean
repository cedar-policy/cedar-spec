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

/-! ============================================================================================
    # Grammar ↔ parser bridge lemmas

    `IsWfDecimal` is phrased over the grammar's productions (`IsWfSign`/`IsNatural`/`IsWfFrac`) as
    a rendering `sign ++ natural ++ "." ++ fraction`. `computeValue` strips that outer sign and
    parses the two unsigned fields, while `Decimal.parse` splits first and parses the signed left
    field through `toInt?'`. These lemmas connect the views: the rendering splits back into its
    parts, a digit string is exactly one the stdlib parser accepts, and both value expressions are
    equal on well-formed inputs. They let the soundness/completeness proofs move between the
    grammar view and the parser view.

    The `IsDigits` predicate and its `toNat?'` bridges (`no_underscore_of_isDigits`,
    `isNat_of_isDigits`, `isDigits_of_isNat`, `toNat?'_isSome_of_isDigits`,
    `isDigits_of_toNat?'_isSome`) are shared with the duration grammar and live in
    `Cedar.Thm.Data.String`; the integer-specific lemmas below build on them.
    ============================================================================================ -/

/-- The concatenation of a well-formed `Sign` and `Natural` — the grammar's integer part —
    contains no `'_'`. -/
theorem no_underscore_of_sign_nat {sign natural : String}
    (hs : IsWfSign sign) (hn : IsDigits natural) : (sign ++ natural).contains '_' = false := by
  obtain ⟨_, hnd⟩ := hn
  have hnot : ¬ ('_' ∈ (sign ++ natural).toList) := by
    rw [String.toList_append]; intro hm
    cases List.mem_append.mp hm with
    | inl h => rcases hs with rfl | rfl <;> simp at h
    | inr h => have := hnd '_' h; simp at this
  simpa [String.contains] using hnot

/-- Forward bridge (integer): a well-formed `Sign` followed by a `Natural` parses as an integer. -/
theorem toInt?'_isSome_of_sign_nat {sign natural : String}
    (hs : IsWfSign sign) (hn : IsDigits natural) :
    (toInt?' (sign ++ natural)).isSome = true := by
  unfold toInt?'
  rw [no_underscore_of_sign_nat hs hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (sign ++ natural).toInt?.isSome = (sign ++ natural).isInt from String.isSome_toInt?,
    String.isInt_iff]
  rcases hs with rfl | rfl
  · right; exact ⟨natural, rfl, isNat_of_isDigits hn⟩
  · left; simpa using isNat_of_isDigits hn

/-- Backward bridge (integer): anything `toInt?'` accepts splits into a well-formed `Sign` and
    `Natural`. -/
theorem sign_nat_of_toInt?'_isSome {s : String} (h : (toInt?' s).isSome = true) :
    ∃ sign natural, s = sign ++ natural ∧ IsWfSign sign ∧ IsDigits natural := by
  unfold toInt?' at h
  split at h
  · simp at h
  · rename_i hnc
    rw [Bool.not_eq_true] at hnc
    rw [show s.toInt?.isSome = s.isInt from String.isSome_toInt?, String.isInt_iff] at h
    rcases h with hnat | ⟨t, hst, htnat⟩
    · exact ⟨"", s, by simp, Or.inr rfl, isDigits_of_isNat hnat hnc⟩
    · refine ⟨"-", t, hst, Or.inl rfl, ?_⟩
      have hnct : t.contains '_' = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have ht : '_' ∈ t.toList := by simpa [String.contains] using hc
        have hs : '_' ∈ s.toList := by
          rw [hst, String.toList_append]; exact List.mem_append_right _ ht
        have hcontains : s.contains '_' = true := by simpa [String.contains] using hs
        rw [hcontains] at hnc; simp at hnc
      exact isDigits_of_isNat htnat hnct

/-- A well-formed integer part is never a bare `"-"`: the grammar's `Digit⁺` requires at least one
    digit after the sign. This is what the `left ≠ "-"` side condition asserts explicitly. -/
theorem ne_dash_of_sign_nat {sign natural : String}
    (hs : IsWfSign sign) (hn : IsDigits natural) : sign ++ natural ≠ "-" := by
  obtain ⟨hlen, hdig⟩ := hn
  rcases hs with rfl | rfl
  · intro hEq
    have ht : natural = "" := by
      have hl := congrArg String.length hEq
      simp only [String.length_append] at hl
      have h1 : ("-" : String).length = 1 := by decide
      rw [h1] at hl
      have hz : natural.length = 0 := by omega
      rw [← String.length_toList] at hz
      rw [← String.toList_inj]; simpa using List.eq_nil_of_length_eq_zero hz
    rw [ht] at hlen; simp at hlen
  · intro hEq
    simp only [String.empty_append] at hEq
    subst hEq
    have := hdig '-' (by decide); simp at this

/-- A digit string contains no `'.'` — the separator can only appear where the grammar puts it. -/
theorem no_dot_of_isDigits {s : String} (h : IsDigits s) :
    ∀ c ∈ s.toList, decide (c = '.') = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq; subst c
  have := h.2 '.' hc; simp at this

/-- The grammar's integer part contains no `'.'`. -/
theorem no_dot_of_sign_nat {sign natural : String}
    (hs : IsWfSign sign) (hn : IsDigits natural) :
    ∀ c ∈ (sign ++ natural).toList, decide (c = '.') = false := by
  intro c hc
  rw [String.toList_append] at hc
  cases List.mem_append.mp hc with
  | inl h =>
    rcases hs with rfl | rfl
    · have hc' : c = '-' := by simpa using h
      subst hc'; decide
    · simp at h
  | inr h => exact no_dot_of_isDigits hn c h

/-- Splitting a well-formed rendering on `'.'` recovers the integer part and the fraction: the
    only `'.'` in `sign ++ natural ++ "." ++ fraction` is the separator the grammar writes. -/
theorem splitToList_of_isWfDecimal {sign natural fraction : String}
    (hs : IsWfSign sign) (hn : IsDigits natural) (hf : IsWfFrac fraction) :
    (sign ++ natural ++ "." ++ fraction).splitToList (· = '.') = [sign ++ natural, fraction] :=
  splitToList_eq (sign ++ natural) fraction (· = '.') '.' (by decide)
    (no_dot_of_sign_nat hs hn) (no_dot_of_isDigits hf.1)

private theorem dash_append_front_eq_dash (body : String) :
    ("-" ++ body).front = '-' := by
  simp [String.front_eq, String.front?_eq, String.toList_append]

private theorem dash_append_drop_one_copy (body : String) :
    (("-" ++ body).drop 1).copy = body := by
  apply String.ext
  simp [String.toList_append]

private theorem startsWith_dash_eq_false_of_isDigits {natural : String}
    (hn : IsDigits natural) : natural.startsWith "-" = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  cases hs : natural.toList with
  | nil =>
    have hp := hn.1
    rw [← String.length_toList, hs] at hp
    simp at hp
  | cons c cs =>
    have hc : c.isDigit = true := hn.2 c (by rw [hs]; simp)
    have hceq : c = '-' := by
      have hcopy : natural = String.ofList (c :: cs) := by
        rw [← String.toList_inj, hs, String.toList_ofList]
      rw [hcopy] at h
      simp at h
      exact h.symm
    rw [hceq] at hc
    simp at hc

private theorem front_ne_dash_of_isDigits_append {natural fraction : String}
    (hn : IsDigits natural) : (natural ++ "." ++ fraction).front ≠ '-' := by
  intro h
  cases hs : natural.toList with
  | nil =>
    have hp := hn.1
    rw [← String.length_toList, hs] at hp
    simp at hp
  | cons c cs =>
    have hc : c.isDigit = true := hn.2 c (by rw [hs]; simp)
    have hceq : c = '-' := by
      simpa [String.front_eq, String.front?_eq, String.toList_append, hs] using h
    rw [hceq] at hc
    simp at hc

private theorem toInt?'_eq_some_of_toNat?' {natural : String} {n : Nat}
    (hn : IsDigits natural) (h : toNat?' natural = some n) :
    toInt?' natural = some (n : Int) := by
  unfold toInt?' toNat?' at *
  rw [no_underscore_of_isDigits hn]
  rw [no_underscore_of_isDigits hn] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [String.toInt?, String.Slice.toInt?_eq_some_iff]
  left
  exact ⟨n, by rwa [String.toNat?_toSlice], rfl⟩

private theorem toInt?'_dash_eq_some_of_toNat?' {natural : String} {n : Nat}
    (hn : IsDigits natural) (h : toNat?' natural = some n) :
    toInt?' ("-" ++ natural) = some (-(n : Int)) := by
  unfold toInt?' toNat?' at *
  rw [no_underscore_of_isDigits hn] at h
  have hno : ("-" ++ natural).contains '_' = false :=
    no_underscore_of_sign_nat (Or.inl rfl) hn
  rw [hno]
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [String.toInt?, String.Slice.toInt?_eq_some_iff]
  right
  refine ⟨natural, ?_, n, h, rfl⟩
  rw [String.copy_toSlice]

/-- `IsWfDecimal` restated in the parser-primitive form the parse proofs consume: the rendering
    becomes a split on `'.'`, the digit-string clauses become `(toInt?'/toNat?').isSome`, and
    `left ≠ "-"` / `0 < right.length` fall out of the grammar's `Digit⁺` productions. -/
theorem isWfDecimal_iff {s : String} :
    IsWfDecimal s ↔
      ∃ left right,
        s.splitToList (· = '.') = [left, right] ∧
        left ≠ "-" ∧
        0 < right.length ∧
        right.length ≤ DECIMAL_DIGITS ∧
        (toInt?' left).isSome ∧
        (toNat?' right).isSome := by
  constructor
  · rintro ⟨sign, natural, fraction, rfl, hs, hn, hf⟩
    exact ⟨sign ++ natural, fraction, splitToList_of_isWfDecimal hs hn hf,
      ne_dash_of_sign_nat hs hn, hf.1.1, hf.2,
      toInt?'_isSome_of_sign_nat hs hn, toNat?'_isSome_of_isDigits hf.1⟩
  · rintro ⟨left, right, h_split, _, _, h_rle, h_lint, h_rnat⟩
    obtain ⟨sign, natural, rfl, hs, hn⟩ := sign_nat_of_toInt?'_isSome h_lint
    refine ⟨sign, natural, right, ?_, hs, hn,
      ⟨isDigits_of_toNat?'_isSome h_rnat, h_rle⟩⟩
    have hjoin := join_splitToList h_split
    simp only [String.append_assoc] at hjoin ⊢
    exact hjoin

/-- On a well-formed input, the grammar's outer-sign value equals the parser's expression, which
    reads the sign together with the left field and branches between adding and subtracting the
    fraction. -/
theorem computeValue_eq_parser_value {s left right : String} {l : Int} {r : Nat}
    (hwf : IsWfDecimal s)
    (h_split : s.splitToList (· = '.') = [left, right])
    (hl : toInt?' left = some l) (hr : toNat?' right = some r) :
    computeValue s = some (if !left.startsWith "-"
      then l * Int.pow 10 DECIMAL_DIGITS + r * Int.pow 10 (DECIMAL_DIGITS - right.length)
      else l * Int.pow 10 DECIMAL_DIGITS - r * Int.pow 10 (DECIMAL_DIGITS - right.length)) := by
  obtain ⟨sign, natural, fraction, hs, hsign, hn, hf⟩ := hwf
  have hparts : left = sign ++ natural ∧ right = fraction := by
    have h := h_split
    rw [hs, splitToList_of_isWfDecimal hsign hn hf] at h
    exact ⟨(List.cons.inj h).1.symm, (List.cons.inj (List.cons.inj h).2).1.symm⟩
  rcases hparts with ⟨rfl, rfl⟩
  obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp (toNat?'_isSome_of_isDigits hn)
  have hbody_split :
      (natural ++ "." ++ right).splitToList (· = '.') = [natural, right] :=
    splitToList_eq natural right (· = '.') '.' (by decide)
      (no_dot_of_isDigits hn) (no_dot_of_isDigits hf.1)
  rcases hsign with rfl | rfl
  · have hl' := toInt?'_dash_eq_some_of_toNat?' hn hnat
    rw [hl'] at hl
    injection hl with hl
    subst l
    rw [hs]
    rw [show "-" ++ natural ++ "." ++ right = "-" ++ (natural ++ "." ++ right) by
      simp [String.append_assoc]]
    unfold computeValue
    rw [dash_append_front_eq_dash, if_pos rfl, dash_append_drop_one_copy]
    simp only
    rw [hbody_split]
    simp only
    rw [hnat, hr]
    simp [Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul]
  · simp only [String.empty_append] at hl hs ⊢
    have hl' := toInt?'_eq_some_of_toNat?' hn hnat
    rw [hl'] at hl
    injection hl with hl
    subst l
    rw [hs]
    have hfront := front_ne_dash_of_isDigits_append (fraction := right) hn
    have hstarts := startsWith_dash_eq_false_of_isDigits hn
    unfold computeValue
    rw [if_neg hfront]
    simp only
    rw [hbody_split]
    simp only
    rw [hnat, hr]
    simp [hstarts]

/-- A well-formed string always has a computed value: `computeValue` succeeds because both the
    parser split and numeric primitives succeed. (The converse fails: `computeValue` can succeed
    on strings that violate the `right.length ≤ DECIMAL_DIGITS` bound.) -/
theorem computeValue_isSome_of_isWfDecimal {s : String} (h : IsWfDecimal s) :
    (computeValue s).isSome = true := by
  obtain ⟨left, right, h_split, _, _, _, h_lint, h_rnat⟩ := isWfDecimal_iff.mp h
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h_lint
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_rnat
  rw [computeValue_eq_parser_value h h_split hl hr]
  rfl

/-! ============================================================================================
    # `toString` well-formedness and value
    ============================================================================================ -/

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
public theorem toString_isWfDecimal (d : Decimal) : IsWfDecimal (toString d) := by
  obtain ⟨h_split, h_rlen, h_lint, h_rnat, _⟩ := toString_split d
  refine isWfDecimal_iff.mpr ⟨_, _, h_split, ?_, ?_, ?_, ?_, ?_⟩
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
public theorem computeValue_toString (d : Decimal) : computeValue (toString d) = some d.toInt := by
  obtain ⟨h_split, h_rlen, h_lint, h_rnat, h_starts⟩ := toString_split d
  rw [computeValue_eq_parser_value (toString_isWfDecimal d) h_split h_lint h_rnat]
  simp only [h_rlen, h_starts, DECIMAL_DIGITS, Option.some.injEq]
  simp only [show Nat.pow 10 4 = 10000 from rfl, show (4 : Nat) - 4 = 0 from rfl,
    show Int.pow 10 4 = (10000 : Int) from rfl,
    show Int.pow 10 0 = (1 : Int) from rfl, Int.mul_one]
  simp (config := { decide := true }) only [Int64.natAbs]
  by_cases hd : d < 0
  · simp only [hd, ↓reduceIte, decide_true, Bool.not_true, Bool.false_eq_true]
    have h3 :
        -(↑(d.toInt.natAbs / 10000) : Int) * 10000 + -↑(d.toInt.natAbs % 10000) =
          -↑d.toInt.natAbs := by
      have := Nat.div_add_mod d.toInt.natAbs 10000
      omega
    rw [Int.sub_eq_add_neg, h3]
    exact Eq.symm (Int.eq_neg_natAbs_of_nonpos (by
      rw [Int64.lt_def_toInt] at hd
      have : (0 : Int64).toInt = 0 := by rfl
      omega))
  ·
    simp only [hd, ↓reduceIte, decide_false, Bool.not_false]
    have hge : d.toInt ≥ 0 := by
      simp only [Int64.lt_def_toInt] at hd
      have : (0 : Int64).toInt = 0 := by rfl
      omega
    have h3 :
        (↑(d.toInt.natAbs / 10000) : Int) * 10000 + ↑(d.toInt.natAbs % 10000) =
          ↑d.toInt.natAbs := by
      have := Nat.div_add_mod d.toInt.natAbs 10000
      omega
    rw [h3, Int.natAbs_of_nonneg hge]

end Cedar.Thm.Decimal

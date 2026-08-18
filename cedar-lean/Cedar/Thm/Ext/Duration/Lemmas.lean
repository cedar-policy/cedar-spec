module

public import Cedar.Thm.Ext.Duration.Grammar

import all Cedar.Thm.Ext.Duration.Grammar
import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Datetime
import all Init.Data.String.Search
import Std.Data.String.ToNat

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-! ============================================================================================
    # Duration parser lemmas

    Duration quantity tokens are the `Digit⁺` strings characterized by `IsDigits`; the
    `IsDigits.ne_empty` / `IsDigits.toNat?'_isSome` / `IsDigits.all_isDigit` projections (in
    `Cedar.Thm.Data.String`) recover the facts these proofs consume.
    ============================================================================================ -/

/-- Total mirror of `extractTrailingQuantity`: the value-side payload it *would* carry, using
    `getD 0` in the (unreachable-on-well-formed-input) parse-failure slot. This lets the internal
    digit-extraction machinery keep reasoning with `.1`/`.2` projections while the public
    `extractTrailingQuantity` remains genuinely `Option`-valued. -/
private def extractPair (s suffix : String) : Nat × String :=
  if s.endsWith suffix then
    let rest := (s.dropEnd suffix.length).toString
    let digits := rest.toList.reverse.takeWhile Char.isDigit |>.reverse
    ((toNat?' (String.ofList digits)).getD 0, (rest.dropEnd digits.length).toString)
  else
    (0, s)

/-- When `extractTrailingQuantity` succeeds, its payload is exactly `extractPair`. -/
private theorem extractPair_eq_of_some (s suffix : String) (p : Nat × String)
    (h : extractTrailingQuantity s suffix = some p) : p = extractPair s suffix := by
  unfold extractTrailingQuantity at h
  unfold extractPair
  by_cases hew : s.endsWith suffix
  · simp only [hew, if_true] at h ⊢
    cases hn : toNat?' (String.ofList
        ((List.takeWhile Char.isDigit (s.dropEnd suffix.length).toString.toList.reverse).reverse)) with
    | none => rw [hn] at h; simp at h
    | some n => rw [hn] at h; simp only [Option.getD_some]; exact (Option.some.inj h).symm
  · simp only [hew] at h ⊢
    exact (Option.some.inj h).symm

/-- When the suffix is absent, `extractTrailingQuantity` passes through as `some (0, s)`. -/
private theorem extract_absent_some (s suffix : String) (h : s.endsWith suffix = false) :
    extractTrailingQuantity s suffix = some (0, s) := by
  unfold extractTrailingQuantity; simp [h]

/-- Total mirror of `computeBodyValue` built on `extractPair` (definitionally the pre-`Option`
    `computeBodyValue`). On well-formed input this coincides with `computeBodyValue`'s payload. -/
private def computeBodyValueD (body : String) : Int :=
  let (ms, body) := extractPair body "ms"
  let (sec, body) := extractPair body "s"
  let (mn, body) := extractPair body "m"
  let (hr, body) := extractPair body "h"
  let (day, _) := extractPair body "d"
  ↑day * MILLISECONDS_PER_DAY + ↑hr * MILLISECONDS_PER_HOUR +
  ↑mn * MILLISECONDS_PER_MINUTE + ↑sec * MILLISECONDS_PER_SECOND + ↑ms

/-- Total mirror of `computeSignedBodyValue`. -/
private def computeSignedBodyValueD (isNegative : Bool) (body : String) : Int :=
  let value := computeBodyValueD body
  if isNegative then -value else value

/-- When all five extract steps succeed, `computeBodyValue` yields the summed value. -/
private theorem computeBodyValue_of_extracts (body r1 r2 r3 r4 : String)
    (n_ms n_s n_m n_h n_d : Nat)
    (e1 : extractTrailingQuantity body "ms" = some (n_ms, r1))
    (e2 : extractTrailingQuantity r1 "s" = some (n_s, r2))
    (e3 : extractTrailingQuantity r2 "m" = some (n_m, r3))
    (e4 : extractTrailingQuantity r3 "h" = some (n_h, r4))
    (e5 : extractTrailingQuantity r4 "d" = some (n_d, "")) :
    computeBodyValue body = some (↑n_d * MILLISECONDS_PER_DAY + ↑n_h * MILLISECONDS_PER_HOUR +
      ↑n_m * MILLISECONDS_PER_MINUTE + ↑n_s * MILLISECONDS_PER_SECOND + ↑n_ms) := by
  unfold computeBodyValue
  simp only [e1, e2, e3, e4, e5, Option.bind_some, bind]

/-- `computeBodyValueD` yields the summed value when all five extract steps succeed. -/
private theorem computeBodyValueD_of_extracts (body r1 r2 r3 r4 : String)
    (n_ms n_s n_m n_h n_d : Nat)
    (e1 : extractTrailingQuantity body "ms" = some (n_ms, r1))
    (e2 : extractTrailingQuantity r1 "s" = some (n_s, r2))
    (e3 : extractTrailingQuantity r2 "m" = some (n_m, r3))
    (e4 : extractTrailingQuantity r3 "h" = some (n_h, r4))
    (e5 : extractTrailingQuantity r4 "d" = some (n_d, "")) :
    computeBodyValueD body = ↑n_d * MILLISECONDS_PER_DAY + ↑n_h * MILLISECONDS_PER_HOUR +
      ↑n_m * MILLISECONDS_PER_MINUTE + ↑n_s * MILLISECONDS_PER_SECOND + ↑n_ms := by
  unfold computeBodyValueD
  rw [(extractPair_eq_of_some body "ms" _ e1).symm]; simp only
  rw [(extractPair_eq_of_some r1 "s" _ e2).symm]; simp only
  rw [(extractPair_eq_of_some r2 "m" _ e3).symm]; simp only
  rw [(extractPair_eq_of_some r3 "h" _ e4).symm]; simp only
  rw [(extractPair_eq_of_some r4 "d" _ e5).symm]

/-- `duration?` fails exactly when the value lies outside the Int64 range. -/
theorem duration?_eq_none_iff_overflow (value : Int) :
    duration? value = none ↔ value < Int64.MIN ∨ value > Int64.MAX := by
  have hopt : duration? value = none ↔ Int64.ofInt? value = none := by
    unfold duration?
    cases Int64.ofInt? value <;> simp
  exact hopt.trans (Int64.ofInt?_none_iff (i := value)).symm

-- Normalized variant of parseUnit? using .toString instead of .copy, easier to reason about.
private def parseUnit?_norm (isNeg : Bool) (str suffix : String) : Option (Int × String) :=
  if str.endsWith suffix
  then
    let rest := (str.dropEnd suffix.length).toString
    let digits := (rest.toList.reverse.takeWhile Char.isDigit).reverse
    if digits.isEmpty
    then none
    else do
      let nUnsignedUnits ← toNat?' (String.ofList digits)
      let units ← if isNeg
        then durationUnits? (Int.negOfNat nUnsignedUnits) suffix
        else durationUnits? (Int.ofNat nUnsignedUnits) suffix
      some (units, (rest.dropEnd digits.length).toString)
  else
    some (0, str)

private theorem parseUnit?_eq_norm (isNeg : Bool) (str suffix : String) :
    parseUnit? isNeg str suffix = parseUnit?_norm isNeg str suffix := by
  unfold parseUnit? parseUnit?_norm
  split
  · have h₁ : (str.dropEnd suffix.length).copy.toList =
        (str.dropEnd suffix.length).toString.toList := by
      congr 1
    have h₂ : ∀ m : Nat, ((str.dropEnd suffix.length).dropEnd m).copy =
        ((str.dropEnd suffix.length).toString.dropEnd m).toString := by
      intro m; apply String.ext; simp
    simp only [h₁, h₂]
  · rfl

-- parseUnit? passes through (returns some (0, s)) when the suffix is not found.
private theorem parseUnit?_no_endsWith (isNeg : Bool) (s suffix : String)
    (h : s.endsWith suffix = false) :
    parseUnit? isNeg s suffix = some (0, s) := by
  rw [parseUnit?_eq_norm]; unfold parseUnit?_norm; simp [h]

/-- When parseUnit? succeeds, the returned rest equals `extractPair`'s rest (the total mirror of
    `extractTrailingQuantity`). Both functions use the same endsWith/dropEnd/takeWhile/toNat?'
    pattern, so the rests agree regardless of well-formedness. -/
private theorem parseUnit?_success_rest (isNeg : Bool) (s suffix : String)
    (v : Int) (rest : String)
    (h : parseUnit? isNeg s suffix = some (v, rest)) :
    rest = (extractPair s suffix).2 := by
  rw [parseUnit?_eq_norm] at h
  unfold parseUnit?_norm at h
  unfold extractPair
  cases h_endsWith : s.endsWith suffix with
  | false =>
    simp only [h_endsWith, Bool.false_eq_true, ite_false] at h ⊢
    have := Option.some.inj h
    exact (Prod.mk.inj this).2.symm
  | true =>
    simp only [h_endsWith, ite_true] at h ⊢
    revert h
    simp only [bind, Option.bind]
    cases (toNat?' (String.ofList ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
        Char.isDigit |>.reverse))) with
    | none => simp
    | some n =>
      cases isNeg with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        cases (durationUnits? (Int.ofNat n) suffix) with
        | none => simp
        | some u =>
          intro h; simp at h
          rw [h.2.2.symm]; apply String.ext; simp
      | true =>
        simp only [ite_true]
        cases (durationUnits? (Int.negOfNat n) suffix) with
        | none => simp
        | some u =>
          intro h; simp at h
          rw [h.2.2.symm]; apply String.ext; simp

/-- If `extractTrailingQuantity` fails, `parseUnit?` also fails: both are driven by the same
    `endsWith`/`toNat?'` failure conditions. -/
private theorem parseUnit?_none_of_extract_none (isNeg : Bool) (s suffix : String)
    (h : extractTrailingQuantity s suffix = none) :
    parseUnit? isNeg s suffix = none := by
  rw [parseUnit?_eq_norm]
  unfold parseUnit?_norm
  unfold extractTrailingQuantity at h
  by_cases hew : s.endsWith suffix
  · simp only [hew, if_true] at h ⊢
    cases hn : toNat?' (String.ofList
        ((List.takeWhile Char.isDigit (s.dropEnd suffix.length).toString.toList.reverse).reverse)) with
    | none =>
      by_cases hemp : ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse.isEmpty
      · simp
      · simp only [hemp, Bool.false_eq_true, ite_false, bind, Option.bind]
    | some n => rw [hn] at h; simp at h
  · simp only [hew] at h; simp at h

/-- When parseUnit? succeeds, `extractTrailingQuantity` also succeeds, returning `extractPair`. -/
private theorem extract_eq_some_of_parseUnit? (isNeg : Bool) (s suffix : String)
    (v : Int) (rest : String) (h : parseUnit? isNeg s suffix = some (v, rest)) :
    extractTrailingQuantity s suffix = some (extractPair s suffix) := by
  cases hx : extractTrailingQuantity s suffix with
  | none => rw [parseUnit?_none_of_extract_none isNeg s suffix hx] at h; simp at h
  | some p => rw [extractPair_eq_of_some s suffix p hx]

/-- When parseUnit? succeeds, `extractTrailingQuantity` also succeeds on the same input, with the
    identical `rest`. This is the bridge from the spec's parser to the value-side extractor. -/
private theorem parseUnit?_extract_some (isNeg : Bool) (s suffix : String) (v : Int) (rest : String)
    (h : parseUnit? isNeg s suffix = some (v, rest)) :
    ∃ n, extractTrailingQuantity s suffix = some (n, rest) := by
  have hrest := parseUnit?_success_rest isNeg s suffix v rest h
  refine ⟨(extractPair s suffix).1, ?_⟩
  rw [extract_eq_some_of_parseUnit? isNeg s suffix v rest h, hrest]

-- ═══════════════════════════════════════════════════════════════════════════════
-- String-level lemmas about IsDigits and suffix interactions
-- ═══════════════════════════════════════════════════════════════════════════════

-- Reconstruct a string starting with '-' from its drop-1.
private theorem string_eq_dash_append_drop_one_of_front_eq_dash (str : String)
    (hfront : str.front = '-') :
    str = "-" ++ (str.drop 1).copy := by
  apply String.ext
  simp [String.front_eq, String.front?_eq] at hfront
  cases hs : str.toList with
  | nil => simp [hs] at hfront
  | cons c cs =>
    simp [hs] at hfront
    subst c
    simp [String.toList_append, hs]

private theorem dash_append_front_eq_dash (body : String) :
    ("-" ++ body).front = '-' := by
  simp [String.front_eq, String.front?_eq, String.toList_append]

private theorem dash_append_drop_one_copy (body : String) :
    (("-" ++ body).drop 1).copy = body := by
  apply String.ext
  simp [String.toList_append]

-- If toNat?' succeeds, the first char is not '-' (it must be a digit).
private theorem toNat?'_some_front_ne_dash (digits : String) (n : Nat)
    (h : toNat?' digits = some n) :
    digits.front ≠ '-' := by
  unfold toNat?' at h
  split at h
  · simp at h
  · have hisNat : digits.isNat = true := String.isNat_of_toNat?_eq_some h
    rw [String.isNat_iff] at hisNat
    obtain ⟨_, hall, _, _, _⟩ := hisNat
    intro hfront
    simp [String.front_eq, String.front?_eq] at hfront
    cases hs : digits.toList with
    | nil => simp [hs] at hfront
    | cons c cs =>
      simp [hs] at hfront
      subst c
      have hd : '-'.isDigit = true ∨ '-' = '_' := hall '-' (by simp [hs])
      rcases hd with hdigit | hund
      · simp [Char.isDigit] at hdigit
      · contradiction

private theorem duration_quantity_front_ne_dash (digits : String)
    (h : IsDigits digits) :
    digits.front ≠ '-' := by
  obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp h.toNat?'_isSome
  exact toNat?'_some_front_ne_dash digits n hnat

private theorem front_append_of_ne_empty (s t : String) (h : s ≠ "") :
    (s ++ t).front = s.front := by
  simp [String.front_eq, String.front?_eq, String.toList_append]
  cases hs : s.toList with
  | nil => exact absurd (by ext; simp [hs]) h
  | cons _ _ => simp

-- A well-formed duration body cannot start with '-'.
theorem duration_body_front_ne_dash (body : String)
    (h : IsWfBody body) :
    body.front ≠ '-' := by
  obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, hne, hwf, hbody⟩ := h
  subst hbody
  simp only [Components.asString, Components.nonempty,
    Components.quantitiesWf, IsWfOptionalQuantity] at hne hwf ⊢
  obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf
  rcases days with _ | d
  · rcases hours with _ | hr
    · rcases minutes with _ | m
      · rcases seconds with _ | s
        · rcases milliseconds with _ | ms
          · simp at hne
          · simp only [durationChunk, String.empty_append]
            rw [front_append_of_ne_empty ms _ hwf_ms.ne_empty]
            exact duration_quantity_front_ne_dash ms hwf_ms
        · simp only [durationChunk, String.empty_append, String.append_assoc]
          rw [front_append_of_ne_empty s _ hwf_s.ne_empty]
          exact duration_quantity_front_ne_dash s hwf_s
      · simp only [durationChunk, String.empty_append, String.append_assoc]
        rw [front_append_of_ne_empty m _ hwf_m.ne_empty]
        exact duration_quantity_front_ne_dash m hwf_m
    · simp only [durationChunk, String.empty_append, String.append_assoc]
      rw [front_append_of_ne_empty hr _ hwf_h.ne_empty]
      exact duration_quantity_front_ne_dash hr hwf_h
  · simp only [durationChunk, String.append_assoc]
    rw [front_append_of_ne_empty d _ hwf_d.ne_empty]
    exact duration_quantity_front_ne_dash d hwf_d

-- All characters in a duration-quantity string are digits.
private theorem allDigit_of_isDurationQuantity (d : String)
    (h : IsDigits d) :
    ∀ c ∈ d.toList, Char.isDigit c = true := h.all_isDigit

-- ═══════════════════════════════════════════════════════════════════════════════
-- Main theorem 1: parseDuration? on well-formed input
-- ═══════════════════════════════════════════════════════════════════════════════

-- A well-formed duration body is always non-empty (it must have at least one component).
private theorem body_ne_empty_of_wf (body : String) (h : IsWfBody body) :
    body ≠ "" := by
  obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, hne, _, hbody⟩ := h
  subst hbody
  simp only [Components.asString, Components.nonempty] at hne ⊢
  rcases days with _ | d <;> rcases hours with _ | hr <;> rcases minutes with _ | m <;>
    rcases seconds with _ | s <;> rcases milliseconds with _ | ms <;> simp_all [durationChunk]

-- When parseUnit? succeeds and endsWith holds, extract returns the same Nat used internally.
private theorem parseUnit?_some_endsWith_value (isNeg : Bool) (s suffix : String)
    (v : Int) (rest : String)
    (h : parseUnit? isNeg s suffix = some (v, rest))
    (hew : s.endsWith suffix = true) :
    ∃ n, (extractPair s suffix).1 = n ∧
      durationUnits? (signedQuantity isNeg n) suffix = some v := by
  rw [parseUnit?_eq_norm] at h; unfold parseUnit?_norm at h
  simp only [hew, ite_true] at h
  generalize hdig : ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
      Char.isDigit).reverse = digs at h
  cases hdne : digs.isEmpty with
  | true => simp [hdne] at h
  | false =>
    simp only [hdne, Bool.false_eq_true, ite_false, bind, Option.bind] at h
    cases hnat : toNat?' (String.ofList digs) with
    | none => simp [hnat] at h
    | some n =>
      simp only [hnat] at h
      have h_ext : (extractPair s suffix).1 = n := by
        unfold extractPair
        simp only [hew, ite_true]
        rw [show ((s.dropEnd ↑suffix.length).toString.toList.reverse.takeWhile Char.isDigit).reverse
            = digs from hdig]
        simp [hnat]
      refine ⟨n, h_ext, ?_⟩
      unfold signedQuantity
      cases isNeg with
      | false =>
        simp only [Bool.false_eq_true, ite_false] at h ⊢
        cases hdu : durationUnits? (Int.ofNat n) suffix with
        | none => rw [hdu] at h; simp at h
        | some u => rw [hdu] at h; simp at h; rw [← h.1]
      | true =>
        simp only [ite_true] at h ⊢
        cases hdu : durationUnits? (Int.negOfNat n) suffix with
        | none => rw [hdu] at h; simp at h
        | some u => rw [hdu] at h; simp at h; rw [← h.1]

-- ═══════════════════════════════════════════════════════════════════════════════
-- Main theorem 2: parseDuration? on non-well-formed input
-- ═══════════════════════════════════════════════════════════════════════════════

-- The digit string extracted by parseUnit? when the suffix was present.
private def digitStr_of_parseUnit? (str suffix : String) : Option String :=
  if str.endsWith suffix then
    let rest := (str.dropEnd suffix.length).toString
    let digits := (rest.toList.reverse.takeWhile Char.isDigit).reverse
    if digits.isEmpty then none
    else some (String.ofList digits)
  else none

-- When parseUnit? succeeds and the suffix was present, digitStr gives a valid IsDigits.
private theorem isDurationQuantity_of_parseUnit?_endsWith (isNeg : Bool) (str suffix : String)
    (v : Int) (rest : String)
    (h : parseUnit? isNeg str suffix = some (v, rest))
    (h_endsWith : str.endsWith suffix = true) :
    ∃ digits, digitStr_of_parseUnit? str suffix = some digits ∧ IsDigits digits := by
  unfold parseUnit? at h
  simp only [h_endsWith, ite_true] at h
  unfold digitStr_of_parseUnit?
  simp only [h_endsWith, ite_true]
  -- Relate .copy to .toString so both computations share the same digit list.
  have hcopy_eq : (str.dropEnd suffix.length).copy.toList =
      (str.dropEnd suffix.length).toString.toList := by
    congr 1
  rw [hcopy_eq] at h
  generalize hd : ((str.dropEnd suffix.length).toString.toList.reverse.takeWhile
      Char.isDigit).reverse = digs at h
  cases hdne : digs.isEmpty
  · simp only [hdne, Bool.false_eq_true, ite_false, bind, Option.bind] at h
    cases hnat : toNat?' (String.ofList digs) with
    | none => simp [hnat] at h
    | some n =>
      refine ⟨String.ofList digs, ?_, ?_⟩
      · simp
      · exact isDigits_of_toNat?'_isSome (by simp [hnat])
  · simp [hdne] at h

-- Reconstruct Components from a body string by peeling each suffix in turn.
private def reconstructComponents (body : String) : Components :=
  let (_, rest₁) := extractPair body "ms"
  let (_, rest₂) := extractPair rest₁ "s"
  let (_, rest₃) := extractPair rest₂ "m"
  let (_, rest₄) := extractPair rest₃ "h"
  { days := digitStr_of_parseUnit? rest₄ "d"
    hours := digitStr_of_parseUnit? rest₃ "h"
    minutes := digitStr_of_parseUnit? rest₂ "m"
    seconds := digitStr_of_parseUnit? rest₁ "s"
    milliseconds := digitStr_of_parseUnit? body "ms" }

-- When the suffix is not found, parseUnit? passes through: v = 0 and rest = str.
private theorem parseUnit?_passthrough (isNeg : Bool) (str suffix : String)
    (v : Int) (rest : String)
    (h : parseUnit? isNeg str suffix = some (v, rest))
    (h_not_endsWith : str.endsWith suffix = false) :
    v = 0 ∧ rest = str := by
  unfold parseUnit? at h; simp [h_not_endsWith] at h; exact ⟨h.1.symm, h.2.symm⟩

-- Stripping a suffix via dropEnd then re-appending gives back the original.
private theorem dropEnd_append_endsWith (str suffix : String)
    (h : str.endsWith suffix = true) :
    (str.dropEnd suffix.length).toString ++ suffix = str := by
  apply String.ext
  simp [String.toList_append, ← String.length_toList, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice] at *
  obtain ⟨pfx, hpfx⟩ := h; rw [← hpfx]; simp

-- dropEnd n then append the dropped tail gives back the original.
private theorem dropEnd_append_drop (s : String) (n : Nat) :
    (s.dropEnd n).toString ++ String.ofList (s.toList.drop (s.toList.length - n)) = s := by
  apply String.ext; simp [String.toList_append]

-- A list equals its (dropWhile p).reverse ++ (takeWhile p).reverse when taken from the reversed list.
private theorem list_takeWhile_decompose (l : List α) (p : α → Bool) :
    l = (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse := by
  suffices h : (l.reverse.dropWhile p).reverse ++ (l.reverse.takeWhile p).reverse = l by
    exact h.symm
  rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]

/-- Core reconstruction step: when `parseUnit?` succeeds, the input string equals the
    extract-rest concatenated with the reconstructed chunk. This is the key infrastructure for
    showing that the 5-step parse chain fully reconstructs the duration body. -/
private theorem extract_reconstruct_step (isNeg : Bool) (s suffix : String) (v : Int) (r : String)
    (hpu : parseUnit? isNeg s suffix = some (v, r)) :
    s = (extractPair s suffix).2 ++
      durationChunk (digitStr_of_parseUnit? s suffix) suffix := by
  unfold extractPair digitStr_of_parseUnit? durationChunk
  have hcopy_eq : (s.dropEnd suffix.length).copy.toList =
      (s.dropEnd suffix.length).toString.toList := by
    congr 1
  by_cases hew : s.endsWith suffix = true
  · simp only [hew, ite_true]
    have hpu' := hpu
    unfold parseUnit? at hpu'
    simp only [hew, ite_true] at hpu'
    rw [hcopy_eq] at hpu'
    generalize hdig : ((s.dropEnd suffix.length).toString.toList.reverse.takeWhile
        Char.isDigit).reverse = digs at hpu'
    cases hdne : digs.isEmpty
    · simp only [hdne, Bool.false_eq_true, ite_false, bind, Option.bind] at hpu'
      cases hnat : toNat?' (String.ofList digs) with
      | none => simp [hnat] at hpu'
      | some n =>
        simp only [show (false = true) = False from by simp, ite_false]
        apply String.ext
        simp only [String.toList_append, String.toList_ofList, ← String.length_toList]
        have hew_suffix : suffix.toList <:+ s.toList := by
          simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice] at hew; exact hew
        obtain ⟨mid, hmid_eq⟩ := hew_suffix
        have hmid_is_take : mid = List.take (s.toList.length - suffix.toList.length) s.toList := by
          rw [← hmid_eq]; simp
        have hmid_decomp := list_takeWhile_decompose mid Char.isDigit
        rw [hmid_is_take] at hmid_decomp
        rw [← hmid_eq, hmid_is_take, hmid_decomp]
        have hdig' : (List.takeWhile Char.isDigit
            (List.take (s.toList.length - suffix.toList.length) s.toList).reverse).reverse = digs := by
          simp [← String.length_toList] at hdig; exact hdig
        rw [hdig', List.append_assoc]
        congr 1
        have hrhs_simp : ((s.dropEnd suffix.toList.length).toString.dropEnd digs.length).toString.toList =
            List.take ((List.take (s.toList.length - suffix.toList.length) s.toList).length - digs.length)
              (List.take (s.toList.length - suffix.toList.length) s.toList) := by
          simp
        rw [hrhs_simp]
        symm
        have hlen_dw : (List.dropWhile Char.isDigit
            (List.take (s.toList.length - suffix.toList.length) s.toList).reverse).reverse.length =
            (List.take (s.toList.length - suffix.toList.length) s.toList).length - digs.length := by
          have h := congrArg List.length hmid_decomp
          simp only [List.length_append, hdig'] at h; omega
        let dw_rev := (List.dropWhile Char.isDigit
            (List.take (s.toList.length - suffix.toList.length) s.toList).reverse).reverse
        show List.take
            ((List.take (s.toList.length - suffix.toList.length) s.toList).length - digs.length)
            (List.take (s.toList.length - suffix.toList.length) s.toList) = dw_rev
        rw [hlen_dw.symm]
        have hmid_eq2 : List.take (s.toList.length - suffix.toList.length) s.toList = dw_rev ++ digs := by
          rw [hmid_decomp, hdig']
        exact List.take_left (l₁ := dw_rev) (l₂ := digs) ▸ hmid_eq2 ▸ rfl
    · simp [hdne] at hpu'
  · have hew' : s.endsWith suffix = false := by
      cases h : s.endsWith suffix <;> simp_all
    simp [hew']

/-- A successful `parseDuration?` call implies the input body is well-formed.
    Used to prove that `parseDuration?_none_of_not_wf` is the right converse. -/
theorem wf_of_parseDuration?_eq_some (isNeg : Bool) (body : String) (d : Duration)
    (h : parseDuration? isNeg body = some d) :
    IsWfBody body := by
  unfold parseDuration? at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i h_ne
    cases h₁ : parseUnit? isNeg body "ms" with
    | none => simp [h₁] at h
    | some p₁ =>
      obtain ⟨v_ms, rest₁⟩ := p₁; simp only [h₁] at h
      cases h₂ : parseUnit? isNeg rest₁ "s" with
      | none => simp [h₂] at h
      | some p₂ =>
        obtain ⟨v_s, rest₂⟩ := p₂; simp only [h₂] at h
        cases h₃ : parseUnit? isNeg rest₂ "m" with
        | none => simp [h₃] at h
        | some p₃ =>
          obtain ⟨v_m, rest₃⟩ := p₃; simp only [h₃] at h
          cases h₄ : parseUnit? isNeg rest₃ "h" with
          | none => simp [h₄] at h
          | some p₄ =>
            obtain ⟨v_h, rest₄⟩ := p₄; simp only [h₄] at h
            cases h₅ : parseUnit? isNeg rest₄ "d" with
            | none => simp [h₅] at h
            | some p₅ =>
              obtain ⟨v_d, rest₅⟩ := p₅; simp only [h₅] at h
              split at h
              · rename_i h_empty
                have hrest₅_eq : rest₅ = "" := String.isEmpty_iff.mp h_empty
                have hr₁ := parseUnit?_success_rest isNeg body "ms" v_ms rest₁ h₁
                have hr₂ := parseUnit?_success_rest isNeg rest₁ "s" v_s rest₂ h₂
                have hr₃ := parseUnit?_success_rest isNeg rest₂ "m" v_m rest₃ h₃
                have hr₄ := parseUnit?_success_rest isNeg rest₃ "h" v_h rest₄ h₄
                have hr₅ := parseUnit?_success_rest isNeg rest₄ "d" v_d rest₅ h₅
                -- When digitStr_of_parseUnit? = none, parseUnit? must have passed through (rest = input).
                have hpass : ∀ (s suf : String) (isN : Bool) (v' : Int) (r : String),
                    parseUnit? isN s suf = some (v', r) →
                    digitStr_of_parseUnit? s suf = none → r = s := by
                  intro s suf isN v' r hpu hds
                  unfold digitStr_of_parseUnit? at hds
                  split at hds
                  · rename_i hew
                    unfold parseUnit? at hpu
                    simp only [hew, ite_true] at hpu
                    have hcopy_eq : (s.dropEnd suf.length).copy.toList =
                        (s.dropEnd suf.length).toString.toList := by
                      congr 1
                    rw [hcopy_eq] at hpu
                    simp only at hds
                    split at hds <;> split at hpu <;> simp_all
                  · rename_i hew
                    have hew' : s.endsWith suf = false := by
                      cases hb : s.endsWith suf <;> simp_all
                    exact (parseUnit?_passthrough isN s suf v' r hpu hew').2
                refine ⟨reconstructComponents body, ?_, ?_, ?_⟩
                · unfold reconstructComponents Components.nonempty
                  by_contra hall
                  simp only [not_or] at hall
                  obtain ⟨hd, hh, hm, hs, hms⟩ := hall
                  simp only [ne_eq, Decidable.not_not] at hms hs hm hh hd
                  have hp₁ : rest₁ = body := hpass body "ms" isNeg v_ms rest₁ h₁ hms
                  have hp₂ : rest₂ = rest₁ := hpass rest₁ "s" isNeg v_s rest₂ h₂ (by
                    rw [hr₁]; exact hs)
                  have hp₃ : rest₃ = rest₂ := hpass rest₂ "m" isNeg v_m rest₃ h₃ (by
                    show digitStr_of_parseUnit? rest₂ "m" = none
                    rw [hr₂, hr₁]; exact hm)
                  have hp₄ : rest₄ = rest₃ := hpass rest₃ "h" isNeg v_h rest₄ h₄ (by
                    show digitStr_of_parseUnit? rest₃ "h" = none
                    rw [hr₃, hr₂, hr₁]; exact hh)
                  have hp₅ : rest₅ = rest₄ := hpass rest₄ "d" isNeg v_d rest₅ h₅ (by
                    show digitStr_of_parseUnit? rest₄ "d" = none
                    rw [hr₄, hr₃, hr₂, hr₁]; exact hd)
                  -- All 5 steps passed through: rest₅ = body, contradicting rest₅ = "" and body ≠ ""
                  have hbody_eq : body = "" := by
                    rw [← hp₁, ← hp₂, ← hp₃, ← hp₄, ← hp₅]; exact hrest₅_eq
                  simp [hbody_eq] at h_ne
                · have hds_endsWith : ∀ (s suf d : String),
                      digitStr_of_parseUnit? s suf = some d → s.endsWith suf = true := by
                    intro s suf d hds
                    unfold digitStr_of_parseUnit? at hds
                    split at hds
                    · rename_i hew; exact hew
                    · simp at hds
                  have hds_wf : ∀ (s suf : String) (isN : Bool) (v' : Int) (r d : String),
                      parseUnit? isN s suf = some (v', r) →
                      digitStr_of_parseUnit? s suf = some d → IsDigits d := by
                    intro s suf isN v' r d hpu hds
                    have hew := hds_endsWith s suf d hds
                    obtain ⟨d', hd'_eq, hd'_wf⟩ :=
                      isDurationQuantity_of_parseUnit?_endsWith isN s suf v' r hpu hew
                    rw [hd'_eq] at hds
                    exact Option.some.inj hds ▸ hd'_wf
                  unfold reconstructComponents Components.quantitiesWf IsWfOptionalQuantity
                  simp only
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · split
                    · trivial
                    · rename_i d hds
                      exact hds_wf _ _ isNeg v_d rest₅ d (by rw [hr₄, hr₃, hr₂, hr₁] at h₅; exact h₅) hds
                  · split
                    · trivial
                    · rename_i d hds
                      exact hds_wf _ _ isNeg v_h rest₄ d (by rw [hr₃, hr₂, hr₁] at h₄; exact h₄) hds
                  · split
                    · trivial
                    · rename_i d hds
                      exact hds_wf _ _ isNeg v_m rest₃ d (by rw [hr₂, hr₁] at h₃; exact h₃) hds
                  · split
                    · trivial
                    · rename_i d hds
                      exact hds_wf _ _ isNeg v_s rest₂ d (by rw [hr₁] at h₂; exact h₂) hds
                  · split
                    · trivial
                    · rename_i d hds
                      exact hds_wf _ _ isNeg v_ms rest₁ d h₁ hds
                · -- body = (reconstructComponents body).asString:
                  -- chain extract_reconstruct_step for all 5 steps to show full reconstruction.
                  have hs₁ := extract_reconstruct_step isNeg body "ms" v_ms rest₁ h₁
                  have hs₂ := extract_reconstruct_step isNeg rest₁ "s" v_s rest₂ h₂
                  have hs₃ := extract_reconstruct_step isNeg rest₂ "m" v_m rest₃ h₃
                  have hs₄ := extract_reconstruct_step isNeg rest₃ "h" v_h rest₄ h₄
                  have hs₅ := extract_reconstruct_step isNeg rest₄ "d" v_d rest₅ h₅
                  have hrest₅_extract : (extractPair rest₄ "d").2 = "" := by
                    rw [← hr₅]; exact hrest₅_eq
                  symm
                  unfold reconstructComponents Components.asString
                  simp only
                  rw [← hr₁, ← hr₂, ← hr₃, ← hr₄]
                  have hd_eq : durationChunk (digitStr_of_parseUnit? rest₄ "d") "d" = rest₄ := by
                    have := hs₅; rw [hrest₅_extract, String.empty_append] at this; exact this.symm
                  have hh_eq : rest₄ ++ durationChunk (digitStr_of_parseUnit? rest₃ "h") "h" = rest₃ := by
                    have := hs₄; rw [← hr₄] at this; exact this.symm
                  have hm_eq : rest₃ ++ durationChunk (digitStr_of_parseUnit? rest₂ "m") "m" = rest₂ := by
                    have := hs₃; rw [← hr₃] at this; exact this.symm
                  have hs_eq : rest₂ ++ durationChunk (digitStr_of_parseUnit? rest₁ "s") "s" = rest₁ := by
                    have := hs₂; rw [← hr₂] at this; exact this.symm
                  have hms_eq : rest₁ ++ durationChunk (digitStr_of_parseUnit? body "ms") "ms" = body := by
                    have := hs₁; rw [← hr₁] at this; exact this.symm
                  rw [hd_eq, hh_eq, hm_eq, hs_eq, hms_eq]
              · simp at h

-- ═══════════════════════════════════════════════════════════════════════════════
-- Int64 overflow helpers
-- ═══════════════════════════════════════════════════════════════════════════════
private theorem nat_gt_max_of_int64_ofInt?_none_signedQuantity (isNeg : Bool) (n : Nat)
    (h : Int64.ofInt? (signedQuantity isNeg n) = none) :
    n > Int64.MAX := by
  unfold signedQuantity at h
  cases isNeg with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    have hrange := Int64.ofInt?_none_iff.mpr h
    simp only [Int64.MIN, Int64.MAX] at hrange
    rw [Int64.MAX]
    have : (↑n : Int) = Int.ofNat n := rfl; omega
  | true =>
    simp only [ite_true] at h
    have hrange := Int64.ofInt?_none_iff.mpr h
    simp only [Int64.MIN, Int64.MAX] at hrange
    rw [Int64.MAX]
    have : Int.negOfNat n = -(↑n : Int) := by cases n <;> simp [Int.negOfNat, Int.negSucc_eq]
    omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- Helpers for extract_chain_rest_empty_of_wf
-- ═══════════════════════════════════════════════════════════════════════════════

-- takeWhile on an all-true prefix followed by a false-headed or empty tail
private theorem takeWhile_append_stop_chain {l₁ l₂ : List α} {p : α → Bool}
    (h₁ : ∀ x ∈ l₁, p x = true)
    (h₂ : l₂ = [] ∨ ∃ y l₂', l₂ = y :: l₂' ∧ p y = false) :
    List.takeWhile p (l₁ ++ l₂) = l₁ := by
  have htw : List.takeWhile p l₁ = l₁ := by
    induction l₁ with
    | nil => simp
    | cons x xs ih =>
      simp [List.takeWhile, h₁ x (by simp)]
      exact ih (fun y hy => h₁ y (by simp [hy]))
  rw [List.takeWhile_append]; simp [htw]
  rcases h₂ with rfl | ⟨y, l₂', rfl, hy⟩
  · simp
  · simp [List.takeWhile, hy]

/-- Extract on `(pfx ++ digits ++ suffix)` succeeds with `(n, pfx)` when `digits` is `IsDigits`
    and `pfx` is empty or ends with a non-digit char. The `= some (n, pfx)` form directly matches
    how `computeBodyValue`'s `do`-block consumes each step. -/
private theorem extract_step_chain_some (pfx digits suffix : String) (n : Nat)
    (hdq : IsDigits digits)
    (hnat : toNat?' digits = some n)
    (hpfx_end : pfx = "" ∨ ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false) :
    extractTrailingQuantity (pfx ++ digits ++ suffix) suffix = some (n, pfx) := by
  unfold extractTrailingQuantity
  have hew : (pfx ++ digits ++ suffix).endsWith suffix = true := by
    simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append]
    exact ⟨pfx.toList ++ digits.toList, by simp [List.append_assoc]⟩
  simp only [hew, ite_true]
  have hdrop_toList : ((pfx ++ digits ++ suffix).dropEnd suffix.length).toString.toList
      = pfx.toList ++ digits.toList := by
    simp [String.toList_append, ← String.length_toList]
    have h1 : pfx.toList.length + (digits.toList.length + suffix.toList.length) -
        suffix.toList.length = (pfx.toList ++ digits.toList).length := by simp; omega
    rw [h1, show pfx.toList ++ (digits.toList ++ suffix.toList)
        = (pfx.toList ++ digits.toList) ++ suffix.toList from by rw [List.append_assoc]]
    exact List.take_left
  have hall_digits : ∀ c ∈ digits.toList.reverse, Char.isDigit c = true := by
    intro c hc; exact allDigit_of_isDurationQuantity digits hdq c (List.mem_reverse.mp hc)
  have htw : (((pfx ++ digits ++ suffix).dropEnd suffix.length).toString.toList.reverse.takeWhile
      Char.isDigit).reverse = digits.toList := by
    rw [hdrop_toList, List.reverse_append, takeWhile_append_stop_chain hall_digits]
    · exact List.reverse_reverse digits.toList
    rcases hpfx_end with rfl | ⟨c, cs, hrev, hc⟩
    · left; simp
    · right; exact ⟨c, cs, hrev, hc⟩
  rw [htw]
  have hdig_eq : String.ofList digits.toList = digits := by simp
  rw [hdig_eq, hnat]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  apply String.ext
  simp [String.toList_append, ← String.length_toList]
  have h1 : pfx.toList.length + (digits.toList.length + suffix.toList.length) -
      suffix.toList.length - digits.toList.length = pfx.toList.length := by omega
  have h2 : pfx.toList.length + (digits.toList.length + suffix.toList.length) -
      suffix.toList.length = (pfx.toList ++ digits.toList).length := by simp; omega
  rw [h1, h2, show pfx.toList ++ (digits.toList ++ suffix.toList)
      = (pfx.toList ++ digits.toList) ++ suffix.toList from by rw [List.append_assoc]]
  rw [List.take_left, List.take_left]

/-- `extractPair` variant of `extract_step_chain_some`: the total mirror's rest equals `pfx`. -/
private theorem extract_step_chain (pfx digits suffix : String) (n : Nat)
    (hdq : IsDigits digits)
    (hnat : toNat?' digits = some n)
    (hpfx_end : pfx = "" ∨ ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false) :
    (extractPair (pfx ++ digits ++ suffix) suffix).2 = pfx := by
  have h := extract_step_chain_some pfx digits suffix n hdq hnat hpfx_end
  rw [← extractPair_eq_of_some _ _ _ h]

/-- `extractPair` variant of `extract_step_chain_some` at the pair level. -/
private theorem extract_step_chain_pair (pfx digits suffix : String) (n : Nat)
    (hdq : IsDigits digits)
    (hnat : toNat?' digits = some n)
    (hpfx_end : pfx = "" ∨ ∃ c cs, pfx.toList.reverse = c :: cs ∧ c.isDigit = false) :
    extractTrailingQuantity (pfx ++ digits ++ suffix) suffix = some (n, pfx) :=
  extract_step_chain_some pfx digits suffix n hdq hnat hpfx_end

-- The reverse of (digits ++ suffix) starts with a non-digit char for duration suffixes.
private theorem chunk_reverse_starts_non_digit (digits suffix : String)
    (_hdq : IsDigits digits)
    (hsuf : suffix = "d" ∨ suffix = "h" ∨ suffix = "m" ∨ suffix = "s" ∨ suffix = "ms") :
    ∃ c cs, (digits ++ suffix).toList.reverse = c :: cs ∧ c.isDigit = false := by
  rcases hsuf with rfl | rfl | rfl | rfl | rfl <;>
    simp only [String.toList_append, List.reverse_append] <;>
    exact ⟨_, _, rfl, by decide⟩

-- Prefixing preserves the "ends with non-digit" property.
private theorem pfx_append_chunk_reverse_non_digit (pfx digits suffix : String)
    (hdq : IsDigits digits)
    (hsuf : suffix = "d" ∨ suffix = "h" ∨ suffix = "m" ∨ suffix = "s" ∨ suffix = "ms") :
    ∃ c cs, (pfx ++ (digits ++ suffix)).toList.reverse = c :: cs ∧ c.isDigit = false := by
  obtain ⟨c, cs, hrev, hnd⟩ := chunk_reverse_starts_non_digit digits suffix hdq hsuf
  have hrev' : suffix.toList.reverse ++ digits.toList.reverse = c :: cs := by
    simpa [String.toList_append, List.reverse_append] using hrev
  refine ⟨c, cs ++ pfx.toList.reverse, ?_, hnd⟩
  simp only [String.toList_append, List.reverse_append]
  rw [hrev']; simp

-- A string ending with (digits ++ "s") where digits is IsDigits
-- does not endWith "ms" (the char before 's' is a digit, not 'm').
private theorem not_endsWith_ms_of_digits_s_chain (pfx digits : String)
    (hdq : IsDigits digits) :
    (pfx ++ digits ++ "s").endsWith "ms" = false := by
  simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append]
  intro ⟨pre, hpre⟩
  have hne : digits.toList ≠ [] := by intro h; exact hdq.ne_empty (by ext; simp [h])
  have hlen : pre.length + 2 = pfx.toList.length + digits.toList.length + 1 := by
    have h := congrArg List.length hpre
    simp only [List.length_append, List.length_cons, List.length_nil] at h; omega
  have hge : pre.length ≥ pfx.toList.length := by
    have : digits.toList.length ≥ 1 := by
      cases h : digits.toList with | nil => exact absurd h hne | cons _ _ => simp
    omega
  have hlt : pre.length - pfx.toList.length < digits.toList.length := by omega
  have h_eq : (pre ++ ['m', 's'])[pre.length]? =
      (pfx.toList ++ (digits.toList ++ ['s']))[pre.length]? := by rw [hpre]
  have h_lhs : (pre ++ ['m', 's'])[pre.length]? = some 'm' := by simp
  have h_rhs : (pfx.toList ++ (digits.toList ++ ['s']))[pre.length]? =
      some (digits.toList[pre.length - pfx.toList.length]'hlt) := by
    rw [List.getElem?_append_right hge, List.getElem?_append_left hlt, List.getElem?_eq_getElem]
  rw [h_lhs, h_rhs] at h_eq
  have h_m_eq : 'm' = digits.toList[pre.length - pfx.toList.length] := Option.some.inj h_eq
  have h_mem : digits.toList[pre.length - pfx.toList.length]'hlt ∈ digits.toList :=
    List.getElem_mem hlt
  have h_digit := allDigit_of_isDurationQuantity digits hdq _ h_mem
  rw [← h_m_eq] at h_digit
  exact absurd h_digit (by decide)

-- A string whose last char ≠ c does not endWith the single-char string [c].
private theorem not_endsWith_single_of_last_ne (s : String) (c : Char)
    (h : s.toList ≠ [])
    (hlast : s.toList.getLast h ≠ c) :
    s.endsWith (String.ofList [c]) = false := by
  simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
  intro ⟨pre, hpre⟩
  have h_last_c : (pre ++ [c]).getLast (by simp) = c := by simp
  have h_eq_last : s.toList.getLast h = (pre ++ [c]).getLast (by simp) := by
    congr 1; exact hpre.symm
  rw [h_last_c] at h_eq_last
  exact hlast h_eq_last

/-- The 5-step parseUnit? chain on well-formed input fully consumes the body (rest₅ = "").
    On well-formed input, each extractTrailingQuantity step peels exactly one component,
    and after all 5 steps nothing remains. -/
private theorem extract_chain_rest_empty_of_wf (isNeg : Bool) (body : String)
    (h : IsWfBody body)
    (h₁ : parseUnit? isNeg body "ms" = some (v_ms, rest₁))
    (h₂ : parseUnit? isNeg rest₁ "s" = some (v_s, rest₂))
    (h₃ : parseUnit? isNeg rest₂ "m" = some (v_m, rest₃))
    (h₄ : parseUnit? isNeg rest₃ "h" = some (v_h, rest₄))
    (h₅ : parseUnit? isNeg rest₄ "d" = some (v_d, rest₅)) :
    rest₅ = "" := by
  obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, hne_comp, hwf_q, hbody⟩ := h
  simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
  have hr₁ := parseUnit?_success_rest isNeg body "ms" v_ms rest₁ h₁
  have hr₂ := parseUnit?_success_rest isNeg rest₁ "s" v_s rest₂ h₂
  have hr₃ := parseUnit?_success_rest isNeg rest₂ "m" v_m rest₃ h₃
  have hr₄ := parseUnit?_success_rest isNeg rest₃ "h" v_h rest₄ h₄
  have hr₅ := parseUnit?_success_rest isNeg rest₄ "d" v_d rest₅ h₅
  subst hbody
  obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf_q
  -- Step 1: rest₁ = (extract asString "ms").2 = d_chunk ++ h_chunk ++ m_chunk ++ s_chunk
  have hrest₁ : rest₁ = durationChunk days "d" ++ durationChunk hours "h" ++
      durationChunk minutes "m" ++ durationChunk seconds "s" := by
    rw [hr₁]; unfold Components.asString
    cases milliseconds with
    | none =>
      -- Use not_endsWith_ms_of_digits_s_chain for the seconds-present cases,
      -- and simp for the rest (where body doesn't end with 's').
      simp only [durationChunk, String.append_empty]
      unfold extractPair
      have hew : (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m" ++ durationChunk seconds "s").endsWith "ms" = false := by
        cases seconds with
        | none =>
          rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
            simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
            (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
              simp [List.getLast?_append, List.getLast?_cons] at this)
        | some s_d =>
          have h_iq : IsDigits s_d := hwf_s
          have := not_endsWith_ms_of_digits_s_chain
            (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
          simp only [String.append_assoc] at this
          simp only [durationChunk, String.append_assoc] at this ⊢
          exact this
      simp only [durationChunk] at hew
      simp [hew]
    | some ms_d =>
      have h_iq := hwf_ms
      have hsome := h_iq.toNat?'_isSome
      obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
      -- pfx = d_chunk ++ h_chunk ++ m_chunk ++ s_chunk ends with 's','m','h','d' (non-digit) or is ""
      have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
          ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
            durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse = c :: cs ∧
            c.isDigit = false := by
        rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
          rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
          simp [durationChunk, String.toList_append]
      have hstep := extract_step_chain
        (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++
          durationChunk seconds "s") ms_d "ms" n h_iq hnat hpfx_end
      simp only [durationChunk, String.append_assoc] at hstep ⊢
      exact hstep
  -- Step 2: rest₂ = (extract rest₁ "s").2 = d_chunk ++ h_chunk ++ m_chunk
  have hrest₂ : rest₂ = durationChunk days "d" ++ durationChunk hours "h" ++
      durationChunk minutes "m" := by
    rw [hr₂, hrest₁]
    cases seconds with
    | none =>
      simp only [durationChunk, String.append_empty, extractPair]
      have hew : (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m").endsWith "s" = false := by
        rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
          simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
          (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
            simp [List.getLast?_append, List.getLast?_cons] at this)
      simp only [durationChunk] at hew; simp [hew]
    | some s_d =>
      -- seconds present: apply extract_step_chain
      have h_iq := hwf_s
      have hsome := h_iq.toNat?'_isSome
      obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
      have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m") = "" ∨
          ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
            durationChunk minutes "m").toList.reverse = c :: cs ∧ c.isDigit = false := by
        rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
          simp [durationChunk, String.toList_append]
      have hstep := extract_step_chain
        (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m")
        s_d "s" n h_iq hnat hpfx_end
      simp only [durationChunk, String.append_assoc] at hstep ⊢
      exact hstep
  -- Step 3: rest₃ = (extract rest₂ "m").2 = d_chunk ++ h_chunk
  have hrest₃ : rest₃ = durationChunk days "d" ++ durationChunk hours "h" := by
    rw [hr₃, hrest₂]
    cases minutes with
    | none =>
      simp only [durationChunk, String.append_empty]
      unfold extractPair
      cases hours with
      | none =>
        simp only [String.append_empty]
        cases days with
        | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
        | some d_d =>
          have h_iq := hwf_d
          obtain ⟨hne_d, _⟩ := h_iq
          have hne_list : (d_d ++ "d").toList ≠ [] := by
            simp only [String.toList_append]
            exact List.append_ne_nil_of_right_ne_nil _ (by decide)
          have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
            simp [String.toList_append, List.getLast_append_of_ne_nil]
          have hew : (d_d ++ "d").endsWith "m" = false := by
            apply not_endsWith_single_of_last_ne _ 'm' hne_list
            rw [hlast]; decide
          simp [hew]
      | some hr_d =>
        have h_iq := hwf_h
        obtain ⟨hne_h, _⟩ := h_iq
        have hne_list : (durationChunk days "d" ++ (hr_d ++ "h")).toList ≠ [] := by
          simp only [String.toList_append]
          intro h
          have := List.append_eq_nil_iff.mp h
          simp at this
        have hlast : (durationChunk days "d" ++ (hr_d ++ "h")).toList.getLast hne_list = 'h' := by
          simp [String.toList_append, List.getLast_append_of_ne_nil]
        have hew : (durationChunk days "d" ++ (hr_d ++ "h")).endsWith "m" = false := by
          apply not_endsWith_single_of_last_ne _ 'm' hne_list
          rw [hlast]; decide
        simp only [durationChunk] at hew ⊢
        simp [hew]
    | some m_d =>
      have h_iq := hwf_m
      have hsome := h_iq.toNat?'_isSome
      obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
      have hpfx_end : durationChunk days "d" ++ durationChunk hours "h" = "" ∨
          ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h").toList.reverse = c :: cs ∧
            c.isDigit = false := by
        cases days with
        | none =>
          cases hours with
          | none => left; simp [durationChunk]
          | some hr_d =>
            right
            have h_iq_h := hwf_h
            exact pfx_append_chunk_reverse_non_digit "" hr_d "h" h_iq_h (Or.inr (Or.inl rfl))
        | some d_d =>
          right
          cases hours with
          | none =>
            simp only [durationChunk, String.append_empty]
            have h_iq_d := hwf_d
            exact pfx_append_chunk_reverse_non_digit "" d_d "d" h_iq_d (Or.inl rfl)
          | some hr_d =>
            have h_iq_h := hwf_h
            exact pfx_append_chunk_reverse_non_digit (durationChunk (some d_d) "d") hr_d "h" h_iq_h
              (Or.inr (Or.inl rfl))
      have := extract_step_chain (durationChunk days "d" ++ durationChunk hours "h") m_d "m" n
        h_iq hnat hpfx_end
      simp only [durationChunk, String.append_assoc] at this ⊢
      exact this
  -- Step 4: rest₄ = (extract rest₃ "h").2 = d_chunk
  have hrest₄ : rest₄ = durationChunk days "d" := by
    rw [hr₄, hrest₃]
    cases hours with
    | none =>
      simp only [durationChunk, String.append_empty]
      unfold extractPair
      cases days with
      | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
      | some d_d =>
        have h_iq := hwf_d
        obtain ⟨hne_d, _hsome_d⟩ := h_iq
        have hne_list : (d_d ++ "d").toList ≠ [] := by
          simp only [String.toList_append]
          exact List.append_ne_nil_of_right_ne_nil _ (by decide)
        have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
          simp [String.toList_append, List.getLast_append_of_ne_nil]
        have hew : (d_d ++ "d").endsWith "h" = false := by
          apply not_endsWith_single_of_last_ne _ 'h' hne_list
          rw [hlast]; decide
        simp [hew]
    | some hr_d =>
      have h_iq := hwf_h
      have hsome := h_iq.toNat?'_isSome
      obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
      have hpfx_end : durationChunk days "d" = "" ∨
          ∃ c cs, (durationChunk days "d").toList.reverse = c :: cs ∧ c.isDigit = false := by
        cases days with
        | none => left; simp [durationChunk]
        | some d_d =>
          right
          have h_iq_d := hwf_d
          exact pfx_append_chunk_reverse_non_digit "" d_d "d" h_iq_d (Or.inl rfl)
      have := extract_step_chain (durationChunk days "d") hr_d "h" n h_iq hnat hpfx_end
      simp only [durationChunk, String.append_assoc] at this ⊢
      exact this
  -- Step 5: rest₅ = (extract rest₄ "d").2 = ""
  rw [hr₅, hrest₄]
  cases days with
  | none => simp [durationChunk, extractPair, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
  | some d_d =>
    have h_iq := hwf_d
    have hsome := h_iq.toNat?'_isSome
    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
    have := extract_step_chain "" d_d "d" n h_iq hnat (Or.inl rfl)
    simpa [durationChunk, String.empty_append] using this

-- ms-step: extract of full asString.
private theorem extract_ms_step
    (days hours minutes seconds milliseconds : Option String)
    (hwf_s : IsWfOptionalQuantity seconds) (hwf_ms : IsWfOptionalQuantity milliseconds) :
    ∃ n, extractTrailingQuantity (Components.asString
        ⟨days, hours, minutes, seconds, milliseconds⟩) "ms" =
      some (n, durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m" ++ durationChunk seconds "s") := by
  unfold Components.asString
  cases milliseconds with
  | none =>
    simp only [durationChunk, String.append_empty]
    refine ⟨0, ?_⟩
    apply extract_absent_some
    have hew : (durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m" ++ durationChunk seconds "s").endsWith "ms" = false := by
      cases seconds with
      | none =>
        rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
          simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
          (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
            simp [List.getLast?_append, List.getLast?_cons] at this)
      | some s_d =>
        have h_iq : IsDigits s_d := hwf_s
        have := not_endsWith_ms_of_digits_s_chain
          (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
        simp only [String.append_assoc, durationChunk] at this ⊢
        exact this
    simp only [durationChunk] at hew ⊢; exact hew
  | some ms_d =>
    have h_iq : IsDigits ms_d := hwf_ms
    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp h_iq.toNat?'_isSome
    have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
        ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse = c :: cs ∧
          c.isDigit = false := by
      rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
        rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
        simp [durationChunk, String.toList_append]
    refine ⟨n, ?_⟩
    have hstep := extract_step_chain_some
      (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++
        durationChunk seconds "s") ms_d "ms" n h_iq hnat hpfx_end
    simp only [durationChunk, String.append_assoc] at hstep ⊢
    exact hstep


private theorem extract_s_step
    (days hours minutes seconds : Option String)
    (hwf_d : IsWfOptionalQuantity days) (hwf_h : IsWfOptionalQuantity hours)
    (hwf_s : IsWfOptionalQuantity seconds) :
    ∃ n, extractTrailingQuantity (durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m" ++ durationChunk seconds "s") "s" =
      some (n, durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") := by
  cases seconds with
  | none =>
    simp only [durationChunk, String.append_empty]
    refine ⟨0, extract_absent_some _ _ ?_⟩
    have hew : (durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m").endsWith "s" = false := by
      rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
        simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
        (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
          simp [List.getLast?_append, List.getLast?_cons] at this)
    simp only [durationChunk] at hew ⊢; exact hew
  | some s_d =>
    have h_iq : IsDigits s_d := hwf_s
    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp h_iq.toNat?'_isSome
    have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m") = "" ∨
        ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m").toList.reverse = c :: cs ∧ c.isDigit = false := by
      rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
        simp [durationChunk, String.toList_append]
    refine ⟨n, ?_⟩
    have hstep := extract_step_chain_some
      (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d "s" n
      h_iq hnat hpfx_end
    simp only [durationChunk, String.append_assoc] at hstep ⊢
    exact hstep

private theorem extract_m_step
    (days hours minutes : Option String)
    (hwf_d : IsWfOptionalQuantity days) (hwf_h : IsWfOptionalQuantity hours)
    (hwf_m : IsWfOptionalQuantity minutes) :
    ∃ n, extractTrailingQuantity (durationChunk days "d" ++ durationChunk hours "h" ++
        durationChunk minutes "m") "m" =
      some (n, durationChunk days "d" ++ durationChunk hours "h") := by
  cases minutes with
  | none =>
    simp only [durationChunk, String.append_empty]
    refine ⟨0, extract_absent_some _ _ ?_⟩
    cases hours with
    | none =>
      simp only [String.append_empty]
      cases days with
      | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
      | some d_d =>
        have hne_list : (d_d ++ "d").toList ≠ [] := by
          simp only [String.toList_append]
          exact List.append_ne_nil_of_right_ne_nil _ (by decide)
        have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
          simp [String.toList_append, List.getLast_append_of_ne_nil]
        have hew : (d_d ++ "d").endsWith "m" = false := by
          apply not_endsWith_single_of_last_ne _ 'm' hne_list; rw [hlast]; decide
        simpa [durationChunk] using hew
    | some hr_d =>
      have hne_list : (durationChunk days "d" ++ (hr_d ++ "h")).toList ≠ [] := by
        simp only [String.toList_append]; intro h
        have := List.append_eq_nil_iff.mp h; simp at this
      have hlast : (durationChunk days "d" ++ (hr_d ++ "h")).toList.getLast hne_list = 'h' := by
        simp [String.toList_append, List.getLast_append_of_ne_nil]
      have hew : (durationChunk days "d" ++ (hr_d ++ "h")).endsWith "m" = false := by
        apply not_endsWith_single_of_last_ne _ 'm' hne_list; rw [hlast]; decide
      simp only [durationChunk] at hew ⊢; exact hew
  | some m_d =>
    have h_iq : IsDigits m_d := hwf_m
    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp h_iq.toNat?'_isSome
    have hpfx_end : durationChunk days "d" ++ durationChunk hours "h" = "" ∨
        ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h").toList.reverse = c :: cs ∧
          c.isDigit = false := by
      cases days with
      | none =>
        cases hours with
        | none => left; simp [durationChunk]
        | some hr_d =>
          right; exact pfx_append_chunk_reverse_non_digit "" hr_d "h" hwf_h (Or.inr (Or.inl rfl))
      | some d_d =>
        right
        cases hours with
        | none =>
          simp only [durationChunk, String.append_empty]
          exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
        | some hr_d =>
          exact pfx_append_chunk_reverse_non_digit (durationChunk (some d_d) "d") hr_d "h" hwf_h
            (Or.inr (Or.inl rfl))
    refine ⟨n, ?_⟩
    have hstep := extract_step_chain_some (durationChunk days "d" ++ durationChunk hours "h") m_d "m" n
      h_iq hnat hpfx_end
    simp only [durationChunk, String.append_assoc] at hstep ⊢
    exact hstep

private theorem extract_h_step
    (days hours : Option String)
    (hwf_d : IsWfOptionalQuantity days) (hwf_h : IsWfOptionalQuantity hours) :
    ∃ n, extractTrailingQuantity (durationChunk days "d" ++ durationChunk hours "h") "h" =
      some (n, durationChunk days "d") := by
  cases hours with
  | none =>
    simp only [durationChunk, String.append_empty]
    refine ⟨0, extract_absent_some _ _ ?_⟩
    cases days with
    | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
    | some d_d =>
      have hne_list : (d_d ++ "d").toList ≠ [] := by
        simp only [String.toList_append]
        exact List.append_ne_nil_of_right_ne_nil _ (by decide)
      have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
        simp [String.toList_append, List.getLast_append_of_ne_nil]
      have hew : (d_d ++ "d").endsWith "h" = false := by
        apply not_endsWith_single_of_last_ne _ 'h' hne_list; rw [hlast]; decide
      simpa [durationChunk] using hew
  | some hr_d =>
    have h_iq : IsDigits hr_d := hwf_h
    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp h_iq.toNat?'_isSome
    have hpfx_end : durationChunk days "d" = "" ∨
        ∃ c cs, (durationChunk days "d").toList.reverse = c :: cs ∧ c.isDigit = false := by
      cases days with
      | none => left; simp [durationChunk]
      | some d_d =>
        right; exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
    refine ⟨n, ?_⟩
    have hstep := extract_step_chain_some (durationChunk days "d") hr_d "h" n h_iq hnat hpfx_end
    simp only [durationChunk, String.append_assoc] at hstep ⊢
    exact hstep

private theorem extract_d_step (days : Option String) (hwf_d : IsWfOptionalQuantity days) :
    ∃ n, extractTrailingQuantity (durationChunk days "d") "d" = some (n, "") := by
  cases days with
  | none =>
    refine ⟨0, ?_⟩
    simp only [durationChunk]
    exact extract_absent_some _ _ (by simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice])
  | some d_d =>
    have h_iq : IsDigits d_d := hwf_d
    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp h_iq.toNat?'_isSome
    refine ⟨n, ?_⟩
    have := extract_step_chain_some "" d_d "d" n h_iq hnat (Or.inl rfl)
    simpa [String.empty_append, durationChunk] using this


/-- The full some-chain of extract steps for a well-formed body: every present component parses,
    so all five right-to-left extractions succeed. -/
private theorem extracts_chain_of_wf (body : String) (h : IsWfBody body) :
    ∃ r1 r2 r3 r4 n_ms n_s n_m n_h n_d,
      extractTrailingQuantity body "ms" = some (n_ms, r1) ∧
      extractTrailingQuantity r1 "s" = some (n_s, r2) ∧
      extractTrailingQuantity r2 "m" = some (n_m, r3) ∧
      extractTrailingQuantity r3 "h" = some (n_h, r4) ∧
      extractTrailingQuantity r4 "d" = some (n_d, "") := by
  obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
  simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
  obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf_q
  subst hbody
  obtain ⟨n_ms, e1⟩ := extract_ms_step days hours minutes seconds milliseconds hwf_s hwf_ms
  obtain ⟨n_s, e2⟩ := extract_s_step days hours minutes seconds hwf_d hwf_h hwf_s
  obtain ⟨n_m, e3⟩ := extract_m_step days hours minutes hwf_d hwf_h hwf_m
  obtain ⟨n_h, e4⟩ := extract_h_step days hours hwf_d hwf_h
  obtain ⟨n_d, e5⟩ := extract_d_step days hwf_d
  exact ⟨_, _, _, _, _, _, _, _, _, e1, e2, e3, e4, e5⟩

/-- Crux: on a well-formed body, `computeBodyValue` is defined and equals its total mirror
    `computeBodyValueD`. -/
private theorem computeBodyValue_eq_some_D_of_wf (body : String) (h : IsWfBody body) :
    computeBodyValue body = some (computeBodyValueD body) := by
  obtain ⟨r1, r2, r3, r4, n_ms, n_s, n_m, n_h, n_d, e1, e2, e3, e4, e5⟩ := extracts_chain_of_wf body h
  rw [computeBodyValue_of_extracts body r1 r2 r3 r4 n_ms n_s n_m n_h n_d e1 e2 e3 e4 e5,
    computeBodyValueD_of_extracts body r1 r2 r3 r4 n_ms n_s n_m n_h n_d e1 e2 e3 e4 e5]

/-- Crux, signed form: on a well-formed body, `computeSignedBodyValue` is defined and equals its
    total mirror `computeSignedBodyValueD`. -/
private theorem computeSignedBodyValue_eq_some_D_of_wf (isNegative : Bool) (body : String)
    (h : IsWfBody body) :
    computeSignedBodyValue isNegative body = some (computeSignedBodyValueD isNegative body) := by
  unfold computeSignedBodyValue computeSignedBodyValueD
  rw [computeBodyValue_eq_some_D_of_wf body h]; simp


/-- The negative-bound derivation used in the overflow omega finisher. -/
private theorem neg_bound_of_int64_overflow (isNeg : Bool) (n : Nat)
    (h_int64 : Int64.ofInt? (signedQuantity isNeg n) = none)
    (hisNeg : isNeg = true) :
    (↑n : Int) > Int64.MAX + 1 := by
  simp [signedQuantity, hisNeg] at h_int64
  have hconv : Int.negOfNat n = -(↑n : Int) := by
    cases n <;> simp [Int.negOfNat, Int.negSucc_eq]
  have hrange := Int64.ofInt?_none_iff.mpr (hconv ▸ h_int64)
  simp only [Int64.MIN, Int64.MAX] at hrange ⊢; omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- Helper lemmas: relating parseUnit? output values to signedQuantity * multiplier
-- ═══════════════════════════════════════════════════════════════════════════════

-- parseUnit? value = signedQuantity isNeg (extract ..).1 for "ms"
private theorem parseUnit?_val_eq_ms (isNeg : Bool) (s : String) (v : Int) (rest : String)
    (hp : parseUnit? isNeg s "ms" = some (v, rest)) :
    v = signedQuantity isNeg (extractPair s "ms").1 := by
  cases hew : s.endsWith "ms" with
  | false =>
    have ⟨hv0, _⟩ := parseUnit?_passthrough isNeg s "ms" v rest hp hew
    subst hv0; unfold extractPair; simp [hew]
    unfold signedQuantity; cases isNeg <;> simp [Int.negOfNat]
  | true =>
    obtain ⟨n, hn_ext, hn_du⟩ := parseUnit?_some_endsWith_value isNeg s "ms" v rest hp hew
    rw [hn_ext]; unfold durationUnits? at hn_du
    cases hᵢ : Int64.ofInt? (signedQuantity isNeg n) with
    | none => rw [hᵢ] at hn_du; simp at hn_du
    | some i => rw [hᵢ] at hn_du; simp at hn_du
                have hi := Int64.ofInt?_some_toInt hᵢ; omega

-- parseUnit? value = signedQuantity isNeg (extract ..).1 * MILLISECONDS_PER_SECOND for "s"
private theorem parseUnit?_val_eq_s (isNeg : Bool) (s : String) (v : Int) (rest : String)
    (hp : parseUnit? isNeg s "s" = some (v, rest)) :
    v = signedQuantity isNeg (extractPair s "s").1 *
      MILLISECONDS_PER_SECOND := by
  cases hew : s.endsWith "s" with
  | false =>
    have ⟨hv0, _⟩ := parseUnit?_passthrough isNeg s "s" v rest hp hew
    subst hv0; unfold extractPair; simp [hew]
    unfold signedQuantity; cases isNeg <;> simp [Int.negOfNat, MILLISECONDS_PER_SECOND]
  | true =>
    obtain ⟨n, hn_ext, hn_du⟩ := parseUnit?_some_endsWith_value isNeg s "s" v rest hp hew
    rw [hn_ext]; unfold durationUnits? at hn_du
    cases hᵢ : Int64.ofInt? (signedQuantity isNeg n) with
    | none => rw [hᵢ] at hn_du; simp at hn_du
    | some i => rw [hᵢ] at hn_du; simp at hn_du
                have hi := Int64.ofInt?_some_toInt hᵢ
                simp only [MILLISECONDS_PER_SECOND] at hn_du ⊢; omega

-- parseUnit? value for "m"
private theorem parseUnit?_val_eq_min (isNeg : Bool) (s : String) (v : Int) (rest : String)
    (hp : parseUnit? isNeg s "m" = some (v, rest)) :
    v = signedQuantity isNeg (extractPair s "m").1 *
      MILLISECONDS_PER_MINUTE := by
  cases hew : s.endsWith "m" with
  | false =>
    have ⟨hv0, _⟩ := parseUnit?_passthrough isNeg s "m" v rest hp hew
    subst hv0; unfold extractPair; simp [hew]
    unfold signedQuantity; cases isNeg <;> simp [Int.negOfNat, MILLISECONDS_PER_MINUTE]
  | true =>
    obtain ⟨n, hn_ext, hn_du⟩ := parseUnit?_some_endsWith_value isNeg s "m" v rest hp hew
    rw [hn_ext]; unfold durationUnits? at hn_du
    cases hᵢ : Int64.ofInt? (signedQuantity isNeg n) with
    | none => rw [hᵢ] at hn_du; simp at hn_du
    | some i => rw [hᵢ] at hn_du; simp at hn_du
                have hi := Int64.ofInt?_some_toInt hᵢ
                simp only [MILLISECONDS_PER_MINUTE] at hn_du ⊢; omega

-- parseUnit? value for "h"
private theorem parseUnit?_val_eq_hr (isNeg : Bool) (s : String) (v : Int) (rest : String)
    (hp : parseUnit? isNeg s "h" = some (v, rest)) :
    v = signedQuantity isNeg (extractPair s "h").1 *
      MILLISECONDS_PER_HOUR := by
  cases hew : s.endsWith "h" with
  | false =>
    have ⟨hv0, _⟩ := parseUnit?_passthrough isNeg s "h" v rest hp hew
    subst hv0; unfold extractPair; simp [hew]
    unfold signedQuantity; cases isNeg <;> simp [Int.negOfNat, MILLISECONDS_PER_HOUR]
  | true =>
    obtain ⟨n, hn_ext, hn_du⟩ := parseUnit?_some_endsWith_value isNeg s "h" v rest hp hew
    rw [hn_ext]; unfold durationUnits? at hn_du
    cases hᵢ : Int64.ofInt? (signedQuantity isNeg n) with
    | none => rw [hᵢ] at hn_du; simp at hn_du
    | some i => rw [hᵢ] at hn_du; simp at hn_du
                have hi := Int64.ofInt?_some_toInt hᵢ
                simp only [MILLISECONDS_PER_HOUR] at hn_du ⊢; omega

-- parseUnit? value for "d"
private theorem parseUnit?_val_eq_day (isNeg : Bool) (s : String) (v : Int) (rest : String)
    (hp : parseUnit? isNeg s "d" = some (v, rest)) :
    v = signedQuantity isNeg (extractPair s "d").1 *
      MILLISECONDS_PER_DAY := by
  cases hew : s.endsWith "d" with
  | false =>
    have ⟨hv0, _⟩ := parseUnit?_passthrough isNeg s "d" v rest hp hew
    subst hv0; unfold extractPair; simp [hew]
    unfold signedQuantity; cases isNeg <;> simp [Int.negOfNat, MILLISECONDS_PER_DAY]
  | true =>
    obtain ⟨n, hn_ext, hn_du⟩ := parseUnit?_some_endsWith_value isNeg s "d" v rest hp hew
    rw [hn_ext]; unfold durationUnits? at hn_du
    cases hᵢ : Int64.ofInt? (signedQuantity isNeg n) with
    | none => rw [hᵢ] at hn_du; simp at hn_du
    | some i => rw [hᵢ] at hn_du; simp at hn_du
                have hi := Int64.ofInt?_some_toInt hᵢ
                simp only [MILLISECONDS_PER_DAY] at hn_du ⊢; omega

/-- On a well-formed duration body, `parseDuration?` agrees with `duration?` applied to the
    computed signed millisecond value. This is the key bridge between the parser and the
    arithmetic semantics. -/
theorem parseDuration?_eq_duration?_of_wf (isNegative : Bool) (body : String)
    (h : IsWfBody body) :
    parseDuration? isNegative body = duration? (computeSignedBodyValueD isNegative body) := by
  have h_ne : body ≠ "" := body_ne_empty_of_wf body h
  have h_ne_isEmpty : body.isEmpty = false := by
    cases hb : body.isEmpty <;> simp_all [String.isEmpty_iff]
  unfold parseDuration?
  simp only [bind, Option.bind, h_ne_isEmpty]
  cases h₁ : parseUnit? isNegative body "ms" with
  | none =>
    -- parseUnit? = none on the ms step; since passthrough returns some, the suffix was found.
    -- The failure must come from durationUnits? overflow (all other cases would be contradictions
    -- with well-formedness of the ms component).
    have hew : body.endsWith "ms" = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      have := parseUnit?_no_endsWith isNegative body "ms" hne
      rw [h₁] at this; simp at this
    rw [parseUnit?_eq_norm] at h₁
    unfold parseUnit?_norm at h₁
    simp only [hew, ite_true] at h₁
    have hcopy_eq : (body.dropEnd "ms".length).copy.toList =
        (body.dropEnd "ms".length).toString.toList := by
      congr 1
    generalize hdig : ((body.dropEnd "ms".length).toString.toList.reverse.takeWhile
        Char.isDigit).reverse = digs at h₁
    cases hdne : digs.isEmpty with
    | true =>
      -- Empty digits contradicts well-formedness: the ms component must be a non-empty digit string.
      exfalso
      obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
      simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
      cases hms : milliseconds with
      | none =>
        simp only [Components.asString, durationChunk, hms, String.append_empty] at hbody
        rw [hbody] at hew
        -- Handle 's' cases (seconds present) separately from non-'s' cases.
        -- ms=none: body without ms-chunk can't endWith "ms".
        cases seconds with
        | none =>
          rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
            simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] at hew <;>
            (obtain ⟨t, ht⟩ := hew; have := congrArg List.getLast? ht;
              simp [List.getLast?_append, List.getLast?_cons] at this)
        | some s_d =>
          have h_iq : IsDigits s_d := by
            have := hwf_q.2.2.2; cases hms; simp at this; exact this
          have hfalse := not_endsWith_ms_of_digits_s_chain
            (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
          simp only [String.append_assoc, durationChunk] at hfalse hew
          rw [hfalse] at hew; exact absurd hew (by decide)
      | some ms_d =>
        have hwf_ms : IsDigits ms_d := by
          have := hwf_q.2.2.2.2; rw [hms] at this; exact this
        have hne_ms := hwf_ms.ne_empty
        have hdigits_all := allDigit_of_isDurationQuantity ms_d hwf_ms
        have hdigs_eq : digs = [] := by
          cases hd : digs with
          | nil => rfl
          | cons _ _ => simp [hd] at hdne
        rw [hdigs_eq] at hdig
        -- hdig says the trailing digit run of (body.dropEnd 2) is empty, but ms_d is a
        -- non-empty all-digit suffix of that string, so it's a contradiction.
        have h_suffix : ms_d.toList <:+ (body.dropEnd "ms".length).toString.toList := by
          -- body = prefix ++ ms_d ++ "ms" from well-formedness
          -- (body.dropEnd 2).toString ++ "ms" = body (from dropEnd_append_endsWith)
          -- So (body.dropEnd 2).toString = prefix ++ ms_d, giving ms_d as suffix.
          have hbody_eq2 : (body.dropEnd "ms".length).toString ++ "ms" = body :=
            dropEnd_append_endsWith body "ms" hew
          -- Show body = something ++ ms_d ++ "ms" at string level
          have hbody_ends : ∃ pfx : String, body = pfx ++ ms_d ++ "ms" := by
            refine ⟨(((durationChunk days "d" ++ durationChunk hours "h") ++
                durationChunk minutes "m") ++ durationChunk seconds "s"), ?_⟩
            rw [hbody]; simp only [Components.asString, durationChunk, hms, String.append_assoc]
          obtain ⟨pfx, hpfx_eq⟩ := hbody_ends
          -- From hbody_eq2 and hpfx_eq:
          -- (body.dropEnd 2).toString ++ "ms" = body = pfx ++ ms_d ++ "ms"
          have h_str_combine : (body.dropEnd "ms".length).toString ++ "ms" = pfx ++ ms_d ++ "ms" := by
            rw [hbody_eq2, hpfx_eq]
          -- String.ext + append cancel on strings
          have h_str_cancel : (body.dropEnd "ms".length).toString = pfx ++ ms_d := by
            have h := congrArg String.toList h_str_combine
            simp [String.toList_append] at h
            apply String.ext
            simp [String.toList_append]
            have h' : List.take (body.length - "ms".length) body.toList ++ ['m', 's'] =
                pfx.toList ++ ms_d.toList ++ ['m', 's'] := by
              rw [List.append_assoc]; exact h
            exact List.append_cancel_right h'
          rw [h_str_cancel]
          simp only [String.toList_append]
          exact ⟨pfx.toList, rfl⟩
        have h_ms_ne : ms_d.toList ≠ [] := by
          intro he; exact hne_ms (by ext; simp [he])
        obtain ⟨pfx, hpfx⟩ := h_suffix
        have hrev_eq : (body.dropEnd "ms".length).toString.toList.reverse =
            ms_d.toList.reverse ++ pfx.reverse := by
          rw [← hpfx, List.reverse_append]
        rw [hrev_eq] at hdig
        cases hms_rev : ms_d.toList.reverse with
        | nil => simp at hms_rev; exact h_ms_ne (List.eq_nil_of_length_eq_zero (by simp [hms_rev]))
        | cons c cs =>
          have hc_digit : Char.isDigit c = true := by
            have : c ∈ ms_d.toList.reverse := by rw [hms_rev]; exact List.Mem.head _
            have : c ∈ ms_d.toList := by rwa [List.mem_reverse] at this
            exact hdigits_all c this
          rw [hms_rev] at hdig
          simp [hc_digit] at hdig
    | false =>
      simp only [hdne, Bool.false_eq_true, ite_false, bind, Option.bind] at h₁
      cases hnat : toNat?' (String.ofList digs) with
      | none =>
        -- toNat?' failed on trailing digits — contradicts well-formedness.
        -- Same structure as the digits-empty case: extract ms component, show digs = ms_d.toList,
        -- then toNat?' ms_d succeeds (from IsDigits), contradiction.
        exfalso
        obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
        simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
        cases hms : milliseconds with
        | none =>
          -- ms=none: body can't endWith "ms" (same as the digs-empty case)
          simp only [Components.asString, durationChunk, hms, String.append_empty] at hbody
          rw [hbody] at hew
          cases seconds with
          | none =>
            rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
              simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] at hew <;>
              (obtain ⟨t, ht⟩ := hew; have := congrArg List.getLast? ht;
                simp [List.getLast?_append, List.getLast?_cons] at this)
          | some s_d =>
            have h_iq : IsDigits s_d := by
              have := hwf_q.2.2.2; cases hms; simp at this; exact this
            have hfalse := not_endsWith_ms_of_digits_s_chain
              (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
            simp only [String.append_assoc, durationChunk] at hfalse hew
            rw [hfalse] at hew; exact absurd hew (by decide)
        | some ms_d =>
          have hwf_ms : IsDigits ms_d := by
            have := hwf_q.2.2.2.2; rw [hms] at this; exact this
          obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hwf_ms.toNat?'_isSome
          -- body = pfx ++ ms_d ++ "ms", so (body.dropEnd 2).toString = pfx ++ ms_d
          -- The trailing digit run of pfx ++ ms_d is ms_d.toList
          have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
              durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
              ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse = c :: cs ∧
                c.isDigit = false := by
            rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
              rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
              simp [durationChunk, String.toList_append]
          have hdrop_eq : (body.dropEnd "ms".length).toString = (durationChunk days "d" ++
              durationChunk hours "h" ++ durationChunk minutes "m" ++
              durationChunk seconds "s") ++ ms_d := by
            have hbody_eq2 : (body.dropEnd "ms".length).toString ++ "ms" = body :=
              dropEnd_append_endsWith body "ms" hew
            have hbody_form : body = (durationChunk days "d" ++ durationChunk hours "h" ++
                durationChunk minutes "m" ++ durationChunk seconds "s") ++ ms_d ++ "ms" := by
              rw [hbody]; simp [Components.asString, durationChunk, hms, String.append_assoc]
            have h_combine : (body.dropEnd "ms".length).toString ++ "ms" =
                ((durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m" ++ durationChunk seconds "s") ++ ms_d) ++ "ms" := by
              rw [hbody_eq2, hbody_form, String.append_assoc]
            have h := congrArg String.toList h_combine
            simp only [String.toList_append] at h
            apply String.ext; simp only [String.toList_append]
            exact List.append_cancel_right h
          have hall_rev : ∀ c ∈ ms_d.toList.reverse, Char.isDigit c = true := by
            intro c hc
            exact allDigit_of_isDurationQuantity ms_d hwf_ms c (List.mem_reverse.mp hc)
          have htw : ((body.dropEnd "ms".length).toString.toList.reverse.takeWhile
              Char.isDigit).reverse = ms_d.toList := by
            rw [hdrop_eq, String.toList_append, List.reverse_append]
            rw [takeWhile_append_stop_chain hall_rev]
            · exact List.reverse_reverse ms_d.toList
            rcases hpfx_end with hpfx_empty | ⟨c, cs, hrev, hc⟩
            · left; simp [hpfx_empty]
            · right; exact ⟨c, cs, hrev, hc⟩
          rw [htw] at hdig
          -- digs = ms_d.toList, so toNat?' (String.ofList digs) = toNat?' ms_d = some n
          have : toNat?' (String.ofList digs) = some n := by
            rw [← hdig, show String.ofList ms_d.toList = ms_d from by simp]; exact hn
          rw [this] at hnat; exact absurd hnat (by simp)
      | some n =>
        -- durationUnits? failed ↔ Int64 overflow on the ms component.
        simp only [hnat] at h₁
        have h_int64 : Int64.ofInt? (signedQuantity isNegative n) = none := by
          unfold signedQuantity
          cases isNegative <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h₁ ⊢ <;> (
            unfold durationUnits? at h₁
            cases hᵢ : Int64.ofInt? _ <;> simp_all)
        have hn_gt := nat_gt_max_of_int64_ofInt?_none_signedQuantity isNegative n h_int64
        symm
        simp [duration?_eq_none_iff_overflow]
        have hext_n : (extractPair body "ms").1 = n := by
          unfold extractPair
          simp only [hew, ite_true]
          rw [show ((body.dropEnd "ms".length).toString.toList.reverse.takeWhile
              Char.isDigit).reverse = digs from hdig]
          simp [hnat]
        unfold computeSignedBodyValueD computeBodyValueD
        simp only [hext_n, MILLISECONDS_PER_DAY, MILLISECONDS_PER_HOUR,
          MILLISECONDS_PER_MINUTE, MILLISECONDS_PER_SECOND] at hn_gt ⊢
        -- For the negative case, need a tighter bound: n > Int64.MAX + 1 (= -Int64.MIN).
        simp only [Int64.MIN, Int64.MAX] at hn_gt ⊢
        cases hisNeg : isNegative with
        | false => simp_all; omega
        | true =>
          have := neg_bound_of_int64_overflow isNegative n h_int64 hisNeg
          simp only [Int64.MAX] at this; omega
  | some p₁ =>
    obtain ⟨v_ms, rest₁⟩ := p₁; simp only []
    cases h₂ : parseUnit? isNegative rest₁ "s" with
    | none =>
      have hr₁ := parseUnit?_success_rest isNegative body "ms" v_ms rest₁ h₁
      have hew : rest₁.endsWith "s" = true := by
        by_contra hne
        simp only [Bool.not_eq_true] at hne
        have := parseUnit?_no_endsWith isNegative rest₁ "s" hne
        rw [h₂] at this; simp at this
      obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
      simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
      obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf_q
      subst hbody
      have hrest₁_eq : rest₁ = durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m" ++ durationChunk seconds "s" := by
        rw [hr₁]
        -- Extract ms step (same as in "d" case)
        unfold Components.asString
        cases milliseconds with
        | none =>
          simp only [durationChunk, String.append_empty]
          unfold extractPair
          have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
              durationChunk minutes "m" ++ durationChunk seconds "s").endsWith "ms" = false := by
            cases seconds with
            | none =>
              rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                rcases days with _ | d_d <;>
                simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                  simp [List.getLast?_append, List.getLast?_cons] at this)
            | some s_d =>
              have h_iq : IsDigits s_d := hwf_s
              have := not_endsWith_ms_of_digits_s_chain
                (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
              simp only [String.append_assoc, durationChunk] at this ⊢
              exact this
          simp only [durationChunk] at hew'; simp [hew']
        | some ms_d =>
          have h_iq := hwf_ms
          have hsome := h_iq.toNat?'_isSome
          obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
          have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
              durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
              ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse =
                c :: cs ∧ c.isDigit = false := by
            rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
              rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
              simp [durationChunk, String.toList_append]
          have hstep := extract_step_chain
            (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++
              durationChunk seconds "s") ms_d "ms" n h_iq hnat hpfx_end
          simp only [durationChunk, String.append_assoc] at hstep ⊢
          exact hstep
      have hsec_some : ∃ s_d, seconds = some s_d := by
        cases seconds with
        | none =>
          exfalso
          have hdc : durationChunk none "s" = "" := rfl
          rw [hdc, String.append_empty] at hrest₁_eq
          rw [hrest₁_eq] at hew
          rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
            rcases days with _ | d_d <;>
            simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] at hew <;>
            (obtain ⟨t, ht⟩ := hew; have := congrArg List.getLast? ht;
              simp [List.getLast?_append, List.getLast?_cons] at this)
        | some s_d => exact ⟨s_d, rfl⟩
      obtain ⟨s_d, hsec_eq⟩ := hsec_some
      rw [hsec_eq] at hrest₁_eq hwf_s
      simp only [durationChunk] at hrest₁_eq
      rw [parseUnit?_eq_norm] at h₂
      unfold parseUnit?_norm at h₂
      simp only [hew, ite_true] at h₂
      have hrest₁_drop : (rest₁.dropEnd "s".length).toString =
          (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") ++ s_d := by
        have hdrop_app : (rest₁.dropEnd "s".length).toString ++ "s" = rest₁ :=
          dropEnd_append_endsWith rest₁ "s" hew
        have hrest₁_form : rest₁ =
            (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++ s_d) ++ "s" := by
          rw [hrest₁_eq]; simp [String.append_assoc, durationChunk]
        have h_combine : (rest₁.dropEnd "s".length).toString ++ "s" =
            (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++ s_d) ++ "s" := by
          rw [hdrop_app, hrest₁_form]
        have h := congrArg String.toList h_combine
        simp only [String.toList_append] at h
        apply String.ext; simp only [String.toList_append]
        exact List.append_cancel_right h
      have hall_digits_s : ∀ c ∈ s_d.toList, Char.isDigit c = true :=
        allDigit_of_isDurationQuantity s_d hwf_s
      have hs_ne : s_d.toList ≠ [] := by
        intro he; exact hwf_s.ne_empty (by ext; simp [he])
      have hall_rev : ∀ c ∈ s_d.toList.reverse, Char.isDigit c = true := by
        intro c hc; exact hall_digits_s c (List.mem_reverse.mp hc)
      have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
          durationChunk minutes "m") = "" ∨
          ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
            durationChunk minutes "m").toList.reverse = c :: cs ∧ c.isDigit = false := by
        rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
          simp [durationChunk, String.toList_append]
      have hdigs_eq : ((rest₁.dropEnd "s".length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse = s_d.toList := by
        rw [hrest₁_drop, String.toList_append, List.reverse_append]
        rw [takeWhile_append_stop_chain hall_rev]
        · exact List.reverse_reverse s_d.toList
        rcases hpfx_end with heq | ⟨c, cs, hrev, hc⟩
        · left; rw [heq]; simp
        · right; exact ⟨c, cs, hrev, hc⟩
      have hdigs_ne_bool : ((rest₁.dropEnd "s".length).toString.toList.reverse.takeWhile
          Char.isDigit).reverse.isEmpty = false := by
        rw [show ((rest₁.dropEnd "s".length).toString.toList.reverse.takeWhile
            Char.isDigit).reverse = s_d.toList from hdigs_eq]
        simp; intro he; exact hwf_s.ne_empty (by ext; simp [he])
      simp only [hdigs_ne_bool, Bool.false_eq_true, ite_false, bind, Option.bind] at h₂
      obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hwf_s.toNat?'_isSome
      have hnat_eq : toNat?' (String.ofList ((rest₁.dropEnd "s".length).toString.toList.reverse.takeWhile
          Char.isDigit |>.reverse)) = some n := by
        rw [hdigs_eq, show String.ofList s_d.toList = s_d from by simp]; exact hnat
      rw [hnat_eq] at h₂
      have h_int64 : Int64.ofInt? (signedQuantity isNegative n) = none := by
        unfold signedQuantity
        cases isNegative <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h₂ ⊢ <;> (
          unfold durationUnits? at h₂; cases hᵢ : Int64.ofInt? _ <;> simp_all)
      have hn_gt := nat_gt_max_of_int64_ofInt?_none_signedQuantity isNegative n h_int64
      have hext_n : (extractPair rest₁ "s").1 = n := by
        unfold extractPair; simp only [hew, ite_true]
        rw [hdigs_eq, show String.ofList s_d.toList = s_d from by simp]; simp [hnat]
      simp only [Bool.false_eq_true, ite_false]
      symm
      rw [duration?_eq_none_iff_overflow]
      unfold computeSignedBodyValueD computeBodyValueD
      simp only [← hr₁, hext_n]
      simp only [MILLISECONDS_PER_DAY, MILLISECONDS_PER_HOUR,
        MILLISECONDS_PER_MINUTE, MILLISECONDS_PER_SECOND, Int64.MAX, Int64.MIN] at hn_gt ⊢
      cases hisNeg : isNegative with
      | false => simp_all; omega
      | true =>
        have := neg_bound_of_int64_overflow isNegative n h_int64 hisNeg
        simp only [Int64.MAX] at this; omega
    | some p₂ =>
      obtain ⟨v_s, rest₂⟩ := p₂; simp only []
      cases h₃ : parseUnit? isNegative rest₂ "m" with
      | none =>
        have hr₁ := parseUnit?_success_rest isNegative body "ms" v_ms rest₁ h₁
        have hr₂ := parseUnit?_success_rest isNegative rest₁ "s" v_s rest₂ h₂
        have hew : rest₂.endsWith "m" = true := by
          by_contra hne
          simp only [Bool.not_eq_true] at hne
          have := parseUnit?_no_endsWith isNegative rest₂ "m" hne
          rw [h₃] at this; simp at this
        obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
        simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
        obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf_q
        subst hbody
        have hrest₂ : rest₂ = durationChunk days "d" ++ durationChunk hours "h" ++
            durationChunk minutes "m" := by
          rw [hr₂]
          have hrest₁ : rest₁ = (extractPair
              (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩) "ms").2 := hr₁
          -- Extract ms step
          have hms_step : (extractPair
              (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩)
              "ms").2 =
              durationChunk days "d" ++ durationChunk hours "h" ++
              durationChunk minutes "m" ++ durationChunk seconds "s" := by
            unfold Components.asString
            cases milliseconds with
            | none =>
              simp only [durationChunk, String.append_empty]
              unfold extractPair
              have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m" ++ durationChunk seconds "s").endsWith "ms" = false := by
                cases seconds with
                | none =>
                  rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                    rcases days with _ | d_d <;>
                    simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                    (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                      simp [List.getLast?_append, List.getLast?_cons] at this)
                | some s_d =>
                  have h_iq : IsDigits s_d := hwf_s
                  have := not_endsWith_ms_of_digits_s_chain
                    (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
                  simp only [String.append_assoc, durationChunk] at this ⊢
                  exact this
              simp only [durationChunk] at hew'; simp [hew']
            | some ms_d =>
              have h_iq := hwf_ms
              have hsome := h_iq.toNat?'_isSome
              obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
              have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
                  ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                    durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse =
                    c :: cs ∧ c.isDigit = false := by
                rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
                  rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
                  simp [durationChunk, String.toList_append]
              have hstep := extract_step_chain
                (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++
                  durationChunk seconds "s") ms_d "ms" n h_iq hnat hpfx_end
              simp only [durationChunk, String.append_assoc] at hstep ⊢
              exact hstep
          rw [hrest₁, hms_step]
          -- Extract s step
          have hs_step : (extractPair
              (durationChunk days "d" ++ durationChunk hours "h" ++
               durationChunk minutes "m" ++ durationChunk seconds "s") "s").2 =
              durationChunk days "d" ++ durationChunk hours "h" ++
              durationChunk minutes "m" := by
            cases seconds with
            | none =>
              simp only [durationChunk, String.append_empty]
              unfold extractPair
              have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m").endsWith "s" = false := by
                rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                  rcases days with _ | d_d <;>
                  simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                  (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                    simp [List.getLast?_append, List.getLast?_cons] at this)
              simp only [durationChunk] at hew'; simp [hew']
            | some s_d =>
              have h_iq := hwf_s
              have hsome := h_iq.toNat?'_isSome
              obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
              have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m") = "" ∨
                  ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                    durationChunk minutes "m").toList.reverse = c :: cs ∧
                    c.isDigit = false := by
                rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                  rcases days with _ | d_d <;>
                  simp [durationChunk, String.toList_append]
              have hstep := extract_step_chain
                (durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m") s_d "s" n h_iq hnat hpfx_end
              simp only [durationChunk, String.append_assoc] at hstep ⊢
              exact hstep
          exact hs_step
        have hmin_some : ∃ m_d, minutes = some m_d := by
          cases minutes with
          | none =>
            exfalso
            have hdc : durationChunk none "m" = "" := rfl
            rw [hdc, String.append_empty] at hrest₂
            rw [hrest₂] at hew
            cases hours with
            | none =>
              simp only [durationChunk, String.append_empty] at hew
              cases days with
              | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice] at hew
              | some d_d =>
                have h_iq := hwf_d
                obtain ⟨hne_d, _⟩ := h_iq
                have hne_list : (d_d ++ "d").toList ≠ [] := by
                  simp only [String.toList_append]
                  exact List.append_ne_nil_of_right_ne_nil _ (by decide)
                have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
                  simp [String.toList_append, List.getLast_append_of_ne_nil]
                have hew' : (d_d ++ "d").endsWith "m" = false := by
                  apply not_endsWith_single_of_last_ne _ 'm' hne_list
                  rw [hlast]; decide
                rw [hew'] at hew; exact absurd hew (by decide)
            | some hr_d =>
              have h_iq := hwf_h
              obtain ⟨hne_h, _⟩ := h_iq
              have hne_list : (durationChunk days "d" ++ (hr_d ++ "h")).toList ≠ [] := by
                simp only [String.toList_append]
                intro habs
                have := List.append_eq_nil_iff.mp habs
                simp at this
              have hlast : (durationChunk days "d" ++ (hr_d ++ "h")).toList.getLast hne_list = 'h' := by
                simp [String.toList_append, List.getLast_append_of_ne_nil]
              have hew' : (durationChunk days "d" ++ (hr_d ++ "h")).endsWith "m" = false := by
                apply not_endsWith_single_of_last_ne _ 'm' hne_list
                rw [hlast]; decide
              simp only [durationChunk] at hew hew'
              rw [hew'] at hew; exact absurd hew (by decide)
          | some m_d => exact ⟨m_d, rfl⟩
        obtain ⟨m_d, hmin_eq⟩ := hmin_some
        rw [hmin_eq] at hrest₂ hwf_m
        rw [parseUnit?_eq_norm] at h₃
        unfold parseUnit?_norm at h₃
        simp only [hew, ite_true] at h₃
        have hrest₂_drop : (rest₂.dropEnd "m".length).toString =
            durationChunk days "d" ++ durationChunk hours "h" ++ m_d := by
          have hdrop_app : (rest₂.dropEnd "m".length).toString ++ "m" = rest₂ :=
            dropEnd_append_endsWith rest₂ "m" hew
          have hrest₂_form : rest₂ =
              (durationChunk days "d" ++ durationChunk hours "h" ++ m_d) ++ "m" := by
            rw [hrest₂]; simp [String.append_assoc, durationChunk]
          have h_combine : (rest₂.dropEnd "m".length).toString ++ "m" =
              (durationChunk days "d" ++ durationChunk hours "h" ++ m_d) ++ "m" := by
            rw [hdrop_app, hrest₂_form]
          have h := congrArg String.toList h_combine
          simp only [String.toList_append] at h
          apply String.ext; simp only [String.toList_append]
          exact List.append_cancel_right h
        have hall_digits_m : ∀ c ∈ m_d.toList, Char.isDigit c = true :=
          allDigit_of_isDurationQuantity m_d hwf_m
        have hm_ne : m_d.toList ≠ [] := by
          intro he; exact hwf_m.ne_empty (by ext; simp [he])
        have hdigs_eq : ((rest₂.dropEnd "m".length).toString.toList.reverse.takeWhile
            Char.isDigit).reverse = m_d.toList := by
          rw [hrest₂_drop, String.toList_append, List.reverse_append]
          have hall_rev : ∀ c ∈ m_d.toList.reverse, Char.isDigit c = true := by
            intro c hc; exact hall_digits_m c (List.mem_reverse.mp hc)
          have hpfx_rev : (durationChunk days "d" ++ durationChunk hours "h").toList.reverse = [] ∨
              ∃ y l₂', (durationChunk days "d" ++ durationChunk hours "h").toList.reverse =
                y :: l₂' ∧ y.isDigit = false := by
            cases days with
            | none =>
              cases hours with
              | none => left; simp [durationChunk]
              | some hr_d =>
                right
                have := pfx_append_chunk_reverse_non_digit "" hr_d "h" hwf_h (Or.inr (Or.inl rfl))
                simp only [durationChunk, String.toList_append,
                  List.reverse_append] at this ⊢
                exact this
            | some d_d =>
              right
              cases hours with
              | none =>
                simp only [durationChunk, String.append_empty]
                exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
              | some hr_d =>
                exact pfx_append_chunk_reverse_non_digit (durationChunk (some d_d) "d") hr_d "h" hwf_h
                  (Or.inr (Or.inl rfl))
          have htw_all := takeWhile_append_stop_chain hall_rev hpfx_rev
          rw [htw_all]
          exact List.reverse_reverse m_d.toList
        have hdigs_ne_bool : ((rest₂.dropEnd "m".length).toString.toList.reverse.takeWhile
            Char.isDigit).reverse.isEmpty = false := by
          rw [show ((rest₂.dropEnd "m".length).toString.toList.reverse.takeWhile
              Char.isDigit).reverse = m_d.toList from hdigs_eq]
          simp; intro he; exact hwf_m.ne_empty (by ext; simp [he])
        simp only [hdigs_ne_bool, Bool.false_eq_true, ite_false, bind, Option.bind] at h₃
        obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hwf_m.toNat?'_isSome
        have hnat_eq : toNat?' (String.ofList ((rest₂.dropEnd "m".length).toString.toList.reverse.takeWhile
            Char.isDigit |>.reverse)) = some n := by
          rw [hdigs_eq, show String.ofList m_d.toList = m_d from by simp]; exact hnat
        rw [hnat_eq] at h₃
        have h_int64 : Int64.ofInt? (signedQuantity isNegative n) = none := by
          unfold signedQuantity
          cases isNegative <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h₃ ⊢ <;> (
            unfold durationUnits? at h₃; cases hᵢ : Int64.ofInt? _ <;> simp_all)
        have hn_gt := nat_gt_max_of_int64_ofInt?_none_signedQuantity isNegative n h_int64
        have hext_n : (extractPair rest₂ "m").1 = n := by
          unfold extractPair; simp only [hew, ite_true]
          rw [hdigs_eq, show String.ofList m_d.toList = m_d from by simp]; simp [hnat]
        simp only [Bool.false_eq_true, ite_false]
        symm
        rw [duration?_eq_none_iff_overflow]
        unfold computeSignedBodyValueD computeBodyValueD
        simp only [← hr₁, ← hr₂, hext_n]
        simp only [MILLISECONDS_PER_DAY, MILLISECONDS_PER_HOUR,
          MILLISECONDS_PER_MINUTE, MILLISECONDS_PER_SECOND, Int64.MAX, Int64.MIN] at hn_gt ⊢
        cases hisNeg : isNegative with
        | false => simp_all; omega
        | true =>
          have := neg_bound_of_int64_overflow isNegative n h_int64 hisNeg
          simp only [Int64.MAX] at this; omega
      | some p₃ =>
        obtain ⟨v_m, rest₃⟩ := p₃; simp only []
        cases h₄ : parseUnit? isNegative rest₃ "h" with
        | none =>
          have hr₁ := parseUnit?_success_rest isNegative body "ms" v_ms rest₁ h₁
          have hr₂ := parseUnit?_success_rest isNegative rest₁ "s" v_s rest₂ h₂
          have hr₃ := parseUnit?_success_rest isNegative rest₂ "m" v_m rest₃ h₃
          have hew : rest₃.endsWith "h" = true := by
            by_contra hne
            simp only [Bool.not_eq_true] at hne
            have := parseUnit?_no_endsWith isNegative rest₃ "h" hne
            rw [h₄] at this; simp at this
          obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
          simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
          obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf_q
          subst hbody
          have hrest₃ : rest₃ = durationChunk days "d" ++ durationChunk hours "h" := by
            rw [hr₃]
            have hrest₁ : rest₁ = (extractPair
                (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩) "ms").2 := hr₁
            have hrest₂ : rest₂ = (extractPair rest₁ "s").2 := hr₂
            have hrest₂_eq : rest₂ = durationChunk days "d" ++ durationChunk hours "h" ++
                durationChunk minutes "m" := by
              rw [hrest₂, hrest₁]
              -- Extract ms step
              have hms_step : (extractPair
                  (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩)
                  "ms").2 =
                  durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m" ++ durationChunk seconds "s" := by
                unfold Components.asString
                cases milliseconds with
                | none =>
                  simp only [durationChunk, String.append_empty]
                  unfold extractPair
                  have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
                      durationChunk minutes "m" ++ durationChunk seconds "s").endsWith "ms" = false := by
                    cases seconds with
                    | none =>
                      rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                        rcases days with _ | d_d <;>
                        simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                        (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                          simp [List.getLast?_append, List.getLast?_cons] at this)
                    | some s_d =>
                      have h_iq : IsDigits s_d := hwf_s
                      have := not_endsWith_ms_of_digits_s_chain
                        (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
                      simp only [String.append_assoc, durationChunk] at this ⊢
                      exact this
                  simp only [durationChunk] at hew'; simp [hew']
                | some ms_d =>
                  have h_iq := hwf_ms
                  have hsome := h_iq.toNat?'_isSome
                  obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
                  have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
                      durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
                      ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse =
                        c :: cs ∧ c.isDigit = false := by
                    rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
                      rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
                      simp [durationChunk, String.toList_append]
                  have hstep := extract_step_chain
                    (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++
                      durationChunk seconds "s") ms_d "ms" n h_iq hnat hpfx_end
                  simp only [durationChunk, String.append_assoc] at hstep ⊢
                  exact hstep
              rw [hms_step]
              -- Extract s step
              have hs_step : (extractPair
                  (durationChunk days "d" ++ durationChunk hours "h" ++
                   durationChunk minutes "m" ++ durationChunk seconds "s") "s").2 =
                  durationChunk days "d" ++ durationChunk hours "h" ++
                  durationChunk minutes "m" := by
                cases seconds with
                | none =>
                  simp only [durationChunk, String.append_empty]
                  unfold extractPair
                  have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
                      durationChunk minutes "m").endsWith "s" = false := by
                    rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                      rcases days with _ | d_d <;>
                      simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                      (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                        simp [List.getLast?_append, List.getLast?_cons] at this)
                  simp only [durationChunk] at hew'; simp [hew']
                | some s_d =>
                  have h_iq := hwf_s
                  have hsome := h_iq.toNat?'_isSome
                  obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
                  have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
                      durationChunk minutes "m") = "" ∨
                      ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m").toList.reverse = c :: cs ∧
                        c.isDigit = false := by
                    rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                      rcases days with _ | d_d <;>
                      simp [durationChunk, String.toList_append]
                  have hstep := extract_step_chain
                    (durationChunk days "d" ++ durationChunk hours "h" ++
                      durationChunk minutes "m") s_d "s" n h_iq hnat hpfx_end
                  simp only [durationChunk, String.append_assoc] at hstep ⊢
                  exact hstep
              rw [hs_step]
            rw [hrest₂_eq]
            -- Extract m step: (extractPair
            --   (dChunk days "d" ++ dChunk hours "h" ++ dChunk minutes "m") "m").2
            cases minutes with
            | none =>
              simp only [durationChunk, String.append_empty]
              unfold extractPair
              cases hours with
              | none =>
                simp only [String.append_empty]
                cases days with
                | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
                | some d_d =>
                  have h_iq := hwf_d
                  obtain ⟨hne_d, _⟩ := h_iq
                  have hne_list : (d_d ++ "d").toList ≠ [] := by
                    simp only [String.toList_append]
                    exact List.append_ne_nil_of_right_ne_nil _ (by decide)
                  have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
                    simp [String.toList_append, List.getLast_append_of_ne_nil]
                  have hew' : (d_d ++ "d").endsWith "m" = false := by
                    apply not_endsWith_single_of_last_ne _ 'm' hne_list
                    rw [hlast]; decide
                  simp [hew']
              | some hr_d =>
                have h_iq := hwf_h
                obtain ⟨hne_h, _⟩ := h_iq
                have hne_list : (durationChunk days "d" ++ (hr_d ++ "h")).toList ≠ [] := by
                  simp only [String.toList_append]
                  intro habs
                  have := List.append_eq_nil_iff.mp habs
                  simp at this
                have hlast : (durationChunk days "d" ++ (hr_d ++ "h")).toList.getLast hne_list = 'h' := by
                  simp [String.toList_append, List.getLast_append_of_ne_nil]
                have hew' : (durationChunk days "d" ++ (hr_d ++ "h")).endsWith "m" = false := by
                  apply not_endsWith_single_of_last_ne _ 'm' hne_list
                  rw [hlast]; decide
                simp only [durationChunk] at hew' ⊢
                simp [hew']
            | some m_d =>
              have h_iq := hwf_m
              have hsome := h_iq.toNat?'_isSome
              obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
              have hpfx_end : durationChunk days "d" ++ durationChunk hours "h" = "" ∨
                  ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h").toList.reverse =
                    c :: cs ∧ c.isDigit = false := by
                cases days with
                | none =>
                  cases hours with
                  | none => left; simp [durationChunk]
                  | some hr_d =>
                    right
                    exact pfx_append_chunk_reverse_non_digit "" hr_d "h" hwf_h (Or.inr (Or.inl rfl))
                | some d_d =>
                  right
                  cases hours with
                  | none =>
                    simp only [durationChunk, String.append_empty]
                    exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
                  | some hr_d =>
                    exact pfx_append_chunk_reverse_non_digit (durationChunk (some d_d) "d") hr_d "h" hwf_h
                      (Or.inr (Or.inl rfl))
              have hstep := extract_step_chain
                (durationChunk days "d" ++ durationChunk hours "h") m_d "m" n
                h_iq hnat hpfx_end
              simp only [durationChunk, String.append_assoc] at hstep ⊢
              exact hstep
          have hhours_some : ∃ hr_d, hours = some hr_d := by
            cases hours with
            | none =>
              have hdc : durationChunk none "h" = "" := rfl
              rw [hdc, String.append_empty] at hrest₃
              rw [hrest₃] at hew
              cases days with
              | none =>
                simp only [durationChunk] at hew
                simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice] at hew
              | some d_d =>
                simp only [durationChunk] at hew
                have h_iq := hwf_d
                obtain ⟨hne_d, _⟩ := h_iq
                have hne_list : (d_d ++ "d").toList ≠ [] := by
                  simp only [String.toList_append]
                  exact List.append_ne_nil_of_right_ne_nil _ (by decide)
                have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
                  simp [String.toList_append, List.getLast_append_of_ne_nil]
                have hew' : (d_d ++ "d").endsWith "h" = false := by
                  apply not_endsWith_single_of_last_ne _ 'h' hne_list
                  rw [hlast]; decide
                rw [hew'] at hew; exact absurd hew (by decide)
            | some hr_d => exact ⟨hr_d, rfl⟩
          obtain ⟨hr_d, hhours_eq⟩ := hhours_some
          rw [hhours_eq] at hrest₃ hwf_h
          simp only [durationChunk] at hrest₃
          rw [parseUnit?_eq_norm] at h₄
          unfold parseUnit?_norm at h₄
          simp only [hew, ite_true] at h₄
          have hrest₃_drop : (rest₃.dropEnd "h".length).toString = durationChunk days "d" ++ hr_d := by
            have hdrop : (rest₃.dropEnd "h".length).toString ++ "h" = rest₃ :=
              dropEnd_append_endsWith rest₃ "h" hew
            have h_eq : rest₃ = (durationChunk days "d" ++ hr_d) ++ "h" := by
              rw [hrest₃]; cases days <;> simp [durationChunk, String.append_assoc]
            rw [h_eq] at hdrop ⊢
            have h3 := congrArg String.toList hdrop
            simp only [String.toList_append] at h3
            apply String.ext; simp only [String.toList_append]
            exact List.append_cancel_right h3
          have hall_digits_h : ∀ c ∈ hr_d.toList, Char.isDigit c = true :=
            allDigit_of_isDurationQuantity hr_d hwf_h
          have hh_ne : hr_d.toList ≠ [] := by
            intro he; exact hwf_h.ne_empty (by ext; simp [he])
          have hdigs_eq : ((rest₃.dropEnd "h".length).toString.toList.reverse.takeWhile
              Char.isDigit).reverse = hr_d.toList := by
            rw [hrest₃_drop, String.toList_append]
            have hall_rev : ∀ c ∈ hr_d.toList.reverse, Char.isDigit c = true := by
              intro c hc; exact hall_digits_h c (List.mem_reverse.mp hc)
            rw [List.reverse_append]
            have hpfx_stop : (durationChunk days "d").toList.reverse = [] ∨
                ∃ c cs, (durationChunk days "d").toList.reverse = c :: cs ∧ c.isDigit = false := by
              cases days with
              | none => left; simp [durationChunk]
              | some d_d =>
                right
                exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
            rw [takeWhile_append_stop_chain hall_rev hpfx_stop]
            exact List.reverse_reverse hr_d.toList
          have hdigs_ne_bool : ((rest₃.dropEnd "h".length).toString.toList.reverse.takeWhile
              Char.isDigit).reverse.isEmpty = false := by
            rw [show ((rest₃.dropEnd "h".length).toString.toList.reverse.takeWhile
                Char.isDigit).reverse = hr_d.toList from hdigs_eq]
            simp; intro he; exact hwf_h.ne_empty (by ext; simp [he])
          simp only [hdigs_ne_bool, Bool.false_eq_true, ite_false, bind, Option.bind] at h₄
          obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hwf_h.toNat?'_isSome
          have hnat_eq : toNat?' (String.ofList ((rest₃.dropEnd "h".length).toString.toList.reverse.takeWhile
              Char.isDigit |>.reverse)) = some n := by
            rw [hdigs_eq, show String.ofList hr_d.toList = hr_d from by simp]; exact hnat
          rw [hnat_eq] at h₄
          have h_int64 : Int64.ofInt? (signedQuantity isNegative n) = none := by
            unfold signedQuantity
            cases isNegative <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h₄ ⊢ <;> (
              unfold durationUnits? at h₄; cases hᵢ : Int64.ofInt? _ <;> simp_all)
          have hn_gt := nat_gt_max_of_int64_ofInt?_none_signedQuantity isNegative n h_int64
          have hext_n : (extractPair rest₃ "h").1 = n := by
            unfold extractPair; simp only [hew, ite_true]
            rw [hdigs_eq, show String.ofList hr_d.toList = hr_d from by simp]; simp [hnat]
          simp only [Bool.false_eq_true, ite_false]
          symm
          rw [duration?_eq_none_iff_overflow]
          unfold computeSignedBodyValueD computeBodyValueD
          -- The chain: rest₁ = extract body "ms" .2, rest₂ = extract rest₁ "s" .2, etc.
          simp only [← hr₁, ← hr₂, ← hr₃, hext_n]
          simp only [MILLISECONDS_PER_DAY, MILLISECONDS_PER_HOUR,
            MILLISECONDS_PER_MINUTE, MILLISECONDS_PER_SECOND, Int64.MAX, Int64.MIN] at hn_gt ⊢
          cases hisNeg : isNegative with
          | false => simp_all; omega
          | true =>
            have := neg_bound_of_int64_overflow isNegative n h_int64 hisNeg
            simp only [Int64.MAX] at this; omega
        | some p₄ =>
          obtain ⟨v_h, rest₄⟩ := p₄; simp only []
          cases h₅ : parseUnit? isNegative rest₄ "d" with
          | none =>
            have hr₁ := parseUnit?_success_rest isNegative body "ms" v_ms rest₁ h₁
            have hr₂ := parseUnit?_success_rest isNegative rest₁ "s" v_s rest₂ h₂
            have hr₃ := parseUnit?_success_rest isNegative rest₂ "m" v_m rest₃ h₃
            have hr₄ := parseUnit?_success_rest isNegative rest₃ "h" v_h rest₄ h₄
            have hew : rest₄.endsWith "d" = true := by
              by_contra hne
              simp only [Bool.not_eq_true] at hne
              have := parseUnit?_no_endsWith isNegative rest₄ "d" hne
              rw [h₅] at this; simp at this
            obtain ⟨⟨days, hours, minutes, seconds, milliseconds⟩, _, hwf_q, hbody⟩ := h
            simp only [Components.quantitiesWf, IsWfOptionalQuantity] at hwf_q
            obtain ⟨hwf_d, hwf_h, hwf_m, hwf_s, hwf_ms⟩ := hwf_q
            subst hbody
            have hrest₄ : rest₄ = durationChunk days "d" := by
              rw [hr₄]
              have hrest₁ : rest₁ = (extractPair
                  (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩) "ms").2 := hr₁
              have hrest₂ : rest₂ = (extractPair rest₁ "s").2 := hr₂
              have hrest₃ : rest₃ = (extractPair rest₂ "m").2 := hr₃
              have hrest₃_eq : rest₃ = durationChunk days "d" ++ durationChunk hours "h" := by
                rw [hrest₃, hrest₂, hrest₁]
                -- Extract ms step
                have hms_step : (extractPair
                    (Components.asString ⟨days, hours, minutes, seconds, milliseconds⟩)
                    "ms").2 =
                    durationChunk days "d" ++ durationChunk hours "h" ++
                    durationChunk minutes "m" ++ durationChunk seconds "s" := by
                  unfold Components.asString
                  cases milliseconds with
                  | none =>
                    simp only [durationChunk, String.append_empty]
                    unfold extractPair
                    have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m" ++ durationChunk seconds "s").endsWith "ms" = false := by
                      cases seconds with
                      | none =>
                        rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                          rcases days with _ | d_d <;>
                          simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                          (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                            simp [List.getLast?_append, List.getLast?_cons] at this)
                      | some s_d =>
                        have h_iq : IsDigits s_d := hwf_s
                        have := not_endsWith_ms_of_digits_s_chain
                          (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m") s_d h_iq
                        simp only [String.append_assoc, durationChunk] at this ⊢
                        exact this
                    simp only [durationChunk] at hew'; simp [hew']
                  | some ms_d =>
                    have h_iq := hwf_ms
                    have hsome := h_iq.toNat?'_isSome
                    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
                    have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m" ++ durationChunk seconds "s") = "" ∨
                        ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                          durationChunk minutes "m" ++ durationChunk seconds "s").toList.reverse =
                          c :: cs ∧ c.isDigit = false := by
                      rcases seconds with _ | s_d <;> rcases minutes with _ | m_d <;>
                        rcases hours with _ | hr_d <;> rcases days with _ | d_d <;>
                        simp [durationChunk, String.toList_append]
                    have hstep := extract_step_chain
                      (durationChunk days "d" ++ durationChunk hours "h" ++ durationChunk minutes "m" ++
                        durationChunk seconds "s") ms_d "ms" n h_iq hnat hpfx_end
                    simp only [durationChunk, String.append_assoc] at hstep ⊢
                    exact hstep
                rw [hms_step]
                -- Extract s step
                have hs_step : (extractPair
                    (durationChunk days "d" ++ durationChunk hours "h" ++
                     durationChunk minutes "m" ++ durationChunk seconds "s") "s").2 =
                    durationChunk days "d" ++ durationChunk hours "h" ++
                    durationChunk minutes "m" := by
                  cases seconds with
                  | none =>
                    simp only [durationChunk, String.append_empty]
                    unfold extractPair
                    have hew' : (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m").endsWith "s" = false := by
                      rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                        rcases days with _ | d_d <;>
                        simp [durationChunk, String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice, String.toList_append] <;>
                        (intro ⟨t, ht⟩; have := congrArg List.getLast? ht;
                          simp [List.getLast?_append, List.getLast?_cons] at this)
                    simp only [durationChunk] at hew'; simp [hew']
                  | some s_d =>
                    have h_iq := hwf_s
                    have hsome := h_iq.toNat?'_isSome
                    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
                    have hpfx_end : (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m") = "" ∨
                        ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h" ++
                          durationChunk minutes "m").toList.reverse = c :: cs ∧
                          c.isDigit = false := by
                      rcases minutes with _ | m_d <;> rcases hours with _ | hr_d <;>
                        rcases days with _ | d_d <;>
                        simp [durationChunk, String.toList_append]
                    have hstep := extract_step_chain
                      (durationChunk days "d" ++ durationChunk hours "h" ++
                        durationChunk minutes "m") s_d "s" n h_iq hnat hpfx_end
                    simp only [durationChunk, String.append_assoc] at hstep ⊢
                    exact hstep
                rw [hs_step]
                -- Extract m step
                have hm_step : (extractPair
                    (durationChunk days "d" ++ durationChunk hours "h" ++
                     durationChunk minutes "m") "m").2 =
                    durationChunk days "d" ++ durationChunk hours "h" := by
                  cases minutes with
                  | none =>
                    simp only [durationChunk, String.append_empty]
                    unfold extractPair
                    cases hours with
                    | none =>
                      simp only [String.append_empty]
                      cases days with
                      | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
                      | some d_d =>
                        have h_iq := hwf_d
                        obtain ⟨hne_d, _⟩ := h_iq
                        have hne_list : (d_d ++ "d").toList ≠ [] := by
                          simp only [String.toList_append]
                          exact List.append_ne_nil_of_right_ne_nil _ (by decide)
                        have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
                          simp [String.toList_append, List.getLast_append_of_ne_nil]
                        have hew' : (d_d ++ "d").endsWith "m" = false := by
                          apply not_endsWith_single_of_last_ne _ 'm' hne_list
                          rw [hlast]; decide
                        simp [hew']
                    | some hr_d =>
                      have h_iq := hwf_h
                      obtain ⟨hne_h, _⟩ := h_iq
                      have hne_list : (durationChunk days "d" ++ (hr_d ++ "h")).toList ≠ [] := by
                        simp only [String.toList_append]
                        intro habs
                        have := List.append_eq_nil_iff.mp habs
                        simp at this
                      have hlast : (durationChunk days "d" ++ (hr_d ++ "h")).toList.getLast hne_list = 'h' := by
                        simp [String.toList_append, List.getLast_append_of_ne_nil]
                      have hew' : (durationChunk days "d" ++ (hr_d ++ "h")).endsWith "m" = false := by
                        apply not_endsWith_single_of_last_ne _ 'm' hne_list
                        rw [hlast]; decide
                      simp only [durationChunk] at hew' ⊢
                      simp [hew']
                  | some m_d =>
                    have h_iq := hwf_m
                    have hsome := h_iq.toNat?'_isSome
                    obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
                    have hpfx_end : durationChunk days "d" ++ durationChunk hours "h" = "" ∨
                        ∃ c cs, (durationChunk days "d" ++ durationChunk hours "h").toList.reverse =
                          c :: cs ∧ c.isDigit = false := by
                      cases days with
                      | none =>
                        cases hours with
                        | none => left; simp [durationChunk]
                        | some hr_d =>
                          right
                          exact pfx_append_chunk_reverse_non_digit "" hr_d "h" hwf_h (Or.inr (Or.inl rfl))
                      | some d_d =>
                        right
                        cases hours with
                        | none =>
                          simp only [durationChunk, String.append_empty]
                          exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
                        | some hr_d =>
                          exact pfx_append_chunk_reverse_non_digit (durationChunk (some d_d) "d") hr_d "h" hwf_h
                            (Or.inr (Or.inl rfl))
                    have hstep := extract_step_chain
                      (durationChunk days "d" ++ durationChunk hours "h") m_d "m" n
                      h_iq hnat hpfx_end
                    simp only [durationChunk, String.append_assoc] at hstep ⊢
                    exact hstep
                exact hm_step
              rw [hrest₃_eq]
              -- Extract h step: (extractPair (dChunk days "d" ++ dChunk hours "h") "h").2
              cases hours with
              | none =>
                simp only [durationChunk, String.append_empty]
                unfold extractPair
                cases days with
                | none => simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice]
                | some d_d =>
                  have h_iq := hwf_d
                  obtain ⟨hne_d, _⟩ := h_iq
                  have hne_list : (d_d ++ "d").toList ≠ [] := by
                    simp only [String.toList_append]
                    exact List.append_ne_nil_of_right_ne_nil _ (by decide)
                  have hlast : (d_d ++ "d").toList.getLast hne_list = 'd' := by
                    simp [String.toList_append, List.getLast_append_of_ne_nil]
                  have hew' : (d_d ++ "d").endsWith "h" = false := by
                    apply not_endsWith_single_of_last_ne _ 'h' hne_list
                    rw [hlast]; decide
                  simp [hew']
              | some hr_d =>
                have h_iq := hwf_h
                have hsome := h_iq.toNat?'_isSome
                obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hsome
                have hpfx_end : durationChunk days "d" = "" ∨
                    ∃ c cs, (durationChunk days "d").toList.reverse = c :: cs ∧
                      c.isDigit = false := by
                  cases days with
                  | none => left; simp [durationChunk]
                  | some d_d =>
                    right
                    exact pfx_append_chunk_reverse_non_digit "" d_d "d" hwf_d (Or.inl rfl)
                have hstep := extract_step_chain (durationChunk days "d") hr_d "h" n
                  h_iq hnat hpfx_end
                simp only [durationChunk, String.append_assoc] at hstep ⊢
                exact hstep
            have hdays_some : ∃ d_d, days = some d_d := by
              cases days with
              | none =>
                have hdc : durationChunk none "d" = "" := rfl
                rw [hdc] at hrest₄
                rw [hrest₄] at hew
                simp [String.endsWith_eq_endsWith_toSlice, -String.endsWith_toSlice] at hew
              | some d_d => exact ⟨d_d, rfl⟩
            obtain ⟨d_d, hdays_eq⟩ := hdays_some
            rw [hdays_eq] at hrest₄ hwf_d
            simp only [durationChunk] at hrest₄
            -- rest₄ = d_d ++ "d", extract digits from it
            rw [parseUnit?_eq_norm] at h₅
            unfold parseUnit?_norm at h₅
            simp only [hew, ite_true] at h₅
            have hrest₄_drop : (rest₄.dropEnd "d".length).toString = d_d := by
              rw [hrest₄]
              apply String.ext; simp [String.toList_append, ← String.length_toList]
            have hall_digits_d : ∀ c ∈ d_d.toList, Char.isDigit c = true :=
              allDigit_of_isDurationQuantity d_d hwf_d
            have hd_ne : d_d.toList ≠ [] := by
              intro he; exact hwf_d.ne_empty (by ext; simp [he])
            have hdigs_eq : ((rest₄.dropEnd "d".length).toString.toList.reverse.takeWhile
                Char.isDigit).reverse = d_d.toList := by
              rw [hrest₄_drop]
              have hall_rev : ∀ c ∈ d_d.toList.reverse, Char.isDigit c = true := by
                intro c hc; exact hall_digits_d c (List.mem_reverse.mp hc)
              have htw_all : (d_d.toList.reverse ++ []).takeWhile Char.isDigit =
                  d_d.toList.reverse :=
                takeWhile_append_stop_chain hall_rev (Or.inl rfl)
              simp at htw_all
              rw [htw_all]
              exact List.reverse_reverse d_d.toList
            have hdigs_ne_bool : ((rest₄.dropEnd "d".length).toString.toList.reverse.takeWhile
                Char.isDigit).reverse.isEmpty = false := by
              rw [show ((rest₄.dropEnd "d".length).toString.toList.reverse.takeWhile
                  Char.isDigit).reverse = d_d.toList from hdigs_eq]
              simp; intro he; exact hwf_d.ne_empty (by ext; simp [he])
            simp only [hdigs_ne_bool, Bool.false_eq_true, ite_false, bind, Option.bind] at h₅
            obtain ⟨n, hnat⟩ := Option.isSome_iff_exists.mp hwf_d.toNat?'_isSome
            have hnat_eq : toNat?' (String.ofList ((rest₄.dropEnd "d".length).toString.toList.reverse.takeWhile
                Char.isDigit |>.reverse)) = some n := by
              rw [hdigs_eq, show String.ofList d_d.toList = d_d from by simp]; exact hnat
            rw [hnat_eq] at h₅
            have h_int64 : Int64.ofInt? (signedQuantity isNegative n) = none := by
              unfold signedQuantity
              cases isNegative <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h₅ ⊢ <;> (
                unfold durationUnits? at h₅; cases hᵢ : Int64.ofInt? _ <;> simp_all)
            have hn_gt := nat_gt_max_of_int64_ofInt?_none_signedQuantity isNegative n h_int64
            have hext_n : (extractPair rest₄ "d").1 = n := by
              unfold extractPair; simp only [hew, ite_true]
              rw [hdigs_eq, show String.ofList d_d.toList = d_d from by simp]; simp [hnat]
            simp only [Bool.false_eq_true, ite_false]
            symm
            rw [duration?_eq_none_iff_overflow]
            unfold computeSignedBodyValueD computeBodyValueD
            -- The chain: rest₁ = extract body "ms" .2, rest₂ = extract rest₁ "s" .2, etc.
            simp only [← hr₁, ← hr₂, ← hr₃, ← hr₄, hext_n]
            simp only [MILLISECONDS_PER_DAY, MILLISECONDS_PER_HOUR,
              MILLISECONDS_PER_MINUTE, MILLISECONDS_PER_SECOND, Int64.MAX, Int64.MIN] at hn_gt ⊢
            cases hisNeg : isNegative with
            | false => simp_all; omega
            | true =>
              have := neg_bound_of_int64_overflow isNegative n h_int64 hisNeg
              simp only [Int64.MAX] at this; omega
          | some p₅ =>
            obtain ⟨v_d, rest₅⟩ := p₅; simp only []
            have hrest₅_empty : rest₅ = "" :=
              extract_chain_rest_empty_of_wf isNegative body h h₁ h₂ h₃ h₄ h₅
            have hrest₅_isEmpty : rest₅.isEmpty = true := String.isEmpty_iff.mpr hrest₅_empty
            simp only [hrest₅_isEmpty, ite_true]
            -- Goal: duration? (v_d + v_h + v_m + v_s + v_ms) =
            --       duration? (computeSignedBodyValue isNegative body)
            have hr₁ := parseUnit?_success_rest isNegative body "ms" v_ms rest₁ h₁
            have hr₂ := parseUnit?_success_rest isNegative rest₁ "s" v_s rest₂ h₂
            have hr₃ := parseUnit?_success_rest isNegative rest₂ "m" v_m rest₃ h₃
            have hr₄ := parseUnit?_success_rest isNegative rest₃ "h" v_h rest₄ h₄
            have hv_ms := parseUnit?_val_eq_ms isNegative body v_ms rest₁ h₁
            have hv_s := parseUnit?_val_eq_s isNegative rest₁ v_s rest₂ h₂
            have hv_m := parseUnit?_val_eq_min isNegative rest₂ v_m rest₃ h₃
            have hv_h := parseUnit?_val_eq_hr isNegative rest₃ v_h rest₄ h₄
            have hv_d := parseUnit?_val_eq_day isNegative rest₄ v_d rest₅ h₅
            rw [hv_ms, hv_s, hv_m, hv_h, hv_d]
            unfold computeSignedBodyValueD computeBodyValueD
            simp only [← hr₁, ← hr₂, ← hr₃, ← hr₄]
            unfold signedQuantity MILLISECONDS_PER_DAY MILLISECONDS_PER_HOUR
              MILLISECONDS_PER_MINUTE MILLISECONDS_PER_SECOND
            cases isNegative with
            | false => simp
            | true =>
              simp [show ∀ m : Nat, Int.negOfNat m = -(↑m : Int) from by
                intro m; cases m <;> simp [Int.negOfNat, Int.negSucc_eq]]
              congr 1; omega

/-- `parseDuration?` always returns `none` on a body string that is not well-formed. -/
theorem parseDuration?_none_of_not_wf (isNegative : Bool) (body : String)
    (h : ¬ IsWfBody body) :
    parseDuration? isNegative body = none := by
  cases hparse : parseDuration? isNegative body with
  | none => rfl
  | some d => exact absurd (wf_of_parseDuration?_eq_some isNegative body d hparse) h

/-- On a well-formed body, `parseDuration?` fails if and only if the computed value overflows Int64.
    Phrased in terms of the total `computeSignedBodyValueD`, which coincides with
    `computeSignedBodyValue`'s payload on well-formed input. -/
theorem parseDuration?_eq_none_iff_overflow_of_wf (isNegative : Bool) (body : String)
    (h : IsWfBody body) :
    parseDuration? isNegative body = none ↔
      computeSignedBodyValueD isNegative body < Int64.MIN ∨
        computeSignedBodyValueD isNegative body > Int64.MAX := by
  rw [parseDuration?_eq_duration?_of_wf isNegative body h]
  exact duration?_eq_none_iff_overflow (computeSignedBodyValueD isNegative body)

/-- `parseDuration?` fails if and only if the body is not well-formed, or the computed value
    overflows Int64. Combines `parseDuration?_none_of_not_wf` and
    `parseDuration?_eq_none_iff_overflow_of_wf` into a single biconditional. -/
theorem parseDuration?_eq_none_iff (isNegative : Bool) (body : String) :
    parseDuration? isNegative body = none ↔
      ¬ IsWfBody body ∨
        (computeSignedBodyValueD isNegative body < Int64.MIN ∨
          computeSignedBodyValueD isNegative body > Int64.MAX) := by
  by_cases hwf : IsWfBody body
  · rw [parseDuration?_eq_none_iff_overflow_of_wf isNegative body hwf]
    simp [hwf]
  · rw [parseDuration?_none_of_not_wf isNegative body hwf]
    simp [hwf]


/-- `IsWfDuration` on a full duration string is equivalent to `IsWfBody` on its body
    (the part after stripping any leading `-`). This bridges the string-level and body-level
    well-formedness predicates. -/
theorem wf_str_iff_signed_body (str : String) :
    IsWfDuration str ↔
      let (_, body) := isNegativeDuration str
      IsWfBody body := by
  by_cases hfront : str.front = '-'
  · have hsplit : isNegativeDuration str = (true, (str.drop 1).copy) := by
      unfold isNegativeDuration
      rw [hfront]
      simp
    simp [hsplit]
    constructor
    · rintro ⟨sign, body, hstr_eq, (rfl | rfl), hbody⟩
      · -- Signed: `str = "-" ++ body`, so the stripped body is exactly `body`.
        subst str
        simpa [dash_append_drop_one_copy] using hbody
      · -- Unsigned: the body would have to start with `'-'`, which it never does.
        simp only [String.empty_append] at hstr_eq
        rw [hstr_eq] at hfront
        exact False.elim ((duration_body_front_ne_dash body hbody) hfront)
    · intro hbody
      exact ⟨"-", (str.drop 1).copy,
        string_eq_dash_append_drop_one_of_front_eq_dash str hfront, Or.inl rfl, hbody⟩
  · have hsplit : isNegativeDuration str = (false, str) := by
      unfold isNegativeDuration
      split
      · contradiction
      · rfl
    simp [hsplit]
    constructor
    · rintro ⟨sign, body, hstr_eq, (rfl | rfl), hbody⟩
      · -- Signed is impossible here: `str` does not start with `'-'`.
        exact False.elim (hfront (by
          subst str
          exact dash_append_front_eq_dash body))
      · simp only [String.empty_append] at hstr_eq
        subst str
        exact hbody
    · intro hbody
      exact ⟨"", str, by simp, Or.inr rfl, hbody⟩

theorem compute_value_eq_signed_body_value (str : String) (_hwf : IsWfDuration str) :
    computeValue str =
      let (isNegative, body) := isNegativeDuration str
      computeSignedBodyValue isNegative body := rfl

theorem duration?_some_toInt (value : Int) (d : Duration)
    (h : duration? value = some d) :
    d.val.toInt = value := by
  unfold duration? at h
  cases hv : Int64.ofInt? value with
  | none =>
    simp [hv] at h
  | some i =>
    simp [hv] at h
    subst h
    exact Int64.ofInt?_some_toInt hv

theorem Int64.sub?_add?_inverse (a b c : Int64)
    (h : Int64.add? a b = some c) :
    Int64.sub? c a = some b := by
  unfold Int64.add? at h
  unfold Int64.sub?
  cases hs : Int64.ofInt? (a.toInt + b.toInt) with
  | none =>
    simp [hs] at h
  | some i =>
    simp [hs] at h
    subst h
    have hi : i.toInt = a.toInt + b.toInt := Int64.ofInt?_some_toInt hs
    rw [hi]
    have hsub : a.toInt + b.toInt - a.toInt = b.toInt := by omega
    rw [hsub]
    exact Int64.ofInt?_toInt b

-- ═══════════════════════════════════════════════════════════════════════════════
-- ROUNDTRIP: Duration.parse ∘ Duration.toString = some
-- ═══════════════════════════════════════════════════════════════════════════════

private theorem toNat?'_toString (n : Nat) : toNat?' (toString n) = some n := by
  unfold toNat?'
  have hno_us : (toString n).contains '_' = false := by
    have h : ¬ ('_' ∈ (toString n).toList) := by
      rw [Nat.toString_eq_repr, Nat.toList_repr]
      exact Nat.underscore_not_in_toDigits
    simp [String.contains]
  rw [hno_us]
  simp [Nat.toString_eq_repr]

private theorem toNat?'_repr (n : Nat) : toNat?' (Nat.repr n) = some n := by
  simpa [Nat.toString_eq_repr] using toNat?'_toString n

theorem duration?_of_val_toInt (d : Duration) :
    duration? d.val.toInt = some d := by
  unfold duration?
  rw [Int64.ofInt?_toInt]
  rfl

private theorem isDurationQuantity_toString (n : Nat) :
    IsDigits (toString n) :=
  isDigits_of_toNat?'_isSome (by rw [toNat?'_toString]; simp)

private theorem isDurationQuantity_repr (n : Nat) :
    IsDigits (Nat.repr n) := by
  simpa [Nat.toString_eq_repr] using isDurationQuantity_toString n

private theorem repr_zero_ms : Nat.repr 0 ++ "ms" = "0ms" := by
  apply String.ext
  simp [Nat.toList_repr]

private theorem canonicalDurationComponents_nonempty
    (days hours minutes seconds ms : Nat) :
    (canonicalComponents days hours minutes seconds ms).nonempty := by
  simp [canonicalComponents, Components.nonempty]

private theorem canonicalDurationComponents_quantitiesWf
    (days hours minutes seconds ms : Nat) :
    (canonicalComponents days hours minutes seconds ms).quantitiesWf := by
  simp [canonicalComponents, Components.quantitiesWf, IsWfOptionalQuantity,
    isDurationQuantity_repr]

private theorem canonicalDurationComponents_asString
    (days hours minutes seconds ms : Nat) :
    (canonicalComponents days hours minutes seconds ms).asString =
      canonicalBody days hours minutes seconds ms := by
  unfold canonicalComponents Components.asString canonicalBody
    durationComponent durationChunk
  simp [String.append_assoc]

theorem canonicalDurationBody_wf (days hours minutes seconds ms : Nat) :
    IsWfBody (canonicalBody days hours minutes seconds ms) :=
  ⟨canonicalComponents days hours minutes seconds ms,
    canonicalDurationComponents_nonempty days hours minutes seconds ms,
    canonicalDurationComponents_quantitiesWf days hours minutes seconds ms,
    (canonicalDurationComponents_asString days hours minutes seconds ms).symm⟩

theorem isNegativeDuration_neg_body (body : String) :
    isNegativeDuration ("-" ++ body) = (true, body) := by
  unfold isNegativeDuration
  rw [dash_append_front_eq_dash]
  simp [dash_append_drop_one_copy]

theorem isNegativeDuration_canonical_body (body : String) (hfront : body.front ≠ '-') :
    isNegativeDuration body = (false, body) := by
  unfold isNegativeDuration
  split
  · contradiction
  · rfl

theorem canonicalDurationBody_value (days hours minutes seconds ms : Nat) :
    computeBodyValue (canonicalBody days hours minutes seconds ms) =
      (days : Int) * MILLISECONDS_PER_DAY +
      (hours : Int) * MILLISECONDS_PER_HOUR +
      (minutes : Int) * MILLISECONDS_PER_MINUTE +
      (seconds : Int) * MILLISECONDS_PER_SECOND +
      (ms : Int) := by
  have hms : extractTrailingQuantity
      (canonicalBody days hours minutes seconds ms) "ms" =
      (ms, durationComponent days "d" ++ durationComponent hours "h" ++
        durationComponent minutes "m" ++ durationComponent seconds "s") := by
    unfold canonicalBody durationComponent
    have hpfx : ((toString days ++ "d") ++ (toString hours ++ "h") ++
        (toString minutes ++ "m") ++ (toString seconds ++ "s")).toList.reverse =
        ((toString days ++ "d") ++ (toString hours ++ "h") ++
          (toString minutes ++ "m") ++ (toString seconds ++ "s")).toList.reverse := rfl
    have hpfx_end :
        ((toString days ++ "d") ++ (toString hours ++ "h") ++
          (toString minutes ++ "m") ++ (toString seconds ++ "s")) = "" ∨
        ∃ c cs, (((toString days ++ "d") ++ (toString hours ++ "h") ++
          (toString minutes ++ "m") ++ (toString seconds ++ "s")).toList.reverse =
          c :: cs ∧ c.isDigit = false) := by
      right
      exact pfx_append_chunk_reverse_non_digit
          ((toString days ++ "d") ++ (toString hours ++ "h") ++ (toString minutes ++ "m"))
          (toString seconds) "s" (isDurationQuantity_toString seconds)
          (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    simpa [String.append_assoc] using
      extract_step_chain_pair
        ((toString days ++ "d") ++ (toString hours ++ "h") ++
          (toString minutes ++ "m") ++ (toString seconds ++ "s"))
        (toString ms) "ms" ms (isDurationQuantity_toString ms) (toNat?'_toString ms)
        hpfx_end
  have hs : extractTrailingQuantity
      (durationComponent days "d" ++ durationComponent hours "h" ++
        durationComponent minutes "m" ++ durationComponent seconds "s") "s" =
      (seconds, durationComponent days "d" ++ durationComponent hours "h" ++
        durationComponent minutes "m") := by
    unfold durationComponent
    have hpfx_end :
        ((toString days ++ "d") ++ (toString hours ++ "h") ++
          (toString minutes ++ "m")) = "" ∨
        ∃ c cs, (((toString days ++ "d") ++ (toString hours ++ "h") ++
          (toString minutes ++ "m")).toList.reverse = c :: cs ∧ c.isDigit = false) := by
      right
      exact pfx_append_chunk_reverse_non_digit
          ((toString days ++ "d") ++ (toString hours ++ "h"))
          (toString minutes) "m" (isDurationQuantity_toString minutes)
          (Or.inr (Or.inr (Or.inl rfl)))
    simpa [String.append_assoc] using
      extract_step_chain_pair
        ((toString days ++ "d") ++ (toString hours ++ "h") ++ (toString minutes ++ "m"))
        (toString seconds) "s" seconds (isDurationQuantity_toString seconds)
        (toNat?'_toString seconds) hpfx_end
  have hm : extractTrailingQuantity
      (durationComponent days "d" ++ durationComponent hours "h" ++ durationComponent minutes "m")
      "m" =
      (minutes, durationComponent days "d" ++ durationComponent hours "h") := by
    unfold durationComponent
    have hpfx_end :
        ((toString days ++ "d") ++ (toString hours ++ "h")) = "" ∨
        ∃ c cs, (((toString days ++ "d") ++ (toString hours ++ "h")).toList.reverse =
          c :: cs ∧ c.isDigit = false) := by
      right
      exact pfx_append_chunk_reverse_non_digit (toString days ++ "d")
          (toString hours) "h" (isDurationQuantity_toString hours)
          (Or.inr (Or.inl rfl))
    simpa [String.append_assoc] using
      extract_step_chain_pair ((toString days ++ "d") ++ (toString hours ++ "h"))
        (toString minutes) "m" minutes (isDurationQuantity_toString minutes)
        (toNat?'_toString minutes) hpfx_end
  have hh : extractTrailingQuantity
      (durationComponent days "d" ++ durationComponent hours "h") "h" =
      (hours, durationComponent days "d") := by
    unfold durationComponent
    have hpfx_end :
        (toString days ++ "d") = "" ∨
        ∃ c cs, (toString days ++ "d").toList.reverse = c :: cs ∧ c.isDigit = false := by
      right
      exact pfx_append_chunk_reverse_non_digit "" (toString days) "d"
          (isDurationQuantity_toString days) (Or.inl rfl)
    simpa [String.append_assoc] using
      extract_step_chain_pair (toString days ++ "d") (toString hours) "h" hours
        (isDurationQuantity_toString hours) (toNat?'_toString hours) hpfx_end
  have hd : extractTrailingQuantity (durationComponent days "d") "d" = (days, "") := by
    unfold durationComponent
    simpa using extract_step_chain_pair "" (toString days) "d" days
      (isDurationQuantity_toString days) (toNat?'_toString days) (Or.inl rfl)
  unfold computeBodyValue
  simp [hms, hs, hm, hh, hd]

private theorem durationParts_value_nat (n : Nat) :
    n / 86400000 * 86400000 +
        n % 86400000 / 3600000 * 3600000 +
      n % 86400000 % 3600000 / 60000 * 60000 +
    n % 86400000 % 3600000 % 60000 / 1000 * 1000 +
    n % 86400000 % 3600000 % 60000 % 1000 = n := by
  have h₁ := Nat.div_add_mod n 86400000
  have h₂ := Nat.div_add_mod (n % 86400000) 3600000
  have h₃ := Nat.div_add_mod (n % 86400000 % 3600000) 60000
  have h₄ := Nat.div_add_mod (n % 86400000 % 3600000 % 60000) 1000
  omega

theorem durationParts_value_int (n : Nat) :
    (↑(n / MILLISECONDS_PER_DAY.toNat) : Int) * MILLISECONDS_PER_DAY +
        (↑(n % MILLISECONDS_PER_DAY.toNat / MILLISECONDS_PER_HOUR.toNat) : Int) *
          MILLISECONDS_PER_HOUR +
      (↑(n % MILLISECONDS_PER_DAY.toNat % MILLISECONDS_PER_HOUR.toNat /
          MILLISECONDS_PER_MINUTE.toNat) : Int) *
        MILLISECONDS_PER_MINUTE +
    (↑(n % MILLISECONDS_PER_DAY.toNat % MILLISECONDS_PER_HOUR.toNat %
        MILLISECONDS_PER_MINUTE.toNat / MILLISECONDS_PER_SECOND.toNat) : Int) *
      MILLISECONDS_PER_SECOND +
    (↑(n % MILLISECONDS_PER_DAY.toNat % MILLISECONDS_PER_HOUR.toNat %
        MILLISECONDS_PER_MINUTE.toNat % MILLISECONDS_PER_SECOND.toNat) : Int) =
      n := by
  change
    (↑(n / 86400000) : Int) * 86400000 +
        (↑(n % 86400000 / 3600000) : Int) * 3600000 +
      (↑(n % 86400000 % 3600000 / 60000) : Int) * 60000 +
    (↑(n % 86400000 % 3600000 % 60000 / 1000) : Int) * 1000 +
    (↑(n % 86400000 % 3600000 % 60000 % 1000) : Int) = n
  have h := durationParts_value_nat n
  omega

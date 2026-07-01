module

public import Cedar.Thm.Ext.Decimal.Lemmas

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Ext.Decimal.Grammar
import all Cedar.Thm.Ext.Decimal.Lemmas

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

/-- Completeness of `Decimal.parse`: if a string is well-formed and its computed value
    matches `d.toInt`, then parsing accepts the string as `d`. -/
public theorem parse_complete (s : String) (d : Decimal)
    (hwf : IsWfStr s) (hval : computeValue s = some d.toInt) :
    Decimal.parse s = some d := by
  obtain ⟨left, right, h_split, h_ne, h_rpos, h_rle, h_lint, h_rnat⟩ := isWfStr_iff.mp hwf
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
      rw [parse_value_eq_sign_form]
      have := hval
      simp only [computeValue, h_split, hl, hr, Option.some.injEq] at this
      exact this
    rw [hval']
    exact Int64.ofInt?_toInt d
  · rename_i h; exact (h left right rfl).elim

/-- Parsing the canonical string representation of a decimal returns the same decimal. -/
public theorem parse_toString_roundtrip (d : Decimal) :
    Decimal.parse (toString d) = some d :=
  parse_complete (toString d) d (toString_isWfStr d) (computeValue_toString d)

/-- Failure characterization for `Decimal.parse`: parsing rejects exactly strings that are
    not well-formed or whose computed value overflows the `Int64` range. -/
public theorem parse_eq_none_iff (s : String) :
    Decimal.parse s = none ↔ ¬ IsWfStr s ∨
    ∃ v, computeValue s = some v ∧ (v < Int64.MIN ∨ v > Int64.MAX) := by
  constructor
  · -- → direction: parse s = none implies malformed or overflow
    intro h
    by_cases hwf : IsWfStr s
    · -- s is well-formed, so it must be overflow
      right
      obtain ⟨left, right, h_split, h_ne, h_rpos, h_rle, h_lint, h_rnat⟩ := isWfStr_iff.mp hwf
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h_lint
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_rnat
      -- parse returned none despite well-formedness → decimal? returned none → overflow
      unfold Decimal.parse at h
      rw [h_split] at h
      simp only [show 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS from ⟨h_rpos, h_rle⟩,
        hl, hr, Decimal.decimal?, ite_true, and_true] at h
      -- h : Int64.ofInt? (if ... then ... + ... else ... - ...) = none
      refine ⟨_, ?_, Int64.ofInt?_none_iff.mpr h⟩
      rw [parse_value_eq_sign_form]
      simp only [computeValue, h_split, hl, hr]
    · left; exact hwf
  · -- ← direction: malformed or overflow implies parse s = none
    intro h
    rcases h with h | ⟨v, hcv, hovf⟩
    · -- ¬ IsWfStr s → parse s = none
      by_contra hne
      have ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
      exact absurd (parse_some_isWfStr s d hd) h
    · -- overflow → parse s = none
      -- If s is not well-formed, parse = none trivially
      by_cases hwf : IsWfStr s
      · -- s is well-formed but overflows
        obtain ⟨left, right, h_split, h_ne, h_rpos, h_rle, h_lint, h_rnat⟩ := isWfStr_iff.mp hwf
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h_lint
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h_rnat
        unfold Decimal.parse
        rw [h_split]
        simp only [show 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS from ⟨h_rpos, h_rle⟩,
          hl, hr, Decimal.decimal?, ite_true, and_true]
        -- Goal: Int64.ofInt? (if ... then ... else ...) = none
        -- computeValue s = some v is out of range, and equals this branching expression
        have hcv' : (if !left.startsWith "-"
            then l * Int.pow 10 DECIMAL_DIGITS + ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length)
            else l * Int.pow 10 DECIMAL_DIGITS - ↑r * Int.pow 10 (DECIMAL_DIGITS - right.length))
            = v := by
          rw [parse_value_eq_sign_form]
          have := hcv
          simp only [computeValue, h_split, hl, hr, Option.some.injEq] at this
          exact this
        rw [hcv']
        exact Int64.ofInt?_none_iff.mp hovf
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
        exact isWfStr_iff.mpr ⟨left, right, h_split, h_ne, h_len.1, h_len.2,
          by rw [heq_l]; rfl, by rw [heq_r]; rfl⟩
      · simp at h
    · simp at h

/-- Soundness of `Decimal.parse`: if parsing succeeds, then the input is well-formed,
    its computed value is in the `Int64` range, and the returned decimal has exactly
    that computed value. -/
public theorem parse_sound (s : String) (d : Decimal) (h : Decimal.parse s = some d) :
    IsWfStr s ∧
    computeValue s = some d.toInt ∧
    Int64.MIN ≤ d.toInt ∧
    d.toInt ≤ Int64.MAX := by
  -- parse succeeded, so `parse_eq_none_iff` rules out both malformedness and overflow.
  have hnot_bad : ¬ (¬ IsWfStr s ∨
      ∃ v, computeValue s = some v ∧ (v < Int64.MIN ∨ v > Int64.MAX)) := by
    intro hbad
    have hnone := (parse_eq_none_iff s).mpr hbad
    simp [h] at hnone
  have hwf : IsWfStr s := by
    by_contra hnwf
    exact hnot_bad (Or.inl hnwf)
  -- well-formed ⇒ `computeValue s = some v` for some value `v`.
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (computeValue_isSome_of_isWfStr hwf)
  have hnot_ovf : ¬ (v < Int64.MIN ∨ v > Int64.MAX) := fun hovf =>
    hnot_bad (Or.inr ⟨v, hv, hovf⟩)
  have hmin : Int64.MIN ≤ v := by omega
  have hmax : v ≤ Int64.MAX := by omega
  -- reconstruct the decimal from `v` and show it is exactly `d`.
  let d' : Decimal := Int64.ofInt v
  have hd'_toInt : d'.toInt = v := by
    dsimp [d']
    exact Int64.toInt_ofInt_of_le
      (by simp only [Int64.MIN] at hmin ⊢; omega)
      (by simp only [Int64.MAX] at hmax ⊢; omega)
  have hparse' : Decimal.parse s = some d' :=
    parse_complete s d' hwf (by rw [hv, hd'_toInt])
  have hd_eq : d = d' := by
    rw [h] at hparse'
    exact Option.some.inj hparse'
  refine ⟨hwf, ?_, ?_, ?_⟩
  · rw [hv, hd_eq, hd'_toInt]
  · rw [hd_eq, hd'_toInt]; exact hmin
  · rw [hd_eq, hd'_toInt]; exact hmax

/-- `toString` is injective: distinct decimals produce distinct strings. -/
public theorem toString_injective (d d' : Decimal) (h : toString d = toString d') : d = d' := by
  have h1 := parse_toString_roundtrip d
  have h2 := parse_toString_roundtrip d'
  rw [h] at h1
  rw [h1] at h2
  injection h2

/-- Equal normal form iff equal value: normalization decides decimal equality. -/
public theorem normalize_eq_iff_parse_eq (s s' : String) :
    normalize s = normalize s' ↔ Decimal.parse s = Decimal.parse s' := by
  constructor
  · intro h
    unfold normalize at h
    match hps : Decimal.parse s, hps' : Decimal.parse s' with
    | .some d, .some d' =>
      simp [hps, hps', Option.map] at h
      exact congrArg _ (toString_injective d d' h)
    | .some d, .none => simp [hps, hps', Option.map] at h
    | .none, .some d' => simp [hps, hps', Option.map] at h
    | .none, .none => rfl
  · intro h
    simp [normalize, h]

end Cedar.Thm.Decimal

module

public import Std.Data.String
public import Batteries.Data.String
public import Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Util

/-- If no element of `l` satisfies `P`, then `splitOnPPrepend P l acc` returns
    the single segment `[acc.reverse ++ l]` (the accumulator is prepended in reverse). -/
theorem splitOnPPrepend_no_sep (P : α → Bool) (l acc : List α)
    (h : ∀ x ∈ l, P x = false) :
    List.splitOnPPrepend P l acc = [(acc.reverse ++ l)] := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    have ha : P a = false := h a (List.mem_cons.mpr (.inl rfl))
    rw [List.splitOnPPrepend_cons_neg ha]
    rw [ih (a :: acc) (fun x hx => h x (List.mem_cons.mpr (.inr hx)))]
    simp [List.reverse_cons, List.append_assoc]

/-- If `as ++ [sep] ++ bs` has exactly one element satisfying `P` (namely `sep`),
    then `splitOnPPrepend P (as ++ sep :: bs) acc` returns `[acc.reverse ++ as, bs]`. -/
theorem splitOnPPrepend_one_sep (P : α → Bool) (as bs acc : List α) (sep : α)
    (hsep : P sep = true) (has : ∀ x ∈ as, P x = false) (hbs : ∀ x ∈ bs, P x = false) :
    List.splitOnPPrepend P (as ++ sep :: bs) acc = (acc.reverse ++ as) :: [bs] := by
  induction as generalizing acc with
  | nil =>
    rw [List.nil_append, List.splitOnPPrepend_cons_eq_if, hsep]
    rw [List.splitOnP_eq_splitOnPPrepend, splitOnPPrepend_no_sep P bs [] hbs]
    simp
  | cons a t ih =>
    simp only [List.cons_append]
    have ha : P a = false := has a (List.mem_cons.mpr (.inl rfl))
    rw [List.splitOnPPrepend_cons_neg ha]
    rw [ih (a :: acc) (fun x hx => has x (List.mem_cons.mpr (.inr hx)))]
    simp [List.reverse_cons, List.append_assoc]

/-- Splitting `s₁ ++ sep ++ s₂` on `sep` yields `[s₁, s₂]` when neither part contains `sep`. -/
theorem splitToList_eq (s₁ s₂ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂).splitToList p = [s₁, s₂] := by
  rw [String.splitToList_of_valid]
  simp [String.toList_append, List.append_assoc]
  rw [List.splitOnP_eq_splitOnPPrepend]
  rw [splitOnPPrepend_one_sep p s₁.toList s₂.toList [] sep hsep h₁ h₂]
  simp

/-- No character in `toString n` is `'.'` (digits never produce a dot). -/
theorem repr_no_dot (n : Nat) :
    ∀ c ∈ (toString n).toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc; simp only [decide_eq_false_iff_not]; intro heq
  have hc' : c ∈ (Nat.repr n).toList := by rwa [← Nat.toString_eq_repr]
  have hc'' : c ∈ Nat.toDigits 10 n := by
    rwa [Nat.repr_eq_ofList_toDigits, String.toList_ofList] at hc'
  rw [heq] at hc''
  exact absurd (Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc'') (by decide)

/-- No character in a zero-padded `toString n` string is `'.'`. -/
theorem zeros_repr_no_dot (zeros : String) (n : Nat)
    (hz : ∀ c ∈ zeros.toList, c = '0') :
    ∀ c ∈ (zeros ++ toString n).toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc; rw [String.toList_append] at hc
  simp only [decide_eq_false_iff_not]; intro heq
  cases List.mem_append.mp hc with
  | inl h => rw [hz c h] at heq; exact absurd heq (by decide)
  | inr h =>
    have := repr_no_dot n c h
    simp [heq] at this

/-- When no character in `l` is `'_'`, the underscore-skipping foldl reduces to the plain
    digit-accumulating foldl. -/
theorem foldl_no_underscore_eq (l : List Char) (acc : Nat)
    (hno : ∀ c ∈ l, c ≠ '_') :
    List.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - 48)) acc l =
    List.foldl (fun n c => n * 10 + (c.toNat - 48)) acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : a ≠ '_' := hno a (List.Mem.head _)
    simp only [ha, ↓reduceIte]
    exact ih _ (fun c hc => hno c (List.Mem.tail _ hc))

/-- The plain digit-accumulating foldl is equivalent to `Nat.ofDigitChars 10 l acc`. -/
theorem foldl_eq_ofDigitChars (l : List Char) (acc : Nat) :
    List.foldl (fun n c => n * 10 + (c.toNat - 48)) acc l =
    Nat.ofDigitChars 10 l acc := by
  rw [Nat.ofDigitChars_eq_foldl]
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl, show Char.toNat '0' = 48 from by rfl]
    rw [Nat.mul_comm 10 acc]
    exact ih _

/-- Folding the underscore-skipping digit accumulator over `Nat.toDigits 10 n` recovers `n`. -/
theorem toDigits_foldl_roundtrip (n : Nat) :
    List.foldl (fun acc c => if c = '_' then acc else acc * 10 + (c.toNat - 48)) 0
      (Nat.toDigits 10 n) = n := by
  rw [foldl_no_underscore_eq _ 0 (fun c hc heq => Nat.underscore_not_in_toDigits (heq ▸ hc)),
    foldl_eq_ofDigitChars]
  exact Nat.ofDigitChars_toDigits (by omega) (by omega)

open Cedar.Spec.Ext

/-- If `toNat?'` succeeds then the string is non-empty. -/
theorem toNat?'_isSome_length_pos (s : String) (h : (toNat?' s).isSome) : s.length > 0 := by
  by_contra hlen
  simp at hlen
  subst hlen
  have hcontains : ("".contains '_') = false := by simp
  simp only [toNat?', hcontains, Bool.false_eq_true, ↓reduceIte] at h
  rw [String.isSome_toNat?, String.isNat_iff] at h
  exact h.1 rfl

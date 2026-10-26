module

public import CedarRustModel.Lemmas.Basic
import all Cedar.Spec.Wildcard

/-! The memoized `wildcardMatch` coincides with a simple recursive matcher. -/

set_option linter.unusedSimpArgs false

namespace CedarRustModel

open Cedar.Spec

public section

/-- A simple recursive wildcard matcher (mirrors `evaluator.wildcard_match`). -/
def wm : List Char → List PatElem → Bool
  | t, [] => t.isEmpty
  | t, .star :: ps => wm t ps || (match t with
    | [] => false
    | _ :: t' => wm t' (.star :: ps))
  | [], .justChar _ :: _ => false
  | d :: t, .justChar c :: ps => c == d && wm t ps
termination_by t ps => t.length + ps.length

theorem wm_nil_right (t : List Char) : wm t [] = t.isEmpty := by simp [wm]
theorem wm_star_cons (d : Char) (t : List Char) (ps : List PatElem) :
    wm (d :: t) (.star :: ps) = (wm (d :: t) ps || wm t (.star :: ps)) := by
  rw [wm]
theorem wm_nil_star (ps : List PatElem) : wm [] (.star :: ps) = wm [] ps := by
  rw [wm]; simp
theorem wm_nil_char (c : Char) (ps : List PatElem) : wm [] (.justChar c :: ps) = false := by
  rw [wm]
theorem wm_char (c d : Char) (t : List Char) (ps : List PatElem) :
    wm (d :: t) (.justChar c :: ps) = (c == d && wm t ps) := by
  rw [wm]

end

def CacheValid (text : List Char) (pattern : Pattern) (c : Std.HashMap (Nat × Nat) Bool) : Prop :=
  ∀ i j b, c.get? (i, j) = some b → b = wm (text.drop i) (pattern.drop j)

theorem CacheValid.insert {text : List Char} {pattern : Pattern} {c : Std.HashMap (Nat × Nat) Bool}
    (hc : CacheValid text pattern c) (i j : Nat) (b : Bool)
    (hb : b = wm (text.drop i) (pattern.drop j)) :
    CacheValid text pattern (c.insert (i, j) b) := by
  intro i' j' b' h
  rw [Std.HashMap.get?_insert] at h
  split at h
  · rename_i heq
    simp only [beq_iff_eq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp at h; subst h; exact hb
  · exact hc _ _ _ h

theorem StateT.bind_id_apply {σ α β} (m : StateT σ Id α) (f : α → StateT σ Id β) (c : σ) :
    StateT.bind m f c = f (m c).1 (m c).2 := rfl

theorem StateT.modifyGet_id_apply {σ α} (f : σ → α × σ) (c : σ) :
    StateT.modifyGet (m := Id) f c = f c := rfl

theorem StateT.pure_id_apply {σ α} (a : α) (c : σ) :
    StateT.pure (m := Id) a c = (a, c) := rfl

theorem wildcardMatchIdx_spec (text : List Char) (pattern : Pattern) :
    ∀ n i j (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length),
      (text.length - i) + (pattern.length - j) = n →
      ∀ c, CacheValid text pattern c →
        (wildcardMatchIdx text pattern i j h₁ h₂ c).1 = wm (text.drop i) (pattern.drop j) ∧
        CacheValid text pattern (wildcardMatchIdx text pattern i j h₁ h₂ c).2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j h₁ h₂ hn c hc
  rw [wildcardMatchIdx.eq_def]
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  cases hget : c.get? (i, j) with
  | some b =>
    simp only
    exact ⟨hc _ _ _ hget, hc⟩
  | none =>
    simp only
    by_cases hj : j = pattern.length
    · simp only [hj, dite_true]
      have hr : decide (i = text.length) = wm (text.drop i) (pattern.drop pattern.length) := by
        simp only [List.drop_length, wm_nil_right, List.isEmpty_iff, List.drop_eq_nil_iff]
        by_cases h : i = text.length
        · simp [h]
        · simp [h]; omega
      refine ⟨hr, hc.insert _ _ _ ?_⟩
      simp [hr, hj]
    · simp only [hj, dite_false]
      have hj' : j < pattern.length := by omega
      have hpd := List.drop_eq_getElem_cons hj'
      by_cases hi : i = text.length
      · simp only [hi, dite_true]
        subst hi
        simp only [StateT.bind_id_apply, StateT.modifyGet_id_apply]
        obtain ⟨e₁, v₁⟩ := ih _ (by omega) text.length (j + 1) h₁ (by omega) rfl c hc
        generalize wildcardMatchIdx text pattern text.length (j + 1) h₁ _ c = p₁ at e₁ v₁ ⊢
        have hr : (wildcard (pattern.get ⟨j, hj'⟩) && p₁.1) =
            wm (text.drop text.length) (pattern.drop j) := by
          rw [hpd, e₁]
          simp only [List.drop_length, List.get_eq_getElem]
          cases pattern[j] <;> simp [wm_nil_star, wm_nil_char, wildcard]
        exact ⟨hr, v₁.insert _ _ _ hr⟩
      · simp only [hi, dite_false]
        have hi' : i < text.length := by omega
        have htd := List.drop_eq_getElem_cons hi'
        by_cases hw : wildcard (pattern.get ⟨j, hj'⟩) = true
        · simp only [hw, ite_true, StateT.bind_id_apply, StateT.modifyGet_id_apply]
          obtain ⟨e₁, v₁⟩ := ih _ (by omega) i (j + 1) h₁ (by omega) rfl c hc
          generalize wildcardMatchIdx text pattern i (j + 1) h₁ _ c = p₁ at e₁ v₁ ⊢
          obtain ⟨e₂, v₂⟩ := ih _ (by omega) (i + 1) j (by omega) h₂ rfl p₁.2 v₁
          generalize wildcardMatchIdx text pattern (i + 1) j _ h₂ p₁.2 = p₂ at e₂ v₂ ⊢
          have hr : (p₁.1 || p₂.1) = wm (text.drop i) (pattern.drop j) := by
            simp only [List.get_eq_getElem] at hw
            have hpj : pattern[j] = .star := by
              revert hw; cases pattern[j] <;> simp [wildcard]
            rw [e₁, e₂, hpd, hpj, htd, wm_star_cons]
          exact ⟨hr, v₂.insert _ _ _ hr⟩
        · simp only [hw, ite_false, Bool.false_eq_true, StateT.bind_id_apply,
            StateT.modifyGet_id_apply]
          obtain ⟨e₁, v₁⟩ := ih _ (by omega) (i + 1) (j + 1) (by omega) (by omega) rfl c hc
          generalize wildcardMatchIdx text pattern (i + 1) (j + 1) _ _ c = p₁ at e₁ v₁ ⊢
          have hr : (charMatch (text.get ⟨i, hi'⟩) (pattern.get ⟨j, hj'⟩) && p₁.1) =
              wm (text.drop i) (pattern.drop j) := by
            simp only [List.get_eq_getElem] at hw ⊢
            rw [e₁, htd, hpd]
            cases hpj : pattern[j] with
            | star => simp [hpj, wildcard] at hw
            | justChar ch =>
              rw [wm_char]
              simp only [charMatch]
              cases h1 : (text[i] == ch) <;> cases h2 : (ch == text[i]) <;> simp_all
          exact ⟨hr, v₁.insert _ _ _ hr⟩

public theorem wildcardMatch_eq_wm (s : String) (p : Pattern) :
    wildcardMatch s p = wm s.toList p := by
  unfold wildcardMatch
  have := wildcardMatchIdx_spec s.toList p _ 0 0 (by simp) (by simp) rfl ∅
    (by intro i j b h; simp at h)
  simp only [StateT.run', StateT.run, Functor.map, StateT.map] at *
  simpa using this.1

public theorem PatElem.toSpec_star : PatElem.toSpec .Star = .star := rfl
public theorem PatElem.toSpec_justChar (c : Char) : PatElem.toSpec (.JustChar c) = .justChar c := rfl

open Aeneas Aeneas.Std Result cedar_rust_model in
public theorem wildcard_match_ok (text : value.List Char) (pattern : value.List expr.PatElem) :
    evaluator.wildcard_match text pattern =
      ok (wm (List.toList text) ((List.toList pattern).map PatElem.toSpec)) := by
  induction pattern generalizing text with
  | Nil => cases text <;> rw [evaluator.wildcard_match.eq_def] <;> simp [wm_nil_right]
  | Cons pe prest ih =>
    cases pe with
    | Star =>
      induction text with
      | Nil =>
        rw [evaluator.wildcard_match.eq_def]
        simp only [ih, List.toList_nil, List.toList_cons, _root_.List.map_cons, PatElem.toSpec_star,
          wm_nil_star]
        cases wm [] ((List.toList prest).map PatElem.toSpec) <;> simp
      | Cons d t ih' =>
        rw [evaluator.wildcard_match.eq_def]
        simp only [ih, List.toList_cons, _root_.List.map_cons, PatElem.toSpec_star,
          wm_star_cons]
        cases wm (d :: List.toList t) ((List.toList prest).map PatElem.toSpec) <;>
          simp [ih', PatElem.toSpec_star]
    | JustChar c =>
      cases text with
      | Nil => rw [evaluator.wildcard_match.eq_def]; simp [PatElem.toSpec_justChar, wm_nil_char]
      | Cons d t =>
        rw [evaluator.wildcard_match.eq_def]
        by_cases h : c = d <;> simp [h, ih, PatElem.toSpec_justChar, wm_char]

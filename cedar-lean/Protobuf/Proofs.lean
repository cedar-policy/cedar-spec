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

import Protobuf.ByteArray
import Protobuf.BParsec
import Protobuf.String

/-!
Theorems about protobuf parsing and its helper functions
-/

namespace ByteArray.ByteIterator

@[simp] theorem next_pos_eq (i : ByteIterator) : i.next.pos = i.pos + 1 := rfl
@[simp] theorem next_data_eq (i : ByteIterator) : i.next.data = i.data := rfl
@[simp] theorem next_size_eq (i : ByteIterator) : i.next.size = i.size := rfl
attribute [simp] remaining

theorem next_le_remaining (i : ByteIterator) : i.next.remaining ≤ i.remaining := by
  simp only [remaining, next_size_eq, next_pos_eq]
  omega

@[simp] theorem hasNext_iff (i : ByteIterator) : i.hasNext ↔ i.remaining != 0 := by
  simp only [hasNext, remaining, bne_iff_ne, ne_eq]

@[simp] theorem not_hasNext_iff (i : ByteIterator) : ¬i.hasNext ↔ i.remaining = 0 := by
  simp only [hasNext, remaining, bne_iff_ne, ne_eq, Decidable.not_not]

@[simp] theorem empty_iff (i : ByteIterator) : i.empty ↔ ¬i.hasNext := by
  simp only [empty, hasNext_iff, remaining, bne_iff_ne, ne_eq, Decidable.not_not, decide_eq_true_eq]

@[simp] theorem not_empty_iff (i : ByteIterator) : ¬i.empty ↔ i.hasNext := by
  simp only [empty_iff, hasNext_iff, remaining, bne_iff_ne, ne_eq, Decidable.not_not]

end ByteArray.ByteIterator

namespace BParsec

instance [DecidableEq α] : DecidableEq (ParseResult α) := by
  unfold DecidableEq
  intro a b
  let ⟨pos₁, res₁⟩ := a ; clear a
  let ⟨pos₂, res₂⟩ := b ; clear b
  cases res₁ <;> cases res₂ <;> simp only [ParseResult.mk.injEq, reduceCtorEq, Except.ok.injEq, Except.error.injEq, and_false]
  case error.ok | ok.error => exact isFalse (by simp only [not_false_eq_true])
  case ok.ok r₁ r₂ | error.error r₁ r₂ => match decEq pos₁ pos₂, decEq r₁ r₂ with
    | isTrue h₁, isTrue h₂ => subst h₁ h₂ ; exact isTrue (by simp only [and_self])
    | _, isFalse h₂ => exact isFalse (by intro h ; simp [h] at h₂)
    | isFalse h₁, _ => exact isFalse (by intro h ; simp [h] at h₁)

@[simp] theorem throw_eq_fail : (throw s : BParsec α) = BParsec.fail s := by
  simp only [throw, throwThe, MonadExceptOf.throw]

attribute [simp] map
attribute [simp] mapConst

theorem ext (x y : BParsec α) (H : ∀ it, x it = y it) : x = y := funext H

@[simp] theorem id_map (x : BParsec α) : id <$> x = x := by
  apply ext
  intro it
  simp only [Functor.map, map, id_eq]
  split <;> simp only [*]

theorem map_const : (@mapConst α β) = ((@map β α) ∘ (@Function.const α β)) := rfl

theorem comp_map (g : α → β) (h : β → γ) (x : BParsec α) : (h ∘ g) <$> x = h <$> g <$> x := by
  apply ext
  intro it
  simp only [Functor.map, map, Function.comp_apply]
  split <;> simp only [*]

instance : LawfulFunctor BParsec := {
  map_const := map_const,
  id_map := id_map,
  comp_map := comp_map
}

attribute [simp] pure
attribute [simp] bind

instance : LawfulMonad BParsec := {
  map_const, id_map,
  seqLeft_eq := by
    intro α β f1 f2
    apply ext
    intro it
    simp only [Monad.toApplicative, instMonad, instFunctor, Functor.map, bind, pure, map]
    split <;> simp only [Function.const_apply]

  seqRight_eq := by
    intro α β x y
    apply ext
    intro it
    simp only [SeqRight.seqRight, bind, Seq.seq, Functor.map, map, Function.const]
    split <;> simp only [id_eq]
    split <;> simp only [*]

  pure_seq := by
    intro α β g x
    apply ext
    intro it
    simp only [Seq.seq, bind, Pure.pure, pure, Monad.toApplicative, instMonad]

  bind_pure_comp := by
    intro α β f x
    simp only [Bind.bind, Pure.pure, Functor.map]
    rfl

  bind_map := by
    intro α β f x
    simp only [Bind.bind, Functor.map, Seq.seq]

  pure_bind := by
    intro α β x f
    simp only [Bind.bind, Pure.pure]
    rfl

  bind_assoc := by
    intro α β γ x f g
    simp only [Bind.bind]
    apply ext
    intro it
    simp only [bind]
    let ⟨pos, res⟩ := x it
    cases res <;> simp only
}

attribute [simp] hasNext
attribute [simp] next
attribute [simp] forward
attribute [simp] size
attribute [simp] remaining
attribute [simp] empty
attribute [simp] pos
attribute [simp] inspect
attribute [simp] fail

theorem foldl_iterator_progress {f : BParsec α} {g : β → α → β} {remaining : Nat} {init : β} {res : β}
  (H1 : remaining > 0)
  (H : foldl f g remaining init pos₀ = { pos := pos₁, res := .ok res }) :
  pos₁.pos > pos₀.pos
:= by
  unfold foldl at H
  revert (H1 : remaining > 0)
  induction remaining using Nat.strongRecOn generalizing f g init res pos₀ pos₁
  next ni IH =>
    intro (H1 : ni > 0)
    unfold foldlHelper at H
    have H2 : ¬(ni = 0) := by omega
    rw [if_neg H2] at H
    simp only [Bind.bind, bind, pos, inspect] at H
    cases H3 : f pos₀ ; simp only [H3] at H ; rename_i pos₂ res₂
    cases res₂ <;> simp only [ParseResult.mk.injEq, reduceCtorEq, and_false] at H
    case ok res₂ =>
      by_cases H4 : (pos₂.pos - pos₀.pos = 0)
      case pos =>
        simp only [H4, reduceIte, throw_eq_fail, fail, ParseResult.mk.injEq, reduceCtorEq, and_false] at H
      case neg =>
        simp only [H4, reduceIte] at H
        let ni2 := ni - (pos₂.pos - pos₀.pos)
        have Hni2 : ni2 = ni - (pos₂.pos - pos₀.pos) := rfl
        rw [← Hni2] at H
        by_cases H6 : (pos₂.pos - pos₀.pos ≥ ni)
        case neg =>
          specialize @IH ni2 (by omega) pos₂ pos₁ f g (g init res₂) res H (by omega)
          omega
        case pos =>
          have Hn : ni2 = 0 := by omega
          simp only [Hn] at H
          unfold foldlHelper at H
          rw [if_pos (by decide)] at H
          simp only [pure, ParseResult.mk.injEq, Except.ok.injEq] at H
          replace ⟨H, _⟩ := H
          subst pos₂
          omega

end BParsec

namespace Proto

instance : DecidableEq (BParsec.ParseResult (Char × Nat)) := by apply inferInstance

theorem utf8DecodeChar.sizeGt0 {pos₀ pos₁ : ByteArray.ByteIterator} {i n : Nat} {c : Char}
  (H : utf8DecodeChar i pos₀ = { pos := pos₁, res := .ok ⟨c, n⟩ }) :
  n > 0
:= by
  unfold utf8DecodeChar at H
  simp only [bind, BParsec.bind, BParsec.inspect, beq_iff_eq, pure, bne_iff_ne, ne_eq,
    BParsec.throw_eq_fail, gt_iff_lt, ite_not, Bool.and_eq_true, not_and, and_imp] at H
  split at H
  · simp only [BParsec.pure, BParsec.ParseResult.mk.injEq, Except.ok.injEq, Prod.mk.injEq] at H
    omega
  · split at H
    · simp only [BParsec.bind, BParsec.inspect] at H
      split at H
      · split at H
        · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
        · split at H
          · simp only [BParsec.pure, BParsec.ParseResult.mk.injEq, Except.ok.injEq,
            Prod.mk.injEq] at H
            omega
          · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
      · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
    · split at H
      · simp only [BParsec.bind, BParsec.inspect] at H
        split at H
        · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
        · split at H
          · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
          · split at H
            · simp only [BParsec.pure, BParsec.ParseResult.mk.injEq, Except.ok.injEq,
                Prod.mk.injEq] at H
              omega
            · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
      · split at H
        · simp only [BParsec.bind, BParsec.inspect] at H
          split at H
          · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
          · split at H
            · simp only [BParsec.pure, BParsec.ParseResult.mk.injEq, Except.ok.injEq,
                Prod.mk.injEq] at H
              omega
            · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H
        · simp only [BParsec.fail, BParsec.ParseResult.mk.injEq, reduceCtorEq, and_false] at H

/-- Uglier version of `parseStringHelper` which is functionally equivalent to
`parseStringHelper`, but has a termination proof, unlike `parseStringHelper`.
-/
private def parseStringHelper_unoptimized (remaining : Nat) (r : String) : BParsec String := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then throw s!"Expected more packed uints, Size Remaining: {remaining}" else
  let pos ← BParsec.pos
  λ pos₀ =>
    let result := utf8DecodeChar pos pos₀
    match H : result with
      | { pos := pos₁, res := .ok ⟨c, elementSize⟩ } =>
        have _ : elementSize > 0 := utf8DecodeChar.sizeGt0 H
        (do
          BParsec.forward (elementSize)
          parseStringHelper_unoptimized (remaining - elementSize) (r.push c)) pos₀
      | { pos := pos₁, res := .error msg } => { pos := pos₁, res := .error msg }

end Proto
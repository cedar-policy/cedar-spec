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
  cases a <;> cases b <;> simp only [reduceCtorEq, ParseResult.success.injEq, ParseResult.error.injEq]
  case error.success | success.error => exact isFalse (by simp only [not_false_eq_true])
  case error.error c d e f | success.success c d e f =>
    match (decEq c e), (decEq d f) with
      | isTrue h1, isTrue h2 => subst e f ; exact isTrue (by simp only [and_self])
      | _, isFalse h2 => exact isFalse (by intro h; simp [h] at h2)
      | isFalse h1, _ => exact isFalse (by intro h; simp [h] at h1)

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
    cases x it <;> simp only
}

attribute [simp] hasNext
attribute [simp] next
attribute [simp] forward
attribute [simp] size
attribute [simp] remaining
attribute [simp] empty
attribute [simp] pos

theorem foldl_iterator_progress {f : BParsec α} {g : β → α → β} {remaining : Nat} {init : β} {result : β} (H1 : remaining > 0) (H : (foldl f g remaining init) it1 = .success it2 result) : it2.pos > it1.pos := by
  unfold foldl at H
  revert (H1 : remaining > 0)
  induction remaining using Nat.strongRecOn generalizing f g init result it1 it2
  next ni IH =>
    intro (H1 : ni > 0)
    unfold foldlHelper at H
    have H2 : ¬(ni = 0) := by omega
    rw [if_neg H2] at H
    simp only [Bind.bind, bind, pos] at H
    cases H3 : f it1 <;> simp only [H3, reduceCtorEq] at H
    case success itn resultn =>
      by_cases H4 : (itn.pos - it1.pos = 0)
      case pos => simp only [H4, reduceIte] at H ; contradiction
      case neg =>
        simp only [H4, reduceIte] at H
        let ni2 := ni - (itn.pos - it1.pos)
        have Hni2 : ni2 = ni - (itn.pos - it1.pos) := rfl
        rw [← Hni2] at H
        by_cases H6 : (itn.pos - it1.pos ≥ ni)
        case neg =>
          specialize @IH ni2 (by omega) itn it2 f g (g init resultn) result H (by omega)
          omega
        case pos =>
          have Hn : ni2 = 0 := by omega
          simp only [Hn] at H
          unfold foldlHelper at H
          rw [if_pos (by decide)] at H
          simp only [pure, ParseResult.success.injEq] at H
          replace ⟨H, _⟩ := H
          subst it2
          omega

end BParsec

namespace Proto

instance : DecidableEq (BParsec.ParseResult (Char × Nat)) := by apply inferInstance

theorem utf8DecodeChar.sizeGt0 (it1 it2 : ByteArray.ByteIterator) (pos : Nat) (c : Char) (H : utf8DecodeChar pos it1 = .success it2 ⟨c, n⟩) : n > 0 := by
  unfold utf8DecodeChar at H
  simp only [beq_iff_eq, bne_iff_ne, ne_eq, gt_iff_lt, ite_not, Bool.and_eq_true, not_and,
    and_imp] at H
  split at H
  · simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
    omega
  · split at H
    · split at H
      · split at H
        · simp only [reduceCtorEq] at H
        · split at H
          · simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
            omega
          · simp only [reduceCtorEq] at H
      · simp only [reduceCtorEq] at H
    · split at H
      · split at H
        · simp only [reduceCtorEq] at H
        · split at H
          · simp only [reduceCtorEq] at H
          · split at H
            · simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
              omega
            · simp only [reduceCtorEq] at H
      · split at H
        · split at H
          · simp only [reduceCtorEq] at H
          · split at H
            · simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
              omega
            · simp only [reduceCtorEq] at H
        · simp only [reduceCtorEq] at H

private def parseStringHelper_unoptimized (remaining : Nat) (r : String) : BParsec String := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then throw s!"Expected more packed uints, Size Remaining: {remaining}" else
  let pos ← BParsec.pos
  fun it =>
    let result := utf8DecodeChar pos it
    match result with
      | .success it2 ⟨c, elementSize⟩ =>
        -- NOTE: I don't know how to get H_Redunant other than
        -- doing this. Which is bad for runtime O(n) of ByteArray
        if H_Redundant : result = .success it2 ⟨c, elementSize⟩ then
          have _ : elementSize > 0 := utf8DecodeChar.sizeGt0 it it2 pos c H_Redundant
          (do
            BParsec.forward (elementSize)
            parseStringHelper_unoptimized (remaining - elementSize) (r.push c)) it
        else
          .error it2 "Impossible case"
      | .error it msg => .error it msg

end Proto

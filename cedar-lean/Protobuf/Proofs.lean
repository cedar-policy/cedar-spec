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
  simp only [remaining.eq_1, next_size_eq, next_pos_eq]
  omega

@[simp] theorem hasNext_iff (i : ByteIterator) : i.hasNext ↔ i.remaining != 0 := by
  apply Iff.intro
  all_goals unfold hasNext
  all_goals simp only [remaining.eq_1, gt_iff_lt, decide_eq_true_eq, imp_self]

@[simp] theorem not_hasNext_iff (i : ByteIterator) : ¬i.hasNext ↔ i.remaining = 0 := by
  apply Iff.intro
  all_goals unfold hasNext
  all_goals simp only [remaining.eq_1, bne_iff_ne, ne_eq, Decidable.not_not, imp_self]

@[simp] theorem empty_iff (i : ByteIterator) : i.empty ↔ ¬i.hasNext := by
  apply Iff.intro
  all_goals unfold empty
  all_goals simp only [hasNext_iff, remaining.eq_1, gt_iff_lt, Nat.not_lt,
   Nat.le_zero_eq, decide_eq_true_eq, imp_self]

@[simp] theorem not_empty_iff (i : ByteIterator) : ¬i.empty ↔ i.hasNext := by
  simp only [empty_iff, hasNext_iff, remaining.eq_1, gt_iff_lt, Nat.not_lt, Nat.le_zero_eq]
  exact Decidable.not_not

end ByteArray.ByteIterator

namespace BParsec

instance [DecidableEq α] : DecidableEq (ParseResult α) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d e f=>
    match (decEq c e), (decEq d f) with
      | isTrue h1, isTrue h2 => apply isTrue (by rw [h1, h2])
      | isTrue _, isFalse h2 => apply isFalse (by intro h; injection h; contradiction)
      | isFalse h1, isTrue _ => apply isFalse (by intro h; injection h; contradiction)
      | isFalse h1, isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case success.success c d e f =>
    match (decEq c e), (decEq d f) with
      | isTrue h1, isTrue h2 => apply isTrue (by rw [h1, h2])
      | isTrue _, isFalse h2 => apply isFalse (by intro h; injection h; contradiction)
      | isFalse h1, isTrue _ => apply isFalse (by intro h; injection h; contradiction)
      | isFalse h1, isFalse _ => apply isFalse (by intro h; injection h; contradiction)

attribute [simp] map
attribute [simp] mapConst

theorem ext (x y : BParsec α) (H : ∀ it, x it = y it) : x = y := funext H

@[simp] theorem id_map : ∀ {α : Type} (x : BParsec α), id <$> x = x := by
  intro α
  intro f
  apply ext
  intro it
  unfold Functor.map
  unfold instFunctor
  simp
  cases (f it)
  all_goals rfl

theorem map_const : ∀ {α β : Type}, (@mapConst α β) = ((@map β α) ∘ (@Function.const α β)) := by
  intros α β
  rfl

theorem comp_map {α β γ : Type} : ∀ (g : α → β) (h : β → γ) (x : BParsec α), (h ∘ g) <$> x = h <$> g <$> x := by
  intro g; intro h
  intro x
  apply ext
  intro it
  unfold Functor.map
  unfold instFunctor
  simp
  cases (x it)
  all_goals rfl

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
    intro α; intro β
    intro f1; intro f2
    apply ext; intro it
    unfold Function.const
    unfold Functor.map
    unfold Applicative.toFunctor
    unfold Monad.toApplicative
    unfold instMonad
    simp
    unfold instFunctor
    simp
    cases (f1 it)
    cases (f2 it)
    next it2 B C D =>
      simp
    next A B C D =>
      simp
    next A B =>
      simp

  seqRight_eq := by
    intro α; intro β
    intro x; intro y
    apply ext; intro it
    unfold Function.const
    unfold Seq.seq
    unfold SeqRight.seqRight
    unfold Applicative.toSeq
    unfold Applicative.toSeqRight
    unfold Monad.toApplicative
    unfold instMonad
    simp
    unfold Functor.map
    unfold instFunctor
    simp
    cases (x it)
    cases (y it)
    next A B C D =>
      simp
      cases (y A)
      all_goals rfl
    next A B C D =>
      simp
      cases (y A)
      all_goals rfl
    next A B =>
      rfl
  ,
  pure_seq := by
    intro α; intro β
    intro g
    intro x
    apply ext; intro it1
    unfold Seq.seq
    unfold Pure.pure
    unfold Applicative.toSeq
    unfold Applicative.toPure
    unfold Monad.toApplicative
    unfold instMonad
    rfl,
  bind_pure_comp := by
    intro α; intro β
    intro f
    intro x
    unfold Bind.bind
    unfold Pure.pure
    unfold Functor.map
    unfold Monad.toBind
    unfold Applicative.toPure
    unfold Applicative.toFunctor
    unfold Monad.toApplicative
    unfold instMonad
    simp
    unfold instFunctor
    simp
    unfold bind
    unfold pure
    unfold map
    rfl,
  bind_map := by
    intro α; intro β
    intro f; intro x
    unfold Bind.bind
    unfold Functor.map
    unfold Seq.seq
    unfold Monad.toBind
    unfold Applicative.toFunctor
    unfold Applicative.toSeq
    unfold Monad.toApplicative
    unfold instMonad
    simp
    unfold instFunctor
    rfl,
  pure_bind := by
    intro α; intro β
    intro x; intro f
    unfold Bind.bind
    unfold Pure.pure
    unfold Monad.toBind
    unfold Applicative.toPure
    unfold Monad.toApplicative
    unfold instMonad
    simp
    unfold pure
    unfold bind
    rfl,
  bind_assoc := by
    intro α; intro β; intro γ
    intro x; intro f; intro g
    unfold Bind.bind
    unfold Monad.toBind
    unfold instMonad
    simp only
    apply ext
    intro it
    unfold bind
    simp only
    cases (x it)
    all_goals rfl
}

attribute [simp] hasNext
attribute [simp] next
attribute [simp] forward
attribute [simp] size
attribute [simp] remaining
attribute [simp] empty
attribute [simp] pos

theorem foldl_iterator_progress {α β : Type} {f : BParsec α} {g : β → α → β} {remaining : Nat} {init : β} {result : β} (H1 : remaining > 0) (H : (foldl f g remaining init) it1 = .success it2 result) : it2.pos > it1.pos := by
  unfold foldl at H
  revert (H1 : remaining > 0)
  induction remaining using Nat.strongRecOn generalizing f g init result it1 it2
  next ni IH =>
    intro (H1 : ni > 0)
    unfold foldlHelper at H
    have H2 : ¬(ni = 0) := by omega
    rw [if_neg H2] at H
    unfold Bind.bind at H
    unfold Monad.toBind at H
    unfold instMonad at H
    simp only [bind, pos] at H
    cases H3 : (f it1)
    case error =>
      rewrite [H3] at H
      contradiction
    case success itn resultn =>
      rewrite [H3] at H
      simp only at H
      by_cases H4 : (itn.pos - it1.pos = 0)
      case pos =>
        rw [if_pos H4] at H
        contradiction
      case neg =>
        rw [if_neg H4] at H
        let ni2 := ni - (itn.pos - it1.pos)
        have Hni2 : ni2 = ni - (itn.pos - it1.pos) := rfl
        rewrite [<- Hni2] at H
        have H5 : ni2 < ni := by omega

        by_cases H6 : (itn.pos - it1.pos ≥ ni)
        case neg =>
          have Hn : ni2 > 0 := by omega
          have X := (@IH ni2 H5 itn it2 f g (g init resultn) result) H Hn
          have X2 : itn.pos > it1.pos := by omega
          omega
        case pos =>
          have Hn : ni2 = 0 := by omega
          rewrite [Hn] at H
          unfold foldlHelper at H
          rewrite [if_pos (by decide)] at H
          unfold pure at H
          have HH : itn = it2 := by
            simp at H
            apply And.left H
          rewrite [HH] at H4
          omega

end BParsec

namespace Proto

instance : DecidableEq (BParsec.ParseResult (Char × Nat)) := by apply inferInstance

theorem utf8DecodeChar.sizeGt0 (it1 it2 : ByteArray.ByteIterator) (pos : Nat) (c : Char) (H : utf8DecodeChar pos it1 = .success it2 ⟨c, n⟩) : n > 0 := by
  unfold utf8DecodeChar at H
  simp only [beq_iff_eq, bne_iff_ne, ne_eq, gt_iff_lt, ite_not, Bool.and_eq_true, not_and,
    and_imp] at H
  split at H
  simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
  omega
  split at H
  split at H
  split at H
  contradiction
  split at H
  simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
  omega
  contradiction
  contradiction
  split at H
  split at H
  contradiction
  split at H
  contradiction
  split at H
  simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
  omega
  contradiction
  split at H
  split at H
  contradiction
  split at H
  simp only [BParsec.ParseResult.success.injEq, Prod.mk.injEq, true_and] at H
  omega
  contradiction
  contradiction

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

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

import CedarGen.Relational.InstanceLaws
import Specimen.Correctness.LawClasses
import Specimen.Correctness.LeafComplete
import Specimen.Correctness.CheckComplete

/-! # Completeness of the hand-written checkers

For each decision procedure of `Instances.lean`, `DecOptComplete`: on a premise that holds, the
check answers `true` (at any size, since none of them uses it). The emitted completeness proofs of
the derived generators use these where a generator checks a premise. -/

namespace Cedar.Validation.Relational

open Cedar.Spec Cedar.Data Cedar.Validation Specimen.Correctness

/-- A check that answers `.ok b` at every size is complete when `b` holds, at every size. -/
theorem decOptComplete_of {P : Prop} [DecOpt P] (b : Bool) (hb : ∀ s, DecOpt.decOpt (P := P) s = .ok b)
    (h : P → b = true) : DecOptCompleteAll P :=
  ⟨fun hp s => by rw [hb s, h hp]⟩

instance : DecOptCompleteAll (CapMem x k c) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (CapTagMem x e c) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (CapAttrMem x a c) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance [BEq α] [BEq β] [ReflBEq α] [ReflBEq β] {k : α} {v : β} {m : Map α β} :
    DecOptCompleteAll (MapContains k v m) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance [DecidableEq α] [BEq α] [LawfulBEq α] {k : α} {m : Map α β} :
    DecOptCompleteAll (MapNotContainsKey (α := α) (β := β) k m) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by
    induction h with
    | empty => rfl
    | skip _ _ _ hne _ ih =>
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at ih ⊢
      exact ⟨fun h => hne h.symm, ih⟩

instance [BEq α] [ReflBEq α] {x : α} {s : Data.Set α} : DecOptCompleteAll (SetContains x s) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (MapContainsAncestors ety ancs ets) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (MapContainsAttrs ety attrs ets) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (MapContainsTagType ety ty ets) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (MapContainsNoTags ety ets) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

instance : DecOptCompleteAll (ValidDecimal s) :=
  decOptComplete_of _ (fun _ => rfl) fun | .mk _ _ h => by simp [h]

instance : DecOptCompleteAll (ValidIP s) :=
  decOptComplete_of _ (fun _ => rfl) fun | .mk _ _ h => by simp [h]

instance : DecOptCompleteAll (ValidDatetime s) :=
  decOptComplete_of _ (fun _ => rfl) fun | .mk _ _ h => by simp [h]

instance : DecOptCompleteAll (ValidDuration s) :=
  decOptComplete_of _ (fun _ => rfl) fun | .mk _ _ h => by simp [h]

instance : DecOptCompleteAll (BothLit x₁ x₂) :=
  decOptComplete_of _ (fun _ => rfl) fun | .mk _ _ => rfl

instance : DecOptCompleteAll (NotFf b) :=
  decOptComplete_of _ (fun _ => rfl) fun | .tt => rfl | .anyBool => rfl

instance : DecOptCompleteAll (BoolTypeNeq a b) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by cases h <;> rfl

instance : DecOptCompleteAll (KeyAbove lb a) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by cases h <;> simp_all

instance [BEq v] [ReflBEq v] {a : EntityType} {b : String} {va : v} {m : Map EntityUID v} :
    DecOptCompleteAll (MapContainsPairKey a b va m) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by
    induction h with
    | here => simp
    | nextA hne _ ih =>
      have : (_ == _) = false := beq_false_of_ne (Ne.symm hne)
      simp only [List.find?_cons, this, Bool.false_and]; exact ih
    | nextB hne _ ih =>
      have : (_ == _) = false := beq_false_of_ne (Ne.symm hne)
      simp only [List.find?_cons, this, Bool.and_false]; exact ih

instance : DecOptCompleteAll (MapContainsEnum ety eids ets) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by induction h <;> simp_all

/-- A key bound in the map is one it contains. -/
theorem contains_of_mapContains [BEq α] [LawfulBEq α] {k : α} {v : β} {m : Map α β}
    (h : MapContains k v m) : m.contains k = true := by
  have : ∃ p ∈ m.toList, (p.1 == k) = true := by
    induction h with
    | here => exact ⟨_, List.mem_cons_self, by simp⟩
    | there _ _ _ _ ih =>
      obtain ⟨p, hp, hk⟩ := ih
      exact ⟨p, List.mem_cons_of_mem _ hp, hk⟩
  obtain ⟨p, hp, hk⟩ := this
  simp only [Map.contains, Map.find?]
  cases hf : m.toList.find? (fun ⟨k', _⟩ => k' == k) with
  | none => exact absurd hk (by simpa using List.find?_eq_none.mp hf p hp)
  | some q => rfl

instance : DecOptCompleteAll (IsActionLitMem x₁ x₂ acts) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by
    cases h with
    | mk _ _ _ _ hm => exact (contains_of_mapContains hm :)

instance : DecOptCompleteAll (IsActionLitMemSet x₁ x₂ acts) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by
    cases h with
    | mk _ xs _ _ hm hxs =>
      rw [isActionLitMemSetB, show acts.contains _ = true from contains_of_mapContains hm, Bool.true_and,
        List.all_eq_true]
      intro x hx
      obtain ⟨u, rfl⟩ := hxs x hx
      rfl

instance : DecOptCompleteAll (CapMerge c₁ c₂ c) :=
  decOptComplete_of _ (fun _ => rfl) fun h => by
    induction h with
    | nil => rfl
    | left _ _ _ _ _ _ ih => simp [capMergeB, ih]
    | right _ _ c₁ _ _ _ ih => cases c₁ <;> simp_all [capMergeB]
    | both _ _ _ _ _ _ ih => simp [capMergeB, ih]

instance : DecOptCompleteAll (MaybeActionDescendentOf acts ety₁ ety₂) :=
  decOptComplete_of _ (fun _ => rfl) fun h => (maybeActionDescendentOf_iff.mp h)

/-! ## Refutation: a premise that fails is checked false

Each from the checker's soundness law: a check answering `true` would prove the premise. -/

theorem decOptRefute_of {P : Prop} [DecOpt P] (b : Bool) (hb : ∀ s, DecOpt.decOpt (P := P) s = .ok b)
    (h : b = true → P) : DecOptRefuteCompleteAll P :=
  ⟨fun hp s => by rw [hb s]; cases b <;> simp_all⟩

instance : DecOptRefuteCompleteAll (CapMem x k c) := decOptRefute_of _ (fun _ => rfl) capMem_of_any
instance : DecOptRefuteCompleteAll (ParserImage x) := decOptRefute_of _ (fun _ => rfl) parserImage_of_test
instance : DecOptCompleteAll (ParserImage x) := decOptComplete_of _ (fun _ => rfl) (parserImage_iff x).mp
instance : DecOptRefuteCompleteAll (CapTagMem x e c) := decOptRefute_of _ (fun _ => rfl) capTagMem_of_any
instance : DecOptRefuteCompleteAll (CapAttrMem x a c) := decOptRefute_of _ (fun _ => rfl) capAttrMem_of_any
instance [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] {k : α} {v : β} {m : Map α β} :
    DecOptRefuteCompleteAll (MapContains k v m) := decOptRefute_of _ (fun _ => rfl) mapContains_of_any
instance [DecidableEq α] {k : α} {m : Map α β} :
    DecOptRefuteCompleteAll (MapNotContainsKey (α := α) (β := β) k m) :=
  decOptRefute_of _ (fun _ => rfl) mapNotContainsKey_of_all
instance [BEq α] [LawfulBEq α] {x : α} {s : Data.Set α} : DecOptRefuteCompleteAll (SetContains x s) :=
  decOptRefute_of _ (fun _ => rfl) setContains_of_any
instance : DecOptRefuteCompleteAll (MapContainsAncestors ety ancs ets) :=
  decOptRefute_of _ (fun _ => rfl) mapContainsAncestors_of_any
instance : DecOptRefuteCompleteAll (MapContainsAttrs ety attrs ets) :=
  decOptRefute_of _ (fun _ => rfl) mapContainsAttrs_of_any
instance : DecOptRefuteCompleteAll (MapContainsTagType ety ty ets) :=
  decOptRefute_of _ (fun _ => rfl) mapContainsTagType_of_any
instance : DecOptRefuteCompleteAll (MapContainsNoTags ety ets) :=
  decOptRefute_of _ (fun _ => rfl) mapContainsNoTags_of_any
instance : DecOptRefuteCompleteAll (KeyAbove lb a) := decOptRefute_of _ (fun _ => rfl) keyAbove_of_test
instance : DecOptRefuteCompleteAll (ValidDecimal s) := decOptRefute_of _ (fun _ => rfl) validDecimal_of_isSome
instance : DecOptRefuteCompleteAll (ValidIP s) := decOptRefute_of _ (fun _ => rfl) validIP_of_isSome
instance : DecOptRefuteCompleteAll (ValidDatetime s) := decOptRefute_of _ (fun _ => rfl) validDatetime_of_isSome
instance : DecOptRefuteCompleteAll (ValidDuration s) := decOptRefute_of _ (fun _ => rfl) validDuration_of_isSome
instance : DecOptRefuteCompleteAll (MapContainsEnum ety eids ets) :=
  decOptRefute_of _ (fun _ => rfl) mapContainsEnum_of_find
instance {v : Type} [BEq v] [LawfulBEq v] {a : EntityType} {b : String} {va : v} {m : Map EntityUID v} :
    DecOptRefuteCompleteAll (MapContainsPairKey a b va m) :=
  decOptRefute_of _ (fun _ => rfl) mapContainsPairKey_of_find
instance : DecOptRefuteCompleteAll (ActionInSet acts uid₁ xs) :=
  decOptRefute_of _ (fun _ => rfl) actionInSet_of_test
instance : DecOptCompleteAll (ActionInSet acts uid₁ xs) :=
  decOptComplete_of _ (fun _ => rfl) actionInSet_test
instance : DecOptRefuteCompleteAll (BothLit x₁ x₂) := decOptRefute_of _ (fun _ => rfl) bothLit_of_test
instance : DecOptRefuteCompleteAll (IsActionLitMem x₁ x₂ acts) :=
  decOptRefute_of _ (fun _ => rfl) isActionLitMem_of_test
instance : DecOptRefuteCompleteAll (IsActionLitMemSet x₁ x₂ acts) :=
  decOptRefute_of _ (fun _ => rfl) isActionLitMemSet_of_test
instance : DecOptRefuteCompleteAll (NotFf b) := decOptRefute_of _ (fun _ => rfl) notFf_of_test
instance : DecOptRefuteCompleteAll (BoolTypeNeq a b) := decOptRefute_of _ (fun _ => rfl) boolTypeNeq_of_test
instance : DecOptRefuteCompleteAll (CapMerge c₁ c₂ c) := decOptRefute_of _ (fun _ => rfl) capMerge_of_test
instance : DecOptRefuteCompleteAll (MaybeActionDescendentOf acts ety₁ ety₂) :=
  decOptRefute_of _ (fun _ => rfl) maybeActionDescendentOf_of_test
instance : DecOptRefuteCompleteAll (DeadOperand decl syn env x) :=
  decOptRefute_of _ (fun _ => rfl) deadOperand_of_ok
instance : DecOptCompleteAll (DeadOperand decl syn env x) :=
  decOptComplete_of _ (fun _ => rfl) deadOperand_iff.mp
instance : DecOptRefuteCompleteAll (SortsTo axs axs') := decOptRefute_of _ (fun _ => rfl) sortsTo_of_test

/-! ## The unconstrained values

The derived generators of `Instances.lean` (`deriving instance Basalt.ArbitrarySized`), and `Int64`'s. -/

instance : ArbitrarySizedComplete Var := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete BoolType := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete Cedar.Spec.Name := ⟨by arbitrary_complete⟩

instance : ArbitrarySizedComplete Int64 where
  complete i := ⟨ArbitrarySizedComplete.bound i.toInt, fun s hs => by
    show Produces (do
      let j : Int ← Basalt.ArbitrarySized.arbitrarySized s
      return Int64.ofInt j : SGen Int64) i
    exact produces_bind_of (ArbitrarySizedComplete.produces (x := i.toInt) hs)
      (produces_pure_iff.mpr (Int64.ofInt_toInt i).symm)⟩

instance : ArbitrarySizedComplete ExtFun := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete ExtType := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete EntityUID := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete Prim := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete PatElem := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete UnaryOp := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete BinaryOp := ⟨by arbitrary_complete⟩
instance : ArbitrarySizedComplete Effect := ⟨by arbitrary_complete⟩
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedComplete α] :
    ArbitrarySizedComplete (Qualified α) := ⟨by arbitrary_complete⟩

/-! ## The map and set producers -/

theorem not_any_of_mapNotContainsKey [DecidableEq α] {k : α} {m : Map α β} (h : MapNotContainsKey k m) :
    (m.toList.any fun p => decide (p.1 = k)) = false := by
  induction h with
  | empty => rfl
  | skip _ _ _ hne _ ih =>
    simp only [Map.toList] at ih ⊢
    simp [List.any_cons, ih, Ne.symm hne]

theorem filter_of_mapNotContainsKey [DecidableEq α] {k : α} {l : List (α × β)}
    (h : MapNotContainsKey k (Map.mk l)) : l.filter (fun p => decide (p.1 ≠ k)) = l := by
  have := not_any_of_mapNotContainsKey h
  simp only [Map.toList, List.any_eq_false, decide_eq_true_eq] at this
  exact List.filter_eq_self.mpr fun p hp => by simpa using this p hp

instance [Basalt.ArbitrarySized α] [ArbitrarySizedComplete α] [DecidableEq α] {m : Map α β} :
    BacktrackGenForComplete α (fun k => MapNotContainsKey k m) where
  complete k h := ⟨ArbitrarySizedComplete.bound k, fun s l _ hl => by
    show Produces (do
      let k : α ← Basalt.ArbitrarySized.arbitrarySized l
      if m.toList.any (fun p => decide (p.1 = k)) then Specimen.Fail.fail else return k : SGen α) k
    refine produces_bind_of (ArbitrarySizedComplete.produces hl) ?_
    rw [not_any_of_mapNotContainsKey h]
    exact produces_pure_iff.mpr rfl⟩

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] [DecidableEq α] {k : α} :
    BacktrackGenForComplete (Map α β) (fun m => MapNotContainsKey k m) where
  complete m h := ⟨ArbitrarySizedComplete.bound m.toList, fun s l _ hl => by
    show Produces (do
      let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
      return Map.mk (rest.filter (fun p => p.1 ≠ k)) : SGen (Map α β)) m
    refine produces_bind_of (ArbitrarySizedComplete.produces hl) (produces_pure_iff.mpr ?_)
    cases m with
    | mk l0 => show _ = Map.mk (l0.filter _); rw [filter_of_mapNotContainsKey h]⟩

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] [DecidableEq α] :
    BacktrackGenForComplete (α × Map α β) (fun (k, m) => MapNotContainsKey k m) where
  complete p h := by
    obtain ⟨k, m⟩ := p
    exact ⟨ArbitrarySizedComplete.bound k + ArbitrarySizedComplete.bound m.toList, fun s l _ hl => by
    show Produces (do
      let k : α ← Basalt.ArbitrarySized.arbitrarySized l
      let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
      return (k, Map.mk (rest.filter (fun p => p.1 ≠ k))) : SGen (α × Map α β)) (k, m)
    refine produces_bind_of (ArbitrarySizedComplete.produces (x := k) (by omega))
      (produces_bind_of (ArbitrarySizedComplete.produces (x := m.toList) (by omega)) (produces_pure_iff.mpr ?_))
    cases m with
    | mk l0 => show _ = (k, Map.mk (l0.filter _)); rw [filter_of_mapNotContainsKey h]⟩

theorem produces_insertSomewhere (x : α) (xs : List α) (i : Nat) (hi : i ≤ xs.length) :
    Produces (insertSomewhere x xs : SGen (List α)) (xs.take i ++ x :: xs.drop i) := by
  show Produces (do
    let i ← chooseNat 0 xs.length
    pure (xs.take i ++ x :: xs.drop i) : SGen (List α)) _
  exact produces_bind_of (produces_chooseNat (k := i) _ (Nat.zero_le _) hi) (produces_pure_iff.mpr rfl)

/-- A binding of the list splits it around the binding. -/
theorem split_of_mapContains {k : α} {v : β} {l : List (α × β)} (h : MapContains k v (Map.mk l)) :
    ∃ pre post, l = pre ++ (k, v) :: post := by
  generalize hm : Map.mk l = m at h
  induction h generalizing l with
  | here rest => cases hm; exact ⟨[], rest, rfl⟩
  | there k' v' rest _ ih =>
    cases hm
    obtain ⟨pre, post, rfl⟩ := ih rfl
    exact ⟨(k', v') :: pre, post, rfl⟩

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] {k : α} {v : β} :
    BacktrackGenForComplete (Map α β) (fun m => MapContains k v m) where
  complete m h := by
    cases m with
    | mk l0 =>
    obtain ⟨pre, post, rfl⟩ := split_of_mapContains h
    exact ⟨ArbitrarySizedComplete.bound (pre ++ post), fun s l _ hl => by
      show Produces (do
        let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
        return Map.mk (← insertSomewhere (k, v) rest) : SGen (Map α β)) _
      refine produces_bind_of (ArbitrarySizedComplete.produces hl) ?_
      have := produces_insertSomewhere (k, v) (pre ++ post) pre.length (by simp)
      simp only [List.take_left', List.drop_left'] at this
      exact produces_bind_of this (produces_pure_iff.mpr rfl)⟩

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [ArbitrarySizedComplete α]
    [ArbitrarySizedComplete β] {k : α} :
    BacktrackGenForComplete (β × Map α β) (fun (v, m) => MapContains k v m) where
  complete p h := by
    obtain ⟨v, ⟨l0⟩⟩ := p
    obtain ⟨pre, post, rfl⟩ := split_of_mapContains h
    exact ⟨ArbitrarySizedComplete.bound v + ArbitrarySizedComplete.bound (pre ++ post), fun s l _ hl => by
      show Produces (do
        let v : β ← Basalt.ArbitrarySized.arbitrarySized l
        let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
        return (v, Map.mk (← insertSomewhere (k, v) rest)) : SGen (β × Map α β)) _
      refine produces_bind_of (ArbitrarySizedComplete.produces (x := v) (by omega))
        (produces_bind_of (ArbitrarySizedComplete.produces (x := pre ++ post) (by omega)) ?_)
      have := produces_insertSomewhere (k, v) (pre ++ post) pre.length (by simp)
      simp only [List.take_left', List.drop_left'] at this
      exact produces_bind_of this (produces_pure_iff.mpr rfl)⟩

theorem split_of_setContains {x : α} {l : List α} (h : SetContains x (Data.Set.mk l)) :
    ∃ pre post, l = pre ++ x :: post := by
  generalize hm : Data.Set.mk l = s at h
  induction h generalizing l with
  | here rest => cases hm; exact ⟨[], rest, rfl⟩
  | there y rest _ ih =>
    cases hm
    obtain ⟨pre, post, rfl⟩ := ih rfl
    exact ⟨y :: pre, post, rfl⟩

instance [Basalt.ArbitrarySized α] [ArbitrarySizedComplete α] :
    BacktrackGenForComplete (α × Data.Set α) (fun (x, s) => SetContains x s) where
  complete p h := by
    obtain ⟨x, ⟨l0⟩⟩ := p
    obtain ⟨pre, post, rfl⟩ := split_of_setContains h
    exact ⟨ArbitrarySizedComplete.bound x + ArbitrarySizedComplete.bound (pre ++ post), fun s l _ hl => by
      show Produces (do
        let x : α ← Basalt.ArbitrarySized.arbitrarySized l
        let rest : List α ← Basalt.ArbitrarySized.arbitrarySized l
        return (x, Data.Set.mk (← insertSomewhere x rest)) : SGen (α × Data.Set α)) _
      refine produces_bind_of (ArbitrarySizedComplete.produces (x := x) (by omega))
        (produces_bind_of (ArbitrarySizedComplete.produces (x := pre ++ post) (by omega)) ?_)
      have := produces_insertSomewhere x (pre ++ post) pre.length (by simp)
      simp only [List.take_left', List.drop_left'] at this
      exact produces_bind_of this (produces_pure_iff.mpr rfl)⟩

instance (b : Attr) : BacktrackGenForComplete Attr (fun a => b < a) where
  complete a h := ⟨ArbitrarySizedComplete.bound a, fun s l _ hl => by
    refine produces_of_reach ((reach_frequency (by simp)).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      by simp, reach_of_produces ?_⟩)
    show Produces (do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail : SGen Attr) a
    refine produces_bind_of (ArbitrarySizedComplete.produces hl) ?_
    simp only [decide_eq_true h, ite_true]
    exact produces_pure_iff.mpr rfl⟩

/-! ## Dead operands: any expression -/

theorem produces_frequency_at {α : Type} {gs : List (Nat × (Unit → SGen α))} {h} (i : Nat)
    (hi : i < gs.length) (hw : 0 < gs[i].1) {x : α} (hx : Produces (gs[i].2 ()) x) :
    Produces (frequency gs h) x :=
  produces_of_reach ((reach_frequency h).mpr ⟨gs[i], List.getElem_mem hi, hw, reach_of_produces hx⟩)

theorem produces_map_of {α β : Type} {g : SGen α} {f : α → β} {a : α} (h : Produces g a) :
    Produces (f <$> g) (f a) := by
  rw [map_eq_pure_bind]; exact produces_bind_of h (produces_pure_iff.mpr rfl)

noncomputable section

/-- A size at which a free attribute draw produces each of the attributes. -/
def attrsBound : List Attr → Nat
  | [] => 0
  | a :: as => max (ArbitrarySizedComplete.bound a) (attrsBound as)

mutual
/-- A fuel and a budget at which `anyExprB` produces the expression: one more than its depth (an
extended `has` spending its attributes), and than what its leaves and lists need. -/
def exprBound : Expr → Nat
  | .lit p => ArbitrarySizedComplete.bound p + 1
  | .var v => ArbitrarySizedComplete.bound v + 1
  | .ite a b c => max (exprBound a) (max (exprBound b) (exprBound c)) + 1
  | .and a b => max (exprBound a) (exprBound b) + 1
  | .or a b => max (exprBound a) (exprBound b) + 1
  | .unaryApp op a => max (ArbitrarySizedComplete.bound op) (exprBound a) + 1
  | .binaryApp op a b => max (ArbitrarySizedComplete.bound op) (max (exprBound a) (exprBound b)) + 1
  | .getAttr a k => max (exprBound a) (ArbitrarySizedComplete.bound k) + 1
  | .hasAttr a k => max (exprBound a) (ArbitrarySizedComplete.bound k) + 1
  | .extHasAttr a k ks =>
    max (exprBound a + ks.length) (max (ArbitrarySizedComplete.bound k) (attrsBound ks)) + 1
  | .set xs => max xs.length (exprListBound xs) + 1
  | .record axs => max axs.length (exprRecordBound axs) + 1
  | .call f xs => max (ArbitrarySizedComplete.bound f) (max xs.length (exprListBound xs)) + 1

def exprListBound : List Expr → Nat
  | [] => 0
  | x :: xs => max (exprBound x) (exprListBound xs)

def exprRecordBound : List (Attr × Expr) → Nat
  | [] => 0
  | (a, x) :: axs => max (max (ArbitrarySizedComplete.bound a) (exprBound x)) (exprRecordBound axs)
end

theorem exprBound_pos : ∀ e : Expr, 0 < exprBound e := by
  intro e; cases e <;> simp [exprBound]

theorem succ_of_exprBound {e : Expr} {n : Nat} (h : exprBound e ≤ n) : ∃ m, n = m + 1 :=
  ⟨n - 1, by have := exprBound_pos e; omega⟩

end

theorem attrs_produces : ∀ (ks : List Attr) (n : Nat), attrsBound ks ≤ n →
    ∀ a ∈ ks, Produces (Basalt.ArbitrarySized.arbitrarySized n : SGen Attr) a
  | [], _, _ => fun _ ha => absurd ha List.not_mem_nil
  | k :: ks, n, h => fun a ha => by
    simp only [attrsBound] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ArbitrarySizedComplete.produces (by omega)
    · exact attrs_produces ks n (by omega) a ha

mutual
theorem anyExprB_produces : ∀ (e : Expr) (n m : Nat), exprBound e ≤ n → exprBound e ≤ m →
    Produces (anyExprB n m : SGen Expr) e
  | .lit p, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 0 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_map_of (ArbitrarySizedComplete.produces (by omega)))
  | .var v, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_map_of (ArbitrarySizedComplete.produces (by omega)))
  | .ite a b c, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 2 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (anyExprB_produces a n m (by omega) (by omega)) (produces_bind_of (anyExprB_produces b n m (by omega) (by omega))
        (produces_bind_of (anyExprB_produces c n m (by omega) (by omega)) (produces_pure_iff.mpr rfl))))
  | .and a b, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 3 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (anyExprB_produces a n m (by omega) (by omega)) (produces_bind_of (anyExprB_produces b n m (by omega) (by omega))
        (produces_pure_iff.mpr rfl)))
  | .or a b, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 4 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (anyExprB_produces a n m (by omega) (by omega)) (produces_bind_of (anyExprB_produces b n m (by omega) (by omega))
        (produces_pure_iff.mpr rfl)))
  | .unaryApp op a, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 5 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (ArbitrarySizedComplete.produces (x := op) (by omega))
        (produces_bind_of (anyExprB_produces a n m (by omega) (by omega)) (produces_pure_iff.mpr rfl)))
  | .binaryApp op a b, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 6 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (ArbitrarySizedComplete.produces (x := op) (by omega))
        (produces_bind_of (anyExprB_produces a n m (by omega) (by omega)) (produces_bind_of (anyExprB_produces b n m (by omega) (by omega))
          (produces_pure_iff.mpr rfl))))
  | .getAttr a k, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 7 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (anyExprB_produces a n m (by omega) (by omega))
        (produces_bind_of (ArbitrarySizedComplete.produces (x := k) (by omega)) (produces_pure_iff.mpr rfl)))
  | .hasAttr a k, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 8 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (anyExprB_produces a n m (by omega) (by omega))
        (produces_bind_of (ArbitrarySizedComplete.produces (x := k) (by omega)) (produces_pure_iff.mpr rfl)))
  | .extHasAttr a k ks, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 9 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (produces_chooseNat (k := ks.length) _ (Nat.zero_le _) (by omega))
        (produces_bind_of (produces_vectorOf ks (attrs_produces ks n (by omega)))
          (produces_bind_of (ArbitrarySizedComplete.produces (x := k) (by omega))
            (produces_bind_of (anyExprB_produces a n (m - ks.length) (by omega) (by omega))
              (produces_pure_iff.mpr rfl)))))
  | .set xs, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 10 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (produces_chooseNat (k := xs.length) _ (Nat.zero_le _) (by omega))
        (produces_bind_of (produces_vectorOf xs (anyExprList_produces xs n m (by omega) (by omega)))
          (produces_pure_iff.mpr rfl)))
  | .record axs, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 11 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (produces_chooseNat (k := axs.length) _ (Nat.zero_le _) (by omega))
        (produces_bind_of (produces_vectorOf axs (anyRecord_produces axs n m (by omega) (by omega)))
          (produces_pure_iff.mpr rfl)))
  | .call f xs, n, m, h, hm => by
    obtain ⟨n, rfl⟩ := succ_of_exprBound h
    obtain ⟨m, rfl⟩ := succ_of_exprBound hm
    simp only [exprBound] at h hm
    refine produces_frequency_at 12 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (ArbitrarySizedComplete.produces (x := f) (by omega))
        (produces_bind_of (produces_chooseNat (k := xs.length) _ (Nat.zero_le _) (by omega))
          (produces_bind_of (produces_vectorOf xs (anyExprList_produces xs n m (by omega) (by omega)))
            (produces_pure_iff.mpr rfl))))

theorem anyExprList_produces : ∀ (xs : List Expr) (n m : Nat), exprListBound xs ≤ n →
    exprListBound xs ≤ m → ∀ x ∈ xs, Produces (anyExprB n m : SGen Expr) x
  | [], _, _, _, _ => fun _ hx => absurd hx List.not_mem_nil
  | y :: ys, n, m, h, hm => fun x hx => by
    simp only [exprListBound] at h hm
    rcases List.mem_cons.mp hx with hxy | hx
    · rw [hxy]; exact anyExprB_produces y n m (by omega) (by omega)
    · exact anyExprList_produces ys n m (by omega) (by omega) x hx

theorem anyRecord_produces : ∀ (axs : List (Attr × Expr)) (n m : Nat), exprRecordBound axs ≤ n →
    exprRecordBound axs ≤ m → ∀ p ∈ axs, Produces (do
      let a ← Basalt.ArbitrarySized.arbitrarySized n
      let x ← anyExprB n m
      pure (a, x) : SGen (Attr × Expr)) p
  | [], _, _, _, _ => fun _ hx => absurd hx List.not_mem_nil
  | (a, y) :: ys, n, m, h, hm => fun p hp => by
    simp only [exprRecordBound] at h hm
    rcases List.mem_cons.mp hp with hpy | hp
    · rw [hpy]
      exact produces_bind_of (ArbitrarySizedComplete.produces (x := a) (by omega))
        (produces_bind_of (anyExprB_produces y n m (by omega) (by omega)) (produces_pure_iff.mpr rfl))
    · exact anyRecord_produces ys n m (by omega) (by omega) p hp
end

theorem anyExpr_produces (e : Expr) (n : Nat) (h : exprBound e ≤ n) :
    Produces (anyExpr n : SGen Expr) e :=
  anyExprB_produces e n n h h



/-! ## Any type -/

noncomputable section

mutual
/-- A size at which `anyCedarType` produces the type. -/
def tyBound : CedarType → Nat
  | .bool b => ArbitrarySizedComplete.bound b + 1
  | .int => 1
  | .string => 1
  | .entity e => ArbitrarySizedComplete.bound e + 1
  | .ext x => ArbitrarySizedComplete.bound x + 1
  | .set t => tyBound t + 1
  | .record (.mk fs) => max fs.length (fieldsBound fs) + 1

def qualTyBound : Qualified CedarType → Nat
  | .required t => tyBound t
  | .optional t => tyBound t

def fieldsBound : List (Attr × Qualified CedarType) → Nat
  | [] => 0
  | (a, q) :: fs => max (max (ArbitrarySizedComplete.bound a) (qualTyBound q)) (fieldsBound fs)
end

theorem succ_of_tyBound {t : CedarType} {n : Nat} (h : tyBound t ≤ n) : ∃ m, n = m + 1 := by
  refine ⟨n - 1, ?_⟩
  have : 0 < tyBound t := by cases t <;> simp [tyBound]
  omega

end

mutual
theorem anyCedarType_produces : ∀ (t : CedarType) (n : Nat), tyBound t ≤ n →
    Produces (anyCedarType n : SGen CedarType) t
  | .int, n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    refine produces_frequency_at 0 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_pure_iff.mpr rfl
  | .string, n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_pure_iff.mpr rfl
  | .bool b, n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    simp only [tyBound] at h
    refine produces_frequency_at 2 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_map_of (ArbitrarySizedComplete.produces (by omega))
  | .entity e, n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    simp only [tyBound] at h
    refine produces_frequency_at 3 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_map_of (ArbitrarySizedComplete.produces (by omega))
  | .ext x, n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    simp only [tyBound] at h
    refine produces_frequency_at 4 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_map_of (ArbitrarySizedComplete.produces (by omega))
  | .set t, n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    simp only [tyBound] at h
    refine produces_frequency_at 5 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_map_of (anyCedarType_produces t n (by omega))
  | .record (.mk fs), n, h => by
    obtain ⟨n, rfl⟩ := succ_of_tyBound h
    simp only [tyBound] at h
    refine produces_frequency_at 6 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx =>
      exact produces_bind_of (produces_chooseNat (k := fs.length) _ (Nat.zero_le _) (by omega))
        (produces_bind_of (produces_vectorOf fs (anyFields_produces fs n (by omega)))
          (produces_pure_iff.mpr rfl))

theorem anyQual_produces : ∀ (q : Qualified CedarType) (n : Nat), qualTyBound q ≤ n →
    Produces (frequency [(1, fun _ => .required <$> anyCedarType n),
      (1, fun _ => .optional <$> anyCedarType n)] : SGen (Qualified CedarType)) q
  | .required t, n, h => by
    simp only [qualTyBound] at h
    refine produces_frequency_at 0 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_map_of (anyCedarType_produces t n h)
  | .optional t, n, h => by
    simp only [qualTyBound] at h
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact produces_map_of (anyCedarType_produces t n h)

theorem anyFields_produces : ∀ (fs : List (Attr × Qualified CedarType)) (n : Nat), fieldsBound fs ≤ n →
    ∀ p ∈ fs, Produces (do
      let a ← Basalt.ArbitrarySized.arbitrarySized n
      let q ← frequency [(1, fun _ => .required <$> anyCedarType n),
        (1, fun _ => .optional <$> anyCedarType n)]
      pure (a, q) : SGen (Attr × Qualified CedarType)) p
  | [], _, _ => fun _ hp => absurd hp List.not_mem_nil
  | (a, q) :: fs, n, h => fun p hp => by
    simp only [fieldsBound] at h
    rcases List.mem_cons.mp hp with hpq | hp
    · rw [hpq]
      exact produces_bind_of (ArbitrarySizedComplete.produces (x := a) (by omega))
        (produces_bind_of (anyQual_produces q n (by omega)) (produces_pure_iff.mpr rfl))
    · exact anyFields_produces fs n (by omega) p hp
end

instance : ArbitrarySizedComplete CedarType where
  complete t := ⟨tyBound t, fun s hs => by
    unfold_arbitrary
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact anyCedarType_produces t s hs⟩

/-- A free expression draw produces every expression: by its `anyExpr` branch. -/
instance : ArbitrarySizedComplete Expr where
  complete x := ⟨exprBound x, fun s hs => by
    show Produces (frequency [(9, fun _ => pure (.lit (.bool true))), (1, fun _ => anyExpr s)] _ :
      SGen Expr) x
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact anyExpr_produces x s hs⟩

/-- A size at which a free key draw produces the key. -/
noncomputable def keyBound : Key → Nat
  | .attr a => ArbitrarySizedComplete.bound a
  | .tag x => exprBound x

instance : ArbitrarySizedComplete Key where
  complete k := ⟨keyBound k, fun s hs => by
    show Produces (frequency [(9, fun _ => pure (.attr "")),
      (1, fun _ => .attr <$> Basalt.ArbitrarySized.arbitrarySized s), (1, fun _ => .tag <$> anyExpr s)] _ :
      SGen Key) k
    cases k with
    | attr a =>
      refine produces_frequency_at 1 ?hi ?hw ?hx
      case hi => simp only [List.length_cons, List.length_nil]; omega
      case hw => exact Nat.zero_lt_succ _
      case hx => exact produces_map_of (ArbitrarySizedComplete.produces (by simpa [keyBound] using hs))
    | tag x =>
      refine produces_frequency_at 2 ?hi ?hw ?hx
      case hi => simp only [List.length_cons, List.length_nil]; omega
      case hw => exact Nat.zero_lt_succ _
      case hx => exact produces_map_of (anyExpr_produces x s (by simpa [keyBound] using hs))⟩

/-- The dead-operand producer produces every dead operand: by its `anyExpr` branch. -/
instance {decl syn : Bool} {env : TypeEnv} :
    BacktrackGenForComplete Expr (fun x => DeadOperand decl syn env x) where
  complete x h := ⟨exprBound x, fun s l _ hl => by
    simp only [BacktrackGenFor.gen]
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx => exact (produces_bind_of (anyExpr_produces x l hl)
        (by rw [if_pos (deadOperand_iff.mp h)]; exact produces_pure_iff.mpr rfl))⟩

/-! ## Action ancestor types -/

theorem mem_maybeActionAncestorTypes {acts : ActionSchema} {ety₁ ety₂ : EntityType}
    (h : MaybeActionDescendentOf acts ety₁ ety₂) : ety₂ ∈ maybeActionAncestorTypes acts ety₁ := by
  cases h with
  | mk uid entry anc hm hs =>
  obtain ⟨l⟩ := acts
  simp only [maybeActionAncestorTypes, List.mem_flatMap]
  refine ⟨(uid, entry), mapContains_iff_mem.mp hm, ?_⟩
  simp only [beq_self_eq_true, if_true, List.mem_map]
  generalize entry.ancestors = as at hs ⊢
  obtain ⟨al⟩ := as
  exact ⟨anc, setContains_mk_iff_mem.mp hs, rfl⟩

/-- The action-ancestor producer draws every ancestor type: by its index among the candidates. -/
instance {acts : ActionSchema} {ety₁ : EntityType} :
    BacktrackGenForComplete EntityType (fun ety₂ => MaybeActionDescendentOf acts ety₁ ety₂) where
  complete ety₂ h := ⟨0, fun _ _ _ _ => by
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mem_maybeActionAncestorTypes h)
    simp only [BacktrackGenFor.gen]
    refine produces_bind_of (produces_chooseNat (k := i) _ (Nat.zero_le _) (by omega)) ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he,
      if_pos (maybeActionDescendentOf_iff.mp h)]
    exact produces_pure_iff.mpr rfl⟩

/-! ## Action literals in a set of entity literals -/

theorem exists_uids_of_all_lits : ∀ (xs : List Expr), (∀ x ∈ xs, ∃ uid, x = Expr.lit (.entityUID uid)) →
    ∃ uids : List EntityUID, xs = uids.map fun u => Expr.lit (.entityUID u)
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨u, rfl⟩ := h x List.mem_cons_self
    obtain ⟨us, rfl⟩ := exists_uids_of_all_lits xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨u :: us, rfl⟩

theorem produces_actionOrAnyUID {acts : ActionSchema} {leaf : Nat} {u : EntityUID}
    (h : ArbitrarySizedComplete.bound u ≤ leaf) : Produces (actionOrAnyUID acts leaf : SGen EntityUID) u := by
  unfold actionOrAnyUID
  refine produces_frequency_at 1 ?hi ?hw ?hx
  case hi => simp only [List.length_cons, List.length_nil]; omega
  case hw => exact Nat.zero_lt_succ _
  case hx => exact ArbitrarySizedComplete.produces h

instance {acts : ActionSchema} :
    BacktrackGenForComplete (Expr × Expr) (fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) where
  complete p h := by
    obtain ⟨x₁, x₂⟩ := p
    have hb := isActionLitMemSet_test h
    cases h with
    | mk uid₁ xs acts entry hm hall =>
    obtain ⟨uids, rfl⟩ := exists_uids_of_all_lits xs hall
    obtain ⟨l⟩ := acts
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mapContains_iff_mem.mp hm)
    exact ⟨uids.length + (uids.map ArbitrarySizedComplete.bound).sum, fun _ leaf _ hl => by
      simp only [BacktrackGenFor.gen]
      refine produces_bind_of (produces_chooseNat (k := i) _ (Nat.zero_le _)
        (by simp only [Map.toList] at hi ⊢; omega)) ?_
      have hg : ((Map.mk l).toList.getD i default).1 = uid₁ := by
        simp only [Map.toList]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
      simp only [hg]
      refine produces_bind_of (produces_chooseNat (k := uids.length) _ (Nat.zero_le _) (by omega)) ?_
      refine produces_bind_of (produces_vectorOf uids fun u hu =>
        produces_actionOrAnyUID (Nat.le_trans (le_sum_of_mem hu) (by omega))) ?_
      rw [if_pos hb]
      exact produces_pure_iff.mpr rfl⟩

instance {acts : ActionSchema} :
    EnumForComplete (Expr × Expr) (fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) where
  complete p h := by
    obtain ⟨x₁, x₂⟩ := p
    have hb := isActionLitMemSet_test h
    cases h with
    | mk uid₁ xs acts entry hm hall =>
    obtain ⟨uids, rfl⟩ := exists_uids_of_all_lits xs hall
    obtain ⟨l⟩ := acts
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mapContains_iff_mem.mp hm)
    exact ⟨uids.length + (uids.map ArbitrarySizedComplete.bound).sum, fun _ leaf _ hl => by
      simp only [EnumFor.enum]
      refine produces_bind_of (produces_chooseNat (k := i) _ (Nat.zero_le _)
        (by simp only [Map.toList] at hi ⊢; omega)) ?_
      have hg : ((Map.mk l).toList.getD i default).1 = uid₁ := by
        simp only [Map.toList]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
      simp only [hg]
      refine produces_bind_of (produces_chooseNat (k := uids.length) _ (Nat.zero_le _) (by omega)) ?_
      refine produces_bind_of (produces_vectorOf uids fun u hu =>
        produces_actionOrAnyUID (Nat.le_trans (le_sum_of_mem hu) (by omega))) ?_
      rw [if_pos hb]
      exact produces_pure_iff.mpr rfl⟩

/-! ## Extension literals and record sorting -/

theorem insertStrict_of_insertSortedField {ax : Attr × Expr} {l l' : List (Attr × Expr)}
    (h : InsertSortedField ax l l') : insertStrict ax l = some l' := by
  induction h with
  | nil => rfl
  | here a x a' x' axs hlt => simp [insertStrict, hlt]
  | there a x a' x' axs axs' hlt _ ih =>
    simp [insertStrict, String.lt_asymm hlt, hlt, ih]

theorem sortStrict_of_sortsTo {axs axs' : List (Attr × Expr)} (h : SortsTo axs axs') :
    sortStrict axs = some axs' := by
  induction h with
  | nil => rfl
  | cons ax axs axs' axs'' _ hi ih => simp [sortStrict, ih, insertStrict_of_insertSortedField hi]

instance : DecOptCompleteAll (SortsTo axs axs') :=
  decOptComplete_of _ (fun _ => rfl) fun h => by simp [sortsToB, sortStrict_of_sortsTo h]

instance {axs : List (Attr × Expr)} :
    BacktrackGenForComplete (List (Attr × Expr)) (fun axs' => SortsTo axs axs') where
  complete axs' h := ⟨0, fun _ _ _ _ => by
    simp only [BacktrackGenFor.gen, sortStrict_of_sortsTo h]
    exact produces_pure_iff.mpr rfl⟩

theorem perm_of_insertSortedField {ax : Attr × Expr} {l l' : List (Attr × Expr)}
    (h : InsertSortedField ax l l') : l'.Perm (ax :: l) := by
  induction h with
  | nil => exact .refl _
  | here => exact .refl _
  | there a x a' x' axs axs' _ _ ih => exact (ih.cons _).trans (.swap _ _ _)

theorem perm_of_sortsTo {axs axs' : List (Attr × Expr)} (h : SortsTo axs axs') : axs'.Perm axs := by
  induction h with
  | nil => exact .nil
  | cons ax axs axs' axs'' _ hi ih => exact (perm_of_insertSortedField hi).trans (ih.cons _)

/-- `shuffle` produces every permutation. -/
theorem produces_shuffle : ∀ (xs l : List α), l.Perm xs → Produces (shuffle xs : SGen (List α)) l
  | [], l, h => by rw [h.eq_nil]; exact produces_pure_iff.mpr rfl
  | x :: xs, l, h => by
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem (h.symm.subset List.mem_cons_self)
    have hp : (pre ++ post).Perm xs := (List.perm_middle.symm.trans h).cons_inv
    show Produces (do insertSomewhere x (← shuffle xs) : SGen (List α)) _
    refine produces_bind_of (produces_shuffle xs _ hp) ?_
    have := produces_insertSomewhere x (pre ++ post) pre.length (by simp)
    simpa only [List.take_left', List.drop_left'] using this

instance {axs' : List (Attr × Expr)} :
    BacktrackGenForComplete (List (Attr × Expr)) (fun axs => SortsTo axs axs') where
  complete axs h := ⟨0, fun _ _ _ _ => by
    simp only [BacktrackGenFor.gen]
    refine produces_frequency_at 1 ?hi ?hw ?hx
    case hi => simp only [List.length_cons, List.length_nil]; omega
    case hw => exact Nat.zero_lt_succ _
    case hx =>
      have hb : sortsToB axs axs' = true := by simp [sortsToB, sortStrict_of_sortsTo h]
      exact produces_bind_of (produces_shuffle axs' axs (perm_of_sortsTo h).symm)
        (by rw [if_pos hb]; exact produces_pure_iff.mpr rfl)⟩

/-- The extension-literal producers (`orParsing`) produce every string that parses: by their
    parsing branch. -/
theorem produces_orParsing {ok : String → Bool} {leaf : Nat} {g : SGen String} {s : String}
    (hs : ok s = true) (hl : ArbitrarySizedComplete.bound s ≤ leaf) :
    Produces (orParsing ok leaf g) s := by
  refine produces_frequency_at 1 ?hi ?hw ?hx
  case hi => simp only [List.length_cons, List.length_nil]; omega
  case hw => exact Nat.zero_lt_succ _
  case hx =>
    exact produces_bind_of (ArbitrarySizedComplete.produces hl)
      (by rw [if_pos hs]; exact produces_pure_iff.mpr rfl)

instance : BacktrackGenForComplete String ValidDecimal where
  complete s h := ⟨ArbitrarySizedComplete.bound s, fun _ _ _ hl =>
    produces_orParsing (ValidDecimal.rec (motive := fun _ => (Cedar.Spec.Ext.Decimal.decimal s).isSome = true)
      (fun _ hd => by rw [hd]; rfl) h) hl⟩

instance : BacktrackGenForComplete String ValidIP where
  complete s h := ⟨ArbitrarySizedComplete.bound s, fun _ _ _ hl =>
    produces_orParsing (ValidIP.rec (motive := fun _ => (Cedar.Spec.Ext.IPAddr.ip s).isSome = true)
      (fun _ hd => by rw [hd]; rfl) h) hl⟩

instance : BacktrackGenForComplete String ValidDatetime where
  complete s h := ⟨ArbitrarySizedComplete.bound s, fun _ _ _ hl =>
    produces_orParsing (ValidDatetime.rec (motive := fun _ => (Cedar.Spec.Ext.Datetime.parse s).isSome = true)
      (fun _ hd => by rw [hd]; rfl) h) hl⟩

instance : BacktrackGenForComplete String ValidDuration where
  complete s h := ⟨ArbitrarySizedComplete.bound s, fun _ _ _ hl =>
    produces_orParsing (ValidDuration.rec (motive := fun _ => (Cedar.Spec.Ext.Datetime.Duration.parse s).isSome = true)
      (fun _ hd => by rw [hd]; rfl) h) hl⟩

/-! ## Unconstrained draws, searched

What a derived enumerator's search for a witness needs of the types it draws freely, for a checker's
completeness: each instance's search reaches what it draws (`ArbitrarySizedHits`). -/

section DrawsHit

instance : ArbitrarySizedHits BoolType := arbitrary_hits
instance : ArbitrarySizedHits ExtType := arbitrary_hits
instance : ArbitrarySizedHits Name := arbitrary_hits
instance : ArbitrarySizedHits EntityType := arbitrary_hits

@[gen_rule] theorem anyCedarType_searchHits : ∀ n,
    SearchHits (anyCedarType n : SGen CedarType) (anyCedarType n : Specimen.Search CedarType)
  | 0 => by unfold anyCedarType; walk
  | n + 1 => by unfold anyCedarType; walk [anyCedarType_searchHits n]

instance : ArbitrarySizedHits CedarType :=
  ⟨by intro n; unfold_arbitrary; walk [anyCedarType_searchHits n]⟩
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedHits α] : ArbitrarySizedHits (Qualified α) :=
  arbitrary_hits
instance : ArbitrarySizedHits EntityUID := arbitrary_hits
instance : ArbitrarySizedHits Int64 := arbitrary_hits
instance : ArbitrarySizedHits Prim := arbitrary_hits
instance : ArbitrarySizedHits Var := arbitrary_hits
instance : ArbitrarySizedHits ExtFun := arbitrary_hits
instance : ArbitrarySizedHits PatElem := arbitrary_hits
instance : ArbitrarySizedHits UnaryOp := arbitrary_hits
instance : ArbitrarySizedHits BinaryOp := arbitrary_hits
instance : ArbitrarySizedHits Effect := arbitrary_hits

@[gen_rule] theorem anyExprB_searchHits : ∀ f b,
    SearchHits (anyExprB f b : SGen Expr) (anyExprB f b : Specimen.Search Expr)
  | 0, _ => by unfold anyExprB; walk
  | _ + 1, 0 => by unfold anyExprB; walk
  | f + 1, _ + 1 => by unfold anyExprB; walk [anyExprB_searchHits f]

@[gen_rule] theorem anyExpr_searchHits (n : Nat) :
    SearchHits (anyExpr n : SGen Expr) (anyExpr n : Specimen.Search Expr) := by
  unfold anyExpr; exact anyExprB_searchHits n n

instance : ArbitrarySizedHits Expr :=
  ⟨by intro n; unfold_arbitrary; walk [anyExpr_searchHits n]⟩
instance {α β : Type} [LT α] [DecidableLT α] [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β]
    [ArbitrarySizedHits α] [ArbitrarySizedHits β] : ArbitrarySizedHits (Map α β) := arbitrary_hits

end DrawsHit

/-! ## The hand-written enumerators, complete and searched -/

instance : ArbitrarySizedHits Key := arbitrary_hits

instance (b : Attr) : EnumForComplete Attr (fun a => b < a) where
  complete a h := ⟨ArbitrarySizedComplete.bound a, fun s l _ hl => by
    refine produces_of_reach ((reach_frequency (by simp)).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      by simp, reach_of_produces ?_⟩)
    show Produces (do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail : SGen Attr) a
    refine produces_bind_of (ArbitrarySizedComplete.produces hl) ?_
    simp only [decide_eq_true h, ite_true]
    exact produces_pure_iff.mpr rfl⟩

instance (b : Attr) : EnumForComplete Attr (fun a => a < b) where
  complete a h := ⟨ArbitrarySizedComplete.bound a, fun s l _ hl => by
    show Produces (do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (a < b) then return a else Specimen.Fail.fail : SGen Attr) a
    refine produces_bind_of (ArbitrarySizedComplete.produces hl) ?_
    simp only [decide_eq_true h, ite_true]
    exact produces_pure_iff.mpr rfl⟩

instance (b : Attr) : EnumForSearch Attr (fun a => b < a) :=
  ⟨fun s l => by show SearchHits (frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail)] : SGen Attr) (frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail)] : Specimen.Search Attr); walk⟩

instance (b : Attr) : EnumForSearch Attr (fun a => a < b) :=
  ⟨fun s l => by
    show SearchHits (do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (a < b) then return a else Specimen.Fail.fail : SGen Attr) (do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (a < b) then return a else Specimen.Fail.fail : Specimen.Search Attr)
    walk⟩

instance {acts : ActionSchema} :
    EnumForSearch (Expr × Expr) (fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) :=
  ⟨fun s l => by simp only [EnumFor.enum, actionOrAnyUID]; walk⟩

end Cedar.Validation.Relational

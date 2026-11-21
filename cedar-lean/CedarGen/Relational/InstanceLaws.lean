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

import CedarGen.Relational.Instances
import Cedar.Thm.Validation.Relational.Soundness
import Specimen.Correctness.SoundOf
import Specimen.Correctness.SearchFinds

/-! # Laws of the hand-written instances

What the soundness proofs of the generators derived against `Instances` need: for each `DecOpt`
instance, `test = true → R …` (`@[specimen_check]`), and its negation where a rule needs `R` to fail;
for each hand-written generator, its soundness (`@[specimen_sound]`); for each unconstrained draw,
`ArbitrarySizedSearch`. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

@[specimen_check] theorem capMem_of_any {x : Expr} {k : Key} :
    ∀ {c : Capabilities}, (c.any fun (x', k') => x' == x && k' == k) = true → CapMem x k c
  | [], h => by simp at h
  | (x', k') :: c, h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .here _ _ _
    · exact .there _ _ _ _ _ (capMem_of_any h)

@[specimen_check] theorem capTagMem_of_any {x e : Expr} :
    ∀ {c : Capabilities}, (c.any fun (x', k') => x' == x && k' == .tag e) = true → CapTagMem x e c
  | [], h => by simp at h
  | (x', k') :: c, h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .here _ _ _
    · exact .there _ _ _ _ _ (capTagMem_of_any h)

@[specimen_check] theorem capAttrMem_of_any {x : Expr} {a : Attr} :
    ∀ {c : Capabilities}, (c.any fun (x', k') => x' == x && k' == .attr a) = true → CapAttrMem x a c
  | [], h => by simp at h
  | (x', k') :: c, h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .here _ _ _
    · exact .there _ _ _ _ _ (capAttrMem_of_any h)

@[specimen_check] theorem mapContains_of_any {α β : Type} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
    {k : α} {v : β} : ∀ {m : Map α β},
    (match m with | .mk l => l.any (fun (k', v') => k' == k && v' == v)) = true → MapContains k v m
  | .mk [], h => by simp at h
  | .mk ((k', v') :: l), h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .here _ _ _
    · exact .there _ _ _ _ _ (mapContains_of_any (m := .mk l) h)

@[specimen_check] theorem mapNotContainsKey_of_all {α β : Type} [DecidableEq α] {k : α} :
    ∀ {m : Map α β}, (match m with | .mk l => l.all (fun (k', _) => k' != k)) = true →
      MapNotContainsKey k m
  | .mk [], _ => .empty _
  | .mk ((k', v') :: l), h => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact .skip _ _ _ _ (fun e => h.1 e.symm) (mapNotContainsKey_of_all (m := .mk l) h.2)

@[specimen_check] theorem setContains_of_any {α : Type} [BEq α] [LawfulBEq α] {x : α} :
    ∀ {s : Data.Set α}, (match s with | .mk l => l.any (· == x)) = true → SetContains x s
  | .mk [], h => by simp at h
  | .mk (y :: l), h => by
    simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .here _ _
    · exact .there _ _ _ (setContains_of_any (s := .mk l) h)

@[specimen_check] theorem mapContainsAncestors_of_any {ety : EntityType} {ancs : Data.Set EntityType} :
    ∀ {ets : EntitySchema}, (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
      match v with | .standard ⟨a, _, _⟩ => a == ancs | _ => false)) = true →
      MapContainsAncestors ety ancs ets
  | .mk [], h => by simp at h
  | .mk ((k, v) :: l), h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h⟩ | h
    · match v, h with
      | .standard ⟨a, _, _⟩, h =>
        simp only [beq_iff_eq] at h; subst h; exact .here _ _ _ _ _
    · exact .there _ _ _ _ _ (mapContainsAncestors_of_any (ets := .mk l) h)

@[specimen_check] theorem mapContainsAttrs_of_any {ety : EntityType} {attrs : RecordType} :
    ∀ {ets : EntitySchema}, (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
      match v with | .standard ⟨_, a, _⟩ => a == attrs | _ => false)) = true →
      MapContainsAttrs ety attrs ets
  | .mk [], h => by simp at h
  | .mk ((k, v) :: l), h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h⟩ | h
    · match v, h with
      | .standard ⟨_, a, _⟩, h =>
        simp only [beq_iff_eq] at h; subst h; exact .here _ _ _ _ _
    · exact .there _ _ _ _ _ (mapContainsAttrs_of_any (ets := .mk l) h)

@[specimen_check] theorem mapContainsTagType_of_any {ety : EntityType} {ty : CedarType} :
    ∀ {ets : EntitySchema}, (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
      match v with | .standard ⟨_, _, .some t⟩ => t == ty | _ => false)) = true →
      MapContainsTagType ety ty ets
  | .mk [], h => by simp at h
  | .mk ((k, v) :: l), h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h⟩ | h
    · match v, h with
      | .standard ⟨_, _, .some t⟩, h =>
        simp only [beq_iff_eq] at h; subst h; exact .here _ _ _ _ _
    · exact .there _ _ _ _ _ (mapContainsTagType_of_any (ets := .mk l) h)

@[specimen_check] theorem mapContainsNoTags_of_any {ety : EntityType} :
    ∀ {ets : EntitySchema}, (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
      match v with | .standard ⟨_, _, .none⟩ => true | _ => false)) = true →
      MapContainsNoTags ety ets
  | .mk [], h => by simp at h
  | .mk ((k, v) :: l), h => by
    simp only [List.any_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h⟩ | h
    · match v, h with
      | .standard ⟨_, _, .none⟩, _ => exact .here _ _ _ _
    · exact .there _ _ _ _ (mapContainsNoTags_of_any (ets := .mk l) h)

@[specimen_check] theorem keyAbove_of_test {lb : Option Attr} {a : Attr} :
    (match lb with | none => true | some b => decide (b < a)) = true → KeyAbove lb a := by
  cases lb with
  | none => intro; exact .none _
  | some b => intro h; exact .some _ _ (of_decide_eq_true h)

@[specimen_check] theorem validDecimal_of_isSome {s : String} :
    (Cedar.Spec.Ext.Decimal.decimal s).isSome = true → ValidDecimal s := by
  intro h; obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h; exact .mk _ _ hd

@[specimen_check] theorem validIP_of_isSome {s : String} :
    (Cedar.Spec.Ext.IPAddr.ip s).isSome = true → ValidIP s := by
  intro h; obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h; exact .mk _ _ hd

@[specimen_check] theorem validDatetime_of_isSome {s : String} :
    (Cedar.Spec.Ext.Datetime.parse s).isSome = true → ValidDatetime s := by
  intro h; obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h; exact .mk _ _ hd

@[specimen_check] theorem validDuration_of_isSome {s : String} :
    (Cedar.Spec.Ext.Datetime.Duration.parse s).isSome = true → ValidDuration s := by
  intro h; obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h; exact .mk _ _ hd

theorem mapContains_of_mem {α β : Type} {k : α} {v : β} :
    ∀ {l : List (α × β)}, (k, v) ∈ l → MapContains k v (.mk l)
  | [], h => by simp at h
  | (k', v') :: l, h => by
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact .here _ _ _
    · exact .there _ _ _ _ _ (mapContains_of_mem h)

@[specimen_check] theorem mapContainsEnum_of_find {ety : EntityType} {eids : Data.Set String} :
    ∀ {ets : EntitySchema}, (match ets with
      | .mk l =>
        match l.find? (fun (k, _) => k == ety) with
        | some (_, .enum e) => e == eids
        | _ => false) = true → MapContainsEnum ety eids ets
  | .mk [], h => by simp at h
  | .mk ((k, v) :: l), h => by
    by_cases hk : k = ety
    · subst hk
      simp only [List.find?_cons, beq_self_eq_true] at h
      match v, h with
      | .enum e, h => simp only [beq_iff_eq] at h; subst h; exact .here _ _ _
      | .standard _, h => simp at h
    · have hk' : (k == ety) = false := by simpa using hk
      simp only [List.find?_cons, hk'] at h
      exact .there _ _ _ _ _ hk (mapContainsEnum_of_find (ets := .mk l) h)

@[specimen_check] theorem mapContainsPairKey_of_find {v : Type} [BEq v] [LawfulBEq v] {a : EntityType}
    {b : String} {va : v} : ∀ {m : Map EntityUID v}, (match m with
      | .mk l =>
        match l.find? (fun (uid, _) => uid.ty == a && uid.eid == b) with
        | some (_, val) => val == va
        | none => false) = true → MapContainsPairKey a b va m
  | .mk [], h => by simp at h
  | .mk ((⟨a', b'⟩, v') :: l), h => by
    by_cases ha : a' = a
    · by_cases hb : b' = b
      · subst ha hb
        simp only [List.find?_cons, beq_self_eq_true, Bool.and_self, beq_iff_eq] at h
        subst h; exact .here
      · have : ((a' == a && b' == b)) = false := by simp [hb]
        simp only [List.find?_cons, this] at h
        exact .nextB (Ne.symm hb) (mapContainsPairKey_of_find (m := .mk l) h)
    · have : ((a' == a && b' == b)) = false := by simp [ha]
      simp only [List.find?_cons, this] at h
      exact .nextA (Ne.symm ha) (mapContainsPairKey_of_find (m := .mk l) h)

theorem actionInSet_of_any {acts : ActionSchema} {uid₁ : EntityUID} :
    ∀ {xs : List Expr}, (xs.any fun x => match x with
      | .lit (.entityUID uid₂) => acts.toList.any (fun (k, e) => k == uid₁ &&
          (uid₁ == uid₂ || match e.ancestors with | .mk l => l.any (· == uid₂)))
      | _ => false) = true → ActionInSet acts uid₁ xs
  | [], h => by simp at h
  | x :: xs, h => by
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · match x, h with
      | .lit (.entityUID uid₂), h =>
        obtain ⟨⟨k, e⟩, hmem, h⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        have hmc : MapContains k e acts := by cases acts; exact mapContains_of_mem hmem
        refine .here _ _ _ _ ?_
        rcases h with rfl | h
        · exact .refl _ _ _ hmc
        · exact .ancestor _ _ _ _ hmc (setContains_of_any h)
    · exact .there _ _ _ _ (actionInSet_of_any h)

theorem contains_iff {α β : Type} [BEq α] [LawfulBEq α] {m : Map α β} {k : α} :
    m.contains k = true ↔ ∃ v, MapContains k v m := by
  obtain ⟨l⟩ := m
  simp only [Map.contains, Map.find?, Map.toList]
  constructor
  · intro h
    have : (l.find? fun (k', _) => k' == k).isSome := by
      revert h; cases l.find? (fun (k', _) => k' == k) <;> simp
    obtain ⟨⟨k', v⟩, hmem, hk⟩ := List.find?_isSome.mp this
    simp only [beq_iff_eq] at hk; subst hk
    exact ⟨v, mapContains_of_mem hmem⟩
  · rintro ⟨v, hv⟩
    have hmem : (k, v) ∈ l := by
      generalize hm : Map.mk l = m at hv
      induction hv generalizing l with
      | here => cases hm; exact List.mem_cons_self
      | there _ _ _ _ ih => cases hm; exact List.mem_cons_of_mem _ (ih _ rfl)
    have : (l.find? fun (k', _) => k' == k).isSome := List.find?_isSome.mpr ⟨_, hmem, by simp⟩
    revert this; cases l.find? (fun (k', _) => k' == k) <;> simp

@[specimen_check] theorem bothLit_of_test {x₁ x₂ : Expr} :
    bothLitB x₁ x₂ = true → BothLit x₁ x₂ := by
  intro h; unfold bothLitB at h; split at h
  · exact .mk _ _
  · simp at h

theorem bothLit_test {x₁ x₂ : Expr} : BothLit x₁ x₂ →
    bothLitB x₁ x₂ = true := by
  intro hr; cases hr; rfl

@[specimen_check] theorem not_bothLit_of_test {x₁ x₂ : Expr} :
    (!bothLitB x₁ x₂) = true → ¬ BothLit x₁ x₂ := by
  intro h hr; rw [bothLit_test hr] at h; simp at h

@[specimen_check] theorem isActionLitMem_of_test {x₁ x₂ : Expr} {acts : ActionSchema} :
    isActionLitMemB x₁ x₂ acts = true → IsActionLitMem x₁ x₂ acts := by
  intro h; unfold isActionLitMemB at h; split at h
  · obtain ⟨_, hv⟩ := contains_iff.mp h; exact .mk _ _ _ _ hv
  · simp at h

theorem isActionLitMem_test {x₁ x₂ : Expr} {acts : ActionSchema} : IsActionLitMem x₁ x₂ acts →
    isActionLitMemB x₁ x₂ acts = true := by
  intro hr; cases hr with
  | mk _ _ _ _ hv => unfold isActionLitMemB; exact contains_iff.mpr ⟨_, hv⟩

@[specimen_check] theorem not_isActionLitMem_of_test {x₁ x₂ : Expr} {acts : ActionSchema} :
    (!isActionLitMemB x₁ x₂ acts) = true → ¬ IsActionLitMem x₁ x₂ acts := by
  intro h hr; rw [isActionLitMem_test hr] at h; simp at h

@[specimen_check] theorem isActionLitMemSet_of_test {x₁ x₂ : Expr} {acts : ActionSchema} :
    isActionLitMemSetB x₁ x₂ acts = true → IsActionLitMemSet x₁ x₂ acts := by
  intro h; unfold isActionLitMemSetB at h; split at h
  · simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨_, hv⟩ := contains_iff.mp h.1
    refine .mk _ _ _ _ hv fun x hx => ?_
    have := h.2 x hx
    split at this
    · exact ⟨_, rfl⟩
    · simp at this
  · simp at h

theorem isActionLitMemSet_test {x₁ x₂ : Expr} {acts : ActionSchema} : IsActionLitMemSet x₁ x₂ acts →
    isActionLitMemSetB x₁ x₂ acts = true := by
  intro hr; cases hr with
  | mk _ xs _ _ hv hall =>
    unfold isActionLitMemSetB
    rw [Bool.and_eq_true]
    refine ⟨contains_iff.mpr ⟨_, hv⟩, List.all_eq_true.mpr fun x hx => ?_⟩
    obtain ⟨_, rfl⟩ := hall x hx
    rfl

@[specimen_check] theorem not_isActionLitMemSet_of_test {x₁ x₂ : Expr} {acts : ActionSchema} :
    (!isActionLitMemSetB x₁ x₂ acts) = true → ¬ IsActionLitMemSet x₁ x₂ acts := by
  intro h hr; rw [isActionLitMemSet_test hr] at h; simp at h

theorem capAttrMem_any {x : Expr} {a : Attr} {c : Capabilities} (h : CapAttrMem x a c) :
    (c.any fun (x', k') => x' == x && k' == .attr a) = true := by
  induction h <;> simp_all

@[specimen_check] theorem not_capAttrMem_of_not_any {x : Expr} {a : Attr} {c : Capabilities} :
    (!(c.any fun (x', k') => x' == x && k' == .attr a)) = true → ¬ CapAttrMem x a c := by
  intro h hr; simp [capAttrMem_any hr] at h

theorem capTagMem_any {x e : Expr} {c : Capabilities} (h : CapTagMem x e c) :
    (c.any fun (x', k') => x' == x && k' == .tag e) = true := by
  induction h <;> simp_all

@[specimen_check] theorem not_capTagMem_of_not_any {x e : Expr} {c : Capabilities} :
    (!(c.any fun (x', k') => x' == x && k' == .tag e)) = true → ¬ CapTagMem x e c := by
  intro h hr; simp [capTagMem_any hr] at h

theorem setContains_any {α : Type} [BEq α] [LawfulBEq α] {x : α} {s : Data.Set α} (hs : SetContains x s) :
    (match s with | .mk l => l.any (· == x)) = true := by
  induction hs with
  | here => simp
  | there _ _ _ ih => simp only [List.any_cons, ih, Bool.or_true]

@[specimen_check] theorem not_setContains_of_not_any {α : Type} [BEq α] [LawfulBEq α] {x : α} {s : Data.Set α} :
    (!(match s with | .mk l => l.any (· == x))) = true → ¬ SetContains x s := by
  intro h hr
  obtain ⟨l⟩ := s
  have := setContains_any hr
  simp_all

theorem mem_toList_of_mapContains {α β : Type} {k : α} {v : β} {m : Map α β} (hm : MapContains k v m) :
    (k, v) ∈ m.toList := by
  induction hm with
  | here => exact List.mem_cons_self
  | there _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem actionInSet_test_any {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr}
    (h : ActionInSet acts uid₁ xs) : (xs.any fun x => match x with
      | .lit (.entityUID uid₂) => acts.toList.any (fun (k, e) => k == uid₁ &&
          (uid₁ == uid₂ || match e.ancestors with | .mk l => l.any (· == uid₂)))
      | _ => false) = true := by
  induction h with
  | here uid₂ _ hd =>
    simp only [List.any_cons, Bool.or_eq_true]
    left
    cases hd with
    | refl e hm => exact List.any_eq_true.mpr ⟨_, mem_toList_of_mapContains hm, by simp⟩
    | ancestor _ e hm hs =>
      refine List.any_eq_true.mpr ⟨_, mem_toList_of_mapContains hm, ?_⟩
      simp only [beq_self_eq_true, Bool.true_and, Bool.or_eq_true]
      right
      exact setContains_any hs
  | there _ _ _ ih => simp [ih]

theorem not_actionInSet_of_not_any {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr} :
    (!(xs.any fun x => match x with
      | .lit (.entityUID uid₂) => acts.toList.any (fun (k, e) => k == uid₁ &&
          (uid₁ == uid₂ || match e.ancestors with | .mk l => l.any (· == uid₂)))
      | _ => false)) = true → ¬ ActionInSet acts uid₁ xs := by
  intro h hr; simp [actionInSet_test_any hr] at h

@[specimen_check] theorem parserImage_of_test {x : Expr} : parserImageB x = true → ParserImage x :=
  (parserImage_iff x).mpr

@[specimen_check] theorem not_parserImage_of_test {x : Expr} : (!parserImageB x) = true → ¬ ParserImage x := by
  intro h hp; simp [(parserImage_iff x).mp hp] at h

@[specimen_check] theorem actionInSet_of_test {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr} :
    actionInSetB acts uid₁ xs = true → ActionInSet acts uid₁ xs := fun h => actionInSet_of_any h

theorem actionInSet_test {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr}
    (h : ActionInSet acts uid₁ xs) : actionInSetB acts uid₁ xs = true := actionInSet_test_any h

@[specimen_check] theorem not_actionInSet_of_test {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr} :
    (!actionInSetB acts uid₁ xs) = true → ¬ ActionInSet acts uid₁ xs := fun h => not_actionInSet_of_not_any h

@[specimen_check] theorem notFf_of_test {b : BoolType} : (b != .ff) = true → NotFf b := by
  cases b <;> intro h <;> first | (simp at h; done) | constructor

@[specimen_check] theorem boolTypeNeq_of_test {a b : BoolType} : (a != b) = true → BoolTypeNeq a b := by
  cases a <;> cases b <;> intro h <;> first | (simp at h; done) | constructor

@[specimen_check] theorem capMerge_of_test : ∀ {c₁ c₂ c : Capabilities},
    capMergeB c₁ c₂ c = true → CapMerge c₁ c₂ c
  | c₁, c₂, [], h => by
    simp only [capMergeB, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h; exact .nil
  | c₁, c₂, (x, k) :: c, h => by
    simp only [capMergeB, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · match c₁, h with
      | q :: c₁', h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        exact .left _ _ _ _ _ (capMerge_of_test h)
    · match c₂, h with
      | q :: c₂', h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h⟩ := h
        exact .right _ _ _ _ _ (capMerge_of_test h)
    · match c₁, c₂, h with
      | q₁ :: c₁', q₂ :: c₂', h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, rfl⟩, h⟩ := h
        exact .both _ _ _ _ _ (capMerge_of_test h)

/-! ## The generators -/

/-! ### Strict-mode premises -/

@[specimen_check] theorem maybeActionDescendentOf_of_test {acts : ActionSchema}
    {ety₁ ety₂ : EntityType} :
    acts.maybeDescendentOf ety₁ ety₂ = true → MaybeActionDescendentOf acts ety₁ ety₂ :=
  maybeActionDescendentOf_iff.mpr

@[specimen_check] theorem not_maybeActionDescendentOf_of_test {acts : ActionSchema}
    {ety₁ ety₂ : EntityType} :
    (!acts.maybeDescendentOf ety₁ ety₂) = true → ¬ MaybeActionDescendentOf acts ety₁ ety₂ := by
  intro h hr; simp [maybeActionDescendentOf_iff.mp hr] at h

/-- The check decides `DeadOperand`. -/
@[specimen_check] theorem deadOperand_of_ok {decl syn : Bool} {env : TypeEnv} {x : Expr} :
    deadOperandOk decl syn env x = true → DeadOperand decl syn env x := deadOperand_iff.mpr

theorem deadOperand_of_test {decl syn : Bool} {env : TypeEnv} {x : Expr} :
    deadOperandB x = true → DeadOperand decl syn env x := by
  intro h
  match x, h with
  | .lit (.bool _), _ => exact .mk _ _ (.yes _ _ _ _ (.litBool _ _ _)) (.yes _ _ (.lit _))
  | .lit (.int _), _ => exact .mk _ _ (.yes _ _ _ _ (.litInt _ _ _)) (.yes _ _ (.lit _))
  | .lit (.string _), _ => exact .mk _ _ (.yes _ _ _ _ (.litString _ _ _)) (.yes _ _ (.lit _))
  | .var _, _ => exact .mk _ _ (.yes _ _ _ _ (.var _ _ _)) (.yes _ _ (.var _))

theorem insertSortedField_cons_of_sorted {a : Attr} {x : Expr} :
    ∀ {rest : List (Attr × Expr)}, strictSortedB ((a, x) :: rest) = true →
      InsertSortedField (a, x) rest ((a, x) :: rest)
  | [], _ => .nil _ _
  | (b, y) :: rest, h => by
    simp only [strictSortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .here _ _ _ _ _ h.1

theorem sortsTo_self_of_strictSortedB : ∀ {l : List (Attr × Expr)}, strictSortedB l = true →
    SortsTo l l
  | [], _ => .nil
  | [(a, x)], _ => .cons _ _ _ _ .nil (.nil _ _)
  | (a, x) :: (b, y) :: rest, h => by
    have h' := h
    simp only [strictSortedB, Bool.and_eq_true] at h'
    exact .cons _ _ _ _ (sortsTo_self_of_strictSortedB h'.2) (insertSortedField_cons_of_sorted h)

theorem insertSortedField_of_insertStrict {ax : Attr × Expr} :
    ∀ {l l' : List (Attr × Expr)}, insertStrict ax l = some l' → InsertSortedField ax l l'
  | [], l', h => by
    obtain ⟨a, x⟩ := ax
    simp only [insertStrict, Option.some.injEq] at h; subst h; exact .nil _ _
  | (a', x') :: rest, l', h => by
    obtain ⟨a, x⟩ := ax
    simp only [insertStrict] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact .here _ _ _ _ _ ‹_›
    · split at h
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .there _ _ _ _ _ _ ‹_› (insertSortedField_of_insertStrict hr)
      · simp at h

theorem sortsTo_of_sortStrict : ∀ {axs l : List (Attr × Expr)}, sortStrict axs = some l →
    SortsTo axs l
  | [], l, h => by simp only [sortStrict, Option.some.injEq] at h; subst h; exact .nil
  | ax :: axs, l, h => by
    simp only [sortStrict] at h
    obtain ⟨r, hr, hi⟩ := Option.bind_eq_some_iff.mp h
    exact .cons _ _ _ _ (sortsTo_of_sortStrict hr) (insertSortedField_of_insertStrict hi)

@[specimen_check] theorem sortsTo_of_test {axs axs' : List (Attr × Expr)} :
    sortsToB axs axs' = true → SortsTo axs axs' := by
  unfold sortsToB
  split
  · next l hl => intro h; simp only [beq_iff_eq] at h; subst h; exact sortsTo_of_sortStrict hl
  · intro h; simp at h

section Generators
open Specimen.Correctness Basalt

theorem mapContains_mid {α β : Type} {k : α} {v : β} :
    ∀ (pre post : List (α × β)), MapContains k v (.mk (pre ++ (k, v) :: post))
  | [], _ => .here _ _ _
  | (_, _) :: pre, post => .there _ _ _ _ _ (mapContains_mid pre post)

theorem setContains_mid {α : Type} {x : α} :
    ∀ (pre post : List α), SetContains x (.mk (pre ++ x :: post))
  | [], _ => .here _ _
  | _ :: pre, post => .there _ _ _ (setContains_mid pre post)

theorem mapNotContainsKey_filter {α β : Type} [DecidableEq α] {k : α} :
    ∀ (l : List (α × β)), MapNotContainsKey k (.mk (l.filter fun p => p.1 ≠ k))
  | [] => .empty _
  | (k', v') :: l => by
    by_cases h : k' = k
    · subst h; simpa using mapNotContainsKey_filter (k := k') l
    · rw [List.filter_cons_of_pos (by simpa using h)]
      exact .skip _ _ _ _ (Ne.symm h) (mapNotContainsKey_filter l)

theorem mapNotContainsKey_of_not_any {α β : Type} [DecidableEq α] {k : α} :
    ∀ {l : List (α × β)}, ¬ (l.any fun p => decide (p.1 = k)) = true → MapNotContainsKey k (.mk l)
  | [], _ => .empty _
  | (k', v') :: l, h => by
    simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq, not_or] at h
    exact .skip _ _ _ _ (Ne.symm h.1) (mapNotContainsKey_of_not_any (by simpa using h.2))

theorem attr_lt_append (b : Attr) (n : Nat) (hn : 1 ≤ n) :
    b < b ++ String.ofList (List.replicate n 'a') := by
  show b.toList < (b ++ String.ofList (List.replicate n 'a')).toList
  rw [String.toList_append, String.toList_ofList]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  generalize b.toList = l
  induction l with
  | nil => exact List.nil_lt_cons _ _
  | cons x xs ih => simp only [List.cons_append]; exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

@[specimen_sound] theorem attr_above_gen (b : Attr) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun a => b < a) (G := SGen) s l) (fun a => b < a) := by
  show succObs.spec (frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail)] : SGen Attr) _
  walk
  · exact attr_lt_append b _ (‹1 ≤ _ ∧ _›).1
  · simp_all

@[specimen_sound] theorem attr_above_enum (b : Attr) (s l : Nat) :
    succObs.spec (EnumFor.enum (P := fun a => b < a) (G := SGen) s l) (fun a => b < a) := by
  show succObs.spec (frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail)] : SGen Attr) _
  walk
  · exact attr_lt_append b _ (‹1 ≤ _ ∧ _›).1
  · simp_all

@[specimen_sound] theorem mapContains_gen {α β : Type} [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β]
    {k : α} {v : β} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun m => MapContains k v m) (G := SGen) s l)
      (fun m => MapContains k v m) := by
  show succObs.spec (do
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
    return Map.mk (← insertSomewhere (k, v) rest) : SGen (Map α β)) _
  simp only [insertSomewhere]
  walk
  exact mapContains_mid _ _

@[specimen_sound] theorem mapContains_pair_gen {α β : Type} [Basalt.ArbitrarySized α]
    [Basalt.ArbitrarySized β] {k : α} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (p : β × Map α β) => MapContains k p.1 p.2) (G := SGen) s l)
      (fun p => MapContains k p.1 p.2) := by
  show succObs.spec (do
    let v : β ← Basalt.ArbitrarySized.arbitrarySized l
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
    return (v, Map.mk (← insertSomewhere (k, v) rest)) : SGen (β × Map α β)) _
  simp only [insertSomewhere]
  walk
  exact mapContains_mid _ _

@[specimen_sound] theorem mapNotContainsKey_gen {α β : Type} [Basalt.ArbitrarySized α]
    [Basalt.ArbitrarySized β] [DecidableEq α] {k : α} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (m : Map α β) => MapNotContainsKey k m) (G := SGen) s l)
      (fun m => MapNotContainsKey k m) := by
  show succObs.spec (do
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
    return Map.mk (rest.filter (fun p => p.1 ≠ k)) : SGen (Map α β)) _
  walk
  exact mapNotContainsKey_filter _

@[specimen_sound] theorem mapNotContainsKey_pair_gen {α β : Type} [Basalt.ArbitrarySized α]
    [Basalt.ArbitrarySized β] [DecidableEq α] (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (p : α × Map α β) => MapNotContainsKey p.1 p.2) (G := SGen) s l)
      (fun p => MapNotContainsKey p.1 p.2) := by
  show succObs.spec (do
    let k : α ← Basalt.ArbitrarySized.arbitrarySized l
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized l
    return (k, Map.mk (rest.filter (fun p => p.1 ≠ k))) : SGen (α × Map α β)) _
  walk
  exact mapNotContainsKey_filter _

@[specimen_sound] theorem mapNotContainsKey_key_gen {α β : Type} [Basalt.ArbitrarySized α] [DecidableEq α]
    {m : Map α β} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun k => MapNotContainsKey k m) (G := SGen) s l)
      (fun k => MapNotContainsKey k m) := by
  show succObs.spec (do
    let k : α ← Basalt.ArbitrarySized.arbitrarySized l
    if m.toList.any (fun p => decide (p.1 = k)) then Specimen.Fail.fail else return k : SGen α) _
  walk
  obtain ⟨l⟩ := m
  exact mapNotContainsKey_of_not_any ‹_›

@[specimen_sound] theorem setContains_gen {α : Type} [Basalt.ArbitrarySized α] (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (p : α × Data.Set α) => SetContains p.1 p.2) (G := SGen) s l)
      (fun p => SetContains p.1 p.2) := by
  show succObs.spec (do
    let x : α ← Basalt.ArbitrarySized.arbitrarySized l
    let rest : List α ← Basalt.ArbitrarySized.arbitrarySized l
    return (x, Data.Set.mk (← insertSomewhere x rest)) : SGen (α × Data.Set α)) _
  simp only [insertSomewhere]
  walk
  exact setContains_mid _ _

/-! Each extension-literal generator keeps the parser as its last check. Their bodies are long, so
the walks get more heartbeats. -/

set_option maxHeartbeats 2000000 in
@[specimen_sound] theorem validDecimal_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := ValidDecimal) (G := SGen) s l) ValidDecimal := by
  simp only [BacktrackGenFor.gen, orParsing]
  walk
  all_goals first | exact .mk _ _ ‹_› | exact validDecimal_of_isSome ‹_›

set_option maxHeartbeats 2000000 in
@[specimen_sound] theorem validIP_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := ValidIP) (G := SGen) s l) ValidIP := by
  simp only [BacktrackGenFor.gen, orParsing]
  walk
  all_goals first | exact .mk _ _ ‹_› | exact validIP_of_isSome ‹_›

theorem datetimeCandidate_any : succObs.spec (datetimeCandidate : SGen String) (fun _ => True) :=
  fun _ _ => trivial

@[specimen_sound] theorem validDatetime_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := ValidDatetime) (G := SGen) s l) ValidDatetime := by
  simp only [BacktrackGenFor.gen, orParsing]
  walk [datetimeCandidate_any]
  all_goals first | exact .mk _ _ ‹_› | exact validDatetime_of_isSome ‹_›

set_option maxHeartbeats 2000000 in
@[specimen_sound] theorem validDuration_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := ValidDuration) (G := SGen) s l) ValidDuration := by
  simp only [BacktrackGenFor.gen, orParsing]
  walk
  all_goals first | exact .mk _ _ ‹_› | exact validDuration_of_isSome ‹_›

@[specimen_sound] theorem maybeActionDescendentOf_gen {acts : ActionSchema} {ety₁ : EntityType}
    (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun ety₂ => MaybeActionDescendentOf acts ety₁ ety₂)
      (G := SGen) s l) (fun ety₂ => MaybeActionDescendentOf acts ety₁ ety₂) := by
  show succObs.spec (do
    let cands := maybeActionAncestorTypes acts ety₁
    let i ← chooseNat 0 (cands.length - 1)
    let t := cands.getD i default
    if acts.maybeDescendentOf ety₁ t then return t else Specimen.Fail.fail : SGen EntityType) _
  walk
  exact maybeActionDescendentOf_of_test ‹_›

@[specimen_sound] theorem deadOperand_gen {decl syn : Bool} {env : TypeEnv} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun x => DeadOperand decl syn env x) (G := SGen) s l)
      (fun x => DeadOperand decl syn env x) := by
  simp only [BacktrackGenFor.gen]
  walk
  all_goals first | exact deadOperand_of_test ‹_› | exact deadOperand_of_ok ‹_›

@[specimen_sound] theorem isActionLitMemSet_gen {acts : ActionSchema} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) (G := SGen) s l)
      (fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) := by
  simp only [BacktrackGenFor.gen]
  walk
  exact isActionLitMemSet_of_test ‹_›

/-- (Its postcondition by projections, not a `match` on the pair: the hypothesis it leaves is then
about `IsActionLitMemSet` itself, which `ctor_leaf` finds.) -/
@[specimen_sound] theorem isActionLitMemSet_enum {acts : ActionSchema} (s l : Nat) :
    succObs.spec (EnumFor.enum (P := fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) (G := SGen) s l)
      (fun p => IsActionLitMemSet p.1 p.2 acts) := by
  simp only [EnumFor.enum]
  walk
  exact isActionLitMemSet_of_test ‹_›

@[specimen_sound] theorem sortsTo_gen {axs' : List (Attr × Expr)} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun axs => SortsTo axs axs') (G := SGen) s l)
      (fun axs => SortsTo axs axs') := by
  simp only [BacktrackGenFor.gen]
  walk
  all_goals first | exact sortsTo_self_of_strictSortedB ‹_› | exact sortsTo_of_test ‹_›

@[specimen_sound] theorem sortsTo_sorted_gen {axs : List (Attr × Expr)} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun axs' => SortsTo axs axs') (G := SGen) s l)
      (fun axs' => SortsTo axs axs') := by
  show succObs.spec (match sortStrict axs with
    | some l => return l
    | none => Specimen.Fail.fail : SGen (List (Attr × Expr))) _
  split
  · walk
    exact sortsTo_of_sortStrict ‹_›
  · walk

@[specimen_sound] theorem attr_below_enum (b : Attr) (s l : Nat) :
    succObs.spec (EnumFor.enum (P := fun a => a < b) (G := SGen) s l) (fun a => a < b) := by
  show succObs.spec (do
    let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
    if decide (a < b) then return a else Specimen.Fail.fail : SGen Attr) _
  walk
  exact of_decide_eq_true ‹_›

/-! The hand-written enumerators' searches find only what they produce (`SearchFinds`), for the
completeness side of the derived checkers that search through them. -/

@[gen_rule] theorem attr_above_search (b : Attr) (s l : Nat) :
    SearchFinds (EnumFor.enum (P := fun a => b < a) (G := Specimen.Search) s l)
      (EnumFor.enum (P := fun a => b < a) (G := SGen) s l) := by
  show SearchFinds (frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail)] : Specimen.Search Attr) (frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
      if decide (b < a) then return a else Specimen.Fail.fail)] : SGen Attr)
  walk

@[gen_rule] theorem attr_below_search (b : Attr) (s l : Nat) :
    SearchFinds (EnumFor.enum (P := fun a => a < b) (G := Specimen.Search) s l)
      (EnumFor.enum (P := fun a => a < b) (G := SGen) s l) := by
  show SearchFinds (do
    let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
    if decide (a < b) then return a else Specimen.Fail.fail : Specimen.Search Attr) (do
    let a : Attr ← Basalt.ArbitrarySized.arbitrarySized l
    if decide (a < b) then return a else Specimen.Fail.fail : SGen Attr)
  walk

end Generators


/-! ## Unconstrained draws

What a derived enumerator's search for a premise's witness needs of the types it draws freely: each
instance's search finds only what it produces (`ArbitrarySizedSearch`), by `walk` over its body. -/

section Draws
open Specimen.Correctness

instance : ArbitrarySizedSearch BoolType := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch ExtType := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Name := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch EntityType := ⟨by arbitrary_search⟩
/-- `anyCedarType`'s search finds what it draws: by induction on the depth. A rule of `walk`, which
cannot unfold the recursion itself. -/
@[gen_rule] theorem anyCedarType_searchFinds : ∀ n,
    SearchFinds (anyCedarType n : Specimen.Search CedarType) (anyCedarType n : SGen CedarType)
  | 0 => by unfold anyCedarType; walk
  | n + 1 => by unfold anyCedarType; walk [anyCedarType_searchFinds n]

instance : ArbitrarySizedSearch CedarType :=
  ⟨by intro n; unfold_arbitrary; walk [anyCedarType_searchFinds n]⟩
instance {α : Type} [Basalt.ArbitrarySized α] [ArbitrarySizedSearch α] : ArbitrarySizedSearch (Qualified α) :=
  ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch EntityUID := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Int64 := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Prim := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Var := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch ExtFun := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch PatElem := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch UnaryOp := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch BinaryOp := ⟨by arbitrary_search⟩
instance : ArbitrarySizedSearch Effect := ⟨by arbitrary_search⟩
/-- `anyExprB`'s search finds what it draws: by induction on the fuel, for every budget. A rule of
`walk`, which cannot unfold the recursion itself. -/
@[gen_rule] theorem anyExprB_searchFinds : ∀ f b,
    SearchFinds (anyExprB f b : Specimen.Search Expr) (anyExprB f b : SGen Expr)
  | 0, _ => by unfold anyExprB; walk
  | _ + 1, 0 => by unfold anyExprB; walk
  | f + 1, _ + 1 => by unfold anyExprB; walk [anyExprB_searchFinds f]

@[gen_rule] theorem anyExpr_searchFinds (n : Nat) :
    SearchFinds (anyExpr n : Specimen.Search Expr) (anyExpr n : SGen Expr) := by
  unfold anyExpr; exact anyExprB_searchFinds n n

instance : ArbitrarySizedSearch Expr := ⟨by intro n; unfold_arbitrary; walk [anyExpr_searchFinds n]⟩
instance {α β : Type} [LT α] [DecidableLT α] [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β]
    [ArbitrarySizedSearch α] [ArbitrarySizedSearch β] : ArbitrarySizedSearch (Map α β) := ⟨by arbitrary_search⟩

end Draws

section ActionSets
open Specimen.Correctness

@[gen_rule] theorem isActionLitMemSet_search {acts : ActionSchema} (s l : Nat) :
    SearchFinds (EnumFor.enum (P := fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) (G := Specimen.Search) s l)
      (EnumFor.enum (P := fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) (G := SGen) s l) := by
  simp only [EnumFor.enum]
  walk

/-- A checker's search with the hand-written enumerator: what it accepts is a witness. (A derived
enumerator's is its worker's `searchSound`.) -/
@[specimen_sound] theorem isActionLitMemSet_searchSound {acts : ActionSchema} (s l : Nat)
    (k : Expr × Expr → Except Plausible.GenError Bool)
    (h : Specimen.CheckerSearch.search (P := fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) s l k = .ok true) :
    ∃ a : Expr × Expr, IsActionLitMemSet a.1 a.2 acts ∧ k a = .ok true := by
  exact search_accepts (isActionLitMemSet_search s l) (isActionLitMemSet_enum s l) h

end ActionSets

end Cedar.Validation.Relational


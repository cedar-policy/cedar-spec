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

import CedarGen.Relational.SchemaGenF
import Specimen.Correctness.SoundOf
import Specimen.Correctness.CompleteOf

/-! # The producers the flagged schema generator delegates to, and their laws

Names (an identifier with `idents`), action types (`ns::Action` with `idents`, not an entity type
with `wfActs`), the transitive closures (a function of the drawn hierarchy, checked), a uniform
pick of an action UID, a rank, and an unconstrained action UID; each with its soundness
(`@[specimen_sound]`) and completeness (`BacktrackGenForComplete`/`ArbitrarySizedComplete`). -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Delegated producers -/

/-- The first characters of an identifier. -/
def identStarts : List Char := "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toList

/-- The other characters of an identifier. -/
def identChars : List Char := "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".toList

/-- An identifier-shaped string of at most `n + 1` characters (possibly reserved). -/
def identString {G : Type → Type} [Gen G] (n : Nat) : G String := do
  let c ← elements identStarts (by simp [identStarts])
  let k ← chooseNat 0 n
  let cs ← vectorOf k (elements identChars (by simp [identChars]))
  pure (String.ofList (c :: cs))

/-- A candidate name: mostly from the pool, sometimes an identifier-shaped string, sometimes any. -/
def nameCandidate {G : Type → Type} [Gen G] [Specimen.Pick G] (s : Nat) : G EntityType :=
  frequency [(6, fun _ => do pure ⟨← elements namePool (by simp [namePool]), []⟩),
             (3, fun _ => do pure ⟨← identString s, []⟩),
             (1, fun _ => Basalt.ArbitrarySized.arbitrarySized s)]

/-- A name, made an identifier if `i` asks for one. -/
def nameFix (i : Bool) (x : EntityType) : EntityType :=
  if i && !isIdentName x then ⟨"User", []⟩ else x

/-- `NameIf i`: the candidate, replaced by a pool name if it must be an identifier and is not. -/
instance {i : Bool} : BacktrackGenFor EntityType (fun x => NameIf i x) where
  gen s _ := do
    let x ← nameCandidate s
    pure (nameFix i x)

/-- A candidate action type: mostly `Action`, sometimes namespaced, sometimes any. -/
def actTyCandidate {G : Type → Type} [Gen G] [Specimen.Pick G] (s : Nat) : G EntityType :=
  frequency [(8, fun _ => pure ⟨"Action", []⟩),
             (1, fun _ => do pure ⟨"Action", [← elements namePool (by simp [namePool])]⟩),
             (1, fun _ => Basalt.ArbitrarySized.arbitrarySized s)]

/-- An action type, made `Action` if `i` asks for one. -/
def actTyFix (i : Bool) (x : EntityType) : EntityType :=
  if i && !isActionType x then ⟨"Action", []⟩ else x

/-- `ActTyOK a i ks`: the candidate, fixed, and rejected if it must not be an entity type and is. -/
instance {a i : Bool} {ks : List EntityType} : BacktrackGenFor EntityType (fun x => ActTyOK a i ks x) where
  gen s _ := do
    let x ← actTyCandidate s
    if a && decide (actTyFix i x ∈ ks) then Specimen.Fail.fail else pure (actTyFix i x)

/-- One closure, checked: `s` in order, at the end otherwise. -/
def closeTry {α β : Type} [DecidableEq α] [LT α] [DecidableLT α] {G : Type → Type} [Gen G]
    [Specimen.Fail G] (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool)
    (s : Bool) (g : List (α × β)) : G (List (α × β)) :=
  if ok (closeAll get set s g) then pure (closeAll get set s g) else Specimen.Fail.fail

/-- One closure, checked, or the hierarchy as drawn if the check fails. -/
def closeOr {α β : Type} [DecidableEq α] [LT α] [DecidableLT α] {G : Type → Type} [Gen G]
    (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool)
    (s : Bool) (g : List (α × β)) : G (List (α × β)) :=
  if ok (closeAll get set s g) then pure (closeAll get set s g) else pure g

/-- The closure producer: closed (and checked so) with `c`, in order or (without `m`) at the end;
mostly as drawn without `c` (and as drawn when a closure fails its check). -/
def closeGen {α β : Type} [DecidableEq α] [LT α] [DecidableLT α] {G : Type → Type} [Gen G]
    [Specimen.Fail G] (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool)
    (c m : Bool) (g : List (α × β)) : G (List (α × β)) :=
  match c, m with
  | true, true => closeTry get set ok true g
  | true, false => frequency [(1, fun _ => closeTry get set ok true g),
                              (1, fun _ => closeTry get set ok false g)]
  | false, true => frequency [(8, fun _ => pure g), (1, fun _ => closeOr get set ok true g)]
  | false, false => frequency [(8, fun _ => pure g), (1, fun _ => closeOr get set ok true g),
                               (1, fun _ => closeOr get set ok false g)]

/-- `CloseEnts c m g`. -/
instance {c m : Bool} {g : List (EntityType × EntitySchemaEntry)} :
    BacktrackGenFor (List (EntityType × EntitySchemaEntry)) (fun g' => CloseEnts c m g g') where
  gen _ _ := closeGen entAncs entWith (closedB entAncs) c m g

/-- `CloseActs a m g`. -/
instance {a m : Bool} {g : List (EntityUID × ActionSchemaEntry)} :
    BacktrackGenFor (List (EntityUID × ActionSchemaEntry)) (fun g' => CloseActs a m g g') where
  gen _ _ := closeGen actAncs actWith (fun g => closedB actAncs g && irreflB actAncs g) a m g

/-- `ShadowIf i ks u`: the action UIDs as drawn, rejected at `i` if a name shadows another. -/
instance {i : Bool} {ks : List EntityType} {u : List EntityUID} :
    BacktrackGenFor (List EntityUID) (fun u' => ShadowIf i ks u u') where
  gen _ _ := if i && !noShadowB ks u then Specimen.Fail.fail else pure u

/-- `DefinedUID us`, uniformly. -/
instance {us : List EntityUID} : BacktrackGenFor EntityUID (fun u => DefinedUID us u) where
  gen _ _ := do
    if us.isEmpty then Specimen.Fail.fail else
    let i ← chooseNat 0 (us.length - 1)
    match us[i]? with
    | some u => pure u
    | none => Specimen.Fail.fail

/-- An action UID: a name and an eid. -/
scoped instance (priority := high) schemaUID : Basalt.ArbitrarySized EntityUID where
  arbitrarySized n := do
    let ty : EntityType ← Basalt.ArbitrarySized.arbitrarySized n
    let eid : String ← Basalt.ArbitrarySized.arbitrarySized n
    pure ⟨ty, eid⟩

/-- `RankOf`: a rank up to the size. -/
instance : BacktrackGenFor Nat (fun k => RankOf k) where
  gen s _ := chooseNat 0 s


/-! ## Their laws

Soundness (`@[specimen_sound]`) and completeness (`BacktrackGenForComplete`) of the hand-written
producers, for the proofs `specimen.emitSound` and `specimen.emitComplete` run on the derived
generator. -/

section Laws
open Specimen.Correctness Basalt

theorem nameIf_nameFix (i : Bool) (x : EntityType) : NameIf i (nameFix i x) := by
  unfold nameFix
  cases i
  · exact .any _
  · by_cases h : isIdentName x = true
    · simp only [h, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact .ident _ _ h
    · simp only [h, Bool.not_false, Bool.and_self, ↓reduceIte]
      exact .ident _ _ (by decide)

theorem notInET_of_not_mem {x : EntityType} : ∀ {ks : List EntityType}, x ∉ ks → NotInET x ks
  | [], _ => .nil _
  | k :: ks, h => .cons _ _ _ (fun e => h (e ▸ List.mem_cons_self))
      (notInET_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm)))

theorem not_mem_of_notInET {x : EntityType} {ks : List EntityType} (h : NotInET x ks) : x ∉ ks := by
  induction h with
  | nil => simp
  | cons _ _ hne _ ih => simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩

theorem actTyOK_actTyFix (a i : Bool) (ks : List EntityType) (x : EntityType)
    (h : ¬ (a && decide (actTyFix i x ∈ ks)) = true) : ActTyOK a i ks (actTyFix i x) := by
  refine .mk _ _ _ _ ?_ ?_
  · unfold actTyFix
    cases i
    · exact .any _
    · by_cases hx : isActionType x = true
      · simp only [hx, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact .action _ _ hx
      · simp only [hx, Bool.not_false, Bool.and_self, ↓reduceIte]
        exact .action _ _ (by decide)
  · cases a
    · exact .lax _ _
    · exact .strict _ _ _ (notInET_of_not_mem (by simpa using h))

@[specimen_sound]
theorem nameIf_gen (i : Bool) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun x => NameIf i x) (G := SGen) s l) (NameIf i) := by
  show succObs.spec (do
    let x ← nameCandidate s
    pure (nameFix i x) : SGen EntityType) _
  walk <;> exact nameIf_nameFix _ _

@[specimen_sound]
theorem actTyOK_gen (a i : Bool) (ks : List EntityType) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun x => ActTyOK a i ks x) (G := SGen) s l)
      (ActTyOK a i ks) := by
  show succObs.spec (do
    let x ← actTyCandidate s
    if a && decide (actTyFix i x ∈ ks) then Specimen.Fail.fail else pure (actTyFix i x) :
      SGen EntityType) _
  walk <;> exact actTyOK_actTyFix _ _ _ _ ‹_›

@[specimen_sound]
theorem closeEnts_gen (c m : Bool) (g : List (EntityType × EntitySchemaEntry)) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun g' => CloseEnts c m g g') (G := SGen) s l)
      (CloseEnts c m g) := by
  show succObs.spec (closeGen entAncs entWith (closedB entAncs) c m g : SGen _) _
  unfold closeGen closeTry closeOr
  cases c <;> cases m <;> walk <;>
    first
    | exact .keep _ _
    | (apply CloseEnts.closeS; assumption)
    | (apply CloseEnts.closeA; assumption)

@[specimen_sound]
theorem closeActs_gen (a m : Bool) (g : List (EntityUID × ActionSchemaEntry)) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun g' => CloseActs a m g g') (G := SGen) s l)
      (CloseActs a m g) := by
  show succObs.spec (closeGen actAncs actWith (fun g => closedB actAncs g && irreflB actAncs g)
    a m g : SGen _) _
  unfold closeGen closeTry closeOr
  cases a <;> cases m <;> walk <;>
    first
    | exact .keep _ _
    | (apply CloseActs.closeS <;> simp_all)
    | (apply CloseActs.closeA <;> simp_all)

theorem definedUID_of_mem {us : List EntityUID} {x : EntityUID} (h : x ∈ us) : DefinedUID us x := by
  induction us with
  | nil => cases h
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy; exact .here _ _
    · exact .there _ _ _ hxy (ih ((List.mem_cons.mp h).resolve_left hxy))

theorem mem_of_definedUID {us : List EntityUID} {x : EntityUID} (h : DefinedUID us x) : x ∈ us := by
  induction h with
  | here => exact List.mem_cons_self
  | there _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

@[specimen_sound]
theorem shadowIf_gen (i : Bool) (ks : List EntityType) (u : List EntityUID) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun u' => ShadowIf i ks u u') (G := SGen) s l)
      (ShadowIf i ks u) := by
  show succObs.spec (if i && !noShadowB ks u then Specimen.Fail.fail else pure u :
    SGen (List EntityUID)) _
  cases i
  · walk; exact .lax _ _
  · walk; next h => exact .strict _ _ _ (by simpa using h)

@[specimen_sound]
theorem definedUID_gen (us : List EntityUID) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun u => DefinedUID us u) (G := SGen) s l)
      (DefinedUID us) := by
  show succObs.spec (do
    if us.isEmpty then Specimen.Fail.fail else
    let i ← chooseNat 0 (us.length - 1)
    match us[i]? with
    | some u => pure u
    | none => Specimen.Fail.fail : SGen EntityUID) _
  walk
  exact definedUID_of_mem (List.mem_of_getElem? ‹_›)

@[specimen_sound]
theorem rankOf_gen (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun k => RankOf k) (G := SGen) s l) RankOf := by
  show succObs.spec (chooseNat 0 s : SGen Nat) _
  walk
  exact .mk _

/-- The arbitrary branch of a candidate, then kept: every value it may keep is produced. -/
theorem produces_nameCandidate (x : EntityType) :
    ∃ n, ∀ s, n ≤ s → Produces (nameCandidate s : SGen EntityType) x := by
  obtain ⟨n, hn⟩ := ArbitrarySizedComplete.complete (α := Cedar.Spec.Name) x
  exact ⟨n, fun s hs => produces_of_reach ((reach_frequency _).mpr ⟨_,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Nat.succ_pos _,
    reach_of_produces (hn s hs)⟩)⟩

theorem produces_actTyCandidate (x : EntityType) :
    ∃ n, ∀ s, n ≤ s → Produces (actTyCandidate s : SGen EntityType) x := by
  obtain ⟨n, hn⟩ := ArbitrarySizedComplete.complete (α := Cedar.Spec.Name) x
  exact ⟨n, fun s hs => produces_of_reach ((reach_frequency _).mpr ⟨_,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Nat.succ_pos _,
    reach_of_produces (hn s hs)⟩)⟩

instance (i : Bool) : BacktrackGenForComplete EntityType (fun x => NameIf i x) where
  complete x h := by
    obtain ⟨n, hn⟩ := produces_nameCandidate x
    refine ⟨n, fun s l hs _ => ?_⟩
    show Produces (do
      let x ← nameCandidate s
      pure (nameFix i x) : SGen EntityType) x
    refine produces_bind_of (hn s hs) (produces_pure_iff.mpr ?_)
    unfold nameFix
    cases h with
    | ident _ _ hx => simp [hx]
    | any => simp

instance (a i : Bool) (ks : List EntityType) :
    BacktrackGenForComplete EntityType (fun x => ActTyOK a i ks x) where
  complete x h := by
    obtain ⟨n, hn⟩ := produces_actTyCandidate x
    refine ⟨n, fun s l hs _ => ?_⟩
    show Produces (do
      let x ← actTyCandidate s
      if a && decide (actTyFix i x ∈ ks) then Specimen.Fail.fail else pure (actTyFix i x) :
        SGen EntityType) x
    obtain ⟨hty, hnot⟩ : ActTyIf i x ∧ NotInIf a x ks := by cases h; exact ⟨‹_›, ‹_›⟩
    have hfix : actTyFix i x = x := by
      unfold actTyFix
      cases hty with
      | action _ _ hx => simp [hx]
      | any => simp
    refine produces_bind_of (hn s hs) ?_
    rw [hfix]
    have hc : (a && decide (x ∈ ks)) = false := by
      cases hnot with
      | strict _ _ _ h => simp [not_mem_of_notInET h]
      | lax => simp
    rw [hc]
    exact produces_pure_iff.mpr rfl

instance (us : List EntityUID) : BacktrackGenForComplete EntityUID (fun u => DefinedUID us u) where
  complete u h := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (mem_of_definedUID h)
    have hlt : i < us.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨0, fun s l _ _ => ?_⟩
    show Produces (do
      if us.isEmpty then Specimen.Fail.fail else
      let i ← chooseNat 0 (us.length - 1)
      match us[i]? with
      | some u => pure u
      | none => Specimen.Fail.fail : SGen EntityUID) u
    have hne : us.isEmpty = false := by cases us <;> simp_all
    rw [hne]
    refine produces_bind_of (produces_chooseNat (k := i) _ (Nat.zero_le _) (by omega)) ?_
    simp only [hi]
    exact produces_pure_iff.mpr rfl

theorem produces_closeTry {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool) (s : Bool)
    (g : List (α × β)) (h : ok (closeAll get set s g) = true) :
    Produces (closeTry get set ok s g : SGen _) (closeAll get set s g) := by
  unfold closeTry
  rw [if_pos h]; exact produces_pure_iff.mpr rfl

theorem produces_closeOr {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool) (s : Bool)
    (g : List (α × β)) (h : ok (closeAll get set s g) = true) :
    Produces (closeOr get set ok s g : SGen _) (closeAll get set s g) := by
  unfold closeOr
  rw [if_pos h]; exact produces_pure_iff.mpr rfl

theorem produces_closeGen_keep {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool) (m : Bool)
    (g : List (α × β)) : Produces (closeGen get set ok false m g : SGen _) g := by
  unfold closeGen
  cases m <;>
  exact produces_of_reach ((reach_frequency _).mpr ⟨_, List.mem_cons_self, by simp,
    reach_of_produces (produces_pure_iff.mpr rfl)⟩)

theorem produces_closeGen_S {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool) (c m : Bool)
    (g : List (α × β)) (h : ok (closeAll get set true g) = true) :
    Produces (closeGen get set ok c m g : SGen _) (closeAll get set true g) := by
  have hb := produces_closeTry get set ok true g h
  have hb' := produces_closeOr get set ok true g h
  unfold closeGen
  cases c <;> cases m
  · exact produces_of_reach ((reach_frequency _).mpr ⟨_,
      List.mem_cons_of_mem _ List.mem_cons_self, by simp, reach_of_produces hb'⟩)
  · exact produces_of_reach ((reach_frequency _).mpr ⟨_,
      List.mem_cons_of_mem _ List.mem_cons_self, by simp, reach_of_produces hb'⟩)
  · exact produces_of_reach ((reach_frequency _).mpr ⟨_, List.mem_cons_self, by simp,
      reach_of_produces hb⟩)
  · exact hb

theorem produces_closeGen_A {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    (get : β → List α) (set : β → List α → β) (ok : List (α × β) → Bool) (c : Bool)
    (g : List (α × β)) (h : ok (closeAll get set false g) = true) :
    Produces (closeGen get set ok c false g : SGen _) (closeAll get set false g) := by
  have hb := produces_closeTry get set ok false g h
  have hb' := produces_closeOr get set ok false g h
  unfold closeGen
  cases c
  · exact produces_of_reach ((reach_frequency _).mpr ⟨_,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by simp,
      reach_of_produces hb'⟩)
  · exact produces_of_reach ((reach_frequency _).mpr ⟨_,
      List.mem_cons_of_mem _ List.mem_cons_self, by simp, reach_of_produces hb⟩)

instance (c m : Bool) (g : List (EntityType × EntitySchemaEntry)) :
    BacktrackGenForComplete (List (EntityType × EntitySchemaEntry)) (fun g' => CloseEnts c m g g') where
  complete g' h := ⟨0, fun s l _ _ => by
    show Produces (closeGen entAncs entWith (closedB entAncs) c m g : SGen _) g'
    cases h with
    | keep => exact produces_closeGen_keep entAncs entWith (closedB entAncs) m g
    | closeS _ _ _ h => exact produces_closeGen_S entAncs entWith (closedB entAncs) c m g h
    | closeA _ _ h => exact produces_closeGen_A entAncs entWith (closedB entAncs) c g h⟩

instance (a m : Bool) (g : List (EntityUID × ActionSchemaEntry)) :
    BacktrackGenForComplete (List (EntityUID × ActionSchemaEntry)) (fun g' => CloseActs a m g g') where
  complete g' h := ⟨0, fun s l _ _ => by
    show Produces (closeGen actAncs actWith (fun g => closedB actAncs g && irreflB actAncs g)
      a m g : SGen _) g'
    cases h with
    | keep => exact produces_closeGen_keep actAncs actWith _ m g
    | closeS _ _ _ h₁ h₂ =>
      exact produces_closeGen_S actAncs actWith (fun g => closedB actAncs g && irreflB actAncs g)
        a m g (by simp [h₁, h₂])
    | closeA _ _ h₁ h₂ =>
      exact produces_closeGen_A actAncs actWith (fun g => closedB actAncs g && irreflB actAncs g)
        a g (by simp [h₁, h₂])⟩

instance (i : Bool) (ks : List EntityType) (u : List EntityUID) :
    BacktrackGenForComplete (List EntityUID) (fun u' => ShadowIf i ks u u') where
  complete u' h := ⟨0, fun s l _ _ => by
    show Produces (if i && !noShadowB ks u then Specimen.Fail.fail else pure u :
      SGen (List EntityUID)) u'
    cases h with
    | strict _ _ _ h => simp only [h, Bool.not_true, Bool.and_false]; exact produces_pure_iff.mpr rfl
    | lax => exact produces_pure_iff.mpr rfl⟩

instance : BacktrackGenForComplete Nat (fun k => RankOf k) where
  complete k _ := ⟨k, fun s l hs _ => by
    show Produces (chooseNat 0 s : SGen Nat) k
    exact produces_chooseNat _ (Nat.zero_le _) hs⟩

instance : @ArbitrarySizedComplete EntityUID schemaUID where
  complete x := by
    obtain ⟨ty, eid⟩ := x
    refine ⟨ArbitrarySizedComplete.bound ty + ArbitrarySizedComplete.bound eid, fun s hs => ?_⟩
    refine produces_bind_of (ArbitrarySizedComplete.produces (x := ty) (by omega)) ?_
    exact produces_bind_of (ArbitrarySizedComplete.produces (x := eid) (by omega))
      (produces_pure_iff.mpr rfl)

end Laws

end Cedar.Validation.Relational.SchemaGen

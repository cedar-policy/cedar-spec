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
import Specimen.Basalt
import Specimen.Correctness.ReachClose

/-! # The schema generator's leaves, complete

The names a schema is built from are drawn mostly from a small pool, so that they repeat, sometimes as
a random printable string, and rarely as any string at all. The last is what makes every name
possible, so that the derived generator is complete; the pool is what makes them useful. Scoped to
the schema generator's namespace, so that the other generators keep their own. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec Cedar.Validation
open Specimen.Correctness Basalt

/-- The names drawn most often. -/
def namePool : List String := ["User", "Group", "Document", "Photo", "Album", "Account", "a", "b"]

/-- Mostly printable ASCII, rarely any character. -/
def anyChar {G : Type → Type} [Gen G] : G Char :=
  frequency [(9, fun _ => do pure (Char.ofNat (← chooseNat 32 126))),
             (1, fun _ => do pure (Char.ofNat (← chooseNat 0 1114111)))]

/-- A string of at most `n` characters, each `anyChar`. -/
def anyString {G : Type → Type} [Gen G] (n : Nat) : G String := do
  let k ← chooseNat 0 n
  let cs ← vectorOf k anyChar
  pure (String.ofList cs)

/-- A printable string of at most `n` characters, as Basalt draws one. -/
def printString {G : Type → Type} [Gen G] (n : Nat) : G String := do
  let k ← chooseNat 0 n
  let cs ← vectorOf k (do pure (Char.ofNat (← chooseNat 32 126)))
  pure (String.ofList cs)

scoped instance (priority := high) schemaString : ArbitrarySized String where
  arbitrarySized n := frequency [(6, fun _ => elements namePool (by simp [namePool])), (3, fun _ => printString n),
    (1, fun _ => anyString n)]

scoped instance (priority := high) schemaName : ArbitrarySized Cedar.Spec.Name where
  arbitrarySized n := do
    let id ← ArbitrarySized.arbitrarySized n
    let path ← frequency [(9, fun _ => pure []), (1, fun _ => ArbitrarySized.arbitrarySized n)]
    pure ⟨id, path⟩

/-! ## Every name is possible -/

theorem char_toNat_le (c : Char) : c.toNat ≤ 1114111 := by
  rcases c.valid with h | h
  all_goals (simp only [Char.toNat]; omega)

theorem produces_anyChar (c : Char) : Produces (anyChar : SGen Char) c :=
  produces_of_reach ((reach_frequency _).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.succ_pos _,
    reach_of_produces (produces_bind_of (produces_chooseNat _ (Nat.zero_le _) (char_toNat_le c))
      (produces_pure_iff.mpr (Char.ofNat_toNat c).symm))⟩)

theorem produces_anyString (x : String) {n : Nat} (h : x.length ≤ n) :
    Produces (anyString n : SGen String) x := by
  unfold anyString
  refine produces_bind_of (produces_chooseNat (k := x.toList.length) _ (Nat.zero_le _)
    (by rw [String.length_toList]; exact h)) ?_
  exact produces_bind_of (produces_vectorOf x.toList fun c _ => produces_anyChar c)
    (produces_pure_iff.mpr String.ofList_toList.symm)

instance : @ArbitrarySizedComplete String schemaString where
  complete x := ⟨x.length, fun _ hs => produces_of_reach ((reach_frequency _).mpr ⟨_,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Nat.succ_pos _,
    reach_of_produces (produces_anyString x hs)⟩)⟩

instance : @ArbitrarySizedComplete Cedar.Spec.Name schemaName where
  complete x := by
    obtain ⟨id, path⟩ := x
    refine ⟨ArbitrarySizedComplete.bound id + ArbitrarySizedComplete.bound path, fun s hs => ?_⟩
    refine produces_bind_of (ArbitrarySizedComplete.produces (x := id) (by omega)) ?_
    refine produces_bind_of (a := path) (produces_of_reach ((reach_frequency _).mpr ⟨_,
      List.mem_cons_of_mem _ List.mem_cons_self, Nat.succ_pos _,
      reach_of_produces (ArbitrarySizedComplete.produces (by omega))⟩)) (produces_pure_iff.mpr rfl)

/-! ## Attribute names above a bound

Mostly the bound and one or more `a`s, so that the attributes of a record come out in order with no
search; sometimes any string, kept when it is above the bound. -/

scoped instance (priority := high) schemaAttrAbove (b : Attr) : BacktrackGenFor Attr (fun a => b < a) where
  gen size _ := frequency [
    (3, fun _ => do
      let n ← chooseNat 1 (size + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a ← anyString size
      return if b < a then a else b ++ String.ofList (List.replicate 1 'a'))]

instance (b : Attr) : @BacktrackGenForComplete Attr (fun a => b < a) (schemaAttrAbove b) where
  complete a h := ⟨a.length, fun s _ hs _ => produces_of_reach ((reach_frequency _).mpr ⟨_,
    List.mem_cons_of_mem _ List.mem_cons_self, Nat.one_pos,
    reach_of_produces (produces_bind_of (produces_anyString a hs) (produces_pure_iff.mpr (by simp [h])))⟩)⟩

end Cedar.Validation.Relational.SchemaGen

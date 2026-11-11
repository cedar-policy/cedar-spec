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

/-! # The flags of `GenTypeEnvF` are monotone

Every strict setting is a sub-relation of every laxer one: `GenTypeEnvF.mono` lowers any subset of
the seven flags at once, keeping the mode and the budget. Each helper relation has the same law,
proved by matching its rules: a rule at `true` has a twin at `false`, and a rule at `false` stays. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-- The flag `x` is no stricter than `y` (`false ≤ true`). -/
abbrev BLe (x y : Bool) : Prop := x = true → y = true

theorem BLe.of_false {x : Bool} (h : BLe x false) : x = false := by
  cases x
  · rfl
  · exact absurd (h rfl) (by decide)

theorem BLe.refl (x : Bool) : BLe x x := id

theorem BLe.false_le (x : Bool) : BLe false x := fun h => absurd h (by decide)

/-! ## Leaves -/

theorem NameIf.mono {i i' x} (h : NameIf i x) (hi : BLe i' i) : NameIf i' x := by
  cases h
  case ident h => exact .ident _ _ h
  case any => obtain rfl := hi.of_false; exact .any _

theorem ActTyIf.mono {i i' x} (h : ActTyIf i x) (hi : BLe i' i) : ActTyIf i' x := by
  cases h
  case action h => exact .action _ _ h
  case any => obtain rfl := hi.of_false; exact .any _

theorem NotInIf.mono {a a' x ks} (h : NotInIf a x ks) (ha : BLe a' a) : NotInIf a' x ks := by
  cases h
  case strict h => exact .strict _ _ _ h
  case lax => obtain rfl := ha.of_false; exact .lax _ _

theorem ActTyOK.mono {a a' i i' ks x} (h : ActTyOK a i ks x) (ha : BLe a' a) (hi : BLe i' i) :
    ActTyOK a' i' ks x := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ _ (h₁.mono hi) (h₂.mono ha)

theorem KeyArrET.mono {m m' xs ys} (h : KeyArrET m xs ys) (hm : BLe m' m) : KeyArrET m' xs ys := by
  cases h with
  | sortT => cases m' <;> first | exact .sortT _ | exact .sortF _
  | sortF => obtain rfl := hm.of_false; exact .sortF _
  | dedupF => obtain rfl := hm.of_false; exact .dedupF _

theorem KeyArrUID.mono {m m' xs ys} (h : KeyArrUID m xs ys) (hm : BLe m' m) : KeyArrUID m' xs ys := by
  cases h with
  | sortT => cases m' <;> first | exact .sortT _ | exact .sortF _
  | sortF => obtain rfl := hm.of_false; exact .sortF _
  | dedupF => obtain rfl := hm.of_false; exact .dedupF _

theorem SetArrET.mono {m m' xs ys} (h : SetArrET m xs ys) (hm : BLe m' m) : SetArrET m' xs ys := by
  cases h with
  | sortT => cases m' <;> first | exact .sortT _ | exact .sortF _
  | sortF => obtain rfl := hm.of_false; exact .sortF _
  | keepF => obtain rfl := hm.of_false; exact .keepF _

theorem SetArrUID.mono {m m' xs ys} (h : SetArrUID m xs ys) (hm : BLe m' m) : SetArrUID m' xs ys := by
  cases h with
  | sortT => cases m' <;> first | exact .sortT _ | exact .sortF _
  | sortF => obtain rfl := hm.of_false; exact .sortF _
  | keepF => obtain rfl := hm.of_false; exact .keepF _

theorem SetArrStr.mono {m m' xs ys} (h : SetArrStr m xs ys) (hm : BLe m' m) : SetArrStr m' xs ys := by
  cases h with
  | sortT => cases m' <;> first | exact .sortT _ | exact .sortF _
  | sortF => obtain rfl := hm.of_false; exact .sortF _
  | keepF => obtain rfl := hm.of_false; exact .keepF _

theorem RawStrsNE.mono {e e' xs} (h : RawStrsNE e xs) (he : BLe e' e) : RawStrsNE e' xs := by
  cases h
  case consT h => cases e' <;> first | exact .consT _ _ h | exact .consF _ _ h
  case consF h => obtain rfl := he.of_false; exact .consF _ _ h
  case nilF => obtain rfl := he.of_false; exact .nilF

theorem BoolIf.mono {d d' b} (h : BoolIf d b) (hd : BLe d' d) : BoolIf d' b := by
  cases h with
  | anyT => cases d' <;> first | exact .anyT | exact .anyF
  | anyF => obtain rfl := hd.of_false; exact .anyF
  | ttF => obtain rfl := hd.of_false; exact .ttF
  | ffF => obtain rfl := hd.of_false; exact .ffF

theorem RefIf.mono {c c' i i' ks ats x} (h : RefIf c i ks ats x) (hc : BLe c' c) (hi : BLe i' i) :
    RefIf c' i' ks ats x := by
  cases h
  case entTT h => cases c' <;> cases i' <;>
      first | exact .entTT _ _ _ h | exact .entTF _ _ _ h | exact .entFT _ _ _ h | exact .entFF _ _ _ h
  case entTF h => obtain rfl := hi.of_false; cases c' <;>
      first | exact .entTF _ _ _ h | exact .entFF _ _ _ h
  case actTF h => obtain rfl := hi.of_false; cases c' <;>
      first | exact .actTF _ _ _ h | exact .actFF _ _ _ h
  case entFT h => obtain rfl := hc.of_false; cases i' <;>
      first | exact .entFT _ _ _ h | exact .entFF _ _ _ h
  case anyFT => obtain rfl := hc.of_false; cases i' <;> first | exact .anyFT _ _ _ | exact .anyFF _ _ _
  case entFF h => obtain rfl := hc.of_false; obtain rfl := hi.of_false; exact .entFF _ _ _ h
  case actFF h => obtain rfl := hc.of_false; obtain rfl := hi.of_false; exact .actFF _ _ _ h
  case anyFF => obtain rfl := hc.of_false; obtain rfl := hi.of_false; exact .anyFF _ _ _

theorem AttrArr.mono {c c' m m' raw attrs} (h : AttrArr c m raw attrs) (hc : BLe c' c)
    (hm : BLe m' m) : AttrArr c' m' raw attrs := by
  cases h with
  | sortTT => cases c' <;> cases m' <;>
      first | exact .sortTT _ | exact .sortTF _ | exact .sortFT _ | exact .sortFF _
  | sortTF => obtain rfl := hm.of_false; cases c' <;> first | exact .sortTF _ | exact .sortFF _
  | dedupTF => obtain rfl := hm.of_false; cases c' <;> first | exact .dedupTF _ | exact .dedupFF _
  | sortFT => obtain rfl := hc.of_false; cases m' <;> first | exact .sortFT _ | exact .sortFF _
  | rawFT => obtain rfl := hc.of_false; cases m' <;> first | exact .rawFT _ | exact .rawFF _
  | sortFF => obtain rfl := hc.of_false; obtain rfl := hm.of_false; exact .sortFF _
  | dedupFF => obtain rfl := hc.of_false; obtain rfl := hm.of_false; exact .dedupFF _
  | rawFF => obtain rfl := hc.of_false; obtain rfl := hm.of_false; exact .rawFF _

/-! ## Types -/

mutual

theorem TyF.mono {m m' d d' i i' c c' ks ats ty} (h : TyF m d i c ks ats ty) (hm : BLe m' m)
    (hd : BLe d' d) (hi : BLe i' i) (hc : BLe c' c) : TyF m' d' i' c' ks ats ty :=
  match h with
  | .bool _ h => .bool _ (h.mono hd)
  | .int => .int
  | .string => .string
  | .decimal => .decimal
  | .ipAddr => .ipAddr
  | .datetime => .datetime
  | .duration => .duration
  | .entity _ h => .entity _ (h.mono hc hi)
  | .set _ h => .set _ (h.mono hm hd hi hc)
  | .record _ _ h₁ h₂ => .record _ _ (h₁.mono hm hd hi hc) (h₂.mono hc hm)

theorem FieldsF.mono {m m' d d' i i' c c' ks ats fs} (h : FieldsF m d i c ks ats fs) (hm : BLe m' m)
    (hd : BLe d' d) (hi : BLe i' i) (hc : BLe c' c) : FieldsF m' d' i' c' ks ats fs :=
  match h with
  | .nil => .nil
  | .req _ _ _ h₁ h₂ => .req _ _ _ (h₁.mono hm hd hi hc) (h₂.mono hm hd hi hc)
  | .opt _ _ _ h₁ h₂ => .opt _ _ _ (h₁.mono hm hd hi hc) (h₂.mono hm hd hi hc)

end

theorem RecTyF.mono {m m' d d' i i' c c' ks ats attrs} (h : RecTyF m d i c ks ats attrs)
    (hm : BLe m' m) (hd : BLe d' d) (hi : BLe i' i) (hc : BLe c' c) :
    RecTyF m' d' i' c' ks ats attrs := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ (h₁.mono hm hd hi hc) (h₂.mono hc hm)

theorem TagsF.mono {m m' d d' i i' ks ats tags} (h : TagsF m d i ks ats tags) (hm : BLe m' m)
    (hd : BLe d' d) (hi : BLe i' i) : TagsF m' d' i' ks ats tags := by
  cases h
  case none => exact .none
  case some h => exact .some _ (h.mono hm hd hi (BLe.refl _))

/-! ## Entities -/

theorem RawNames.mono {i i' xs} (h : RawNames i xs) (hi : BLe i' i) : RawNames i' xs := by
  induction h
  case nil => exact .nil _
  case cons h _ ih => exact .cons _ _ _ (h.mono hi) ih

theorem AncPool.mono {n n' all std pool} (h : AncPool n all std pool) (hn : BLe n' n) :
    AncPool n' all std pool := by
  cases h with
  | stdT => cases n' <;> first | exact .stdT _ _ | exact .stdF _ _
  | stdF => obtain rfl := hn.of_false; exact .stdF _ _
  | allF => obtain rfl := hn.of_false; exact .allF _ _

theorem NotEnumIf.mono {n n' eks x} (h : NotEnumIf n eks x) (hn : BLe n' n) : NotEnumIf n' eks x := by
  cases h
  case strictT h => cases n' <;> first | exact .strictT _ _ h | exact .strictF _ _ h
  case strictF h => obtain rfl := hn.of_false; exact .strictF _ _ h
  case laxF => obtain rfl := hn.of_false; exact .laxF _ _

theorem AncElem.mono {d d' n n' ks sks eks x} (h : AncElem d n ks sks eks x) (hd : BLe d' d)
    (hn : BLe n' n) : AncElem d' n' ks sks eks x := by
  cases h
  case declT h₁ h₂ => cases d' <;>
      first | exact .declT _ _ _ _ _ _ (h₁.mono hn) h₂ | exact .declF _ _ _ _ _ _ (h₁.mono hn) h₂
  case declF h₁ h₂ => obtain rfl := hd.of_false; exact .declF _ _ _ _ _ _ (h₁.mono hn) h₂
  case anyF h => obtain rfl := hd.of_false; exact .anyF _ _ _ _ _ (h.mono hn)

theorem AncElems.mono {d d' n n' ks sks eks xs} (h : AncElems d n ks sks eks xs) (hd : BLe d' d)
    (hn : BLe n' n) : AncElems d' n' ks sks eks xs := by
  induction h
  case nil => exact .nil _ _ _ _ _
  case cons h _ ih => exact .cons _ _ _ _ _ _ _ (h.mono hd hn) ih

theorem ParentsF.mono {r m m' d d' n n' ks sks eks seen seenStd ps}
    (h : ParentsF r m d n ks sks eks seen seenStd ps) (hm : BLe m' m) (hd : BLe d' d)
    (hn : BLe n' n) : ParentsF r m' d' n' ks sks eks seen seenStd ps := by
  cases h
  case denseStdT h₁ h₂ => cases n' <;>
      first
      | exact .denseStdT _ _ _ _ _ _ _ _ _ h₁ (h₂.mono hm)
      | exact .denseStdF _ _ _ _ _ _ _ _ _ h₁ (h₂.mono hm)
  case denseStdF h₁ h₂ =>
    obtain rfl := hn.of_false; exact .denseStdF _ _ _ _ _ _ _ _ _ h₁ (h₂.mono hm)
  case denseAllF h₁ h₂ =>
    obtain rfl := hn.of_false; exact .denseAllF _ _ _ _ _ _ _ _ _ h₁ (h₂.mono hm)
  case freeT h₁ h₂ => cases n' <;>
      first
      | exact .freeT _ _ _ _ _ _ _ _ _ (h₁.mono hd hn) (h₂.mono hm)
      | exact .freeF _ _ _ _ _ _ _ _ _ (h₁.mono hd hn) (h₂.mono hm)
  case freeF h₁ h₂ =>
    obtain rfl := hn.of_false; exact .freeF _ _ _ _ _ _ _ _ _ (h₁.mono hd hn) (h₂.mono hm)
  case sparseNoneT => cases n' <;> first | exact .sparseNoneT _ _ _ _ _ _ _ | exact .sparseNoneF _ _ _ _ _ _ _
  case sparseNoneF => obtain rfl := hn.of_false; exact .sparseNoneF _ _ _ _ _ _ _
  case sparseStdT h => cases n' <;>
      first | exact .sparseStdT _ _ _ _ _ _ _ _ h | exact .sparseStdF _ _ _ _ _ _ _ _ h
  case sparseStdF h => obtain rfl := hn.of_false; exact .sparseStdF _ _ _ _ _ _ _ _ h
  case sparseAllF h => obtain rfl := hn.of_false; exact .sparseAllF _ _ _ _ _ _ _ _ h
  case flatT => cases n' <;> first | exact .flatT _ _ _ _ _ _ _ | exact .flatF _ _ _ _ _ _ _
  case flatF => obtain rfl := hn.of_false; exact .flatF _ _ _ _ _ _ _

theorem EidsF.mono {m m' e e' eids} (h : EidsF m e eids) (hm : BLe m' m) (he : BLe e' e) :
    EidsF m' e' eids := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ _ (h₁.mono he) (h₂.mono hm)

theorem EntsF.mono {m m' e e' d d' n n' i i' r ks sks eks ats seen seenStd kinds ents}
    (h : EntsF m e d n i r ks sks eks ats seen seenStd kinds ents) (hm : BLe m' m) (he : BLe e' e)
    (hd : BLe d' d) (hn : BLe n' n) (hi : BLe i' i) :
    EntsF m' e' d' n' i' r ks sks eks ats seen seenStd kinds ents := by
  induction h
  case nil => exact .nil _ _
  case std h₁ h₂ h₃ _ ih =>
    exact .std _ _ _ _ _ _ _ _ (h₁.mono hm hd hn) (h₂.mono hm hd hi (BLe.refl _)) (h₃.mono hm hd hi) ih
  case enum h₁ _ ih => exact .enum _ _ _ _ _ _ (h₁.mono hm he) ih

theorem CloseEnts.mono {c c' m m' g g'} (h : CloseEnts c m g g') (hc : BLe c' c) (hm : BLe m' m) :
    CloseEnts c' m' g g' := by
  cases h
  case keep => obtain rfl := hc.of_false; exact .keep _ _
  case closeS h => exact .closeS _ _ _ h
  case closeA h => obtain rfl := hm.of_false; exact .closeA _ _ h

/-! ## Actions -/

theorem ACands.mono {a a' ranked k uids pool} (h : ACands a ranked k uids pool) (ha : BLe a' a) :
    ACands a' ranked k uids pool := by
  cases h
  case lowerT h => cases a' <;> first | exact .lowerT _ _ _ _ h | exact .lowerF _ _ _ _ h
  case lowerF h => obtain rfl := ha.of_false; exact .lowerF _ _ _ _ h
  case allF => obtain rfl := ha.of_false; exact .allF _ _ _

theorem AElem.mono {d d' a a' ranked k uids x} (h : AElem d a ranked k uids x) (hd : BLe d' d)
    (ha : BLe a' a) : AElem d' a' ranked k uids x := by
  cases h
  case declT h₁ h₂ => cases d' <;>
      first | exact .declT _ _ _ _ _ _ (h₁.mono ha) h₂ | exact .declF _ _ _ _ _ _ (h₁.mono ha) h₂
  case declF h₁ h₂ => obtain rfl := hd.of_false; exact .declF _ _ _ _ _ _ (h₁.mono ha) h₂
  case undeclF h => obtain rfl := hd.of_false; exact .undeclF _ _ _ _ _ _ h

theorem AElems.mono {d d' a a' ranked k uids xs} (h : AElems d a ranked k uids xs) (hd : BLe d' d)
    (ha : BLe a' a) : AElems d' a' ranked k uids xs := by
  induction h
  case nil => exact .nil _ _ _ _ _
  case cons h _ ih => exact .cons _ _ _ _ _ _ _ (h.mono hd ha) ih

theorem AParents.mono {r m m' d d' a a' ranked k uids ps} (h : AParents r m d a ranked k uids ps)
    (hm : BLe m' m) (hd : BLe d' d) (ha : BLe a' a) : AParents r m' d' a' ranked k uids ps := by
  cases h
  case denseLowerT h₁ h₂ => cases a' <;>
      first
      | exact .denseLowerT _ _ _ _ _ _ _ h₁ (h₂.mono hm)
      | exact .denseLowerF _ _ _ _ _ _ _ h₁ (h₂.mono hm)
  case denseLowerF h₁ h₂ =>
    obtain rfl := ha.of_false; exact .denseLowerF _ _ _ _ _ _ _ h₁ (h₂.mono hm)
  case denseAllF h₁ h₂ =>
    obtain rfl := ha.of_false; exact .denseAllF _ _ _ _ _ _ _ h₁ (h₂.mono hm)
  case freeT h₁ h₂ => cases a' <;>
      first
      | exact .freeT _ _ _ _ _ _ _ (h₁.mono hd ha) (h₂.mono hm)
      | exact .freeF _ _ _ _ _ _ _ (h₁.mono hd ha) (h₂.mono hm)
  case freeF h₁ h₂ =>
    obtain rfl := ha.of_false; exact .freeF _ _ _ _ _ _ _ (h₁.mono hd ha) (h₂.mono hm)
  case sparseNoneT => cases a' <;> first | exact .sparseNoneT _ _ _ _ _ | exact .sparseNoneF _ _ _ _ _
  case sparseNoneF => obtain rfl := ha.of_false; exact .sparseNoneF _ _ _ _ _
  case sparseLowerT h => cases a' <;>
      first | exact .sparseLowerT _ _ _ _ _ _ h | exact .sparseLowerF _ _ _ _ _ _ h
  case sparseLowerF h => obtain rfl := ha.of_false; exact .sparseLowerF _ _ _ _ _ _ h
  case sparseAllF h => obtain rfl := ha.of_false; exact .sparseAllF _ _ _ _ _ _ h
  case flatT => cases a' <;> first | exact .flatT _ _ _ _ _ | exact .flatF _ _ _ _ _
  case flatF => obtain rfl := ha.of_false; exact .flatF _ _ _ _ _

theorem AppliesF.mono {d d' i i' ks ats xs} (h : AppliesF d i ks ats xs) (hd : BLe d' d)
    (hi : BLe i' i) : AppliesF d' i' ks ats xs := by
  induction h
  case nil => exact .nil _ _ _ _
  case cons h _ ih => exact .cons _ _ _ _ _ _ (h.mono hd hi) ih

theorem AppliesBounded.mono {d d' i i' ks ats n n' xs} (h : AppliesBounded d i ks ats n xs)
    (hd : BLe d' d) (hi : BLe i' i) (hn : n ≤ n') : AppliesBounded d' i' ks ats n' xs := by
  induction h generalizing n'
  case nil => exact .nil _ _ _ _ _
  case cons h _ ih =>
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    exact .cons _ _ _ _ _ _ _ (h.mono hd hi) (ih (by omega))

theorem AppliesBounded.appliesF {d i ks ats n xs} (h : AppliesBounded d i ks ats n xs) :
    AppliesF d i ks ats xs := by
  induction h
  case nil => exact .nil _ _ _ _
  case cons h _ ih => exact .cons _ _ _ _ _ _ h ih

theorem AppliesNE.mono {d d' i i' ks ats n n' xs} (h : AppliesNE d i ks ats n xs) (hd : BLe d' d)
    (hi : BLe i' i) (hn : n ≤ n') : AppliesNE d' i' ks ats n' xs := by
  cases h
  case mk h₁ h₂ =>
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    exact .mk _ _ _ _ _ _ _ (h₁.mono hd hi) (h₂.mono hd hi (by omega))

theorem RawResources.mono {d d' i i' ks ats b b' ps raw} (h : RawResources d i ks ats b ps raw)
    (hd : BLe d' d) (hi : BLe i' i) (hb : b ≤ b') : RawResources d' i' ks ats b' ps raw := by
  cases h
  case none h => exact .none _ _ _ _ _ _ (h.mono hd hi)
  case some h => exact .some _ _ _ _ _ _ _ _ (h.mono hd hi (Nat.div_le_div_right hb))

theorem PrincipalsF.mono {m m' d d' i i' ks ats ps} (h : PrincipalsF m d i ks ats ps)
    (hm : BLe m' m) (hd : BLe d' d) (hi : BLe i' i) : PrincipalsF m' d' i' ks ats ps := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ _ _ _ _ (h₁.mono hd hi) (h₂.mono hm)

theorem ResourcesF.mono {m m' d d' i i' ks ats b b' ps rs} (h : ResourcesF m d i ks ats b ps rs)
    (hm : BLe m' m) (hd : BLe d' d) (hi : BLe i' i) (hb : b ≤ b') :
    ResourcesF m' d' i' ks ats b' ps rs := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ _ _ _ _ _ _ (h₁.mono hd hi hb) (h₂.mono hm)

theorem AppliesNEF.mono {m m' d d' i i' ks ats n n' ps} (h : AppliesNEF m d i ks ats n ps)
    (hm : BLe m' m) (hd : BLe d' d) (hi : BLe i' i) (hn : n ≤ n') :
    AppliesNEF m' d' i' ks ats n' ps := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ _ _ _ _ _ (h₁.mono hd hi hn) (h₂.mono hm)

theorem ActsB.mono {m m' a a' d d' i i' r ks ats uids ranked b todo acts}
    (h : ActsB m a d i r ks ats uids ranked b todo acts) (hm : BLe m' m) (ha : BLe a' a)
    (hd : BLe d' d) (hi : BLe i' i) : ActsB m' a' d' i' r ks ats uids ranked b todo acts := by
  induction h
  case nil => exact .nil _
  case cons h₁ h₂ h₃ h₄ _ ih =>
    exact .cons _ _ _ _ _ _ _ _ _ (h₁.mono hm hd hi) (h₂.mono hm hd hi (Nat.le_refl _))
      (h₃.mono hm hd ha) (h₄.mono hm hd hi hd) ih

theorem ActsR.mono {m m' a a' d d' i i' r ks ats uids ranked b todo acts reqty}
    (h : ActsR m a d i r ks ats uids ranked b todo acts reqty) (hm : BLe m' m) (ha : BLe a' a)
    (hd : BLe d' d) (hi : BLe i' i) : ActsR m' a' d' i' r ks ats uids ranked b todo acts reqty := by
  induction h
  case cons h₁ h₂ h₃ h₄ _ ih =>
    exact .cons _ _ _ _ _ _ _ _ _ _ (h₁.mono hm hd hi) (h₂.mono hm hd hi (Nat.le_refl _))
      (h₃.mono hm hd ha) (h₄.mono hm hd hi hd) ih
  case request h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
    exact .request _ _ _ _ _ _ _ _ _ _ _ (h₁.mono hm hd hi (Nat.le_refl _)) h₂
      (h₃.mono hm hd hi (Nat.le_refl _)) h₄ (h₅.mono hm hd ha) (h₆.mono hm hd hi hd)
      (h₇.mono hm ha hd hi)

theorem CloseActs.mono {a a' m m' g g'} (h : CloseActs a m g g') (ha : BLe a' a) (hm : BLe m' m) :
    CloseActs a' m' g g' := by
  cases h
  case keep => obtain rfl := ha.of_false; exact .keep _ _
  case closeS h₁ h₂ => exact .closeS _ _ _ h₁ h₂
  case closeA h₁ h₂ => obtain rfl := hm.of_false; exact .closeA _ _ h₁ h₂

/-! ## The skeleton and the environment -/

theorem RawUids.mono {a a' i i' ks us} (h : RawUids a i ks us) (ha : BLe a' a) (hi : BLe i' i) :
    RawUids a' i' ks us := by
  induction h
  case nil => exact .nil _ _ _
  case cons h _ ih => exact .cons _ _ _ _ _ _ (h.mono ha hi) ih

theorem NamesF.mono {m m' i i' ks} (h : NamesF m i ks) (hm : BLe m' m) (hi : BLe i' i) :
    NamesF m' i' ks := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ _ (h₁.mono hi) (h₂.mono hm)

theorem UidsF.mono {m m' a a' i i' ks uids ats ranked} (h : UidsF m a i ks uids ats ranked)
    (hm : BLe m' m) (ha : BLe a' a) (hi : BLe i' i) : UidsF m' a' i' ks uids ats ranked := by
  cases h
  case mk h₁ h₂ h₃ h₄ => exact .mk _ _ _ _ _ _ _ _ (h₁.mono ha hi) (h₂.mono hm) h₃ h₄

theorem ShadowIf.mono {i i' ks u u'} (h : ShadowIf i ks u u') (hi : BLe i' i) :
    ShadowIf i' ks u u' := by
  cases h with
  | strict _ _ _ hs => exact .strict _ _ _ hs
  | lax =>
    cases i' with
    | true => exact absurd (hi rfl) (by decide)
    | false => exact .lax _ _

theorem SkelF.mono {m m' a a' i i' sk} (h : SkelF m a i sk) (hm : BLe m' m) (ha : BLe a' a)
    (hi : BLe i' i) : SkelF m' a' i' sk := by
  cases h
  case mk h₁ h₂ h₃ h₄ h₅ h₆ =>
    exact .mk _ _ _ _ _ _ _ _ _ _ _ (h₁.mono hm hi) h₂ h₃ h₄ (h₅.mono hm ha hi) (h₆.mono hi)

theorem EntsAll.mono {m m' e e' d d' c c' n n' i i' r sk ents} (h : EntsAll m e d c n i r sk ents)
    (hm : BLe m' m) (he : BLe e' e) (hd : BLe d' d) (hc : BLe c' c) (hn : BLe n' n)
    (hi : BLe i' i) : EntsAll m' e' d' c' n' i' r sk ents := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ (h₁.mono hm he hd hn hi) (h₂.mono hc hm)

theorem ActsAllR.mono {m m' a a' i i' r sk b acts reqty} (h : ActsAllR m a i r sk b acts reqty)
    (hm : BLe m' m) (ha : BLe a' a) (hi : BLe i' i) : ActsAllR m' a' i' r sk b acts reqty := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ _ (h₁.mono hm ha (BLe.refl _) hi) (h₂.mono ha hm)

theorem ActsAllB.mono {m m' a a' i i' r sk b acts} (h : ActsAllB m a i r sk b acts)
    (hm : BLe m' m) (ha : BLe a' a) (hi : BLe i' i) : ActsAllB m' a' i' r sk b acts := by
  cases h
  case mk h₁ h₂ => exact .mk _ _ (h₁.mono hm ha (BLe.refl _) hi) (h₂.mono ha hm)

theorem ReqFree.mono {m m' i i' ks ats reqty} (h : ReqFree m i ks ats reqty) (hm : BLe m' m)
    (hi : BLe i' i) : ReqFree m' i' ks ats reqty := by
  cases h
  case mk h₁ h₂ h₃ h₄ =>
    exact .mk _ _ _ _ _ _ _ _ _ (h₁.mono (BLe.refl _) hi) (h₂.mono (BLe.refl _) hi) h₃
      (h₄.mono hm (BLe.refl _) hi (BLe.refl _))

end Cedar.Validation.Relational.SchemaGen

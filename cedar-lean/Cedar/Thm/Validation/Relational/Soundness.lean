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

module

public import Cedar.Thm.Validation.Typechecker.LUB
public import Cedar.Validation.Relational.Assumptions
public import Cedar.Validation.Relational.Schema
import Batteries.Data.List.Lemmas
import all Cedar.Data.List -- unfolds `canonicalize`, `insertCanonical`, `mapM₁`, …
import all Cedar.Data.Map -- unfolds `contains`, `empty`, `find`, …
import all Cedar.Data.Set -- unfolds `all`, `any`, `contains`, …
import all Cedar.Spec.Entities -- unfolds `ancestors`, `attrs`, `tags`
import all Cedar.Spec.Policy -- unfolds `bound`
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.Subtyping -- unfolds `lub`, `lubBool`, `lubQualifiedType`, …
import all Cedar.Validation.Typechecker -- unfolds `Capabilities`, `actionUID`, `entityUID`, …
import all Cedar.Validation.TypedExpr -- unfolds `typeOf`
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `QualifiedType`, …
import all Cedar.Validation.Validator -- unfolds `environment`, `environments`

/-! # Soundness of the relational typing spec

Every `HasType` derivation is a successful run of `typeOf` (`hasType_sound`), with the output
capabilities equal up to `CapsEquiv`. -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Capability set-equality -/

/-- Two capability lists are equivalent when they have the same elements. -/
def CapsEquiv (c₁ c₂ : Capabilities) : Prop := ∀ k, k ∈ c₁ ↔ k ∈ c₂

theorem CapsEquiv.refl (c : Capabilities) : CapsEquiv c c := fun _ => Iff.rfl

theorem CapsEquiv.symm {c₁ c₂ : Capabilities} (h : CapsEquiv c₁ c₂) : CapsEquiv c₂ c₁ :=
  fun k => (h k).symm

theorem CapsEquiv.trans {c₁ c₂ c₃ : Capabilities}
    (h₁ : CapsEquiv c₁ c₂) (h₂ : CapsEquiv c₂ c₃) : CapsEquiv c₁ c₃ :=
  fun k => (h₁ k).trans (h₂ k)

/-- `∪` respects capability set-equality. -/
theorem CapsEquiv.union {a a' b b' : Capabilities}
    (ha : CapsEquiv a a') (hb : CapsEquiv b b') : CapsEquiv (a ∪ b) (a' ∪ b') := by
  intro k; simp only [List.mem_union_iff, ha k, hb k]

/-- `∩` respects capability set-equality. -/
theorem CapsEquiv.inter {a a' b b' : Capabilities}
    (ha : CapsEquiv a a') (hb : CapsEquiv b b') : CapsEquiv (a ∩ b) (a' ∩ b') := by
  intro k; simp only [List.mem_inter_iff, ha k, hb k]

/-! ## Foundational lemmas about the auxiliary relations

These are self-contained (no induction over `HasType`) and establish that each
structural relation faithfully mirrors the function it replaces. -/

/-- `PrimNeq` faithfully witnesses primitive disequality. -/
theorem primNeq_ne {p₁ p₂ : Prim} (h : PrimNeq p₁ p₂) : p₁ ≠ p₂ := by
  cases h <;> simp_all

/-- `BoolTypeNeq` faithfully witnesses `BoolType` disequality. -/
theorem boolTypeNeq_ne {b₁ b₂ : BoolType} (h : BoolTypeNeq b₁ b₂) : b₁ ≠ b₂ := by
  cases h <;> simp

/-- Membership through a structural `CapMerge` is exactly membership in either side. -/
theorem capMerge_mem {c₁ c₂ c : Capabilities} (h : CapMerge c₁ c₂ c) (k : Expr × Key) :
    k ∈ c ↔ k ∈ c₁ ∨ k ∈ c₂ := by
  induction h with
  | nil => simp
  | left _ _ _ _ _ ih => simp only [List.mem_cons]; grind
  | right _ _ _ _ _ ih => simp only [List.mem_cons]; grind
  | both _ _ _ _ _ ih => simp only [List.mem_cons]; grind

/-- A structural `CapMerge` output is set-equivalent to the functional `∪`. -/
theorem capMerge_capsEquiv_union {c₁ c₂ c : Capabilities} (h : CapMerge c₁ c₂ c) :
    CapsEquiv c (c₁ ∪ c₂) := by
  intro k
  rw [capMerge_mem h k, List.mem_union_iff]

/-- Membership in `capIntersect` is membership in both operands. -/
theorem capIntersect_mem (c₁ c₂ : Capabilities) (k : Expr × Key) :
    k ∈ capIntersect c₁ c₂ ↔ k ∈ c₁ ∧ k ∈ c₂ := by
  obtain ⟨ke, kk⟩ := k
  simp only [capIntersect, List.mem_filter, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  grind

/-- `capIntersect` is set-equivalent to the functional `∩`. -/
theorem capIntersect_capsEquiv_inter (c₁ c₂ : Capabilities) :
    CapsEquiv (capIntersect c₁ c₂) (c₁ ∩ c₂) := by
  intro k
  rw [capIntersect_mem c₁ c₂ k, List.mem_inter_iff]

/-- `SetContains` is exactly list membership on the underlying elements. -/
theorem setContains_mem {α} [BEq α] {x : α} {s : Set α} (h : SetContains x s) :
    x ∈ s.elts := by
  induction h with
  | here => simp [Set.elts]
  | there _ _ _ ih => simp only [Set.elts] at *; exact List.mem_cons_of_mem _ ih

/-! ## Structural map/set membership ↔ lookup

`MapContains`/`SetContains` mirror `Map.find?`/`Set.contains`. The `find?`
direction needs the map to have distinct keys, which `EnvAssumptions` supplies. -/

/-- `MapContains` implies the pair is in the underlying list (well-formedness free). -/
theorem mapContains_mem {α β : Type} {k : α} {v : β} {m : Map α β} (h : MapContains k v m) :
    (k, v) ∈ m.toList := by
  induction h with
  | here => simp [Map.toList]
  | there _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Converse of `mapContains_mem`: list membership rebuilds a `MapContains` witness. -/
theorem mem_toList_mapContains {α β : Type} {k : α} {v : β} {m : Map α β}
    (h : (k, v) ∈ m.toList) : MapContains k v m := by
  obtain ⟨l⟩ := m
  simp only [Map.toList] at h
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rcases List.mem_cons.mp h with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact MapContains.here _ _ _
    · exact MapContains.there _ _ _ _ _ (ih hmem)

/-- On a map with duplicate-free keys, `MapContains` agrees with `find?`. -/
theorem mapContains_find?_nodup {α β : Type} [BEq α] [LawfulBEq α]
    {k : α} {v : β} {m : Map α β}
    (h : MapContains k v m) (hnd : (m.toList.map Prod.fst).Nodup) :
    m.find? k = some v := by
  induction h with
  | here rest => simp [Map.find?, Map.toList]
  | there k' v' rest hmc ih =>
    simp only [Map.toList, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    have hkin : k ∈ rest.map Prod.fst :=
      List.mem_map.mpr ⟨(k, v), by simpa only [Map.toList] using mapContains_mem hmc, rfl⟩
    have hne : (k' == k) = false := by
      rw [beq_eq_false_iff_ne]; exact fun heq => hnotin (heq ▸ hkin)
    have hih := ih hnd'
    simp only [Map.find?, Map.toList, List.find?_cons, hne] at hih ⊢
    exact hih

/-- `MapNotContainsKey` mirrors `find? = none`. -/
theorem mapNotContainsKey_find? {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    {k : α} {m : Map α β} (h : MapNotContainsKey k m) : m.find? k = none := by
  induction h with
  | empty => simp [Map.find?, Map.toList]
  | skip k' v' rest hne hrec ih =>
    have : (k' == k) = false := by rw [beq_eq_false_iff_ne]; exact fun heq => hne heq.symm
    simp only [Map.find?, Map.toList, List.find?_cons, this] at ih ⊢
    exact ih

/-- Converse of `setContains_mem`. -/
theorem mem_elts_setContains {α} {x : α} {s : Set α} (h : x ∈ s.elts) : SetContains x s := by
  obtain ⟨l⟩ := s
  simp only [Set.elts] at h
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact SetContains.here _ _
    · exact SetContains.there _ _ _ (ih hmem)

/-- `SetContains` mirrors `Set.contains`. -/
theorem setContains_iff_contains {α} [DecidableEq α] {x : α} {s : Set α} :
    SetContains x s ↔ s.contains x = true := by
  constructor
  · intro h; simp only [Set.contains, List.elem_eq_mem, decide_eq_true_eq]; exact setContains_mem h
  · intro h; simp only [Set.contains, List.elem_eq_mem, decide_eq_true_eq] at h
    exact mem_elts_setContains h

/-- `CapTagMem` mirrors capability membership. -/
theorem capTagMem_iff {x e : Expr} {c : Capabilities} :
    CapTagMem x e c ↔ (x, Key.tag e) ∈ c := by
  constructor
  · intro h; induction h with
    | here => simp
    | there _ _ _ _ ih => exact List.mem_cons_of_mem _ ih
  · intro h; induction c with
    | nil => simp at h
    | cons hd tl ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact CapTagMem.here _ _ _
      · obtain ⟨x', k'⟩ := hd; exact CapTagMem.there _ _ _ _ _ (ih hmem)

/-- `CapAttrMem` mirrors attribute-capability membership. -/
theorem capAttrMem_iff {x : Expr} {a : Attr} {c : Capabilities} :
    CapAttrMem x a c ↔ (x, Key.attr a) ∈ c := by
  constructor
  · intro h; induction h with
    | here => simp
    | there _ _ _ _ ih => exact List.mem_cons_of_mem _ ih
  · intro h; induction c with
    | nil => simp at h
    | cons hd tl ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact CapAttrMem.here _ _ _
      · obtain ⟨x', k'⟩ := hd; exact CapAttrMem.there _ _ _ _ _ (ih hmem)

/-! ## Least-upper-bound soundness

`Lub` mirrors `⊔`/`lub?`.  Mutual with `LubRecord`/`LubQualified`. -/

mutual

theorem lub_sound {t₁ t₂ t : CedarType} (h : Lub t₁ t₂ t) : (t₁ ⊔ t₂) = some t := by
  cases h with
  | boolSame b => simp [lub?, lubBool]
  | boolDiff b₁ b₂ hne => simp [lub?, lubBool, ite_eq_right (boolTypeNeq_ne hne)]
  | int => simp [lub?]
  | string => simp [lub?]
  | entity ety => simp [lub?]
  | ext xty => simp [lub?]
  | set s₁ s₂ s hs => simp [lub?, lub_sound hs]
  | record r₁ r₂ r hr => simp [lub?, lubRecord_sound hr]

theorem lubQualified_sound {q₁ q₂ q : QualifiedType} (h : LubQualified q₁ q₂ q) :
    lubQualifiedType q₁ q₂ = some q := by
  cases h with
  | optional t₁ t₂ t ht => simp [lubQualifiedType, lub_sound ht]
  | required t₁ t₂ t ht => simp [lubQualifiedType, lub_sound ht]

theorem lubRecord_sound {r₁ r₂ r : List (Attr × QualifiedType)} (h : LubRecord r₁ r₂ r) :
    lubRecordType r₁ r₂ = some r := by
  cases h with
  | nil => simp [lubRecordType]
  | cons k v₁ v₂ v a b c hq hr => simp [lubRecordType, lubQualified_sound hq, lubRecord_sound hr]

end

/-! ## `typeOf` capability congruence -/

/-- `hasAttrInRecord` reads capabilities only via `(x, .attr a) ∈ c`, so
    `≈`-equivalent capabilities give an identical result. -/
theorem hasAttrInRecord_capsEquiv {rty : RecordType} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} {b : Bool} (h : CapsEquiv c₁ c₂) :
    hasAttrInRecord rty x a c₁ b = hasAttrInRecord rty x a c₂ b := by
  unfold hasAttrInRecord
  simp only [h (x, .attr a)]

/-- `getAttrInRecord` reads capabilities only via `(x, .attr a) ∈ c`. -/
theorem getAttrInRecord_capsEquiv {ty : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} (h : CapsEquiv c₁ c₂) :
    getAttrInRecord ty rty x a c₁ = getAttrInRecord ty rty x a c₂ := by
  unfold getAttrInRecord
  simp only [h (x, .attr a)]

/-- `typeOfHasTag` reads capabilities only via `(x, .tag t) ∈ c`. -/
theorem typeOfHasTag_capsEquiv {ety : EntityType} {x t : Expr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfHasTag ety x t c₁ env = typeOfHasTag ety x t c₂ env := by
  unfold typeOfHasTag
  simp only [h (x, .tag t)]

/-- `typeOfGetTag` reads capabilities only via `(x, .tag t) ∈ c`. -/
theorem typeOfGetTag_capsEquiv {ety : EntityType} {x t : Expr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfGetTag ety x t c₁ env = typeOfGetTag ety x t c₂ env := by
  unfold typeOfGetTag
  simp only [h (x, .tag t)]

theorem typeOfBinaryApp_capsEquiv {op : BinaryOp} {ty₁ ty₂ : TypedExpr} {x₁ x₂ : Expr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c₁ env = typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c₂ env := by
  unfold typeOfBinaryApp
  simp only [typeOfHasTag_capsEquiv h, typeOfGetTag_capsEquiv h]

theorem typeOfHasAttr_capsEquiv {ty : TypedExpr} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfHasAttr ty x a c₁ env = typeOfHasAttr ty x a c₂ env := by
  unfold typeOfHasAttr
  simp only [hasAttrInRecord_capsEquiv h]

theorem typeOfGetAttr_capsEquiv {ty : TypedExpr} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfGetAttr ty x a c₁ env = typeOfGetAttr ty x a c₂ env := by
  unfold typeOfGetAttr
  simp only [getAttrInRecord_capsEquiv h]

/-- The extended-`has` chain reads capabilities only through `typeOfHasAttr` and
    `typeOfGetAttr`, so its result is unchanged under `≈`-equivalent capabilities. -/
theorem typeOfExtHasAttr_capsEquiv {ty : TypedExpr} {x : Expr} {attrs : List Attr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfExtHasAttr ty x attrs c₁ env = typeOfExtHasAttr ty x attrs c₂ env := by
  induction attrs generalizing ty x c₁ c₂ with
  | nil => simp only [typeOfExtHasAttr]
  | cons a rest ih =>
    cases rest with
    | nil => simp only [typeOfExtHasAttr, typeOfHasAttr_capsEquiv h]
    | cons b rest' =>
      simp only [typeOfExtHasAttr, typeOfHasAttr_capsEquiv h]
      cases hhas : typeOfHasAttr ty x a c₂ env with
      | error e => rfl
      | ok r =>
        obtain ⟨tyHas, ci⟩ := r
        have hu : CapsEquiv (c₁ ∪ ci) (c₂ ∪ ci) := CapsEquiv.union h (CapsEquiv.refl ci)
        simp only [Except.bind_ok, typeOfGetAttr_capsEquiv hu, ih hu]

/-- Capability-congruence for a `mapM` of `justType ∘ typeOf` (the `set`/`call`
    element pass): given per-element congruence, a successful run under `c₁`
    reruns identically under `≈`-equivalent `c₂`. -/
theorem typeOfList_capsEquiv {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv}
    (ih : ∀ x ∈ xs, ∀ {tx : TypedExpr} {o : Capabilities}, typeOf x c₁ env = .ok (tx, o) →
            ∃ o', typeOf x c₂ env = .ok (tx, o') ∧ CapsEquiv o o') :
    ∀ {tys : List TypedExpr}, xs.mapM (fun x => justType (typeOf x c₁ env)) = .ok tys →
             xs.mapM (fun x => justType (typeOf x c₂ env)) = .ok tys := by
  induction xs with
  | nil => intro tys hm; simpa using hm
  | cons x xs ihxs =>
    intro tys hm
    simp only [List.mapM_cons] at hm ⊢
    cases hx1 : typeOf x c₁ env with
    | error e =>
      have hj1 : justType (typeOf x c₁ env) = .error e := by simp only [hx1, justType, Except.map]
      simp [hj1] at hm
    | ok r =>
      obtain ⟨t, o⟩ := r
      obtain ⟨o', hx2, _⟩ := ih x (List.mem_cons_self ..) hx1
      have hj1 : justType (typeOf x c₁ env) = .ok t := by simp only [hx1, justType, Except.map]
      have hj2 : justType (typeOf x c₂ env) = .ok t := by simp only [hx2, justType, Except.map]
      cases htl : xs.mapM (fun x => justType (typeOf x c₁ env)) with
      | error e => simp [hj1, htl] at hm
      | ok ts =>
        have htl2 := ihxs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) htl
        simpa [hj1, hj2, htl, htl2] using hm

/-- Capability-congruence for the `record` element pass (`mapM₂`). -/
theorem typeOfRecordList_capsEquiv {axs : List (Attr × Expr)} {c₁ c₂ : Capabilities} {env : TypeEnv}
    (ih : ∀ ax ∈ axs, ∀ {tx : TypedExpr} {o : Capabilities}, typeOf ax.2 c₁ env = .ok (tx, o) →
            ∃ o', typeOf ax.2 c₂ env = .ok (tx, o') ∧ CapsEquiv o o') :
    ∀ {atys : List (Attr × TypedExpr)},
      axs.mapM (fun ax => (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1))) = .ok atys →
      axs.mapM (fun ax => (typeOf ax.2 c₂ env).map (fun r => (ax.1, r.1))) = .ok atys := by
  induction axs with
  | nil => intro atys hm; simpa using hm
  | cons ax axs ihxs =>
    intro atys hm
    simp only [List.mapM_cons] at hm ⊢
    cases hx1 : typeOf ax.2 c₁ env with
    | error e =>
      have hj1 : (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1)) = .error e := by
        simp only [hx1, Except.map]
      simp [hj1] at hm
    | ok r =>
      obtain ⟨t, o⟩ := r
      obtain ⟨o', hx2, _⟩ := ih ax (List.mem_cons_self ..) hx1
      have hj1 : (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1)) = .ok (ax.1, t) := by
        simp only [hx1, Except.map]
      have hj2 : (typeOf ax.2 c₂ env).map (fun r => (ax.1, r.1)) = .ok (ax.1, t) := by
        simp only [hx2, Except.map]
      cases htl : axs.mapM (fun ax => (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1))) with
      | error e => simp [hj1, htl] at hm
      | ok ts =>
        have htl2 := ihxs (fun ax hx => ih ax (List.mem_cons_of_mem _ hx)) htl
        simpa [hj1, hj2, htl, htl2] using hm

theorem typeOf_capsEquiv {x : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {tx : TypedExpr} {o₁ : Capabilities}
    (h : CapsEquiv c₁ c₂) (h1 : typeOf x c₁ env = .ok (tx, o₁)) :
    ∃ o₂, typeOf x c₂ env = .ok (tx, o₂) ∧ CapsEquiv o₁ o₂ := by
  induction x, c₁ using typeOf.induct generalizing c₂ tx o₁
  -- lit: `typeOfLit` ignores capabilities
  case _ =>
    simp only [typeOf] at h1 ⊢
    exact ⟨o₁, h1, CapsEquiv.refl _⟩
  -- var: `typeOfVar` ignores capabilities
  case _ =>
    simp only [typeOf] at h1 ⊢
    exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- ite: thread `c ∪ c₁` into the then-branch; combine outputs via ∪/∩
    rename_i c x₁ x₂ x₃ ihA ihB ihC
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨ty₁, cc₁⟩ := r1
      obtain ⟨cc₁', hx1', hcc1⟩ := ihA h hx1
      have hu : CapsEquiv (c ∪ cc₁) (c₂ ∪ cc₁') := CapsEquiv.union h hcc1
      simp only [hx1, hx1', Except.bind_ok, typeOfIf] at h1 ⊢
      split at h1
      next => -- condition : .bool .tt
        cases hx2 : typeOf x₂ (c ∪ cc₁) env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB cc₁ hu hx2
          simp only [hx2, Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          simp only [hx2', Except.bind_ok, ok]
          exact ⟨_, rfl, CapsEquiv.union hcc1 hc2⟩
      next => -- condition : .bool .ff
        cases hx3 : typeOf x₃ c env with
        | error e => simp [hx3] at h1
        | ok r3 =>
          obtain ⟨ty₃, c3⟩ := r3
          obtain ⟨c3', hx3', hc3⟩ := ihC h hx3
          simp only [hx3, Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          simp only [hx3', Except.bind_ok, ok]
          exact ⟨_, rfl, hc3⟩
      next => -- condition : .bool .anyBool
        cases hx2 : typeOf x₂ (c ∪ cc₁) env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB cc₁ hu hx2
          cases hx3 : typeOf x₃ c env with
          | error e => simp [hx2, hx3] at h1
          | ok r3 =>
            obtain ⟨ty₃, c3⟩ := r3
            obtain ⟨c3', hx3', hc3⟩ := ihC h hx3
            simp only [hx2, hx3, Except.bind_ok] at h1
            simp only [hx2', hx3', Except.bind_ok]
            split at h1
            next ty hlub =>
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              simp only [ok]
              exact ⟨_, rfl, CapsEquiv.inter (CapsEquiv.union hcc1 hc2) hc3⟩
            next hlub => simp [err] at h1
      next => simp [err] at h1 -- condition : non-boolean
  case _ => -- and: threads `c ∪ c₁` into the second operand like `ite`
    rename_i c x₁ x₂ ihA ihB
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨ty₁, cc₁⟩ := r1
      obtain ⟨cc₁', hx1', hcc1⟩ := ihA h hx1
      have hu : CapsEquiv (c ∪ cc₁) (c₂ ∪ cc₁') := CapsEquiv.union h hcc1
      simp only [hx1, hx1', Except.bind_ok, typeOfAnd] at h1 ⊢
      split at h1
      next => -- ty₁ = .bool .ff : short-circuit, output ∅
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [ok]
        exact ⟨_, rfl, CapsEquiv.refl _⟩
      next => -- ty₁ = .bool _ (tt / anyBool)
        cases hx2 : typeOf x₂ (c ∪ cc₁) env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB cc₁ hu hx2
          simp only [hx2, Except.bind_ok] at h1
          simp only [hx2', Except.bind_ok]
          split at h1
          next => -- ty₂ = .bool .ff : output ∅
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            simp only [ok]; exact ⟨_, rfl, CapsEquiv.refl _⟩
          next => -- ty₂ = .bool .tt
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            simp only [ok]; exact ⟨_, rfl, CapsEquiv.union hcc1 hc2⟩
          next => -- ty₂ = .bool .anyBool
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            simp only [ok]; exact ⟨_, rfl, CapsEquiv.union hcc1 hc2⟩
          next => simp [err] at h1 -- ty₂ non-boolean
      next => simp [err] at h1 -- ty₁ non-boolean
  case _ => -- or: second operand typed under `c` (not threaded)
    rename_i c x₁ x₂ ihA ihB
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨ty₁, cc₁⟩ := r1
      obtain ⟨cc₁', hx1', hcc1⟩ := ihA h hx1
      simp only [hx1, hx1', Except.bind_ok, typeOfOr] at h1 ⊢
      split at h1
      next => -- ty₁ = .bool .tt : output ∅
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [ok]; exact ⟨_, rfl, CapsEquiv.refl _⟩
      next => -- ty₁ = .bool .ff
        cases hx2 : typeOf x₂ c env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB h hx2
          simp only [hx2, Except.bind_ok] at h1
          simp only [hx2', Except.bind_ok]
          split at h1
          next => -- ty₂ = .bool _ : output c₂
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, hc2⟩
          next => simp [err] at h1
      next => -- ty₁ = .bool .anyBool
        cases hx2 : typeOf x₂ c env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB h hx2
          simp only [hx2, Except.bind_ok] at h1
          simp only [hx2', Except.bind_ok]
          split at h1
          next => -- ty₂ = .bool .tt : output ∅
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, CapsEquiv.refl _⟩
          next => -- ty₂ = .bool .ff : output c₁
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, hcc1⟩
          next => -- ty₂ = .bool .anyBool : output c₁ ∩ c₂
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, CapsEquiv.inter hcc1 hc2⟩
          next => simp [err] at h1
      next => simp [err] at h1 -- ty₁ non-boolean
  case _ => -- unaryApp: recurse on `x₁`; `typeOfUnaryApp` is capability-free
    rename_i c op x₁ ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- binaryApp: recurse on both operands; `typeOfBinaryApp` reads caps
            -- only in the hasTag/getTag arms (invariant under ≈)
    rename_i c op x₁ x₂ ihx1 ihx2
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨t1, oc1⟩ := r1
      cases hx2 : typeOf x₂ c env with
      | error e => simp [hx1, hx2, Except.bind_ok] at h1
      | ok r2 =>
        obtain ⟨t2, oc2⟩ := r2
        obtain ⟨oc1', hx1', _⟩ := ihx1 h hx1
        obtain ⟨oc2', hx2', _⟩ := ihx2 h hx2
        simp only [hx1, hx2, hx1', hx2', Except.bind_ok, typeOfBinaryApp_capsEquiv h] at h1 ⊢
        exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- hasAttr: `typeOfHasAttr` reads caps only via membership (invariant under ≈)
    rename_i c x₁ a ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok, typeOfHasAttr_capsEquiv h] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- extHasAttr: the chain reads caps only via `typeOfHasAttr`/`typeOfGetAttr`
    rename_i c x₁ a as ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok, typeOfExtHasAttr_capsEquiv h] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- getAttr
    rename_i c x₁ a ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok, typeOfGetAttr_capsEquiv h] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- set: element pass via `typeOfList_capsEquiv`; `typeOfSet` is cap-free
    rename_i c xs ih1
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)),
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c₂ env))] at h1 ⊢
    cases hm : List.mapM (fun x => justType (typeOf x c env)) xs with
    | error e => simp [hm] at h1
    | ok tys =>
      have hm2 := typeOfList_capsEquiv (fun x hx => ih1 x hx h) hm
      simp only [hm, hm2, Except.bind_ok] at h1 ⊢
      exact ⟨_, h1, CapsEquiv.refl _⟩
  case _ => -- record: element pass via `typeOfRecordList_capsEquiv`; builder is cap-free
    rename_i c axs ih1
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1))),
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c₂ env).map (fun r => (p.1, r.1)))] at h1 ⊢
    cases hm : axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
    | error e => simp [hm] at h1
    | ok atys =>
      have hm2 := typeOfRecordList_capsEquiv
        (fun ax hx => ih1 ax.1 ax.2 (List.sizeOf_snd_lt_sizeOf_list hx) h) hm
      simp only [hm, hm2, Except.bind_ok, ok] at h1 ⊢
      exact ⟨_, h1, CapsEquiv.refl _⟩
  case _ => -- call: same element pass as `set`; `typeOfCall` is cap-free
    rename_i c xfn xs ih1
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)),
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c₂ env))] at h1 ⊢
    cases hm : List.mapM (fun x => justType (typeOf x c env)) xs with
    | error e => simp [hm] at h1
    | ok tys =>
      have hm2 := typeOfList_capsEquiv (fun x hx => ih1 x hx h) hm
      simp only [hm, hm2, Except.bind_ok] at h1 ⊢
      exact ⟨_, h1, CapsEquiv.refl _⟩

/-! ## Schema well-formedness gives distinct keys -/

theorem notInET_not_mem {et : EntityType} {names : List EntityType}
    (h : Schema.NotInET et names) : et ∉ names := by
  induction h with
  | nil => simp
  | cons x rest hne hrec ih => simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩

theorem wfEntitiesGo_nodup {built names allNames entries}
    (h : Schema.WfEntitiesGo built names allNames entries) :
    (entries.map Prod.fst).Nodup ∧ ∀ k ∈ entries.map Prod.fst, k ∉ names := by
  induction h with
  | nil => simp
  | standard built names et ancestors attrs tags allNames rest hni hpca hattrs htags hgo ih =>
    obtain ⟨ihnd, ihnotin⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => (ihnotin et hmem) List.mem_cons_self, ihnd⟩
    · intro k hk
      simp only [List.map_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact notInET_not_mem hni
      · exact fun hmem => ihnotin k hk (List.mem_cons_of_mem et hmem)
  | enum built names et eids allNames rest hni hgo ih =>
    obtain ⟨ihnd, ihnotin⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => (ihnotin et hmem) List.mem_cons_self, ihnd⟩
    · intro k hk
      simp only [List.map_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact notInET_not_mem hni
      · exact fun hmem => ihnotin k hk (List.mem_cons_of_mem et hmem)

theorem wfEntitySchema_nodup {allNames entries}
    (h : Schema.WfEntitySchema allNames entries) : (entries.map Prod.fst).Nodup := by
  cases h with
  | mk hgo => exact (wfEntitiesGo_nodup hgo).1

/-- Entity-store keys of a well-formed `TypeEnv` are distinct. -/
theorem wfTypeEnv_ets_nodup {env : TypeEnv} (h : Schema.WfTypeEnv env) :
    (env.ets.toList.map Prod.fst).Nodup := by
  cases h with
  | mk entityTypes entityEntries actionEntries reqty hes _ _ =>
    simpa only [Map.toList] using wfEntitySchema_nodup hes

theorem selectRemove_mem {α} {avail : List α} {eid : α} {avail' : List α}
    (h : Schema.SelectRemove avail eid avail') : eid ∈ avail := by
  induction h with
  | here => exact List.mem_cons_self
  | there x xs y ys hsr ih => exact List.mem_cons_of_mem _ ih

theorem selectRemove_subset {α} {avail : List α} {eid : α} {avail' : List α}
    (h : Schema.SelectRemove avail eid avail') : ∀ x ∈ avail', x ∈ avail := by
  induction h with
  | here => exact fun x hx => List.mem_cons_of_mem _ hx
  | there x xs y ys hsr ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih z hz)

theorem selectRemove_nodup {α} {avail : List α} {eid : α} {avail' : List α}
    (h : Schema.SelectRemove avail eid avail') (hnd : avail.Nodup) :
    avail'.Nodup ∧ eid ∉ avail' := by
  induction h with
  | here => rw [List.nodup_cons] at hnd; exact ⟨hnd.2, hnd.1⟩
  | there x xs y ys hsr ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hxnotin, hndxs⟩ := hnd
    obtain ⟨ihnd, ihnotin⟩ := ih hndxs
    refine ⟨?_, ?_⟩
    · rw [List.nodup_cons]; exact ⟨fun hmem => hxnotin (selectRemove_subset hsr x hmem), ihnd⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨fun heq => hxnotin (heq ▸ selectRemove_mem hsr), ihnotin⟩

theorem actionEidPool_nodup : Schema.actionEidPool.Nodup := by decide

theorem wfActionsGo_nodup {ets built avail entries}
    (h : Schema.WfActionsGo ets built avail entries) :
    avail.Nodup → (entries.map Prod.fst).Nodup ∧
      ∀ uid ∈ entries.map Prod.fst, EntityUID.eid uid ∈ avail := by
  induction h with
  | nil => intro _; simp
  | cons =>
    rename_i hsr hpca hp hr hattrs hgo ih
    intro hnd
    obtain ⟨hndavail', hnotin⟩ := selectRemove_nodup hsr hnd
    obtain ⟨ihnd, ihmem⟩ := ih hndavail'
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => hnotin (ihmem _ hmem), ihnd⟩
    · intro uid huid
      simp only [List.map_cons, List.mem_cons] at huid
      rcases huid with rfl | huid
      · exact selectRemove_mem hsr
      · exact selectRemove_subset hsr _ (ihmem _ huid)

theorem wfActionSchema_nodup {ets entries} (h : Schema.WfActionSchema ets entries) :
    (entries.map Prod.fst).Nodup := by
  cases h with
  | mk hgo => exact (wfActionsGo_nodup hgo actionEidPool_nodup).1

/-- Action-store keys of a well-formed `TypeEnv` are distinct. -/
theorem wfTypeEnv_acts_nodup {env : TypeEnv} (h : Schema.WfTypeEnv env) :
    (env.acts.toList.map Prod.fst).Nodup := by
  cases h with
  | mk entityTypes entityEntries actionEntries reqty _ has _ =>
    simpa only [Map.toList] using wfActionSchema_nodup has

/-! ## Action ancestry -/

/-- `MaybeActionDescendentOf` mirrors `ActionSchema.maybeDescendentOf`. -/
theorem maybeActionDescendentOf_iff {acts : ActionSchema} {ety₁ ety₂ : EntityType} :
    MaybeActionDescendentOf acts ety₁ ety₂ ↔ acts.maybeDescendentOf ety₁ ety₂ = true := by
  simp only [ActionSchema.maybeDescendentOf, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Prod.exists, Set.any, beq_iff_eq]
  constructor
  · intro h
    cases h with
    | mk uid entry anc hmc hsc =>
      exact ⟨uid, entry, mapContains_mem hmc, rfl, anc, setContains_mem hsc, rfl⟩
  · rintro ⟨uid, entry, hmem, rfl, anc, hanc, rfl⟩
    exact .mk _ _ _ _ (mem_toList_mapContains hmem) (mem_elts_setContains hanc)

/-! ## Structural extractors ↔ schema lookups -/

theorem mapContainsAttrs_mc {ety rty ets} (h : MapContainsAttrs ety rty ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.attrs entry = rty := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsTagType_mc {ety ty ets} (h : MapContainsTagType ety ty ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.tags? entry = some ty := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsNoTags_mc {ety ets} (h : MapContainsNoTags ety ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.tags? entry = none := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsEnum_mc {ety eids ets} (h : MapContainsEnum ety eids ets) :
    MapContains ety (.enum eids) ets := by
  induction h with
  | here => exact MapContains.here _ _ _
  | there => rename_i ih; exact MapContains.there _ _ _ _ _ ih

theorem mapContainsAncestors_mc {ety ancs ets} (h : MapContainsAncestors ety ancs ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.ancestors entry = ancs := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsPairKey_mc {v : Type} {ety : EntityType} {eid : String} {entry : v}
    {acts : Map EntityUID v} (h : MapContainsPairKey ety eid entry acts) :
    MapContains ⟨ety, eid⟩ entry acts := by
  induction h with
  | here => exact MapContains.here _ _ _
  | nextA hne _ ih => exact MapContains.there _ _ _ _ _ ih
  | nextB hne _ ih => exact MapContains.there _ _ _ _ _ ih

/-- A `MapContainsPairKey` witness makes the type an action type (`actionType?`). -/
theorem mapContainsPairKey_actionType? {ety eid entry acts}
    (h : MapContainsPairKey ety eid entry acts) : ActionSchema.actionType? acts ety = true := by
  simp only [ActionSchema.actionType?, Set.any, Map.keys, Map.toList, List.any_eq_true]
  induction h with
  | here => exact ⟨_, List.mem_cons_self, by simp⟩
  | nextA hne hrec ih => obtain ⟨x, hx, hxe⟩ := ih; exact ⟨x, List.mem_cons_of_mem _ hx, hxe⟩
  | nextB hne hrec ih => obtain ⟨x, hx, hxe⟩ := ih; exact ⟨x, List.mem_cons_of_mem _ hx, hxe⟩

/-- `MapContainsAttrs` ⇒ `EntitySchema.attrs?` (on distinct-keyed store). -/
theorem mapContainsAttrs_attrs? {ety rty ets} (h : MapContainsAttrs ety rty ets)
    (hnd : (ets.toList.map Prod.fst).Nodup) : EntitySchema.attrs? ets ety = some rty := by
  obtain ⟨entry, hmc, he⟩ := mapContainsAttrs_mc h
  simp only [EntitySchema.attrs?, mapContains_find?_nodup hmc hnd, Option.map_some, he]

/-- `HasTagSchema` ⇒ `EntitySchema.tags? = some (some ty)`. -/
theorem hasTagSchema_tags? {ety ty ets} (h : HasTagSchema ets ety ty)
    (hnd : (ets.toList.map Prod.fst).Nodup) : EntitySchema.tags? ets ety = some (some ty) := by
  cases h with
  | mk hmct =>
    obtain ⟨entry, hmc, he⟩ := mapContainsTagType_mc hmct
    simp only [EntitySchema.tags?, mapContains_find?_nodup hmc hnd, Option.map_some, he]

/-- `NoTags` ⇒ `EntitySchema.tags? = some none`. -/
theorem noTags_tags? {ety ets} (h : NoTags ets ety)
    (hnd : (ets.toList.map Prod.fst).Nodup) : EntitySchema.tags? ets ety = some none := by
  cases h with
  | none hmcn =>
    obtain ⟨entry, hmc, he⟩ := mapContainsNoTags_mc hmcn
    simp only [EntitySchema.tags?, mapContains_find?_nodup hmc hnd, Option.map_some, he]
  | enum eids hmce =>
    have hmc := mapContainsEnum_mc hmce
    simp only [EntitySchema.tags?, mapContains_find?_nodup hmc hnd, Option.map_some,
      EntitySchemaEntry.tags?]

/-- `lub?` of two distinct entity types is `none`. -/
theorem lub_entity_ne {ety₁ ety₂ : EntityType} (h : ety₁ ≠ ety₂) :
    lub? (.entity ety₁) (.entity ety₂) = none := by
  simp only [lub?, CedarType.entity.injEq, ite_eq_right_iff]
  intro heq; exact absurd heq h

/-! ## Entity/action hierarchy ↔ `descendentOf` -/

/-- `DescendentOf` ⇒ `TypeEnv.descendentOf = true`. -/
theorem descendentOf_sound {ets acts ety₁ ety₂ reqty} (h : DescendentOf ets acts ety₁ ety₂)
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = true := by
  cases h with
  | refl => simp only [TypeEnv.descendentOf, ↓reduceIte]
  | ancestor =>
    rename_i hanc hsc
    by_cases heq : ety₁ = ety₂
    · simp only [TypeEnv.descendentOf, heq, ↓reduceIte]
    · obtain ⟨entry, hmc, he⟩ := mapContainsAncestors_mc hanc
      simp only [TypeEnv.descendentOf, ite_eq_right heq, mapContains_find?_nodup hmc hnd, he,
        (setContains_iff_contains).mp hsc]
  | action =>
    rename_i hnc hmd
    by_cases heq : ety₁ = ety₂
    · simp only [TypeEnv.descendentOf, heq, ↓reduceIte]
    · simp only [TypeEnv.descendentOf, heq, ↓reduceIte, mapNotContainsKey_find? hnc]
      exact maybeActionDescendentOf_iff.mp hmd

/-- `NotDescendentOf` ⇒ `TypeEnv.descendentOf = false`. -/
theorem notDescendentOf_sound {ets acts ety₁ ety₂ reqty} (h : NotDescendentOf ets acts ety₁ ety₂)
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = false := by
  cases h with
  | diff =>
    rename_i hne hanc hnsc
    obtain ⟨entry, hmc, he⟩ := mapContainsAncestors_mc hanc
    have hc : Set.contains _ ety₂ = false :=
      Bool.eq_false_iff.mpr (fun hcon => hnsc ((setContains_iff_contains).mpr hcon))
    simp only [TypeEnv.descendentOf, ite_eq_right hne, mapContains_find?_nodup hmc hnd, he, hc]
  | enum =>
    rename_i hne hmce
    have hmc := mapContainsEnum_mc hmce
    have hc : Set.contains (EntitySchemaEntry.enum ‹Set String›).ancestors ety₂ = false := by
      simp [EntitySchemaEntry.ancestors, Set.contains, Set.elts_empty]
    simp only [TypeEnv.descendentOf, ite_eq_right hne, mapContains_find?_nodup hmc hnd, hc]

/-- `ActionDescendentOf` ⇒ `ActionSchema.descendentOf = true`. -/
theorem actionDescendentOf_sound {acts uid₁ uid₂} (h : ActionDescendentOf acts uid₁ uid₂)
    (hnd : (acts.toList.map Prod.fst).Nodup) :
    ActionSchema.descendentOf acts uid₁ uid₂ = true := by
  cases h with
  | refl => simp only [ActionSchema.descendentOf, beq_self_eq_true, ↓reduceIte]
  | ancestor =>
    rename_i hmc hsc
    by_cases heq : uid₁ = uid₂
    · simp only [ActionSchema.descendentOf, heq, beq_self_eq_true, ↓reduceIte]
    · simp only [ActionSchema.descendentOf, beq_iff_eq, ite_eq_right heq,
        mapContains_find?_nodup hmc hnd, (setContains_iff_contains).mp hsc]

/-- `NotActionDescendentOf` ⇒ `ActionSchema.descendentOf = false`. -/
theorem notActionDescendentOf_sound {acts uid₁ uid₂} (h : NotActionDescendentOf acts uid₁ uid₂)
    (hnd : (acts.toList.map Prod.fst).Nodup) :
    ActionSchema.descendentOf acts uid₁ uid₂ = false := by
  cases h with
  | diff =>
    rename_i hne hmc hnsc
    have hc : Set.contains _ uid₂ = false :=
      Bool.eq_false_iff.mpr (fun hcon => hnsc ((setContains_iff_contains).mpr hcon))
    simp only [ActionSchema.descendentOf, beq_iff_eq, ite_eq_right hne,
      mapContains_find?_nodup hmc hnd, hc]

/-! ## `AllLub` ↔ `foldlM lub?` -/

/-- `AllLub` mirrors the `foldlM lub?` pass in `typeOfSet`. -/
theorem allLub_foldlM {acc tyList result} (h : AllLub acc tyList result) :
    tyList.foldlM lub? acc = some result := by
  induction h with
  | nil => simp [List.foldlM]
  | cons acc hd tl lubTy result hlub hrest ih =>
    rw [List.foldlM_cons, lub_sound hlub]; exact ih

/-! ## `ValidEntityUID` ↔ `typeOfLit` entity validity -/

/-- `ValidEntityUID` ⇒ the `typeOfLit` validity guard holds. -/
theorem validEntityUID_lit {ety eid ets acts}
    (h : ValidEntityUID ety eid ets acts)
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    (EntitySchema.isValidEntityUID ets ⟨ety, eid⟩ || ActionSchema.contains acts ⟨ety, eid⟩) = true := by
  cases h with
  | standard =>
    obtain ⟨entry, hmc⟩ : ∃ e, MapContains ety (EntitySchemaEntry.standard e) ets := ⟨_, by assumption⟩
    simp only [EntitySchema.isValidEntityUID, mapContains_find?_nodup hmc hndE,
      EntitySchemaEntry.isValidEntityEID, Bool.true_or]
  | enum =>
    obtain ⟨eids, hmc, hsc⟩ :
        ∃ eids, MapContains ety (EntitySchemaEntry.enum eids) ets ∧ SetContains eid eids :=
      ⟨_, by assumption, by assumption⟩
    simp only [EntitySchema.isValidEntityUID, mapContains_find?_nodup hmc hndE,
      EntitySchemaEntry.isValidEntityEID, (setContains_iff_contains).mp hsc, Bool.true_or]
  | action =>
    obtain ⟨entry, hpk⟩ : ∃ e, MapContainsPairKey ety eid e acts := ⟨_, by assumption⟩
    simp only [ActionSchema.contains, mapContains_find?_nodup (mapContainsPairKey_mc hpk) hndA,
      Option.isSome_some, Bool.or_true]

/-! ## `LubCompat` ⇒ `lub?` succeeds -/

mutual
/-- `LubCompat` ⇒ the two types have a least upper bound. -/
theorem lubCompat_lub? {t₁ t₂} (h : LubCompat t₁ t₂) : ∃ t, lub? t₁ t₂ = some t := by
  cases h with
  | bool b₁ b₂ => exact ⟨.bool (lubBool b₁ b₂), by simp [lub?]⟩
  | int => exact ⟨.int, by simp [lub?]⟩
  | string => exact ⟨.string, by simp [lub?]⟩
  | entity ety => exact ⟨.entity ety, by simp [lub?]⟩
  | ext xty => exact ⟨.ext xty, by simp [lub?]⟩
  | set s₁ s₂ hs => obtain ⟨t, ht⟩ := lubCompat_lub? hs; exact ⟨.set t, by simp [lub?, ht]⟩
  | record r₁ r₂ hr =>
    obtain ⟨r, hrr⟩ := lubCompatRecord_lubRecord hr; exact ⟨.record (.mk r), by simp [lub?, hrr]⟩
theorem lubCompatRecord_lubRecord {r₁ r₂} (h : LubCompatRecord r₁ r₂) :
    ∃ r, lubRecordType r₁ r₂ = some r := by
  cases h with
  | nil => exact ⟨[], by simp [lubRecordType]⟩
  | consReq k t₁ t₂ r₁ r₂ ht hr =>
    obtain ⟨t, htt⟩ := lubCompat_lub? ht; obtain ⟨r, hrr⟩ := lubCompatRecord_lubRecord hr
    exact ⟨(k, .required t) :: r, by simp [lubRecordType, lubQualifiedType, htt, hrr]⟩
  | consOpt k t₁ t₂ r₁ r₂ ht hr =>
    obtain ⟨t, htt⟩ := lubCompat_lub? ht; obtain ⟨r, hrr⟩ := lubCompatRecord_lubRecord hr
    exact ⟨(k, .optional t) :: r, by simp [lubRecordType, lubQualifiedType, htt, hrr]⟩
end

/-! ## Action-literal membership: `entityUID?`/`actionUID?` inversion + `typeOfIn` fallback -/

/-- `MapContains` reconstructs from `contains = true` (converse via `find?`). -/
theorem contains_mapContains {α β : Type} [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α]
    {k : α} {m : Map α β} (h : m.contains k = true) : ∃ v, MapContains k v m := by
  simp only [Map.contains, Option.isSome_iff_exists] at h
  obtain ⟨v, hv⟩ := h
  exact ⟨v, mem_toList_mapContains (Map.find?_mem_toList hv)⟩

theorem entityUID?_some {x : Expr} {uid : EntityUID} (h : entityUID? x = some uid) :
    x = .lit (.entityUID uid) := by unfold entityUID? at h; split at h <;> simp_all

theorem actionUID?_some {x : Expr} {acts : ActionSchema} {uid : EntityUID}
    (h : actionUID? x acts = some uid) : x = .lit (.entityUID uid) ∧ acts.contains uid = true := by
  unfold actionUID? at h
  cases he : entityUID? x with
  | none => rw [he] at h; simp at h
  | some uid' =>
    rw [he] at h
    have h2 : (if acts.contains uid' = true then some uid' else none) = some uid := h
    split at h2
    · rename_i hc; simp only [Option.some.injEq] at h2; subst h2; exact ⟨entityUID?_some he, hc⟩
    · exact absurd h2 (by simp)

theorem mapM_entityUID?_lits {xs : List Expr} {uids : List EntityUID}
    (h : xs.mapM entityUID? = some uids) : ∀ y ∈ xs, ∃ uid, y = .lit (.entityUID uid) := by
  induction xs generalizing uids with
  | nil => intro y hy; simp at hy
  | cons hd tl ih =>
    simp only [List.mapM_cons] at h
    cases hh : entityUID? hd with
    | none => rw [hh] at h; simp at h
    | some u =>
      rw [hh] at h
      cases ht : tl.mapM entityUID? with
      | none => rw [ht] at h; simp at h
      | some us =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨u, entityUID?_some hh⟩
        · exact ih (by rw [ht]) y hy

theorem entityUIDs?_some {x : Expr} {uids : List EntityUID} (h : entityUIDs? x = some uids) :
    ∃ xs, x = .set xs ∧ ∀ y ∈ xs, ∃ uid, y = .lit (.entityUID uid) := by
  unfold entityUIDs? at h
  split at h
  · rename_i xs; exact ⟨xs, rfl, mapM_entityUID?_lits h⟩
  · simp at h

/-- When `x₁ in x₂` is not a known action-literal membership, `typeOfInₑ` takes the
    entity-hierarchy fallback branch. -/
theorem typeOfInₑ_fallback {ety₁ ety₂ : EntityType} {x₁ x₂ : Expr} {env : TypeEnv}
    (h : ¬ IsActionLitMem x₁ x₂ env.acts) :
    typeOfInₑ ety₁ ety₂ x₁ x₂ env = if env.descendentOf ety₁ ety₂ then .anyBool else .ff := by
  unfold typeOfInₑ
  cases ha : actionUID? x₁ env.acts with
  | none => simp
  | some uid₁ =>
    cases he : entityUID? x₂ with
    | none => simp
    | some uid₂ =>
      exfalso
      obtain ⟨hx1, hcont⟩ := actionUID?_some ha
      obtain ⟨entry, hmc⟩ := contains_mapContains hcont
      refine h ?_; rw [hx1, entityUID?_some he]
      exact IsActionLitMem.mk uid₁ uid₂ env.acts entry hmc

/-- Set analogue of `typeOfInₑ_fallback`. -/
theorem typeOfInₛ_fallback {ety₁ ety₂ : EntityType} {x₁ x₂ : Expr} {env : TypeEnv}
    (h : ¬ IsActionLitMemSet x₁ x₂ env.acts) :
    typeOfInₛ ety₁ ety₂ x₁ x₂ env = if env.descendentOf ety₁ ety₂ then .anyBool else .ff := by
  unfold typeOfInₛ
  cases ha : actionUID? x₁ env.acts with
  | none => simp
  | some uid₁ =>
    cases he : entityUIDs? x₂ with
    | none => simp
    | some uids =>
      exfalso
      obtain ⟨hx1, hcont⟩ := actionUID?_some ha
      obtain ⟨entry, hmc⟩ := contains_mapContains hcont
      obtain ⟨xs, hxs, hall⟩ := entityUIDs?_some he
      refine h ?_; rw [hx1, hxs]
      exact IsActionLitMemSet.mk uid₁ xs env.acts entry hmc hall

/-! ## `typeOf` produces record types with distinct keys (`TyWf`) -/


/-- `WfAttrs` (with its `KeyAbove` threading) ⇒ strictly-ascending, hence distinct, keys. -/
theorem wfAttrs_keys {ets attrs} : ∀ {lb}, Schema.WfAttrs lb ets attrs →
    (attrs.map Prod.fst).Nodup ∧ ∀ k ∈ attrs.map Prod.fst, ∀ b, lb = some b → b < k := by
  induction attrs with
  | nil => intro lb h; simp
  | cons hd rest ih =>
    intro lb h; obtain ⟨a, q⟩ := hd
    have hstep : ∀ (attr : Attr), Schema.KeyAbove lb attr → Schema.WfAttrs (some attr) ets rest →
        ((attr :: rest.map Prod.fst).Nodup ∧
          ∀ k ∈ attr :: rest.map Prod.fst, ∀ b, lb = some b → b < k) := by
      intro attr hka hrest
      obtain ⟨ihnd, ihab⟩ := ih hrest
      have hka' : ∀ b, lb = some b → b < attr := by
        intro b hlb; cases hka with
        | none => exact absurd hlb (by simp)
        | some b' _ hlt => cases hlb; exact hlt
      refine ⟨by simp only [List.nodup_cons]; exact
        ⟨fun hmem => absurd (ihab attr hmem attr rfl) (StrictLT.irreflexive attr), ihnd⟩, ?_⟩
      intro k hk b hlb
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hka' b hlb
      · exact StrictLT.transitive _ _ _ (hka' b hlb) (ihab k hk attr rfl)
    cases h with
    | consRequired => simpa using hstep a (by assumption) (by assumption)
    | consOptional => simpa using hstep a (by assumption) (by assumption)

/-- `Schema.WfCedarType` types are `TyWf`: `WfAttrs` sorts record keys strictly. -/
theorem wfCedarType_tyWf {ets ty} (h : Schema.WfCedarType ets ty) : TyWf ty := by
  induction h using Schema.WfCedarType.rec (motive_2 := fun _ _ attrs _ =>
      ∀ q ∈ attrs.map Prod.snd, TyWfQ q) with
  | bool => exact TyWf.bool _
  | int => exact TyWf.int
  | string => exact TyWf.string
  | entity => exact TyWf.entity _
  | set _ _ _ ih => exact TyWf.set _ ih
  | record ets attrs hwa ihf =>
    exact TyWf.record (.mk attrs) (by simpa using (wfAttrs_keys hwa).1) (by simpa using ihf)
  | extDecimal => exact TyWf.ext _
  | extIPAddr => exact TyWf.ext _
  | extDatetime => exact TyWf.ext _
  | extDuration => exact TyWf.ext _
  | nil => rename_i q hq; simp at hq
  | consRequired _ _ attr ty rest hka hty hrest ihty ihrest =>
    rename_i q hq; simp only [List.map_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact TyWfQ.required _ ihty
    · exact ihrest q hq
  | consOptional _ _ attr ty rest hka hty hrest ihty ihrest =>
    rename_i q hq; simp only [List.map_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact TyWfQ.optional _ ihty
    · exact ihrest q hq

/-- `lub?` preserves `TyWf`: the least upper bound of two well-formed types is
    well-formed. Proven by functional induction on `lub?` (with motives for the
    mutually-recursive `lubQualifiedType`/`lubRecordType`). The record arm relies
    on `lubRecordType` keeping the left operand's keys, so `Nodup` transfers. -/
theorem lub_tyWf (ty₁ ty₂ : CedarType) :
    TyWf ty₁ → TyWf ty₂ → ∀ {t : CedarType}, lub? ty₁ ty₂ = some t → TyWf t := by
  induction ty₁, ty₂ using lub?.induct
    (motive_1 := fun q₁ q₂ =>
      TyWfQ q₁ → TyWfQ q₂ → ∀ {q}, lubQualifiedType q₁ q₂ = some q → TyWfQ q)
    (motive_3 := fun r₁ r₂ =>
      (∀ q ∈ r₁.map Prod.snd, TyWfQ q) → (∀ q ∈ r₂.map Prod.snd, TyWfQ q) →
        ∀ {r}, lubRecordType r₁ r₂ = some r →
          r.map Prod.fst = r₁.map Prod.fst ∧ ∀ q ∈ r.map Prod.snd, TyWfQ q) with
  | case1 b₁ b₂ =>
    intro _ _ a h; simp only [lub?, Option.some.injEq] at h; subst h; exact TyWf.bool _
  | case2 s₁ s₂ ih =>
    intro h1 h2 a h
    simp only [lub?] at h
    cases hlub : s₁ ⊔ s₂ with
    | none => rw [hlub] at h; simp at h
    | some lub =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      cases h1 with | set _ hs1 => cases h2 with | set _ hs2 =>
        exact TyWf.set _ (ih hs1 hs2 hlub)
  | case3 r₁ r₂ ih3 =>
    intro h1 h2 a h
    simp only [lub?] at h
    cases hlub : lubRecordType r₁ r₂ with
    | none => rw [hlub] at h; simp at h
    | some lub =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      cases h1 with | record _ hnd1 hfs1 => cases h2 with | record _ hnd2 hfs2 =>
        simp only [show (Map.mk r₁).toList = r₁ from rfl] at hnd1 hfs1
        simp only [show (Map.mk r₂).toList = r₂ from rfl] at hnd2 hfs2
        obtain ⟨hkeys, hfields⟩ := ih3 hfs1 hfs2 hlub
        refine TyWf.record _ ?_ ?_
        · simp only [show (Map.mk lub).toList = lub from rfl, hkeys]; exact hnd1
        · simp only [show (Map.mk lub).toList = lub from rfl]; exact hfields
  | case4 ty₂ _ _ _ =>
    intro h1 _ a h
    rw [Cedar.Thm.lub_refl] at h; simp only [Option.some.injEq] at h; subst h; exact h1
  | case5 a ty₂ hne _ _ _ =>
    intro _ _ t h
    simp only [lub?] at h; split at h <;> simp_all
  | case6 => rename_i _ _ r h; simp only [lubRecordType, Option.some.injEq] at h; subst h; simp
  | case7 k₁ v₁ r₁ k₂ v₂ r₂ hbne =>
    rename_i _ _ _ h; simp [lubRecordType, hbne] at h
  | case8 k₁ v₁ r₁ k₂ v₂ r₂ hbne ihq ihr =>
    rename_i hf1 hf2 r h
    have hk : k₁ = k₂ := by simpa using hbne
    subst hk
    simp only [lubRecordType] at h; rw [ite_eq_right hbne] at h
    cases hty : lubQualifiedType v₁ v₂ with
    | none => rw [hty] at h; simp at h
    | some ty =>
      cases htys : lubRecordType r₁ r₂ with
      | none => rw [hty, htys] at h; simp at h
      | some tys =>
        rw [hty, htys] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
        rw [List.map_cons, List.forall_mem_cons] at hf1 hf2
        obtain ⟨hv1, htl1⟩ := hf1
        obtain ⟨hv2, htl2⟩ := hf2
        obtain ⟨hkeys, hflds⟩ := ihr htl1 htl2 htys
        refine ⟨by simp only [List.map_cons, hkeys], ?_⟩
        intro q hq
        simp only [List.map_cons, List.mem_cons] at hq
        rcases hq with hq | hq
        · subst hq; exact ihq hv1 hv2 hty
        · exact hflds q hq
  | case9 t ty₂ _ _ =>
    rename_i _ _ _ h; simp [lubRecordType] at h
  | case10 ty₁ ty₂ ih =>
    rename_i hq1 hq2 q h
    simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      cases hq1 with | optional _ ht1 => cases hq2 with | optional _ ht2 =>
        exact TyWfQ.optional _ (ih ht1 ht2 hlub)
  | case11 ty₁ ty₂ ih =>
    rename_i hq1 hq2 q h
    simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      cases hq1 with | required _ ht1 => cases hq2 with | required _ ht2 =>
        exact TyWfQ.required _ (ih ht1 ht2 hlub)
  | case12 t q₂ _ _ =>
    rename_i _ _ _ h; simp [lubQualifiedType] at h

/-! ## `TyWf` preservation lemmas -/

/-- A strictly-sorted-by-`f` list has duplicate-free `f`-images. -/
theorem sortedBy_map_nodup {α β} [LT β] [StrictLT β] {f : α → β} {xs : List α}
    (h : List.SortedBy f xs) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (List.tail_sortedBy h)⟩
    intro hmem
    simp only [List.mem_map] at hmem
    obtain ⟨y, hy, hfy⟩ := hmem
    have hlt := List.sortedBy_implies_head_lt_tail h y hy
    rw [hfy] at hlt
    exact absurd hlt (StrictLT.irreflexive (f x))

/-- The value found by `Map.find?` in a `TyWf` record is itself well-formed. -/
theorem tyWf_record_find {rty : Map Attr QualifiedType} {a : Attr} {qty : QualifiedType}
    (h : TyWf (.record rty)) (hf : rty.find? a = some qty) : TyWfQ qty := by
  cases h with
  | record _ _ hfields => exact hfields _ (List.mem_map_of_mem (Map.find?_mem_toList hf))

/-- `foldlM lub?` over well-formed types yields a well-formed type. -/
theorem foldlM_lub_tyWf {init : CedarType} {rest : List CedarType} {ty : CedarType}
    (hinit : TyWf init) (hrest : ∀ t ∈ rest, TyWf t)
    (h : List.foldlM lub? init rest = some ty) : TyWf ty := by
  induction rest generalizing init with
  | nil => simp only [List.foldlM_nil, pure, Option.some.injEq] at h; subst h; exact hinit
  | cons hd tl ih =>
    simp only [List.foldlM_cons] at h
    cases hlub : lub? init hd with
    | none => rw [hlub] at h; simp at h
    | some m =>
      rw [hlub] at h; simp only [Option.bind_some_fun] at h
      exact ih (lub_tyWf init hd hinit (hrest hd (by simp)) hlub)
        (fun t ht => hrest t (by simp [ht])) h

/-- Every entry's attribute record in a well-formed entity schema is `TyWf`. -/
theorem wfEntitiesGo_mem_attrs_tyWf {built names allNames entries}
    (h : Schema.WfEntitiesGo built names allNames entries) :
    ∀ {ety : EntityType} {entry : EntitySchemaEntry}, (ety, entry) ∈ entries →
      TyWf (.record entry.attrs) := by
  induction h with
  | nil => intro ety entry hmem; simp at hmem
  | standard built names et ancestors attrs tags allNames rest hni hpick hwa hwt hrest ih =>
    intro ety entry hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp only [EntitySchemaEntry.attrs]
      exact wfCedarType_tyWf (Schema.WfCedarType.record (et :: names) attrs hwa)
    · exact ih hmem
  | enum built names et eids allNames rest hni hrest ih =>
    intro ety entry hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp only [EntitySchemaEntry.attrs]
      exact TyWf.record Map.empty (by simp [Map.empty, Map.toList]) (by simp [Map.empty, Map.toList])
    · exact ih hmem

/-- Every entry's tag type in a well-formed entity schema is `TyWf`. -/
theorem wfEntitiesGo_mem_tags_tyWf {built names allNames entries}
    (h : Schema.WfEntitiesGo built names allNames entries) :
    ∀ {ety entry ty}, (ety, entry) ∈ entries → EntitySchemaEntry.tags? entry = some ty →
      TyWf ty := by
  induction h with
  | nil => intro ety entry ty hmem _; simp at hmem
  | standard built names et ancestors attrs tags allNames rest hni hpick hwa hwt hrest ih =>
    intro ety entry ty hmem htag
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp only [EntitySchemaEntry.tags?] at htag
      cases hwt with
      | none => simp at htag
      | some ty' hwct =>
        simp only [Option.some.injEq] at htag; subst htag; exact wfCedarType_tyWf hwct
    · exact ih hmem htag
  | enum built names et eids allNames rest hni hrest ih =>
    intro ety entry ty hmem htag
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp [EntitySchemaEntry.tags?] at htag
    · exact ih hmem htag

/-- The request context comes from an action entry present in the action schema. -/
theorem requestFromAction_ctx_mem {ets acts reqty}
    (h : Schema.RequestFromAction ets acts reqty) :
    ∃ uid p r a ctx, reqty.context = Map.mk ctx ∧
      (uid, ActionSchemaEntry.mk p r a (Map.mk ctx)) ∈ acts := by
  induction h with
  | here acts uid principals resources ancestors context principal resource hp hr =>
    exact ⟨uid, Set.mk principals, Set.mk resources, Set.mk ancestors, context, rfl, by simp⟩
  | there act acts reqty hrfa ih =>
    obtain ⟨uid, p, r, a, ctx, hc, hmem⟩ := ih
    exact ⟨uid, p, r, a, ctx, hc, by simp [hmem]⟩

/-- Every action entry's context record in a well-formed action schema is `WfAttrs`. -/
theorem wfActionsGo_mem_ctx_wf {ets built avail entries}
    (h : Schema.WfActionsGo ets built avail entries) :
    ∀ {uid p r a ctx}, (uid, ActionSchemaEntry.mk p r a (Map.mk ctx)) ∈ entries →
      Schema.WfAttrs Option.none ets ctx := by
  induction h with
  | nil => intro uid p r a ctx hmem; simp at hmem
  | cons built avail avail' eid ancestors principals resources context rest
      hsel hpick hwp hwr hwa hrest ih =>
    intro uid p r a ctx hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq
      injection he with _ _ _ hctx; injection hctx with hcc; subst hcc; exact hwa
    · exact ih hmem

/-- Entity attributes looked up in a well-formed schema form a `TyWf` record. -/
theorem wfTypeEnv_attrs?_tyWf {env : TypeEnv} {ety rty}
    (hwf : Schema.WfTypeEnv env)
    (hattr : EntitySchema.attrs? env.ets ety = some rty) : TyWf (.record rty) := by
  cases hwf with
  | mk entityTypes entityEntries actionEntries reqty hes has hrfa =>
    simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattr
    obtain ⟨entry, hfind, hea⟩ := hattr
    have hmem := Map.find?_mem_toList hfind
    cases hes with
    | mk hgo => have h := wfEntitiesGo_mem_attrs_tyWf hgo hmem; rw [hea] at h; exact h

/-- An entity tag type looked up in a well-formed schema is `TyWf`. -/
theorem wfTypeEnv_tags?_tyWf {env : TypeEnv} {ety ty}
    (hwf : Schema.WfTypeEnv env)
    (htag : EntitySchema.tags? env.ets ety = some (some ty)) : TyWf ty := by
  cases hwf with
  | mk entityTypes entityEntries actionEntries reqty hes has hrfa =>
    simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htag
    obtain ⟨entry, hfind, hea⟩ := htag
    have hmem := Map.find?_mem_toList hfind
    cases hes with
    | mk hgo => exact wfEntitiesGo_mem_tags_tyWf hgo hmem hea

/-- The request context record type in a well-formed environment is `TyWf`. -/
theorem wfTypeEnv_context_tyWf {env : TypeEnv}
    (hwf : Schema.WfTypeEnv env) : TyWf (.record env.reqty.context) := by
  cases hwf with
  | mk entityTypes entityEntries actionEntries reqty hes has hrfa =>
    obtain ⟨uid, p, r, a, ctx, hc, hmem⟩ := requestFromAction_ctx_mem hrfa
    cases has with
    | mk hgo =>
      have hwa := wfActionsGo_mem_ctx_wf hgo hmem
      show TyWf (.record reqty.context)
      rw [hc]
      exact wfCedarType_tyWf (Schema.WfCedarType.record entityTypes ctx hwa)

/-! ## `TyWf` for each `typeOf` helper -/

theorem typeOfLit_tyWf {p env tx c'} (h : typeOfLit p env = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfLit] at h
  split at h
  case' h_5 => split at h
  all_goals simp only [ok, err, Function.comp, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, _⟩ := h
  all_goals first | exact TyWf.bool _ | exact TyWf.int | exact TyWf.string | exact TyWf.entity _

theorem typeOfVar_tyWf {v env tx c'} (hwf : EnvAssumptions env)
    (h : typeOfVar v env = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfVar] at h
  split at h <;>
    simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, _⟩ := h <;>
    simp only [TypedExpr.typeOf]
  · exact TyWf.entity _
  · exact TyWf.entity _
  · exact TyWf.entity _
  · exact hwf.context_tyWf

theorem typeOfUnaryApp_tyWf {op ty tx c'} (h : typeOfUnaryApp op ty = .ok (tx, c')) :
    TyWf tx.typeOf := by
  simp only [typeOfUnaryApp] at h
  split at h <;>
    simp only [ok, err, Function.comp, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, _⟩ := h <;>
    first | exact TyWf.bool _ | exact TyWf.int

theorem hasAttrInRecord_bool {rty x a c k bty c'}
    (h : hasAttrInRecord rty x a c k = .ok (bty, c')) : ∃ b, bty = .bool b := by
  simp only [hasAttrInRecord] at h
  split at h
  · split at h <;> (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩)
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩

theorem typeOfHasAttr_tyWf {ty x a c env tx c'}
    (h : typeOfHasAttr ty x a c env = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfHasAttr] at h
  split at h
  · cases hh : hasAttrInRecord _ x a c true with
    | error e => rw [hh] at h; simp at h
    | ok r =>
      obtain ⟨b1, b2⟩ := r
      rw [hh] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      obtain ⟨b, hb⟩ := hasAttrInRecord_bool hh
      simp only [TypedExpr.typeOf, hb]; exact TyWf.bool _
  · split at h
    · cases hh : hasAttrInRecord _ x a c false with
      | error e => rw [hh] at h; simp at h
      | ok r =>
        obtain ⟨b1, b2⟩ := r
        rw [hh] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        obtain ⟨b, hb⟩ := hasAttrInRecord_bool hh
        simp only [TypedExpr.typeOf, hb]; exact TyWf.bool _
    · split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
        exact TyWf.bool _
      · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem typeOfConstructor_result {α} {mk : String → Option α} {xs ty rty c'}
    (h : typeOfConstructor mk xs ty = .ok (rty, c')) : rty = ty := by
  simp only [typeOfConstructor] at h
  split at h
  · split at h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1.symm
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem IpAddrTypes.cons_all {tys : List CedarType} (h : IpAddrTypes tys) :
    ∃ t ts, tys = t :: ts ∧ (t :: ts).all (· == .ext .ipAddr) = true := by
  induction h with
  | one => exact ⟨_, _, rfl, by simp⟩
  | cons tys _ ih =>
    obtain ⟨t, ts, rfl, hall⟩ := ih
    exact ⟨_, _, rfl, by simp only [List.all_cons] at hall ⊢; simp [hall]⟩

theorem typeOfCall_tyWf {xfn tys xs tx c'}
    (h : typeOfCall xfn tys xs = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfCall] at h
  split at h <;>
    first
    | (cases hc : typeOfConstructor _ xs _ with
       | error e => rw [hc] at h; simp at h
       | ok r =>
         obtain ⟨r1, r2⟩ := r; rw [hc] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, _⟩ := h
         have hr := typeOfConstructor_result hc; subst hr
         simp only [TypedExpr.typeOf]; exact TyWf.ext _)
    | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
       simp only [TypedExpr.typeOf]
       first | exact TyWf.bool _ | exact TyWf.ext _ | exact TyWf.int)
    | (simp only [err, reduceCtorEq] at h)
    | (simp only [typeOfIsInRange] at h
       split at h
       · split at h
         · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
           simp only [TypedExpr.typeOf]; exact TyWf.bool _
         · simp only [err, reduceCtorEq] at h
       · simp only [err, reduceCtorEq] at h)

theorem typeOfAnd_tyWf {r₁ r₂ tx c'} (h : typeOfAnd r₁ r₂ = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfAnd] at h
  split at h <;>
    first
    | (rename_i heq; simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
       rw [heq]; exact TyWf.bool _)
    | (cases hr2 : r₂ with
       | error e => rw [hr2] at h; simp at h
       | ok p =>
         obtain ⟨t2, c2⟩ := p; rw [hr2] at h; simp only [Except.bind_ok] at h
         split at h <;>
           first
           | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
              simp only [TypedExpr.typeOf]; exact TyWf.bool _)
           | (simp only [err, reduceCtorEq] at h))
    | (simp only [err, reduceCtorEq] at h)

theorem typeOfOr_tyWf {r₁ r₂ tx c'} (h : typeOfOr r₁ r₂ = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfOr] at h
  split at h <;>
    first
    | (rename_i heq; simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
       rw [heq]; exact TyWf.bool _)
    | (cases hr2 : r₂ with
       | error e => rw [hr2] at h; simp at h
       | ok p =>
         obtain ⟨t2, c2⟩ := p; rw [hr2] at h; simp only [Except.bind_ok] at h
         split at h <;>
           first
           | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
              simp_all only [TypedExpr.typeOf]; exact TyWf.bool _)
           | (simp only [err, reduceCtorEq] at h))
    | (simp only [err, reduceCtorEq] at h)

theorem typeOfEq_tyWf {ty₁ ty₂ x₁ x₂ tx c'}
    (h : typeOfEq ty₁ ty₂ x₁ x₂ = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfEq] at h
  repeat' first
    | (simp only [ok] at h; obtain ⟨rfl, _⟩ := h
       simp only [TypedExpr.typeOf]; exact TyWf.bool _)
    | (simp only [err, reduceCtorEq] at h)
    | split at h

theorem typeOfHasTag_bool {ety x t c env ty c'}
    (h : typeOfHasTag ety x t c env = .ok (ty, c')) : ∃ b, ty = .bool b := by
  simp only [typeOfHasTag] at h
  repeat' first
    | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩)
    | (simp only [err, reduceCtorEq] at h)
    | split at h

theorem ifLubThenBool_bool {ty₁ ty₂ ty c'}
    (h : ifLubThenBool ty₁ ty₂ = .ok (ty, c')) : ∃ b, ty = .bool b := by
  simp only [ifLubThenBool] at h
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨_, h.1.symm⟩
  · simp only [err, reduceCtorEq] at h

theorem typeOfGetTag_tyWf {ety x t c env ty c'} (hwf : EnvAssumptions env)
    (h : typeOfGetTag ety x t c env = .ok (ty, c')) : TyWf ty := by
  simp only [typeOfGetTag] at h
  split at h
  · simp only [err, reduceCtorEq] at h
  · rename_i tagty htags
    split at h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      exact hwf.tags_tyWf htags
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem getAttrInRecord_tyWf {ty rty x a c aty c'}
    (hrec : TyWf (.record rty)) (h : getAttrInRecord ty rty x a c = .ok (aty, c')) : TyWf aty := by
  simp only [getAttrInRecord] at h
  split at h
  · rename_i aty' heqf
    have hq := tyWf_record_find hrec heqf
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
    cases hq with | required _ ht => exact ht
  · rename_i aty' heqf
    split at h
    · have hq := tyWf_record_find hrec heqf
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      cases hq with | optional _ ht => exact ht
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem typeOfGetAttr_tyWf {ty x a c env tx c'} (hwf : EnvAssumptions env)
    (hty : TyWf ty.typeOf) (h : typeOfGetAttr ty x a c env = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfGetAttr] at h
  split at h
  · rename_i rty heqty
    cases hg : getAttrInRecord ty.typeOf rty x a c with
    | error e => rw [hg] at h; simp at h
    | ok r =>
      obtain ⟨aty, ac⟩ := r; rw [hg] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      simp only [TypedExpr.typeOf]
      have hrec : TyWf (.record rty) := by rw [← heqty]; exact hty
      exact getAttrInRecord_tyWf hrec hg
  · rename_i ety heqty
    split at h
    · rename_i rty hattr
      cases hg : getAttrInRecord ty.typeOf rty x a c with
      | error e => rw [hg] at h; simp at h
      | ok r =>
        obtain ⟨aty, ac⟩ := r; rw [hg] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
        simp only [TypedExpr.typeOf]
        exact getAttrInRecord_tyWf (hwf.attrs_tyWf hattr) hg
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem typeOfBinaryApp_tyWf {op ty₁ ty₂ x₁ x₂ c env tx c'} (hwf : EnvAssumptions env)
    (h : typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c env = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfBinaryApp] at h
  split at h <;>
    first
    | exact typeOfEq_tyWf h
    | (cases hs : typeOfGetTag _ x₁ x₂ c env with
       | error e => rw [hs] at h; simp at h
       | ok r =>
         obtain ⟨rty, rc⟩ := r; rw [hs] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
         simp only [TypedExpr.typeOf]; exact typeOfGetTag_tyWf hwf hs)
    | (cases hs : typeOfHasTag _ x₁ x₂ c env with
       | error e => rw [hs] at h; simp at h
       | ok r =>
         obtain ⟨rty, rc⟩ := r; rw [hs] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
         obtain ⟨b, hb⟩ := typeOfHasTag_bool hs
         simp only [TypedExpr.typeOf, hb]; exact TyWf.bool _)
    | (cases hs : ifLubThenBool _ _ with
       | error e => rw [hs] at h; simp at h
       | ok r =>
         obtain ⟨rty, rc⟩ := r; rw [hs] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
         obtain ⟨b, hb⟩ := ifLubThenBool_bool hs
         simp only [TypedExpr.typeOf, hb]; exact TyWf.bool _)
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
       obtain ⟨rfl, _⟩ := h; simp only [TypedExpr.typeOf]
       first | exact TyWf.bool _ | exact TyWf.int)
    | (simp only [err, reduceCtorEq] at h)

theorem typeOfIf_tyWf {r₁ r₂ r₃ tx c'}
    (h2 : ∀ t2 cc2, r₂ = .ok (t2, cc2) → TyWf t2.typeOf)
    (h3 : ∀ t3 cc3, r₃ = .ok (t3, cc3) → TyWf t3.typeOf)
    (h : typeOfIf r₁ r₂ r₃ = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfIf] at h
  split at h
  · cases hr2 : r₂ with
    | error e => rw [hr2] at h; simp at h
    | ok p =>
      obtain ⟨t2, cc2⟩ := p; rw [hr2] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      simp only [TypedExpr.typeOf]; exact h2 t2 cc2 hr2
  · cases hr3 : r₃ with
    | error e => rw [hr3] at h; simp at h
    | ok p =>
      obtain ⟨t3, cc3⟩ := p; rw [hr3] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      simp only [TypedExpr.typeOf]; exact h3 t3 cc3 hr3
  · cases hr2 : r₂ with
    | error e => rw [hr2] at h; simp at h
    | ok p2 =>
      obtain ⟨t2, cc2⟩ := p2; rw [hr2] at h; simp only [Except.bind_ok] at h
      cases hr3 : r₃ with
      | error e => rw [hr3] at h; simp at h
      | ok p3 =>
        obtain ⟨t3, cc3⟩ := p3; rw [hr3] at h; simp only [Except.bind_ok] at h
        split at h
        · rename_i ty hlub
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
          simp only [TypedExpr.typeOf]
          exact lub_tyWf _ _ (h2 t2 cc2 hr2) (h3 t3 cc3 hr3) hlub
        · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem typeOfSet_tyWf {tys tx c'} (htys : ∀ t ∈ tys, TyWf (TypedExpr.typeOf t))
    (h : typeOfSet tys = .ok (tx, c')) : TyWf tx.typeOf := by
  simp only [typeOfSet] at h
  split at h
  · simp only [err, reduceCtorEq] at h
  · rename_i hd tl
    split at h
    · rename_i ty hfold
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      simp only [TypedExpr.typeOf]
      refine TyWf.set _ (foldlM_lub_tyWf (htys hd (by simp)) ?_ hfold)
      intro t ht; simp only [List.mem_map] at ht
      obtain ⟨t', ht', rfl⟩ := ht; exact htys t' (by simp [ht'])
    · simp only [err, reduceCtorEq] at h

/-- Every element type produced by the `set` element pass (`mapM`) is `TyWf`. -/
theorem mapM_forall_tyWf {xs : List Expr} {c : Capabilities} {env tys}
    (ih : ∀ x ∈ xs, ∀ {tx cc}, typeOf x c env = .ok (tx, cc) → TyWf (TypedExpr.typeOf tx))
    (hm : xs.mapM (fun x => justType (typeOf x c env)) = .ok tys) :
    ∀ t ∈ tys, TyWf (TypedExpr.typeOf t) := by
  induction xs generalizing tys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm; subst hm; simp
  | cons hd tl ih2 =>
    simp only [List.mapM_cons] at hm
    cases hhd : justType (typeOf hd c env) with
    | error e => rw [hhd] at hm; simp at hm
    | ok thd =>
      rw [hhd] at hm; simp only [Except.bind_ok] at hm
      cases htl : tl.mapM (fun x => justType (typeOf x c env)) with
      | error e => rw [htl] at hm; simp at hm
      | ok ttl =>
        rw [htl] at hm
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at hm
        subst hm
        intro t ht; simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · cases hhd2 : typeOf hd c env with
          | error e => rw [hhd2] at hhd; simp [justType, Except.map] at hhd
          | ok v =>
            have hvt : v.fst = t := by
              rw [hhd2] at hhd; simp only [justType, Except.map, Except.ok.injEq] at hhd; exact hhd
            exact ih hd (by simp) (show typeOf hd c env = .ok (t, v.2) by rw [hhd2, ← hvt])
        · exact ih2 (fun x hx => ih x (by simp [hx])) htl t ht

/-- Every field type produced by the `record` element pass (`mapM₂`) is `TyWf`. -/
theorem mapM₂_record_forall_tyWf {axs : List (Attr × Expr)} {c : Capabilities} {env atys}
    (ih : ∀ p ∈ axs, ∀ {tx cc}, typeOf p.2 c env = .ok (tx, cc) → TyWf (TypedExpr.typeOf tx))
    (hm : axs.mapM (fun p => (typeOf p.2 c env).map (fun r => (p.1, r.1))) = .ok atys) :
    ∀ q ∈ atys, TyWf (TypedExpr.typeOf q.2) := by
  induction axs generalizing atys with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm; subst hm; simp
  | cons hd tl ih2 =>
    simp only [List.mapM_cons] at hm
    cases hhd : (typeOf hd.2 c env).map (fun r => (hd.1, r.1)) with
    | error e => rw [hhd] at hm; simp at hm
    | ok qhd =>
      rw [hhd] at hm; simp only [Except.bind_ok] at hm
      cases htl : tl.mapM (fun p => (typeOf p.2 c env).map (fun r => (p.1, r.1))) with
      | error e => rw [htl] at hm; simp at hm
      | ok qtl =>
        rw [htl] at hm; simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at hm
        subst hm
        intro q hq; simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · cases hhd2 : typeOf hd.2 c env with
          | error e => rw [hhd2] at hhd; simp [Except.map] at hhd
          | ok v =>
            rw [hhd2] at hhd; simp only [Except.map, Except.ok.injEq] at hhd
            rw [← hhd]; exact ih hd (by simp) (by rw [hhd2])
        · exact ih2 (fun p hp => ih p (by simp [hp])) htl q hq

/-- `typeOf` produces canonical (`TyWf`) types on a well-formed environment. This
    is the invariant that makes `Map.find?` on a record-typed receiver agree with
    the structural attribute witness in the `getAttr`/`hasAttr` soundness cases. -/
theorem typeOf_tyWf {env : TypeEnv} (hwf : EnvAssumptions env) :
    ∀ {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      typeOf x c env = .ok (tx, c') → TyWf tx.typeOf := by
  intro x c
  induction x, c using typeOf.induct with
  | case1 c p => intro tx c' h; simp only [typeOf] at h; exact typeOfLit_tyWf h
  | case2 c v => intro tx c' h; simp only [typeOf] at h; exact typeOfVar_tyWf hwf h
  | case3 c x₁ x₂ x₃ ih1 ih2 ih3 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      exact typeOfIf_tyWf (fun t2 cc2 he => ih2 cc1 he) (fun t3 cc3 he => ih3 he) h
  | case4 c x₁ x₂ ih1 ih2 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      exact typeOfAnd_tyWf h
  | case5 c x₁ x₂ ih1 ih2 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      exact typeOfOr_tyWf h
  | case6 c op₁ x₁ ih1 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      exact typeOfUnaryApp_tyWf h
  | case7 c op₂ x₁ x₂ ih1 ih2 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      cases h2 : typeOf x₂ c env with
      | error e => rw [h2] at h; simp at h
      | ok r2 =>
        obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h; simp only [Except.bind_ok] at h
        exact typeOfBinaryApp_tyWf hwf h
  | case8 c x₁ a ih1 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      exact typeOfHasAttr_tyWf h
  | case9 c x₁ a as ih1 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      cases h2 : typeOfExtHasAttr ty1 x₁ (a :: as) c env with
      | error e => rw [h2] at h; simp at h
      | ok r2 =>
        obtain ⟨bty, cc2⟩ := r2; rw [h2] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp only [TypedExpr.typeOf]
        exact TyWf.bool _
  | case10 c x₁ a ih1 =>
    intro tx c' h; simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      exact typeOfGetAttr_tyWf hwf (ih1 h1) h
  | case11 c xs ih =>
    intro tx c' h
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
    | error e => rw [hm] at h; simp at h
    | ok tys =>
      rw [hm] at h; simp only [Except.bind_ok] at h
      exact typeOfSet_tyWf (mapM_forall_tyWf ih hm) h
  | case12 c axs ih =>
    intro tx c' h
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1)))] at h
    cases hm : axs.mapM (fun p => (typeOf p.2 c env).map (fun r => (p.1, r.1))) with
    | error e => rw [hm] at h; simp at h
    | ok atys =>
      rw [hm] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [TypedExpr.typeOf]
      have hfields := mapM₂_record_forall_tyWf
        (fun p hp => ih p.1 p.2 (by
          have h := List.sizeOf_lt_of_mem hp
          obtain ⟨a, x⟩ := p
          simp only [sizeOf, Prod._sizeOf_1] at *
          omega)) hm
      refine TyWf.record _ ?_ ?_
      · rw [Map.toList_make_eq_canonicalize]
        exact sortedBy_map_nodup (List.canonicalize_sortedBy Prod.fst _)
      · intro q hq
        have hval := Map.mem_values_make (v := q) hq
        simp only [List.map_map, Function.comp, List.mem_map] at hval
        obtain ⟨⟨a, ty⟩, hp, rfl⟩ := hval
        exact TyWfQ.required _ (hfields (a, ty) hp)
  | case13 c xfn xs ih =>
    intro tx c' h; simp only [typeOf] at h
    cases hm : xs.mapM₁ (fun x => justType (typeOf x.1 c env)) with
    | error e => rw [hm] at h; simp at h
    | ok tys => rw [hm] at h; simp only [Except.bind_ok] at h; exact typeOfCall_tyWf h

/-! ## Sorting record literals -/

/-- Inserting an attribute into a list by key, then relating elementwise, is relating
    elementwise, then inserting with `List.insertCanonical`. -/
theorem insertSortedField_forall₂ {β : Type} {R : Attr × Expr → Attr × β → Prop}
    (hR : ∀ {ax r}, R ax r → r.1 = ax.1) {ax : Attr × Expr} {axs axs' : List (Attr × Expr)}
    (h : InsertSortedField ax axs axs') :
    ∀ {rs' : List (Attr × β)}, List.Forall₂ R axs' rs' →
      ∃ r rs, R ax r ∧ List.Forall₂ R axs rs ∧ List.insertCanonical Prod.fst r rs = rs' := by
  induction h with
  | nil a x =>
    intro rs' h
    cases h with
    | cons hr hrest => cases hrest; exact ⟨_, [], hr, .nil, rfl⟩
  | here a x a' x' axs hlt =>
    intro rs' h
    cases h with
    | cons hr hrest =>
      cases hrest with
      | cons hr' hrest' =>
        refine ⟨_, _, hr, .cons hr' hrest', ?_⟩
        simp only [List.insertCanonical, hR hr, hR hr', hlt, ↓reduceIte]
  | there a x a' x' axs axs' hlt _ ih =>
    intro rs' h
    cases h with
    | cons hr' hrest =>
      obtain ⟨r, rs, hr, hrs, heq⟩ := ih hrest
      refine ⟨r, _, hr, .cons hr' hrs, ?_⟩
      simp only [List.insertCanonical, hR hr, hR hr', StrictLT.asymmetric a' a hlt, hlt,
        ↓reduceIte, heq]

/-- Typing a record literal's attribute keeps its key. -/
theorem typeOfAttr_key {c : Capabilities} {env : TypeEnv} {ax : Attr × Expr}
    {r : Attr × TypedExpr} (h : (typeOf ax.2 c env).map (fun r => (ax.1, r.1)) = .ok r) :
    r.1 = ax.1 := by
  simp only [Except.map] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h; rfl

/-- Sorting a record literal's attributes, then relating elementwise, is relating elementwise,
    then canonicalizing with `List.canonicalize Prod.fst`. -/
theorem sortsTo_forall₂ {β : Type} {R : Attr × Expr → Attr × β → Prop}
    (hR : ∀ {ax r}, R ax r → r.1 = ax.1) {axs axs' : List (Attr × Expr)} (h : SortsTo axs axs') :
    ∀ {rs' : List (Attr × β)}, List.Forall₂ R axs' rs' →
      ∃ rs, List.Forall₂ R axs rs ∧ List.canonicalize Prod.fst rs = rs' := by
  induction h with
  | nil => intro rs' h; cases h; exact ⟨[], .nil, rfl⟩
  | cons ax axs axs' axs'' _ hins ih =>
    intro rs'' h
    obtain ⟨r, rs', hr, hrs', heq⟩ := insertSortedField_forall₂ hR hins h
    obtain ⟨rs, hrs, heq'⟩ := ih hrs'
    exact ⟨r :: rs, .cons hr hrs, by simp only [List.canonicalize, heq', heq]⟩

/-- `InsertSortedField` computes `List.insertCanonical Prod.fst`. -/
theorem insertSortedField_insertCanonical {ax : Attr × Expr} {axs axs' : List (Attr × Expr)}
    (h : InsertSortedField ax axs axs') : List.insertCanonical Prod.fst ax axs = axs' := by
  induction h with
  | nil => simp only [List.insertCanonical]
  | here a x a' x' axs hlt => simp only [List.insertCanonical, hlt, ↓reduceIte]
  | there a x a' x' axs axs' hlt _ ih =>
    simp only [List.insertCanonical, StrictLT.asymmetric a' a hlt, hlt, ↓reduceIte, ih]

/-- `SortsTo` computes `List.canonicalize Prod.fst`. -/
theorem sortsTo_canonicalize {axs axs' : List (Attr × Expr)} (h : SortsTo axs axs') :
    List.canonicalize Prod.fst axs = axs' := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ hins ih =>
    simp only [List.canonicalize, ih, insertSortedField_insertCanonical hins]

/-- A list of entity-UID literals maps under `entityUID?` to `some` list. -/
theorem mapM_entityUID?_all_lits {xs : List Expr}
    (h : ∀ x ∈ xs, ∃ uid, x = .lit (.entityUID uid)) :
    ∃ uids, xs.mapM entityUID? = some uids := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons hd tl ih =>
    obtain ⟨uid, rfl⟩ := h hd (by simp)
    obtain ⟨uids, huids⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨uid :: uids, by simp [List.mapM_cons, entityUID?, huids]⟩

/-- `ActionInSet` (some element is an action descendent) implies the functional
    `uids.any (acts.descendentOf uid₁ ·)` holds, given the elements are the UID
    literals of `uids`. -/
theorem actionInSet_any {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr}
    {uids : List EntityUID} (h : ActionInSet acts uid₁ xs)
    (huids : xs.mapM entityUID? = some uids) (hnd : (acts.toList.map Prod.fst).Nodup) :
    uids.any (fun u => acts.descendentOf uid₁ u) = true := by
  induction h generalizing uids with
  | here uid₂ rest hdesc =>
    simp only [List.mapM_cons, entityUID?] at huids
    cases hr : rest.mapM entityUID? with
    | none => rw [hr] at huids; simp at huids
    | some ruids =>
      rw [hr] at huids
      simp only [Option.bind_some_fun, Option.pure_def, Option.some.injEq] at huids
      subst huids
      simp only [List.any_cons, actionDescendentOf_sound hdesc hnd, Bool.true_or]
  | there x rest hin ih =>
    simp only [List.mapM_cons] at huids
    cases hx : entityUID? x with
    | none => rw [hx] at huids; simp at huids
    | some ux =>
      rw [hx] at huids
      cases hr : rest.mapM entityUID? with
      | none => rw [hr] at huids; simp at huids
      | some ruids =>
        rw [hr] at huids
        simp only [Option.bind_some_fun, Option.pure_def, Option.some.injEq] at huids
        subst huids
        simp only [List.any_cons, ih hr, Bool.or_true]

/-- Completeness of `ActionSchema.descendentOf` into `ActionDescendentOf` (given the
    source action is present). Reverse of `actionDescendentOf_sound`. -/
theorem descendentOf_actionDescendentOf {acts : ActionSchema} {uid₁ u : EntityUID} {entry}
    (hmc : MapContains uid₁ entry acts) (hnd : (acts.toList.map Prod.fst).Nodup)
    (h : acts.descendentOf uid₁ u = true) : ActionDescendentOf acts uid₁ u := by
  simp only [ActionSchema.descendentOf] at h
  split at h
  · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
    exact ActionDescendentOf.refl _ _ _ hmc
  · simp only [mapContains_find?_nodup hmc hnd] at h
    exact ActionDescendentOf.ancestor _ _ _ _ hmc ((setContains_iff_contains).mpr h)

/-- If some UID in `uids` (the literals of `xs`) is an action-descendent of `uid₁`,
    then `ActionInSet` holds. Reverse of `actionInSet_any`. -/
theorem actionInSet_of_mem {acts : ActionSchema} {uid₁ : EntityUID} {xs : List Expr}
    {uids : List EntityUID} {u : EntityUID}
    (huids : xs.mapM entityUID? = some uids) (hmem : u ∈ uids)
    (hdesc : ActionDescendentOf acts uid₁ u) : ActionInSet acts uid₁ xs := by
  induction xs generalizing uids with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at huids; subst huids
    simp at hmem
  | cons hd tl ih =>
    simp only [List.mapM_cons] at huids
    cases hhd : entityUID? hd with
    | none => rw [hhd] at huids; simp at huids
    | some uhd =>
      rw [hhd] at huids
      cases htl : tl.mapM entityUID? with
      | none => rw [htl] at huids; simp at huids
      | some ruids =>
        rw [htl] at huids
        simp only [Option.bind_some_fun, Option.pure_def, Option.some.injEq] at huids
        subst huids
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · rw [entityUID?_some hhd]; exact ActionInSet.here _ _ _ _ hdesc
        · exact ActionInSet.there _ _ _ _ (ih htl hmem)

/-! ## Main soundness theorem -/

/-! ## The extended `has` chain

The chain's steps take the receiver's type as an input, so their soundness lemmas hold for any
receiver `tx` of that type; `tx` is not retyped. -/

/-- `HasAttrOn` agrees with `typeOfHasAttr`, capabilities included. -/
theorem hasAttrOn_sound {env : TypeEnv} {ty : CedarType} {x : Expr} {a : Attr}
    {c : Capabilities} {b : BoolType} {ci : Capabilities}
    (hwf : EnvAssumptions env) (h : HasAttrOn env ty x a c b ci)
    {tx : TypedExpr} (ht : tx.typeOf = ty) (htw : TyWf ty) :
    typeOfHasAttr tx x a c env = .ok (.hasAttr tx a (.bool b), ci) := by
  cases h with
  | record _ rty _ _ _ _ _ hin =>
    have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
    cases hin with
    | found_in_caps _ qty hcap hmc =>
      try simp only [id_eq] at hmc
      simp [typeOfHasAttr, ht, hasAttrInRecord, mapContains_find?_nodup hmc hnd,
        capAttrMem_iff.mp hcap, ok]
    | found_required_known ty' hmc =>
      simp [typeOfHasAttr, ht, hasAttrInRecord, mapContains_find?_nodup hmc hnd,
        Qualified.isRequired, ok]
    | found_optional_known ty' hmc hcap =>
      have hcapneg : ¬ ((x, Key.attr a) ∈ c) := fun hm => hcap (capAttrMem_iff.mpr hm)
      simp [typeOfHasAttr, ht, hasAttrInRecord, mapContains_find?_nodup hmc hnd,
        Qualified.isRequired, hcapneg, ok, Capabilities.singleton]
  | recordNotFound _ rts _ _ _ hnk =>
    simp only [typeOfHasAttr, ht, hasAttrInRecord, mapNotContainsKey_find? hnk, ok]; rfl
  | entity ets acts reqty ety rty _ _ _ _ _ hma hin =>
    have hattr := mapContainsAttrs_attrs? hma hwf.ets_keys_nodup
    have hnd : (rty.toList.map Prod.fst).Nodup := by
      cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
    cases hin with
    | found_in_caps _ qty hcap hmc =>
      try simp only [id_eq] at hmc
      simp [typeOfHasAttr, ht, hattr, hasAttrInRecord, mapContains_find?_nodup hmc hnd,
        capAttrMem_iff.mp hcap, ok]
    | found_not_known qty hmc hcap =>
      have hcapneg : ¬ ((x, Key.attr a) ∈ c) := fun hm => hcap (capAttrMem_iff.mpr hm)
      simp [typeOfHasAttr, ht, hattr, hasAttrInRecord, mapContains_find?_nodup hmc hnd,
        hcapneg, ok, Capabilities.singleton]
  | entityNotFound ets acts reqty ety rty _ _ _ hma hnk =>
    have hattr := mapContainsAttrs_attrs? hma hwf.ets_keys_nodup
    simp only [typeOfHasAttr, ht, hattr, hasAttrInRecord, mapNotContainsKey_find? hnk, ok]; rfl
  | enum ets acts reqty ety eids _ _ _ hme =>
    have hfind := mapContains_find?_nodup (mapContainsEnum_mc hme) hwf.ets_keys_nodup
    have hattr : EntitySchema.attrs? ets ety = some Map.empty := by
      simp only [EntitySchema.attrs?, hfind, Option.map_some, EntitySchemaEntry.attrs]
    simp only [typeOfHasAttr, ht, hattr, hasAttrInRecord,
      show (Map.empty : RecordType).find? a = none from rfl, ok]; rfl
  | action ets acts reqty ety eid entry _ _ _ hnc hpk =>
    simp only [typeOfHasAttr, ht, EntitySchema.attrs?, mapNotContainsKey_find? hnc, Option.map,
      mapContainsPairKey_actionType? hpk, ite_true, ok]; rfl

/-- `GetAttrOn` agrees with `typeOfGetAttr`. -/
theorem getAttrOn_sound {env : TypeEnv} {ty : CedarType} {x : Expr} {a : Attr}
    {c : Capabilities} {aty : CedarType}
    (hwf : EnvAssumptions env) (h : GetAttrOn env ty x a c aty)
    {tx : TypedExpr} (ht : tx.typeOf = ty) (htw : TyWf ty) :
    typeOfGetAttr tx x a c env = .ok (.getAttr tx a aty, ∅) := by
  cases h with
  | record _ rty _ _ _ _ hg =>
    have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
    cases hg with
    | required hmc =>
      simp only [typeOfGetAttr, ht, getAttrInRecord, mapContains_find?_nodup hmc hnd,
        Except.bind_ok, ok]
    | optional hcap hmc =>
      simp only [id_eq] at hmc
      simp only [typeOfGetAttr, ht, getAttrInRecord, mapContains_find?_nodup hmc hnd,
        ite_eq_left (capAttrMem_iff.mp hcap), Except.bind_ok, ok]
  | entity ets acts reqty ety rty _ _ _ _ hma hg =>
    have hattr := mapContainsAttrs_attrs? hma hwf.ets_keys_nodup
    have hnd : (rty.toList.map Prod.fst).Nodup := by
      cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
    cases hg with
    | required hmc =>
      simp only [typeOfGetAttr, ht, hattr, getAttrInRecord, mapContains_find?_nodup hmc hnd,
        Except.bind_ok, ok]
    | optional hcap hmc =>
      simp only [id_eq] at hmc
      simp only [typeOfGetAttr, ht, hattr, getAttrInRecord, mapContains_find?_nodup hmc hnd,
        ite_eq_left (capAttrMem_iff.mp hcap), Except.bind_ok, ok]

/-- `ExtHasAttrChain` agrees with `typeOfExtHasAttr`, capabilities up to `CapsEquiv`. -/
theorem extHasAttrChain_sound {env : TypeEnv} (hwf : EnvAssumptions env)
    {ty : CedarType} {x : Expr} {a : Attr} {as : List Attr} {c : Capabilities}
    {b : BoolType} {cout : Capabilities} (h : ExtHasAttrChain env ty x a as c b cout) :
    ∀ {tx : TypedExpr}, tx.typeOf = ty → TyWf ty →
      ∃ c', typeOfExtHasAttr tx x (a :: as) c env = .ok (b, c') ∧ CapsEquiv cout c' := by
  induction h with
  | last _ _ _ _ _ _ hha =>
    intro tx ht htw
    exact ⟨_, by simp only [typeOfExtHasAttr, hasAttrOn_sound hwf hha ht htw, Except.bind_ok,
      TypedExpr.typeOf], CapsEquiv.refl _⟩
  | absent _ _ _ _ _ _ _ hha =>
    intro tx ht htw
    exact ⟨_, by simp only [typeOfExtHasAttr, hasAttrOn_sound hwf hha ht htw, Except.bind_ok,
      TypedExpr.typeOf], CapsEquiv.refl _⟩
  | restFf _ x a _ _ c _ ci cc tyNext _ hha hnf hm hga _ ih =>
    intro tx ht htw
    have hcc : CapsEquiv cc (c ∪ ci) := capMerge_capsEquiv_union hm
    have hg := getAttrOn_sound hwf hga ht htw
    rw [typeOfGetAttr_capsEquiv hcc] at hg
    have htwN : TyWf tyNext := typeOfGetAttr_tyWf hwf (ht ▸ htw) hg
    obtain ⟨_, hr, _⟩ := ih (tx := .getAttr tx a tyNext) rfl htwN
    rw [typeOfExtHasAttr_capsEquiv hcc] at hr
    refine ⟨∅, ?_, CapsEquiv.refl _⟩
    cases hnf <;> simp only [typeOfExtHasAttr, hasAttrOn_sound hwf hha ht htw, Except.bind_ok,
      TypedExpr.typeOf, hg, hr]
  | restTt _ x a _ _ c _ ci cc tyNext cr _ hha hnf hm hga _ hm2 ih =>
    intro tx ht htw
    have hcc : CapsEquiv cc (c ∪ ci) := capMerge_capsEquiv_union hm
    have hg := getAttrOn_sound hwf hga ht htw
    rw [typeOfGetAttr_capsEquiv hcc] at hg
    have htwN : TyWf tyNext := typeOfGetAttr_tyWf hwf (ht ▸ htw) hg
    obtain ⟨cr', hr, hce⟩ := ih (tx := .getAttr tx a tyNext) rfl htwN
    rw [typeOfExtHasAttr_capsEquiv hcc] at hr
    refine ⟨ci ∪ cr', ?_,
      (capMerge_capsEquiv_union hm2).trans (CapsEquiv.union (CapsEquiv.refl ci) hce)⟩
    cases hnf <;> simp only [typeOfExtHasAttr, hasAttrOn_sound hwf hha ht htw, Except.bind_ok,
      TypedExpr.typeOf, hg, hr]
  | restAnyBool _ x a _ _ c _ ci cc tyNext cr _ hha hnf hm hga _ hm2 ih =>
    intro tx ht htw
    have hcc : CapsEquiv cc (c ∪ ci) := capMerge_capsEquiv_union hm
    have hg := getAttrOn_sound hwf hga ht htw
    rw [typeOfGetAttr_capsEquiv hcc] at hg
    have htwN : TyWf tyNext := typeOfGetAttr_tyWf hwf (ht ▸ htw) hg
    obtain ⟨cr', hr, hce⟩ := ih (tx := .getAttr tx a tyNext) rfl htwN
    rw [typeOfExtHasAttr_capsEquiv hcc] at hr
    refine ⟨ci ∪ cr', ?_,
      (capMerge_capsEquiv_union hm2).trans (CapsEquiv.union (CapsEquiv.refl ci) hce)⟩
    cases hnf <;> simp only [typeOfExtHasAttr, hasAttrOn_sound hwf hha ht htw, Except.bind_ok,
      TypedExpr.typeOf, hg, hr]

/-- Soundness of `HasType`, by mutual induction on the derivation. -/
theorem hasType_sound {decl syn : Bool} {x : Expr} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {cout : Capabilities}
    (hwf : EnvAssumptions env)
    (h : HasType decl syn x c env ty cout) :
    ∃ tx c', typeOf x c env = .ok (tx, c') ∧ tx.typeOf = ty ∧ CapsEquiv cout c' := by
  induction h using HasType.rec (motive_2 := fun xs c env tys _ =>
      EnvAssumptions env → ∃ txs, xs.mapM (fun x => justType (typeOf x c env)) = .ok txs ∧
        txs.map TypedExpr.typeOf = tys)
    (motive_3 := fun _ axs c env atys _ =>
      EnvAssumptions env → ∃ txs,
        axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) = .ok txs ∧
        txs.map (fun p => (p.1, Qualified.required p.2.typeOf)) = atys)
    (motive_4 := fun xfn args c env ty _ =>
      EnvAssumptions env → ∃ tx c', typeOf (.call xfn args) c env = .ok (tx, c') ∧
        tx.typeOf = ty ∧ CapsEquiv [] c')
    (motive_5 := fun _ axs c env rty _ =>
      EnvAssumptions env → ∃ txs,
        axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) = .ok txs ∧
        Map.make (txs.map (fun p => (p.1, Qualified.required p.2.typeOf))) = rty)
    (motive_6 := fun axs c env atys _ =>
      EnvAssumptions env → ∃ txs,
        axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) = .ok txs ∧
        txs.map (fun p => (p.1, Qualified.required p.2.typeOf)) = atys) with
  -- Literals and variables → `typeOfLit`/`typeOfVar`.
  | litBoolTrue _ _ _ _ | litBoolFalse _ _ _ _ | litInt _ _ _ _ _ | litString _ _ _ _ _
  | varPrincipal _ _ _ _ _ _ _ | varAction _ _ _ _ _ _ _ _ | varResource _ _ _ _ _ _ _
  | varContext _ _ _ _ _ _ _ =>
    exact ⟨_, [], by simp only [typeOf, typeOfLit, typeOfVar, ok, Function.comp_apply]; rfl, by rfl,
      fun _ => Iff.rfl⟩
  -- Unary → `typeOfUnaryApp`
  | unaryAppNotTt _ _ _ _ ih | unaryAppNotFf _ _ _ _ ih | unaryAppNotAny _ _ _ _ ih
  | unaryAppNeg _ _ _ _ ih | unaryAppIsEmpty _ _ _ _ _ ih | unaryAppLike _ _ _ _ _ ih =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih hwf
    exact ⟨_, ∅, by simp only [typeOf, h1, Except.bind_ok, typeOfUnaryApp, ht1, BoolType.not, ok,
      Function.comp_apply]; rfl, by rfl, fun _ => Iff.rfl⟩
  -- Arithmetic / comparison binaryApps → `typeOfBinaryApp`
  | binaryAppLessInt _ _ _ _ _ _ ih1 ih2 | binaryAppLessDatetime _ _ _ _ _ _ ih1 ih2
  | binaryAppLessDuration _ _ _ _ _ _ ih1 ih2 | binaryAppLessEqInt _ _ _ _ _ _ ih1 ih2
  | binaryAppLessEqDatetime _ _ _ _ _ _ ih1 ih2 | binaryAppLessEqDuration _ _ _ _ _ _ ih1 ih2
  | binaryAppAdd _ _ _ _ _ _ ih1 ih2 | binaryAppSub _ _ _ _ _ _ ih1 ih2
  | binaryAppMul _ _ _ _ _ _ ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf; obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    exact ⟨_, ∅, by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2, ok]; rfl,
      by rfl, fun _ => Iff.rfl⟩
  -- litEntity → `typeOfLit` entity-validity guard
  | litEntity ety eid c ets acts reqty a =>
    rename_i hwf
    have hv := validEntityUID_lit a (hwf.ets_keys_nodup) (hwf.acts_keys_nodup)
    exact ⟨.lit (.entityUID ⟨ety, eid⟩) (.entity ety), [],
      by simp [typeOf, typeOfLit, hv, ok], rfl, fun _ => Iff.rfl⟩
  -- unaryApp .is → `typeOfUnaryApp`
  | unaryAppIsTrue ety x₁ c env a a1 ih =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih hwf
    exact ⟨.unaryApp (.is ety) t1 (.bool .tt), ∅,
      by simp [typeOf, h1, typeOfUnaryApp, ht1, ok], rfl, fun _ => Iff.rfl⟩
  | unaryAppIsFalse ety₁ ety₂ x₁ c env a a1 hne a3 ih =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih hwf
    exact ⟨.unaryApp (.is ety₁) t1 (.bool .ff), ∅,
      by simp [typeOf, h1, typeOfUnaryApp, ht1, ok, hne], rfl, fun _ => Iff.rfl⟩
  -- contains / containsAll / containsAny → `ifLubThenBool` (needs `lubCompat_lub?`)
  | binaryAppContains _ _ _ _ _ _ a _ _ ih1 ih2 | binaryAppContainsAll _ _ _ _ _ _ a _ _ ih1 ih2
  | binaryAppContainsAny _ _ _ _ _ _ a _ _ ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf; obtain ⟨tt2, c2, h2, ht2, _⟩ := ih2 hwf
    obtain ⟨lt, hlt⟩ := lubCompat_lub? a
    exact ⟨_, ∅, by
      simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2, ifLubThenBool, hlt, ok]
      rfl, by rfl, fun _ => Iff.rfl⟩
  -- hasTag / getTag → `typeOfHasTag` / `typeOfGetTag`
  | hasTagAnyBool x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have htg := hasTagSchema_tags? a (hwf.ets_keys_nodup)
    have hcap : ¬ ((x₁, Key.tag x₂) ∈ c) := fun hm => a1 (capTagMem_iff.mpr hm)
    exact ⟨.binaryApp .hasTag t1 t2 (.bool .anyBool), Capabilities.singleton x₁ (.tag x₂),
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2, typeOfHasTag, htg,
        ite_eq_right hcap, ok], rfl, fun _ => Iff.rfl⟩
  | hasTagTt x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    simp only [id_eq] at h1 h2
    have htg := hasTagSchema_tags? a1 (hwf.ets_keys_nodup)
    have hcap : (x₁, Key.tag x₂) ∈ c := capTagMem_iff.mp a
    exact ⟨.binaryApp .hasTag t1 t2 (.bool .tt), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2, typeOfHasTag, htg,
        ite_eq_left hcap, ok], rfl, fun _ => Iff.rfl⟩
  | hasTagFf x₁ x₂ c ets acts reqty ety a a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have htg := noTags_tags? a (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .hasTag t1 t2 (.bool .ff), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2, typeOfHasTag, htg,
        ok], rfl, fun _ => Iff.rfl⟩
  | getTag x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    simp only [id_eq] at h1 h2
    have htg := hasTagSchema_tags? a1 (hwf.ets_keys_nodup)
    have hcap : (x₁, Key.tag x₂) ∈ c := capTagMem_iff.mp a
    exact ⟨.binaryApp .getTag t1 t2 ty, ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2, typeOfGetTag, htg,
        ite_eq_left hcap, ok], rfl, fun _ => Iff.rfl⟩
  -- and short-circuit → `typeOfAnd` .ff arm (returns x₁'s typed expr)
  | andShort x₁ x₂ c env c₁ a a1 ih =>
    rename_i hwf; obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    exact ⟨t1, ∅, by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, ok], ht1,
      fun _ => Iff.rfl⟩
  -- or → `typeOfOr` (second operand typed under `c`, no cap threading)
  | orShort x₁ x₂ c env c₁ a a1 ih =>
    rename_i hwf; obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    exact ⟨t1, ∅, by simp only [typeOf, h1, Except.bind_ok, typeOfOr, ht1, ok], ht1,
      fun _ => Iff.rfl⟩
  | orFfThen x₁ x₂ c env c₁ b₂ c₂ a a1 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1', h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2', h2, ht2, hc2⟩ := ih2 hwf
    exact ⟨.or t1 t2 (.bool b₂), c2',
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfOr, ht1, ht2, ok], rfl, hc2⟩
  | orAnyTt x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1', h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2', h2, ht2, _⟩ := ih2 hwf
    exact ⟨.or t1 t2 (.bool .tt), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfOr, ht1, ht2, ok], rfl, fun _ => Iff.rfl⟩
  | orAnyFf x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1', h1, ht1, hc1⟩ := ih1 hwf
    obtain ⟨t2, c2', h2, ht2, _⟩ := ih2 hwf
    exact ⟨.or t1 t2 (.bool .anyBool), c1',
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfOr, ht1, ht2, ok], rfl, hc1⟩
  | orAnyAny x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1', h1, ht1, hc1⟩ := ih1 hwf
    obtain ⟨t2, c2', h2, ht2, hc2⟩ := ih2 hwf
    exact ⟨.or t1 t2 (.bool .anyBool), c1' ∩ c2',
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfOr, ht1, ht2, ok], rfl,
      (capIntersect_capsEquiv_inter c₁ c₂).trans (CapsEquiv.inter hc1 hc2)⟩
  -- and (threads `c ∪ c₁` into the 2nd operand → bridge `CapMerge` via `typeOf_capsEquiv`)
  | andTtFf x₁ x₂ c env c₁ c_c₁ c₂ a a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨t2, cc2', h2, ht2, _⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', _⟩ := typeOf_capsEquiv hb h2
    exact ⟨.and t1 t2 (.bool .ff), ∅,
      by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, h2', ht2, ok], rfl, fun _ => Iff.rfl⟩
  | andTtTt x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨t2, cc2', h2, ht2, hcc2⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', ho2⟩ := typeOf_capsEquiv hb h2
    exact ⟨.and t1 t2 (.bool .tt), cc1' ∪ o₂,
      by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, h2', ht2, ok], rfl,
      (capMerge_capsEquiv_union a3).trans (CapsEquiv.union hcc1 (hcc2.trans ho2))⟩
  | andTtAny x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨t2, cc2', h2, ht2, hcc2⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', ho2⟩ := typeOf_capsEquiv hb h2
    exact ⟨.and t1 t2 (.bool .anyBool), cc1' ∪ o₂,
      by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, h2', ht2, ok], rfl,
      (capMerge_capsEquiv_union a3).trans (CapsEquiv.union hcc1 (hcc2.trans ho2))⟩
  | andAnyFf x₁ x₂ c env c₁ c_c₁ c₂ a a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨t2, cc2', h2, ht2, _⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', _⟩ := typeOf_capsEquiv hb h2
    exact ⟨.and t1 t2 (.bool .ff), ∅,
      by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, h2', ht2, ok], rfl, fun _ => Iff.rfl⟩
  | andAnyTt x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨t2, cc2', h2, ht2, hcc2⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', ho2⟩ := typeOf_capsEquiv hb h2
    exact ⟨.and t1 t2 (.bool .anyBool), cc1' ∪ o₂,
      by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, h2', ht2, ok], rfl,
      (capMerge_capsEquiv_union a3).trans (CapsEquiv.union hcc1 (hcc2.trans ho2))⟩
  | andAnyAny x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨t2, cc2', h2, ht2, hcc2⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', ho2⟩ := typeOf_capsEquiv hb h2
    exact ⟨.and t1 t2 (.bool .anyBool), cc1' ∪ o₂,
      by simp only [typeOf, h1, Except.bind_ok, typeOfAnd, ht1, h2', ht2, ok], rfl,
      (capMerge_capsEquiv_union a3).trans (CapsEquiv.union hcc1 (hcc2.trans ho2))⟩
  -- ite → `typeOfIf` (threads `c ∪ c₁`; anyBool arm needs `lub_sound`)
  | iteTt x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ cout a a1 a2 a3 a4 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨tt2, cc2', h2, ht2, hcc2⟩ := ih2 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', ho2⟩ := typeOf_capsEquiv hb h2
    exact ⟨.ite t1 tt2 tt2 tt2.typeOf, cc1' ∪ o₂,
      by simp only [typeOf, h1, Except.bind_ok, typeOfIf, ht1, h2', ok], ht2,
      (capMerge_capsEquiv_union a3).trans (CapsEquiv.union hcc1 (hcc2.trans ho2))⟩
  | iteFf x₁ x₂ x₃ c env c₁ t₃ c₃ a a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t3, c3', h3, ht3, hcc3⟩ := ih2 hwf
    exact ⟨.ite t1 t3 t3 t3.typeOf, c3',
      by simp only [typeOf, h1, Except.bind_ok, typeOfIf, ht1, h3, ok], ht3, hcc3⟩
  | iteAnyBool x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ c₃ lubTy c₁₂ a a1 a2 a3 a4 a5 ih1 ih2 ih3 =>
    rename_i hwf
    obtain ⟨t1, cc1', h1, ht1, hcc1⟩ := ih1 hwf
    obtain ⟨tt2, cc2', h2, ht2, hcc2⟩ := ih2 hwf
    obtain ⟨t3, c3', h3, ht3, hcc3⟩ := ih3 hwf
    have hb : CapsEquiv c_c₁ (c ∪ cc1') := (capMerge_capsEquiv_union a1).trans
      (CapsEquiv.union (CapsEquiv.refl c) hcc1)
    obtain ⟨o₂, h2', ho2⟩ := typeOf_capsEquiv hb h2
    refine ⟨.ite t1 tt2 t3 lubTy, (cc1' ∪ o₂) ∩ c3',
      by simp only [typeOf, h1, Except.bind_ok, typeOfIf, ht1, h2', h3, ht2, ht3, lub_sound a4,
        ok], rfl, ?_⟩
    exact (capIntersect_capsEquiv_inter c₁₂ c₃).trans
      (CapsEquiv.inter ((capMerge_capsEquiv_union a5).trans
        (CapsEquiv.union hcc1 (hcc2.trans ho2))) hcc3)
  -- eq → `typeOfEq`
  | binaryAppEqLitSame p c env ty a ih =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih hwf
    exact ⟨.binaryApp .eq t1 t1 (.bool .tt), ∅,
      by simp [typeOf, h1, typeOfBinaryApp, typeOfEq, ok], rfl, fun _ => Iff.rfl⟩
  | binaryAppEqLitDiff p₁ p₂ c env ty₁ ty₂ a a1 a2 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf; obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hne := primNeq_ne a
    exact ⟨.binaryApp .eq t1 t2 (.bool .ff), ∅,
      by simp [typeOf, h1, h2, typeOfBinaryApp, typeOfEq, ok, beq_eq_false_iff_ne.mpr hne], rfl,
      fun _ => Iff.rfl⟩
  | binaryAppEqNonLitLub x₁ x₂ c env t₁ t₂ lubTy a a1 a2 a3 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf; obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    refine ⟨.binaryApp .eq t1 t2 (.bool .anyBool), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp]
    unfold typeOfEq
    split
    · exact absurd (BothLit.mk _ _) a3
    · simp [ht1, ht2, lub_sound a, ok]
  | binaryAppEqEntityDiff x₁ x₂ c env ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    rename_i hwf; obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf; obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    refine ⟨.binaryApp .eq t1 t2 (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp]
    unfold typeOfEq
    split
    · exact absurd (BothLit.mk _ _) a5
    · simp [ht1, ht2, lub_entity_ne a2, ok]
  -- mem (generic, non-action-literal) → `typeOfInₑ`/`typeOfInₛ` fallback + ancestry
  | binaryAppMemEntityEntity x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hd := descendentOf_sound (reqty := reqty) a1 (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .mem t1 t2 (.bool .anyBool), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2,
        typeOfInₑ_fallback (env := ⟨ets, acts, reqty⟩) a2, hd, ite_true, ok], rfl, fun _ => Iff.rfl⟩
  | binaryAppMemEntitySame x₁ x₂ c ets acts reqty ety a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hd := descendentOf_sound (reqty := reqty) (DescendentOf.refl ets acts ety)
      (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .mem t1 t2 (.bool .anyBool), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2,
        typeOfInₑ_fallback (env := ⟨ets, acts, reqty⟩) a1, hd, ite_true, ok], rfl, fun _ => Iff.rfl⟩
  | binaryAppMemEntitySet x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hd := descendentOf_sound (reqty := reqty) a1 (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .mem t1 t2 (.bool .anyBool), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2,
        typeOfInₛ_fallback (env := ⟨ets, acts, reqty⟩) a2, hd, ite_true, ok], rfl, fun _ => Iff.rfl⟩
  | binaryAppMemEntitySetSame x₁ x₂ c ets acts reqty ety a a1 a2 a3 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hd := descendentOf_sound (reqty := reqty) (DescendentOf.refl ets acts ety)
      (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .mem t1 t2 (.bool .anyBool), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2,
        typeOfInₛ_fallback (env := ⟨ets, acts, reqty⟩) a1, hd, ite_true, ok], rfl, fun _ => Iff.rfl⟩
  | binaryAppMemEntityEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hd := notDescendentOf_sound (reqty := reqty) a2 (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .mem t1 t2 (.bool .ff), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2,
        typeOfInₑ_fallback (env := ⟨ets, acts, reqty⟩) a3, hd, ite_false, ok, Bool.false_eq_true], rfl, fun _ => Iff.rfl⟩
  | binaryAppMemEntitySetFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hd := notDescendentOf_sound (reqty := reqty) a2 (hwf.ets_keys_nodup)
    exact ⟨.binaryApp .mem t1 t2 (.bool .ff), ∅,
      by simp only [typeOf, h1, h2, Except.bind_ok, typeOfBinaryApp, ht1, ht2,
        typeOfInₛ_fallback (env := ⟨ets, acts, reqty⟩) a3, hd, ite_false, ok, Bool.false_eq_true], rfl, fun _ => Iff.rfl⟩
  -- set → `typeOfSet` (element pass via `motive_2` IH + `allLub_foldlM`)
  | set x xs c env ty tyList lubTy a a1 a2 ih_x ih_xs =>
    rename_i hwf
    obtain ⟨tx, cx, hx, htx, _⟩ := ih_x hwf
    obtain ⟨txs, hxs, htxs⟩ := ih_xs hwf
    have hjx : justType (typeOf x c env) = .ok tx := by rw [hx]; rfl
    refine ⟨.set (tx :: txs) (.set lubTy), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), List.mapM_cons,
      hjx, hxs, bind, Except.bind, pure, Except.pure, typeOfSet, htx, htxs,
      allLub_foldlM a2, ok]
  -- HasTypeList (motive_2)
  | nil c env =>
    rename_i hwf; exact ⟨[], rfl, rfl⟩
  | cons x xs c env ty tys a a1 ih_x ih_xs =>
    rename_i hwf
    obtain ⟨tx, cx, hx, htx, _⟩ := ih_x hwf
    obtain ⟨txs, hxs, htxs⟩ := ih_xs hwf
    have hjx : justType (typeOf x c env) = .ok tx := by rw [hx]; rfl
    exact ⟨tx :: txs, by simp only [List.mapM_cons, hjx, hxs, Except.bind_ok]; rfl,
      by simp only [List.map_cons, htx, htxs]⟩
  -- callExt delegates to the motive_4 IH
  | callExt xfn args c env ty a ih => rename_i hwf; exact ih hwf
  -- HasTypeExtCall (motive_4): construction via `typeOfConstructor`, methods via `typeOfCall`
  | decimal s c env a | ip s c env a | datetime s c env a | duration s c env a =>
    obtain ⟨_, hd⟩ := a
    exact ⟨_, ∅, by
      simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), List.mapM_cons,
        List.mapM_nil]
      simp only [justType, typeOfLit, Function.comp_apply, Except.map, bind, Except.bind, pure, Except.pure,
        typeOfCall, typeOfConstructor, hd, ok]
      rfl, by rfl, fun _ => Iff.rfl⟩
  | lessThan a b c env _ _ ih_a ih_b | lessThanOrEqual a b c env _ _ ih_a ih_b
  | greaterThan a b c env _ _ ih_a ih_b | greaterThanOrEqual a b c env _ _ ih_a ih_b
  | offset a b c env _ _ ih_a ih_b | durationSince a b c env _ _ ih_a ih_b =>
    rename_i hwf
    obtain ⟨ta, _, hta, htta, _⟩ := ih_a hwf
    obtain ⟨tb, _, htb, httb, _⟩ := ih_b hwf
    exact ⟨_, ∅, by
      simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), List.mapM_cons,
        List.mapM_nil]
      simp only [justType, hta, htb, Except.map, bind, Except.bind, pure, Except.pure,
        typeOfCall, List.map_cons, List.map_nil, htta, httb, ok]
      rfl, by rfl, fun _ => Iff.rfl⟩
  | isIpv4 a c env _ ih_a | isIpv6 a c env _ ih_a | isLoopback a c env _ ih_a
  | isMulticast a c env _ ih_a | toDate a c env _ ih_a | toTime a c env _ ih_a
  | toMilliseconds a c env _ ih_a | toSeconds a c env _ ih_a | toMinutes a c env _ ih_a
  | toHours a c env _ ih_a | toDays a c env _ ih_a =>
    rename_i hwf
    obtain ⟨ta, _, hta, htta, _⟩ := ih_a hwf
    exact ⟨_, ∅, by
      simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), List.mapM_cons,
        List.mapM_nil]
      simp only [justType, hta, Except.map, bind, Except.bind, pure, Except.pure,
        typeOfCall, List.map_cons, List.map_nil, htta, ok]
      rfl, by rfl, fun _ => Iff.rfl⟩
  | isInRange a xs c env tys ha hip hxs ih_a ih_xs =>
    rename_i hwf
    obtain ⟨ta, ca, hta, htta, _⟩ := ih_a hwf
    obtain ⟨txs, hjxs, htxs⟩ := ih_xs hwf
    have hja : justType (typeOf a c env) = .ok ta := by rw [hta]; rfl
    obtain ⟨t, ts, rfl, hall⟩ := hip.cons_all
    refine ⟨.call .isInRange (ta :: txs) (.bool .anyBool), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [id] at htxs
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), List.mapM_cons,
      hja, hjxs, bind, Except.bind, pure, Except.pure, typeOfCall, typeOfIsInRange,
      List.map_cons, htta, htxs, hall, ite_true, ok]
  -- action-literal mem (entity) → `typeOfInₑ` action branch
  | binaryAppMemActionLitTt uid₁ uid₂ c ets acts reqty a a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hnd := hwf.acts_keys_nodup
    obtain ⟨entry, hmc⟩ : ∃ e, MapContains uid₁ e acts := by cases a <;> exact ⟨_, by assumption⟩
    have hc1 : acts.contains uid₁ = true := by simp [ActionSchema.contains, mapContains_find?_nodup hmc hnd]
    have hdesc := actionDescendentOf_sound a hnd
    refine ⟨.binaryApp .mem t1 t2 (.bool .tt), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp [typeOf, h1, h2, typeOfBinaryApp, ht1, ht2, typeOfInₑ, actionUID?, entityUID?, hc1,
      hdesc, ok]
  | binaryAppMemActionLitFf uid₁ uid₂ c ets acts reqty a a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hnd := hwf.acts_keys_nodup
    obtain ⟨entry, hmc⟩ : ∃ e, MapContains uid₁ e acts := by
      cases a
      exact ⟨_, by assumption⟩
    have hc1 : acts.contains uid₁ = true := by simp [ActionSchema.contains, mapContains_find?_nodup hmc hnd]
    have hdesc := notActionDescendentOf_sound a hnd
    refine ⟨.binaryApp .mem t1 t2 (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp [typeOf, h1, h2, typeOfBinaryApp, ht1, ht2, typeOfInₑ, actionUID?, entityUID?, hc1,
      hdesc, ok]
  -- getAttr — record receiver: `typeOf_tyWf` gives the record type is key-distinct,
  -- so `Map.find?` agrees with the structural `MapContains` witness.
  | getAttrRecord x₁ a c env rty ty a1 a2 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have htw := typeOf_tyWf hwf h1; rw [ht1] at htw
    have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
    cases a2 with
    | required hmc =>
      have hf := mapContains_find?_nodup hmc hnd
      exact ⟨.getAttr t1 a ty, ∅, by
        simp only [typeOf, h1, Except.bind_ok, typeOfGetAttr, ht1, getAttrInRecord, hf, ok],
        rfl, fun _ => Iff.rfl⟩
    | optional hcap hmc =>
      simp only [id_eq] at hmc
      have hf := mapContains_find?_nodup hmc hnd
      have hcapc : (x₁, Key.attr a) ∈ c := capAttrMem_iff.mp hcap
      exact ⟨.getAttr t1 a ty, ∅, by
        simp only [typeOf, h1, Except.bind_ok, typeOfGetAttr, ht1, getAttrInRecord, hf,
          ite_eq_left hcapc, ok], rfl, fun _ => Iff.rfl⟩
  -- getAttr — entity receiver: the record type comes from the (key-distinct) schema.
  | getAttrEntity x₁ a c ets acts reqty ety ty rty a1 a2 a3 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have hattr := mapContainsAttrs_attrs? a1 (hwf.ets_keys_nodup)
    have hnd : (rty.toList.map Prod.fst).Nodup := by
      cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
    cases a3 with
    | required hmc =>
      have hf := mapContains_find?_nodup hmc hnd
      exact ⟨.getAttr t1 a ty, ∅, by
        simp only [typeOf, h1, Except.bind_ok, typeOfGetAttr, ht1, hattr, getAttrInRecord, hf, ok],
        rfl, fun _ => Iff.rfl⟩
    | optional hcap hmc =>
      simp only [id_eq] at hmc
      have hf := mapContains_find?_nodup hmc hnd
      have hcapc : (x₁, Key.attr a) ∈ c := capAttrMem_iff.mp hcap
      exact ⟨.getAttr t1 a ty, ∅, by
        simp only [typeOf, h1, Except.bind_ok, typeOfGetAttr, ht1, hattr, getAttrInRecord, hf,
          ite_eq_left hcapc, ok], rfl, fun _ => Iff.rfl⟩
  -- hasAttr — record receiver (attribute found); `knownToExist = true`.
  | hasAttrRecord x₁ a c env rty ty caps a1 a2 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have htw := typeOf_tyWf hwf h1; rw [ht1] at htw
    have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
    cases a2 with
    | found_in_caps _ _ _ =>
      have hcapc : (x₁, Key.attr a) ∈ c := capAttrMem_iff.mp ‹CapAttrMem x₁ a c›
      have hmc := ‹MapContains (id a) _ rty›
      simp only [id_eq] at hmc
      have hf := mapContains_find?_nodup hmc hnd
      exact ⟨.hasAttr t1 a (.bool .tt), ∅, by
        simp [typeOf, h1, typeOfHasAttr, ht1, hasAttrInRecord, hf, hcapc, ok], rfl, fun _ => Iff.rfl⟩
    | found_required_known ty' hmc =>
      have hf := mapContains_find?_nodup hmc hnd
      exact ⟨.hasAttr t1 a (.bool .tt), ∅, by
        simp [typeOf, h1, typeOfHasAttr, ht1, hasAttrInRecord, hf, Qualified.isRequired, ok],
        rfl, fun _ => Iff.rfl⟩
    | found_optional_known ty' hmc hcap =>
      have hf := mapContains_find?_nodup hmc hnd
      have hcapneg : ¬ ((x₁, Key.attr a) ∈ c) := fun hm => hcap (capAttrMem_iff.mpr hm)
      exact ⟨.hasAttr t1 a (.bool .anyBool), Capabilities.singleton x₁ (.attr a), by
        simp [typeOf, h1, typeOfHasAttr, ht1, hasAttrInRecord, hf, Qualified.isRequired, hcapneg,
          ok], rfl, fun _ => Iff.rfl⟩
  -- hasAttr — record receiver (attribute not found).
  | hasAttrRecordNotFound x₁ a c env rty a1 a2 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have hf := mapNotContainsKey_find? a2
    exact ⟨.hasAttr t1 a (.bool .ff), ∅, by
      simp only [typeOf, h1, Except.bind_ok, typeOfHasAttr, ht1, hasAttrInRecord, hf, ok], rfl,
      fun _ => Iff.rfl⟩
  -- hasAttr — entity receiver (attribute found); `knownToExist = false`.
  | hasAttrEntity x₁ a c ets acts reqty ety ty caps rty a1 a2 a3 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have hattr := mapContainsAttrs_attrs? a1 (hwf.ets_keys_nodup)
    have hnd : (rty.toList.map Prod.fst).Nodup := by
      cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
    cases a3 with
    | found_in_caps _ _ _ =>
      have hcapc : (x₁, Key.attr a) ∈ c := capAttrMem_iff.mp ‹CapAttrMem x₁ a c›
      have hmc := ‹MapContains (id a) _ rty›
      simp only [id_eq] at hmc
      have hf := mapContains_find?_nodup hmc hnd
      exact ⟨.hasAttr t1 a (.bool .tt), ∅, by
        simp [typeOf, h1, typeOfHasAttr, ht1, hattr, hasAttrInRecord, hf, hcapc, ok],
        rfl, fun _ => Iff.rfl⟩
    | found_not_known qty hmc hcap =>
      have hf := mapContains_find?_nodup hmc hnd
      have hcapneg : ¬ ((x₁, Key.attr a) ∈ c) := fun hm => hcap (capAttrMem_iff.mpr hm)
      exact ⟨.hasAttr t1 a (.bool .anyBool), Capabilities.singleton x₁ (.attr a), by
        simp [typeOf, h1, typeOfHasAttr, ht1, hattr, hasAttrInRecord, hf, hcapneg, ok],
        rfl, fun _ => Iff.rfl⟩
  -- hasAttr — entity receiver (attribute not found).
  | hasAttrEntityNotFound x₁ a c ets acts reqty ety rty a1 a2 a3 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have hattr := mapContainsAttrs_attrs? a1 (hwf.ets_keys_nodup)
    have hf := mapNotContainsKey_find? a3
    exact ⟨.hasAttr t1 a (.bool .ff), ∅, by
      simp only [typeOf, h1, Except.bind_ok, typeOfHasAttr, ht1, hattr, hasAttrInRecord, hf, ok],
      rfl, fun _ => Iff.rfl⟩
  -- hasAttr — enum entity: `attrs? = some Map.empty`, so `hasAttrInRecord` finds
  -- nothing and returns `.bool .ff`.
  | hasAttrEnum x₁ a c ets acts reqty ety eids a1 a2 ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have hfind := mapContains_find?_nodup (mapContainsEnum_mc a1) (hwf.ets_keys_nodup)
    have hattr : EntitySchema.attrs? ets ety = some Map.empty := by
      simp only [EntitySchema.attrs?, hfind, Option.map_some, EntitySchemaEntry.attrs]
    exact ⟨.hasAttr t1 a (.bool .ff), ∅, by
      simp only [typeOf, h1, Except.bind_ok, typeOfHasAttr, ht1, hattr, hasAttrInRecord,
        show (Map.empty : RecordType).find? a = none from rfl, ok], rfl, fun _ => Iff.rfl⟩
  -- mem — action literal in a set of entity literals (tt: some descendent).
  | binaryAppMemActionLitSetTt uid₁ xs c ets acts reqty ety₂ a1 a2 a3 a4 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hnd := hwf.acts_keys_nodup
    obtain ⟨entry, hmc⟩ : ∃ e, MapContains uid₁ e acts := by
      cases a1 with | mk _ _ _ e hmc _ => exact ⟨e, hmc⟩
    have hc1 : acts.contains uid₁ = true := by
      simp [ActionSchema.contains, mapContains_find?_nodup hmc hnd]
    have hall : ∀ x ∈ xs, ∃ uid, x = .lit (.entityUID uid) := by
      cases a1 with | mk _ _ _ _ _ hall => exact hall
    obtain ⟨uids, huids⟩ := mapM_entityUID?_all_lits hall
    have hany := actionInSet_any a2 huids hnd
    refine ⟨.binaryApp .mem t1 t2 (.bool .tt), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp [typeOf, h1, h2, typeOfBinaryApp, ht1, ht2, typeOfInₛ, actionUID?, entityUID?,
      entityUIDs?, hc1, huids, hany, ok]
  -- mem — action literal in a set of entity literals (ff: no descendent).
  | binaryAppMemActionLitSetFf uid₁ xs c ets acts reqty ety₂ a1 a2 a3 a4 ih1 ih2 =>
    rename_i hwf
    obtain ⟨t1, c1, h1, ht1, _⟩ := ih1 hwf
    obtain ⟨t2, c2, h2, ht2, _⟩ := ih2 hwf
    have hnd := hwf.acts_keys_nodup
    obtain ⟨entry, hmc⟩ : ∃ e, MapContains uid₁ e acts := by
      cases a1 with | mk _ _ _ e hmc _ => exact ⟨e, hmc⟩
    have hc1 : acts.contains uid₁ = true := by
      simp [ActionSchema.contains, mapContains_find?_nodup hmc hnd]
    have hall : ∀ x ∈ xs, ∃ uid, x = .lit (.entityUID uid) := by
      cases a1 with | mk _ _ _ _ _ hall => exact hall
    obtain ⟨uids, huids⟩ := mapM_entityUID?_all_lits hall
    have hany : uids.any (fun u => acts.descendentOf uid₁ u) = false := by
      by_contra hne
      simp only [Bool.not_eq_false, List.any_eq_true] at hne
      obtain ⟨u, hu_mem, hdesc⟩ := hne
      exact a2 (actionInSet_of_mem huids hu_mem
        (descendentOf_actionDescendentOf hmc hnd hdesc))
    refine ⟨.binaryApp .mem t1 t2 (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp [typeOf, h1, h2, typeOfBinaryApp, ht1, ht2, typeOfInₛ, actionUID?, entityUID?,
      entityUIDs?, hc1, huids, hany, ok]
  -- record literal → `typeOfRecord`.
  | record axs c env rty a ih =>
    rename_i hwf
    obtain ⟨txs, hmapM, hrty⟩ := ih hwf
    refine ⟨.record txs (.record rty), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1))),
      hmapM, Except.bind_ok, ok, hrty]
  -- RecordTypeOf (motive_5): `sorted` reorders the attributes, `lax` is `typeOf`'s `Map.make`.
  | sorted b axs axs' c env atyList hsort a1 ih3 =>
    rename_i hwf
    obtain ⟨txs', hmapM', hmap⟩ := ih3 hwf
    obtain ⟨txs, hmapM, hcan⟩ :=
      sortsTo_forall₂ typeOfAttr_key hsort (List.mapM_ok_iff_forall₂.mp hmapM')
    refine ⟨txs, List.mapM_ok_iff_forall₂.mpr hmapM, ?_⟩
    show Map.make (txs.map (Prod.map id (fun t => Qualified.required t.typeOf))) = Map.mk atyList
    rw [Map.make, List.canonicalize_of_map_fst, hcan, ← hmap]
    rfl
  | lax axs c env atys a ih =>
    rename_i hwf
    obtain ⟨txs, hmapM, hmap⟩ := ih hwf
    exact ⟨txs, hmapM, by rw [hmap]⟩
  -- Action-typed operands of `in`, `has` and `hasTag` (all `.bool .ff` with `[]` caps).
  | binaryAppMemActionEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ hnc hne hnmd hnal a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨tx₁, c₁', hty1, htty1, _⟩ := ih1 hwf
    obtain ⟨tx₂, c₂', hty2, htty2, _⟩ := ih2 hwf
    have hdesc : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = false := by
      simp only [TypeEnv.descendentOf, ite_eq_right hne, mapNotContainsKey_find? hnc]
      exact Bool.eq_false_iff.mpr (fun h => hnmd (maybeActionDescendentOf_iff.mpr h))
    have hfb : typeOfInₑ ety₁ ety₂ x₁ x₂ ⟨ets, acts, reqty⟩ = .ff := by
      rw [typeOfInₑ_fallback hnal, hdesc]; rfl
    refine ⟨.binaryApp .mem tx₁ tx₂ (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, hty1, hty2, Except.bind_ok, typeOfBinaryApp, htty1, htty2, hfb, ok]
  | binaryAppMemActionSetFf x₁ x₂ c ets acts reqty ety₁ ety₂ hnc hne hnmd hnal a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨tx₁, c₁', hty1, htty1, _⟩ := ih1 hwf
    obtain ⟨tx₂, c₂', hty2, htty2, _⟩ := ih2 hwf
    have hdesc : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = false := by
      simp only [TypeEnv.descendentOf, ite_eq_right hne, mapNotContainsKey_find? hnc]
      exact Bool.eq_false_iff.mpr (fun h => hnmd (maybeActionDescendentOf_iff.mpr h))
    have hfb : typeOfInₛ ety₁ ety₂ x₁ x₂ ⟨ets, acts, reqty⟩ = .ff := by
      rw [typeOfInₛ_fallback hnal, hdesc]; rfl
    refine ⟨.binaryApp .mem tx₁ tx₂ (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, hty1, hty2, Except.bind_ok, typeOfBinaryApp, htty1, htty2, hfb, ok]
  | hasTagActionFf x₁ x₂ c ets acts reqty ety eid entry hnc hpk a1 a2 ih1 ih2 =>
    rename_i hwf
    obtain ⟨tx₁, c₁', hty1, htty1, _⟩ := ih1 hwf
    obtain ⟨tx₂, c₂', hty2, htty2, _⟩ := ih2 hwf
    refine ⟨.binaryApp .hasTag tx₁ tx₂ (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, hty1, hty2, Except.bind_ok, typeOfBinaryApp, htty1, htty2, typeOfHasTag,
      EntitySchema.tags?, mapNotContainsKey_find? hnc, Option.map,
      mapContainsPairKey_actionType? hpk, ite_true, ok]
  | hasAttrActionFf x₁ a c ets acts reqty ety eid entry hnc hpk a1 ih1 =>
    rename_i hwf
    obtain ⟨tx₁, c₁', hty1, htty1, _⟩ := ih1 hwf
    refine ⟨.hasAttr tx₁ a (.bool .ff), ∅, ?_, rfl, fun _ => Iff.rfl⟩
    simp only [typeOf, hty1, Except.bind_ok, typeOfHasAttr, htty1, EntitySchema.attrs?,
      mapNotContainsKey_find? hnc, Option.map, mapContainsPairKey_actionType? hpk,
      ite_true, ok]
  | extHasAttr x₁ a as c env ty₁ oc b cout a1 a2 _ ih =>
    rename_i hwf
    obtain ⟨t1, c1', h1, ht1, _⟩ := ih hwf
    have htw := typeOf_tyWf hwf h1; rw [ht1] at htw
    obtain ⟨c', hc, hce⟩ := extHasAttrChain_sound hwf a2 ht1 htw
    exact ⟨.extHasAttr t1 a as (.bool b), c', by
      simp only [typeOf, h1, Except.bind_ok, hc, ok], rfl, hce⟩
  -- HasTypeRecord (motive_3) and HasTypeFields (motive_6): nil / cons, handled together (they
  -- share the `nil`/`cons` recursor tags with `HasTypeList`, so cannot be named separately in
  -- `with`).
  | _ =>
    first
    | -- HasTypeRecord.nil
      (intro _; exact ⟨[], rfl, rfl⟩)
    | -- HasTypeRecord.cons
      (rename_i _ a x axs c env ty atyList _ _ _
       intro ihHT ihR hwf
       obtain ⟨tx, cx, hx, htx, _⟩ := ihHT hwf
       obtain ⟨txs, hmapM, hmap⟩ := ihR hwf
       refine ⟨(a, tx) :: txs, ?_, ?_⟩
       · simp only [List.mapM_cons, hx, hmapM, Except.bind_ok]; rfl
       · simp only [List.map_cons, htx, hmap])
    | -- HasTypeFields.nil
      (exact ⟨[], rfl, rfl⟩)
    | -- HasTypeFields.cons
      (rename_i a x axs c env ty atyList _ _ ihHT ihR
       intro hwf
       obtain ⟨tx, cx, hx, htx, _⟩ := ihHT hwf
       obtain ⟨txs, hmapM, hmap⟩ := ihR hwf
       refine ⟨(a, tx) :: txs, ?_, ?_⟩
       · simp only [List.mapM_cons, hx, hmapM, Except.bind_ok]; rfl
       · simp only [List.map_cons, htx, hmap])

end Cedar.Validation.Relational

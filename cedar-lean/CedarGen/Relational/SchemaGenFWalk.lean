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

import CedarGen.Relational.SchemaGenFTypes

/-! # What `GenTypeEnvF` builds, entry by entry

For every flag setting: the keys of the entity and action lists are the skeleton's, each entry's
types, ancestors and `appliesTo` sets are what the flags ask, the request is one of the actions'
(with `wfRest`), and the actions declare at most the budget of request environments. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-- `l` is sorted when `m` asks for it. -/
def SortedIf (m : Bool) {α} [LT α] (l : List α) : Prop := m = true → EltsSorted l

theorem sortedIf_nil {m α} [LT α] : SortedIf m ([] : List α) := fun _ => .nil
theorem sortedIf_single {m α} [LT α] (x : α) : SortedIf m [x] := fun _ => .single _

theorem SetArrET.sortedIf {m xs ys} (h : SetArrET m xs ys) : SortedIf m ys := by
  intro hm; subst hm; exact h.sorted
theorem SetArrUID.sortedIf {m xs ys} (h : SetArrUID m xs ys) : SortedIf m ys := by
  intro hm; subst hm; exact h.sorted
theorem SetArrStr.sortedIf {m xs ys} (h : SetArrStr m xs ys) : SortedIf m ys := by
  intro hm; subst hm; exact h.sorted

/-! ## The skeleton -/

theorem Kinds.keys {ks kinds} (h : Kinds ks kinds) : kinds.map Prod.fst = ks := by
  induction h
  case nil => rfl
  case cons ih => simp [ih]

theorem StdNames.mem {kinds sks} (h : StdNames kinds sks) : ∀ x, x ∈ sks ↔ (x, false) ∈ kinds := by
  induction h
  case nil => simp
  case std ih => intro y; simp [ih]
  case enum ih => intro y; simp [ih]

theorem EnumNames.mem {kinds eks} (h : EnumNames kinds eks) : ∀ x, x ∈ eks ↔ (x, true) ∈ kinds := by
  induction h
  case nil => simp
  case std ih => intro y; simp [ih]
  case enum ih => intro y; simp [ih]

theorem TypesOf.eq {uids ats} (h : TypesOf uids ats) : ats = uids.map (·.ty) := by
  induction h
  case nil => rfl
  case cons ih => simp [ih]

theorem Ranked.keys {uids ranked} (h : Ranked uids ranked) : ranked.map Prod.fst = uids := by
  induction h
  case nil => rfl
  case cons ih => simp [ih]

theorem RawUids.ok {a i ks us} (h : RawUids a i ks us) : ∀ u ∈ us, ActTyOK a i ks u.ty := by
  induction h
  case nil => simp
  case cons hty _ ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hty
    · exact ih u hu

theorem RawNames.ok {i xs} (h : RawNames i xs) : ∀ x ∈ xs, NameIf i x := by
  induction h
  case nil => simp
  case cons hx _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ih y hy

/-- What the skeleton is: the names' kinds and partition, the actions' types and ranks. -/
structure SkelInv (m a i : Bool) (sk : Skeleton) : Prop where
  ks_nodup : sk.ks.Nodup
  ks_sorted : SortedIf m sk.ks
  ks_names : ∀ x ∈ sk.ks, NameIf i x
  kinds_keys : sk.kinds.map Prod.fst = sk.ks
  sks_mem : ∀ x, x ∈ sk.sks ↔ (x, false) ∈ sk.kinds
  eks_mem : ∀ x, x ∈ sk.eks ↔ (x, true) ∈ sk.kinds
  uids_nodup : sk.uids.Nodup
  uids_sorted : SortedIf m sk.uids
  uids_ty : ∀ u ∈ sk.uids, ActTyOK a i sk.ks u.ty
  ats_eq : sk.ats = sk.uids.map (·.ty)
  ranked_keys : sk.ranked.map Prod.fst = sk.uids
  no_shadow : i = true → noShadowB sk.ks sk.uids = true

theorem SkelF.inv {m a i sk} (h : SkelF m a i sk) : SkelInv m a i sk := by
  cases h
  case mk hn hk hs he hu hsh =>
    obtain ⟨rfl, hns⟩ := hsh.eq_ok
    cases hn
    case mk hraw harr =>
      cases hu
      case mk hrawU harrU hty hrk =>
        exact {
          ks_nodup := harr.nodup
          ks_sorted := fun hm => by subst hm; exact harr.sorted
          ks_names := fun x hx => hraw.ok x (harr.sub x hx)
          kinds_keys := hk.keys
          sks_mem := hs.mem
          eks_mem := he.mem
          uids_nodup := harrU.nodup
          uids_sorted := fun hm => by subst hm; exact harrU.sorted
          uids_ty := fun u hu => hrawU.ok u (harrU.sub u hu)
          ats_eq := hty.eq
          ranked_keys := hrk.keys
          no_shadow := hns }

theorem SkelInv.sks_sub {m a i sk} (h : SkelInv m a i sk) : ∀ x ∈ sk.sks, x ∈ sk.ks := by
  intro x hx
  rw [← h.kinds_keys]
  exact List.mem_map.mpr ⟨_, (h.sks_mem x).mp hx, rfl⟩

/-! ## Entities -/

/-- What an entity entry is apart from its ancestors: checked attribute and tag types, and for an
enumeration its eids. -/
def EntShapeOK (m e d i : Bool) (ks ats : List EntityType) : EntitySchemaEntry → Prop
  | .standard se => RecTyF m d i true ks ats se.attrs.toList ∧ TagsF m d i ks ats se.tags
  | .enum eids => EidsF m e eids.elts

theorem entShapeOK_entShape {m e d i ks ats} (x : EntitySchemaEntry) :
    EntShapeOK m e d i ks ats (entShape x) ↔ EntShapeOK m e d i ks ats x := by
  cases x <;> exact Iff.rfl

/-- An entity entry's ancestors: declared with `wfRest`, sorted with `wfMaps`. -/
def EntAncsOK (m d : Bool) (ks : List EntityType) (x : EntitySchemaEntry) : Prop :=
  (d = true → ∀ y ∈ entAncs x, y ∈ ks) ∧ SortedIf m (entAncs x)

theorem AncPool.sub {n all std pool} (h : AncPool n all std pool) (hstd : ∀ y ∈ std, y ∈ all) :
    ∀ y ∈ pool, y ∈ all := by
  cases h
  · exact hstd
  · exact hstd
  · exact fun _ h => h

theorem AncElems.decl {d n ks sks eks xs} (h : AncElems d n ks sks eks xs) (hd : d = true)
    (hsks : ∀ y ∈ sks, y ∈ ks) : ∀ y ∈ xs, y ∈ ks := by
  induction h
  case nil => simp
  case cons hx _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · cases hx
      case declT hp hm => exact hp.sub hsks _ (definedEntityType_iff_mem.mp hm)
      case declF => cases hd
      case anyF => cases hd
    · exact ih y hy

theorem ParentsF.ok {r m d n ks sks eks seen seenStd ps}
    (h : ParentsF r m d n ks sks eks seen seenStd ps) (hsks : ∀ y ∈ sks, y ∈ ks)
    (hseen : ∀ y ∈ seen, y ∈ ks) (hseenStd : ∀ y ∈ seenStd, y ∈ ks) :
    (d = true → ∀ y ∈ ps, y ∈ ks) ∧ SortedIf m ps := by
  cases h
  case denseStdT h₁ h₂ =>
                 exact ⟨fun _ y hy => hseenStd y (subET_sub h₁ y (h₂.sub y hy)), h₂.sortedIf⟩
  case denseStdF h₁ h₂ =>
                 exact ⟨fun _ y hy => hseenStd y (subET_sub h₁ y (h₂.sub y hy)), h₂.sortedIf⟩
  case denseAllF h₁ h₂ =>
                 exact ⟨fun _ y hy => hseen y (subET_sub h₁ y (h₂.sub y hy)), h₂.sortedIf⟩
  case freeT h₁ h₂ =>
             exact ⟨fun hd y hy => by subst hd; exact h₁.decl rfl hsks y (h₂.sub y hy), h₂.sortedIf⟩
  case freeF h₁ h₂ =>
             exact ⟨fun hd y hy => by subst hd; exact h₁.decl rfl hsks y (h₂.sub y hy), h₂.sortedIf⟩
  case sparseNoneT => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
  case sparseNoneF => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
  case sparseStdT h =>
                  exact ⟨fun _ y hy => by
                    rcases List.mem_singleton.mp hy with rfl
                    exact hseenStd _ (definedEntityType_iff_mem.mp h), sortedIf_single _⟩
  case sparseStdF h =>
                  exact ⟨fun _ y hy => by
                    rcases List.mem_singleton.mp hy with rfl
                    exact hseenStd _ (definedEntityType_iff_mem.mp h), sortedIf_single _⟩
  case sparseAllF h =>
                  exact ⟨fun _ y hy => by
                    rcases List.mem_singleton.mp hy with rfl
                    exact hseen _ (definedEntityType_iff_mem.mp h), sortedIf_single _⟩
  case flatT => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
  case flatF => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩

theorem EntsF.ok {m e d n i r ks sks eks ats seen seenStd kinds ents}
    (h : EntsF m e d n i r ks sks eks ats seen seenStd kinds ents) (hsks : ∀ y ∈ sks, y ∈ ks)
    (hseen : ∀ y ∈ seen, y ∈ ks) (hseenStd : ∀ y ∈ seenStd, y ∈ ks)
    (hkinds : ∀ p ∈ kinds, p.1 ∈ ks) :
    ents.map Prod.fst = kinds.map Prod.fst ∧
      ∀ p ∈ ents, EntShapeOK m e d i ks ats p.2 ∧ EntAncsOK m d ks p.2 := by
  induction h
  case nil => simp
  case std x _ _ _ _ _ hpar ha ht _ ih =>
    have hx : x ∈ ks := hkinds _ List.mem_cons_self
    have ih := ih (fun y hy => by rcases List.mem_cons.mp hy with rfl | hy; exacts [hx, hseen y hy])
      (fun y hy => by rcases List.mem_cons.mp hy with rfl | hy; exacts [hx, hseenStd y hy])
      (fun p hp => hkinds p (List.mem_cons_of_mem _ hp))
    refine ⟨by simp [ih.1], ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨⟨ha, ht⟩, hpar.ok hsks hseen hseenStd⟩
    · exact ih.2 p hp
  case enum x _ _ _ he _ ih =>
    have hx : x ∈ ks := hkinds _ List.mem_cons_self
    have ih := ih (fun y hy => by rcases List.mem_cons.mp hy with rfl | hy; exacts [hx, hseen y hy])
      hseenStd (fun p hp => hkinds p (List.mem_cons_of_mem _ hp))
    refine ⟨by simp [ih.1], ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨he, fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
    · exact ih.2 p hp

/-- The closure keeps the shapes, draws the ancestors from the given ones, and (closing in order)
keeps them sorted. -/
theorem closeAll_ents_ok {m e d i ks ats} (s : Bool) (hs : m = true → s = true)
    (g : List (EntityType × EntitySchemaEntry))
    (hg : ∀ p ∈ g, EntShapeOK m e d i ks ats p.2 ∧ EntAncsOK m d ks p.2) :
    (closeAll entAncs entWith s g).map Prod.fst = g.map Prod.fst ∧
      ∀ p ∈ closeAll entAncs entWith s g, EntShapeOK m e d i ks ats p.2 ∧ EntAncsOK m d ks p.2 := by
  refine ⟨closeAll_map_fst _ _ _ _, fun p hp => ⟨?_, ?_, ?_⟩⟩
  · have hmap := closeAll_map_proj entAncs entWith entShape entShape_entWith s g
    have : (p.1, entShape p.2) ∈ g.map (fun p => (p.1, entShape p.2)) := by
      rw [← hmap]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at hqp
    rw [← entShapeOK_entShape, ← hqp.2, entShapeOK_entShape]
    exact (hg q hq).1
  · intro hd y hy
    obtain ⟨q, hq, hyq⟩ := closeAll_sub entAncs entWith entAncs_entWith_sub s g hp hy
    exact (hg q hq).2.1 hd y hyq
  · intro hm
    have := closeAll_sorted entAncs entWith entAncs_entWith g (fun q hq => (hg q hq).2.2 hm)
    rw [hs hm] at hp
    exact this p hp

theorem CloseEnts.ok {c m e d i ks ats g g'} (h : CloseEnts c m g g')
    (hg : ∀ p ∈ g, EntShapeOK m e d i ks ats p.2 ∧ EntAncsOK m d ks p.2) :
    g'.map Prod.fst = g.map Prod.fst ∧
      ∀ p ∈ g', EntShapeOK m e d i ks ats p.2 ∧ EntAncsOK m d ks p.2 := by
  cases h with
  | keep => exact ⟨rfl, hg⟩
  | closeS => exact closeAll_ents_ok true (fun _ => rfl) g hg
  | closeA => exact closeAll_ents_ok false (fun h => absurd h (by decide)) g hg

theorem EntsAll.ok {m e d c n i r sk ents} (h : EntsAll m e d c n i r sk ents)
    {a} (hsk : SkelInv m a i sk) :
    ents.map Prod.fst = sk.ks ∧
      ∀ p ∈ ents, EntShapeOK m e d i sk.ks sk.ats p.2 ∧ EntAncsOK m d sk.ks p.2 := by
  cases h
  case mk pre hpre hclose =>
    have hk : ∀ p ∈ sk.kinds, p.1 ∈ sk.ks := fun p hp => by
      rw [← hsk.kinds_keys]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have h₁ := hpre.ok hsk.sks_sub (by simp) (by simp) hk
    have h₂ := hclose.ok h₁.2
    simp only [id] at h₂
    exact ⟨by rw [h₂.1, h₁.1, hsk.kinds_keys], h₂.2⟩

/-! ## Actions -/

/-- What an action entry is apart from its ancestors: checked `appliesTo` types, sorted with
`wfMaps`, and a context type, checked with `wfRest`. -/
def ActShapeOK (m d i : Bool) (ks ats : List EntityType) (x : ActionSchemaEntry) : Prop :=
  (∀ y ∈ x.appliesToPrincipal.elts, RefIf d i ks ats y) ∧ SortedIf m x.appliesToPrincipal.elts ∧
  (∀ y ∈ x.appliesToResource.elts, RefIf d i ks ats y) ∧ SortedIf m x.appliesToResource.elts ∧
  RecTyF m d i d ks ats x.context.toList

theorem actShapeOK_actShape {m d i ks ats} (x : ActionSchemaEntry) :
    ActShapeOK m d i ks ats (actShape x) ↔ ActShapeOK m d i ks ats x := Iff.rfl

/-- An action's ancestors: declared with `wfRest`, sorted with `wfMaps`. -/
def ActAncsOK (m d : Bool) (uids : List EntityUID) (x : ActionSchemaEntry) : Prop :=
  (d = true → ∀ y ∈ actAncs x, y ∈ uids) ∧ SortedIf m (actAncs x)

theorem AppliesF.ok {d i ks ats xs} (h : AppliesF d i ks ats xs) : ∀ y ∈ xs, RefIf d i ks ats y := by
  induction h
  case nil => simp
  case cons hx _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ih y hy

theorem AppliesBounded.ok {d i ks ats n xs} (h : AppliesBounded d i ks ats n xs) :
    (∀ y ∈ xs, RefIf d i ks ats y) ∧ xs.length ≤ n := by
  induction h
  case nil => simp
  case cons hx _ ih =>
    refine ⟨fun y hy => ?_, by simp only [List.length_cons]; omega⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ih.1 y hy

theorem AppliesNE.ok {d i ks ats n xs} (h : AppliesNE d i ks ats n xs) :
    (∀ y ∈ xs, RefIf d i ks ats y) ∧ xs.length ≤ n ∧ xs ≠ [] := by
  cases h
  case mk hx hxs =>
    have := hxs.ok
    refine ⟨fun y hy => ?_, by simp only [List.length_cons]; omega, by simp⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact this.1 y hy

theorem PrincipalsF.ok {m d i ks ats ps} (h : PrincipalsF m d i ks ats ps) :
    (∀ y ∈ ps, RefIf d i ks ats y) ∧ SortedIf m ps := by
  cases h
  case mk h₁ h₂ => exact ⟨fun y hy => h₁.ok y (h₂.sub y hy), h₂.sortedIf⟩

theorem ResourcesF.ok {m d i ks ats b ps rs} (h : ResourcesF m d i ks ats b ps rs) :
    (∀ y ∈ rs, RefIf d i ks ats y) ∧ SortedIf m rs ∧ ps.length * rs.length ≤ b := by
  cases h
  case mk raw h₁ h₂ =>
    cases h₁
    case none h₁ =>
      exact ⟨fun y hy => h₁.ok y (h₂.sub y hy), h₂.sortedIf, by simp⟩
    case some p ps h₁ =>
      have := h₁.ok
      refine ⟨fun y hy => this.1 y (h₂.sub y hy), h₂.sortedIf, ?_⟩
      have hl := h₂.length_le
      simp only [List.length_cons]
      calc (ps.length + 1) * rs.length ≤ (ps.length + 1) * (b / (ps.length + 1)) :=
            Nat.mul_le_mul_left _ (Nat.le_trans hl this.2)
        _ ≤ b := Nat.mul_div_le _ _

theorem AppliesNEF.ok {m d i ks ats n ps} (h : AppliesNEF m d i ks ats n ps) :
    (∀ y ∈ ps, RefIf d i ks ats y) ∧ SortedIf m ps ∧ ps.length ≤ n ∧ ps ≠ [] := by
  cases h
  case mk raw h₁ h₂ =>
    have := h₁.ok
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil this.2.2
    exact ⟨fun y hy => this.1 y (h₂.sub y hy), h₂.sortedIf,
      Nat.le_trans h₂.length_le this.2.1, h₂.ne_nil⟩

theorem lowerOf_sub {ranked : List (EntityUID × Nat)} {uids : List EntityUID}
    (hrk : ranked.map Prod.fst = uids) {k : Nat} : ∀ y ∈ lowerOf ranked k, y ∈ uids := by
  intro y hy
  obtain ⟨j, hj, -⟩ := mem_lowerOf.mp hy
  rw [← hrk]
  exact List.mem_map.mpr ⟨_, hj, rfl⟩

theorem AElems.decl {d a ranked k uids xs} (h : AElems d a ranked k uids xs) (hd : d = true)
    (hrk : ranked.map Prod.fst = uids) : ∀ y ∈ xs, y ∈ uids := by
  induction h
  case nil => simp
  case cons hx _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · cases hx
      case declT hc hm =>
        have hm := definedUID_iff_mem.mp hm
        cases hc
        case lowerT hl => cases hl; exact lowerOf_sub hrk _ hm
        case lowerF hl => cases hl; exact lowerOf_sub hrk _ hm
        case allF => exact hm
      case declF => cases hd
      case undeclF => cases hd
    · exact ih y hy

theorem AParents.ok {r m d a ranked k uids ps} (h : AParents r m d a ranked k uids ps)
    (hrk : ranked.map Prod.fst = uids) : (d = true → ∀ y ∈ ps, y ∈ uids) ∧ SortedIf m ps := by
  cases h
  case denseLowerT h₁ h₂ =>
                   exact ⟨fun _ y hy => lowerOf_sub hrk _ (subUID_sub h₁ y (h₂.sub y hy)), h₂.sortedIf⟩
  case denseLowerF h₁ h₂ =>
                   exact ⟨fun _ y hy => lowerOf_sub hrk _ (subUID_sub h₁ y (h₂.sub y hy)), h₂.sortedIf⟩
  case denseAllF h₁ h₂ => exact ⟨fun _ y hy => subUID_sub h₁ y (h₂.sub y hy), h₂.sortedIf⟩
  case freeT h₁ h₂ =>
             exact ⟨fun hd y hy => by subst hd; exact h₁.decl rfl hrk y (h₂.sub y hy), h₂.sortedIf⟩
  case freeF h₁ h₂ =>
             exact ⟨fun hd y hy => by subst hd; exact h₁.decl rfl hrk y (h₂.sub y hy), h₂.sortedIf⟩
  case sparseNoneT => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
  case sparseNoneF => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
  case sparseLowerT h =>
                    exact ⟨fun _ y hy => by
                      rcases List.mem_singleton.mp hy with rfl
                      exact lowerOf_sub hrk _ (definedUID_iff_mem.mp h), sortedIf_single _⟩
  case sparseLowerF h =>
                    exact ⟨fun _ y hy => by
                      rcases List.mem_singleton.mp hy with rfl
                      exact lowerOf_sub hrk _ (definedUID_iff_mem.mp h), sortedIf_single _⟩
  case sparseAllF h =>
                  exact ⟨fun _ y hy => by
                    rcases List.mem_singleton.mp hy with rfl
                    exact definedUID_iff_mem.mp h, sortedIf_single _⟩
  case flatT => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩
  case flatF => exact ⟨fun _ _ h => absurd h List.not_mem_nil, sortedIf_nil⟩

private theorem set_mk_toList {α : Type} (l : List α) : (Set.mk l).toList = l := rfl

theorem ActsB.ok {m a d i r ks ats uids ranked b todo acts}
    (h : ActsB m a d i r ks ats uids ranked b todo acts) (hrk : ranked.map Prod.fst = uids) :
    acts.map Prod.fst = todo.map Prod.fst ∧ envCount acts ≤ b ∧
      ∀ p ∈ acts, ActShapeOK m d i ks ats p.2 ∧ ActAncsOK m d uids p.2 := by
  induction h
  case nil => simp [envCount]
  case cons b _ _ _ ps rs _ _ _ hp hr ha hc _ ih =>
    have hp := hp.ok
    have hr := hr.ok
    refine ⟨by simp [ih.1], ?_, ?_⟩
    · rw [envCount_cons]
      simp only [set_mk_toList]
      have := ih.2.1
      generalize ps.length * rs.length = P at this hr ⊢
      omega
    · intro p hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨⟨hp.1, hp.2, hr.1, hr.2.1, hc⟩, ha.ok hrk⟩
      · exact ih.2.2 p hp'

/-- The request is one of the actions': it applies to the principal and resource, with its context. -/
def ReqIn (acts : List (EntityUID × ActionSchemaEntry)) (reqty : RequestType) : Prop :=
  ∃ e, (reqty.action, e) ∈ acts ∧ reqty.principal ∈ e.appliesToPrincipal.elts ∧
    reqty.resource ∈ e.appliesToResource.elts ∧ reqty.context = e.context

theorem ActsR.ok {m a d i r ks ats uids ranked b todo acts reqty}
    (h : ActsR m a d i r ks ats uids ranked b todo acts reqty) (hrk : ranked.map Prod.fst = uids) :
    acts.map Prod.fst = todo.map Prod.fst ∧ envCount acts ≤ b ∧
      (∀ p ∈ acts, ActShapeOK m d i ks ats p.2 ∧ ActAncsOK m d uids p.2) ∧ ReqIn acts reqty := by
  induction h
  case cons b _ _ _ ps rs _ _ _ _ hp hr ha hc _ ih =>
    have hp := hp.ok
    have hr := hr.ok
    refine ⟨by simp [ih.1], ?_, ?_, ?_⟩
    · rw [envCount_cons]
      simp only [set_mk_toList]
      have := ih.2.1
      generalize ps.length * rs.length = P at this hr ⊢
      omega
    · intro p hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨⟨hp.1, hp.2, hr.1, hr.2.1, hc⟩, ha.ok hrk⟩
      · exact ih.2.2.1 p hp'
    · obtain ⟨e, he, h₁, h₂, h₃⟩ := ih.2.2.2
      exact ⟨e, List.mem_cons_of_mem _ he, h₁, h₂, h₃⟩
  case request b u _ _ ps p rs res _ _ _ hp hpp hr hrr ha hc hrest =>
    have hp := hp.ok
    have hr := hr.ok
    have hrest := hrest.ok hrk
    refine ⟨by simp [hrest.1], ?_, ?_, ?_⟩
    · rw [envCount_cons]
      simp only [set_mk_toList]
      have := hrest.2.1
      have hpos : 0 < ps.length := List.length_pos_iff.mpr hp.2.2.2
      have : ps.length * rs.length ≤ b :=
        Nat.le_trans (Nat.mul_le_mul_left _ hr.2.2.1) (Nat.mul_div_le _ _)
      generalize ps.length * rs.length = P at *
      omega
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨⟨hp.1, hp.2.1, hr.1, hr.2.1, hc⟩, ha.ok hrk⟩
      · exact hrest.2.2 q hq
    · exact ⟨_, List.mem_cons_self, definedEntityType_iff_mem.mp hpp,
        definedEntityType_iff_mem.mp hrr, rfl⟩

theorem closeAll_acts_ok {m d i ks ats uids} (s : Bool) (hs : m = true → s = true)
    (g : List (EntityUID × ActionSchemaEntry))
    (hg : ∀ p ∈ g, ActShapeOK m d i ks ats p.2 ∧ ActAncsOK m d uids p.2) :
    (closeAll actAncs actWith s g).map Prod.fst = g.map Prod.fst ∧
      (closeAll actAncs actWith s g).map (fun p => (p.1, actShape p.2)) =
        g.map (fun p => (p.1, actShape p.2)) ∧
      ∀ p ∈ closeAll actAncs actWith s g, ActShapeOK m d i ks ats p.2 ∧ ActAncsOK m d uids p.2 := by
  have hmap := closeAll_map_proj actAncs actWith actShape actShape_actWith s g
  refine ⟨closeAll_map_fst _ _ _ _, hmap, fun p hp => ⟨?_, ?_, ?_⟩⟩
  · have : (p.1, actShape p.2) ∈ g.map (fun p => (p.1, actShape p.2)) := by
      rw [← hmap]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at hqp
    rw [← actShapeOK_actShape, ← hqp.2, actShapeOK_actShape]
    exact (hg q hq).1
  · intro hd y hy
    obtain ⟨q, hq, hyq⟩ := closeAll_sub actAncs actWith actAncs_actWith_sub s g hp hy
    exact (hg q hq).2.1 hd y hyq
  · intro hm
    have := closeAll_sorted actAncs actWith actAncs_actWith g (fun q hq => (hg q hq).2.2 hm)
    rw [hs hm] at hp
    exact this p hp

/-- The closure keeps the request one of the actions'. -/
theorem reqIn_of_shape {g g' : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    (hmap : g'.map (fun p => (p.1, actShape p.2)) = g.map (fun p => (p.1, actShape p.2)))
    (h : ReqIn g reqty) : ReqIn g' reqty := by
  obtain ⟨e, he, h₁, h₂, h₃⟩ := h
  have : (reqty.action, actShape e) ∈ g'.map (fun p => (p.1, actShape p.2)) := by
    rw [hmap]; exact List.mem_map.mpr ⟨_, he, rfl⟩
  obtain ⟨⟨u, e'⟩, he', hee⟩ := List.mem_map.mp this
  simp only [Prod.mk.injEq] at hee
  obtain ⟨rfl, hee⟩ := hee
  have hp : e'.appliesToPrincipal = e.appliesToPrincipal := by
    simpa [actShape] using congrArg ActionSchemaEntry.appliesToPrincipal hee
  have hr : e'.appliesToResource = e.appliesToResource := by
    simpa [actShape] using congrArg ActionSchemaEntry.appliesToResource hee
  have hc : e'.context = e.context := by
    simpa [actShape] using congrArg ActionSchemaEntry.context hee
  exact ⟨e', he', hp ▸ h₁, hr ▸ h₂, hc ▸ h₃⟩

theorem envCount_of_shape {g g' : List (EntityUID × ActionSchemaEntry)}
    (hmap : g'.map (fun p => (p.1, actShape p.2)) = g.map (fun p => (p.1, actShape p.2))) :
    envCount g' = envCount g := by
  have : ∀ l : List (EntityUID × ActionSchemaEntry), envCount l =
      ((l.map (fun p => (p.1, actShape p.2))).map fun (_, e) =>
        e.appliesToPrincipal.toList.length * e.appliesToResource.toList.length).sum := by
    intro l; simp only [envCount, List.map_map]; rfl
  rw [this, this g, hmap]

theorem CloseActs.ok {a m d i ks ats uids g g'} (h : CloseActs a m g g')
    (hg : ∀ p ∈ g, ActShapeOK m d i ks ats p.2 ∧ ActAncsOK m d uids p.2) :
    g'.map Prod.fst = g.map Prod.fst ∧
      g'.map (fun p => (p.1, actShape p.2)) = g.map (fun p => (p.1, actShape p.2)) ∧
      (∀ p ∈ g', ActShapeOK m d i ks ats p.2 ∧ ActAncsOK m d uids p.2) ∧
      (a = true → closedB actAncs g' = true ∧ irreflB actAncs g' = true) := by
  cases h
  case keep => exact ⟨rfl, rfl, hg, fun h => absurd h (by decide)⟩
  case closeS h₁ h₂ =>
    have := closeAll_acts_ok true (fun _ => rfl) g hg
    exact ⟨this.1, this.2.1, this.2.2, fun _ => ⟨h₁, h₂⟩⟩
  case closeA h₁ h₂ =>
    have := closeAll_acts_ok false (fun h => absurd h (by decide)) g hg
    exact ⟨this.1, this.2.1, this.2.2, fun _ => ⟨h₁, h₂⟩⟩

theorem ActsAllB.ok {m a i r sk b acts} (h : ActsAllB m a i r sk b acts) {e}
    (hsk : SkelInv m e i sk) :
    acts.map Prod.fst = sk.uids ∧ envCount acts ≤ b ∧
      (∀ p ∈ acts, ActShapeOK m false i sk.ks sk.ats p.2 ∧ ActAncsOK m false sk.uids p.2) := by
  cases h
  case mk pre hpre hclose =>
    have h₁ := hpre.ok hsk.ranked_keys
    have h₂ := hclose.ok h₁.2.2
    simp only [id] at h₂
    exact ⟨by rw [h₂.1, h₁.1, hsk.ranked_keys], by rw [envCount_of_shape h₂.2.1]; exact h₁.2.1,
      h₂.2.2.1⟩

theorem ActsAllR.ok {m a i r sk b acts reqty} (h : ActsAllR m a i r sk b acts reqty) {e}
    (hsk : SkelInv m e i sk) :
    acts.map Prod.fst = sk.uids ∧ envCount acts ≤ b ∧
      (∀ p ∈ acts, ActShapeOK m true i sk.ks sk.ats p.2 ∧ ActAncsOK m true sk.uids p.2) ∧
      ReqIn acts reqty ∧ (a = true → closedB actAncs acts = true ∧ irreflB actAncs acts = true) := by
  cases h
  case mk pre hpre hclose =>
    have h₁ := hpre.ok hsk.ranked_keys
    have h₂ := hclose.ok h₁.2.2.1
    simp only [id] at h₂
    exact ⟨by rw [h₂.1, h₁.1, hsk.ranked_keys], by rw [envCount_of_shape h₂.2.1]; exact h₁.2.1,
      h₂.2.2.1, reqIn_of_shape h₂.2.1 h₁.2.2.2, h₂.2.2.2⟩

end Cedar.Validation.Relational.SchemaGen

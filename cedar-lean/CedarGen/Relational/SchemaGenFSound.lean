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

import CedarGen.Relational.SchemaGenFWalk

/-! # `GenTypeEnvF` is monotone in its flags and sound

* `GenTypeEnvF.mono`: lowering any flags keeps an environment (and its mode and budget);
* `GenTypeEnvF.envAssumptions`: at every setting, the environments satisfy `EnvAssumptions` and
  have at most `budget` request environments;
* `GenTypeEnvF.typeEnvWF`: with `wfMaps`, `wfActs`, `wfEnum` and `wfRest`, they are `TypeEnvWF`
  (hence `validateWellFormed`). -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-! ## Lists and maps -/

theorem map_mk_toList {α β} (m : Map α β) : Map.mk m.toList = m := rfl

theorem set_mk_elts {α} (s : Data.Set α) : Data.Set.mk s.elts = s := rfl

theorem keysSorted_of_map_fst {α β} [LT α] : ∀ {l : List (α × β)}, EltsSorted (l.map Prod.fst) →
    KeysSorted l
  | [], _ => .nil
  | [(k, v)], _ => .single k v
  | (k₁, v₁) :: (k₂, v₂) :: rest, h => by
    cases h with
    | cons _ _ _ hlt h => exact .cons _ _ _ _ _ hlt (keysSorted_of_map_fst h)

theorem map_fst_of_keysSorted {α β} [LT α] : ∀ {l : List (α × β)}, KeysSorted l →
    EltsSorted (l.map Prod.fst)
  | [], _ => .nil
  | [(k, v)], _ => .single k
  | (k₁, v₁) :: (k₂, v₂) :: rest, h => by
    cases h with
    | cons _ _ _ _ _ hlt h => exact .cons _ _ _ hlt (map_fst_of_keysSorted h)

theorem mem_keys_iff {α β} {l : List (α × β)} {k : α} : k ∈ l.map Prod.fst ↔ ∃ v, (k, v) ∈ l := by
  simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right]

/-- With distinct keys, `find?` finds the binding of a key. -/
theorem find?_of_mem_nodup {α β} [DecidableEq α] : ∀ {l : List (α × β)} {k : α} {v : β},
    (l.map Prod.fst).Nodup → (k, v) ∈ l → (Map.mk l).find? k = some v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (k', v') :: l, k, v, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [Map.find?, Map.toList]
    · have hne : k' ≠ k := fun e => hnd.1 (e ▸ List.mem_map.mpr ⟨_, h, rfl⟩)
      have ih := find?_of_mem_nodup hnd.2 h
      simp only [Map.find?, Map.toList] at ih ⊢
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih

theorem mem_of_find? {α β} [DecidableEq α] [LT α] [DecidableLT α] {l : List (α × β)} {k : α} {v : β}
    (h : (Map.mk l).find? k = some v) : (k, v) ∈ l :=
  Map.find?_mem_toList h

/-! ## The environment's declared types -/

theorem validEntityType_of_mem {ents : List (EntityType × EntitySchemaEntry)}
    {acts : List (EntityUID × ActionSchemaEntry)} {x : EntityType}
    (h : x ∈ ents.map Prod.fst ∨ x ∈ (acts.map Prod.fst).map (·.ty)) :
    ValidEntityType x (Map.mk ents) (Map.mk acts) := by
  rcases h with h | h
  · obtain ⟨e, he⟩ := mem_keys_iff.mp h
    exact .inSchema _ _ _ _ (mem_toList_mapContains he)
  · obtain ⟨⟨ty, eid⟩, hu, rfl⟩ := List.mem_map.mp h
    obtain ⟨e, he⟩ := mem_keys_iff.mp hu
    obtain ⟨e', he'⟩ := mapContainsPairKey_of_mapContains (mem_toList_mapContains (m := Map.mk acts) he)
    exact .isAction _ _ _ _ _ he'

theorem mem_of_validEntityType {ents : List (EntityType × EntitySchemaEntry)}
    {acts : List (EntityUID × ActionSchemaEntry)} {x : EntityType}
    (h : ValidEntityType x (Map.mk ents) (Map.mk acts)) :
    x ∈ ents.map Prod.fst ∨ x ∈ (acts.map Prod.fst).map (·.ty) := by
  cases h
  case inSchema h => exact .inl (mem_keys_iff.mpr ⟨_, mapContains_mem h⟩)
  case isAction eid _ h =>
    exact .inr (List.mem_map.mpr ⟨⟨x, eid⟩, mem_keys_iff.mpr ⟨_, mapContains_mem (mapContainsPairKey_mc h)⟩, rfl⟩)

theorem entityTypeWF_of_mem {ents : List (EntityType × EntitySchemaEntry)}
    {acts : List (EntityUID × ActionSchemaEntry)} {x : EntityType}
    (h : x ∈ ents.map Prod.fst ∨ x ∈ (acts.map Prod.fst).map (·.ty)) :
    EntityTypeWF (Map.mk ents) (Map.mk acts) x := by
  rcases h with h | h
  · obtain ⟨e, he⟩ := mem_keys_iff.mp h
    exact .entity _ _ _ _ (mem_toList_mapContains he)
  · obtain ⟨⟨ty, eid⟩, hu, rfl⟩ := List.mem_map.mp h
    obtain ⟨e, he⟩ := mem_keys_iff.mp hu
    exact .action _ _ _ _ _ (mem_toList_mapContains (m := Map.mk acts) he)

theorem mem_of_entityTypeWF {ents : List (EntityType × EntitySchemaEntry)}
    {acts : List (EntityUID × ActionSchemaEntry)} {x : EntityType}
    (h : EntityTypeWF (Map.mk ents) (Map.mk acts) x) :
    x ∈ ents.map Prod.fst ∨ x ∈ (acts.map Prod.fst).map (·.ty) := by
  cases h
  case entity h => exact .inl (mem_keys_iff.mpr ⟨_, mapContains_mem h⟩)
  case action eid _ h =>
    exact .inr (List.mem_map.mpr ⟨⟨x, eid⟩, mem_keys_iff.mpr ⟨_, mapContains_mem h⟩, rfl⟩)

/-! ## Monotonicity -/

theorem appliesBounded_of_appliesNE {d i ks ats n xs} (h : AppliesNE d i ks ats n xs) :
    AppliesBounded d i ks ats n xs := by
  cases h
  case mk hx hxs => exact .cons _ _ _ _ _ _ _ hx hxs

/-- Placing the request is one way to build the actions. -/
theorem ActsR.toB {m a d i r ks ats uids ranked b todo acts reqty}
    (h : ActsR m a d i r ks ats uids ranked b todo acts reqty) :
    ActsB m a d i r ks ats uids ranked b todo acts := by
  induction h
  case cons hp hr ha hc _ ih =>
    exact .cons _ _ _ _ _ _ _ _ _ hp (hr.mono (BLe.refl _) (BLe.refl _) (BLe.refl _) (by omega)) ha hc ih
  case request b _ _ _ ps _ rs _ _ _ _ hp hpp hr _ ha hc hrest =>
    have hpne := hp.ok.2.2.2
    obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hpne
    refine .cons _ _ _ _ _ _ _ _ _ ?_ ?_ ha hc hrest
    · cases hp
      case mk raw h₁ h₂ => exact .mk _ _ _ _ _ _ raw (appliesBounded_of_appliesNE h₁).appliesF h₂
    · cases hr
      case mk raw h₁ h₂ => exact .mk _ _ _ _ _ _ _ _ raw (.some _ _ _ _ _ _ _ _
                (appliesBounded_of_appliesNE h₁)) h₂

/-- **Monotonicity.** Lowering any of the flags keeps every environment, in the same mode and
within the same budget. -/
theorem GenTypeEnvF.mono {m a e d c n i m' a' e' d' c' n' i' r b env}
    (h : GenTypeEnvF m a e d c n i r b env)
    (hm : BLe m' m) (ha : BLe a' a) (he : BLe e' e) (hd : BLe d' d) (hc : BLe c' c)
    (hn : BLe n' n) (hi : BLe i' i) : GenTypeEnvF m' a' e' d' c' n' i' r b env := by
  match h with
  | .decl _ _ _ _ _ _ _ _ ents acts reqty sk hreg hsk hents hacts =>
    cases d'
    · -- the request, one of the actions', is free
      have hinv := hsk.inv
      have hA := hacts.ok hinv
      cases hacts
      case mk pre hpre hclose =>
      refine .free _ _ _ _ _ _ _ _ ents acts reqty sk hreg (hsk.mono hm ha hi)
        (hents.mono hm he hd hc hn hi)
        (.mk _ pre (hpre.toB.mono hm ha (BLe.false_le _) hi) (hclose.mono ha hm)) ?_
      obtain ⟨p, u, res, ctx⟩ := reqty
      obtain ⟨en, hen, hp, hr, hctx⟩ := hA.2.2.2.1
      have hshape := (hA.2.2.1 _ hen).1
      obtain ⟨ty, eid⟩ := u
      obtain ⟨cl⟩ := ctx
      have hA1 : acts.map Prod.fst = sk.uids := hA.1
      have hu : (⟨ty, eid⟩ : EntityUID) ∈ sk.uids := by
        rw [← hA1]; exact List.mem_map.mpr ⟨_, hen, rfl⟩
      refine .mk _ _ _ _ _ _ _ _ _ ((hshape.1 _ hp).mono (BLe.refl _) hi)
        ((hshape.2.2.1 _ hr).mono (BLe.refl _) hi) ?_ ?_
      · exact refAny_of_mem (.inr (by show _ ∈ sk.ats; rw [hinv.ats_eq]; exact List.mem_map.mpr ⟨_, hu, rfl⟩))
      · have := hshape.2.2.2.2
        simp only at hctx
        rw [← hctx] at this
        exact this.mono hm (BLe.false_le _) hi (BLe.refl _)
    · exact .decl _ _ _ _ _ _ _ _ ents acts reqty sk hreg (hsk.mono hm ha hi)
        (hents.mono hm he hd hc hn hi) (hacts.mono hm ha hi)
  | .free _ _ _ _ _ _ _ _ ents acts reqty sk hreg hsk hents hacts hreq =>
    obtain rfl := hd.of_false
    exact .free _ _ _ _ _ _ _ _ ents acts reqty sk hreg (hsk.mono hm ha hi)
      (hents.mono hm he hd hc hn hi) (hacts.mono hm ha hi) (hreq.mono hm hi)

/-! ## Soundness: `EnvAssumptions` -/

theorem entShape_attrs {m e d i ks ats} {entry : EntitySchemaEntry}
    (h : EntShapeOK m e d i ks ats entry) :
    TyF m d i true ks ats (.record entry.attrs) ∧
      ∀ ty, entry.tags? = some ty → TyF m d i true ks ats ty := by
  cases entry with
  | standard se =>
    obtain ⟨ancs, attrs, tags⟩ := se
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨h₁.tyF, fun ty hty => ?_⟩
    cases h₂
    case none => simp [EntitySchemaEntry.tags?] at hty
    case some h => simp only [EntitySchemaEntry.tags?, Option.some.injEq] at hty; subst hty; exact h
  | enum eids =>
    exact ⟨recTyF_nil.tyF, fun ty hty => by simp [EntitySchemaEntry.tags?] at hty⟩

/-- Without `wfRest`, every environment satisfies `EnvAssumptions` and the budget. -/
theorem GenTypeEnvF.envAssumptions_free {m a e c n i r b env}
    (h : GenTypeEnvF m a e false c n i r b env) :
    EnvAssumptions env ∧ env.schema.environments.length ≤ b := by
  match h with
  | .free _ _ _ _ _ _ _ _ ents acts reqty sk hreg hsk hents hacts hreq =>
  have hinv := hsk.inv
  have hE := hents.ok hinv
  have hA := hacts.ok hinv
  simp only [id] at hE hA
  have hv : ∀ x, x ∈ sk.ks ∨ x ∈ sk.ats →
      ValidEntityType x (Map.mk ents) (Map.mk acts) := fun x hx =>
    validEntityType_of_mem (by rw [hE.1, hA.1, ← hinv.ats_eq]; exact hx)
  have hent : ∀ {ety entry}, (Map.mk ents).find? ety = some entry →
      TyF m false i true sk.ks sk.ats (.record entry.attrs) ∧
        ∀ ty, entry.tags? = some ty → TyF m false i true sk.ks sk.ats ty := fun hf =>
    entShape_attrs (hE.2 _ (mem_of_find? hf)).1
  refine ⟨{ ets_keys_nodup := ?_, acts_keys_nodup := ?_, attrs_tyWf := ?_, tags_tyWf := ?_,
            context_tyWf := ?_, attrs_typeValid := ?_, tags_typeValid := ?_, reqty_valid := ?_ }, ?_⟩
  · show (ents.map Prod.fst).Nodup; rw [hE.1]; exact hinv.ks_nodup
  · show (acts.map Prod.fst).Nodup; rw [hA.1]; exact hinv.uids_nodup
  · intro ety rty hr
    simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hr
    obtain ⟨entry, hf, rfl⟩ := hr
    exact ((hent hf).1.tyWf_typeValid (env := ⟨Map.mk ents, Map.mk acts, reqty⟩) hv).1
  · intro ety ty hr
    simp only [EntitySchema.tags?, Option.map_eq_some_iff] at hr
    obtain ⟨entry, hf, ht⟩ := hr
    exact (((hent hf).2 ty ht).tyWf_typeValid (env := ⟨Map.mk ents, Map.mk acts, reqty⟩) hv).1
  · cases hreq
    case mk p ty eid res ctx h₁ h₂ h₃ h₄ =>
            exact (h₄.tyF.tyWf_typeValid
              (env := ⟨Map.mk ents, Map.mk acts, ⟨p, ⟨ty, eid⟩, res, Map.mk ctx⟩⟩) hv).1
  · intro ety rty hr
    simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hr
    obtain ⟨entry, hf, rfl⟩ := hr
    exact ((hent hf).1.tyWf_typeValid (env := ⟨Map.mk ents, Map.mk acts, reqty⟩) hv).2
  · intro ety ty hr
    simp only [EntitySchema.tags?, Option.map_eq_some_iff] at hr
    obtain ⟨entry, hf, ht⟩ := hr
    exact (((hent hf).2 ty ht).tyWf_typeValid (env := ⟨Map.mk ents, Map.mk acts, reqty⟩) hv).2
  · cases hreq
    case mk p ty eid res ctx h₁ h₂ h₃ h₄ =>
      exact ⟨hv _ h₁.mem, hv _ h₂.mem, hv _ h₃.mem,
        (h₄.tyF.tyWf_typeValid
          (env := ⟨Map.mk ents, Map.mk acts, ⟨p, ⟨ty, eid⟩, res, Map.mk ctx⟩⟩) hv).2⟩
  · rw [environments_length]; exact hA.2.1

/-- **Soundness for `typeOf`.** At every flag setting, the environments satisfy `EnvAssumptions`
and have at most `budget` request environments. -/
theorem GenTypeEnvF.envAssumptions {m a e d c n i r b env}
    (h : GenTypeEnvF m a e d c n i r b env) :
    EnvAssumptions env ∧ env.schema.environments.length ≤ b :=
  (h.mono (BLe.refl _) (BLe.refl _) (BLe.refl _) (BLe.false_le _) (BLe.refl _) (BLe.refl _)
    (BLe.refl _)).envAssumptions_free

/-! ## Soundness: `TypeEnvWF` -/

/-- **Soundness for `validateWellFormed`.** With the four `wf` flags, every environment is
`TypeEnvWF`, whatever the other flags. -/
theorem GenTypeEnvF.typeEnvWF {c n i r b env} (h : GenTypeEnvF true true true true c n i r b env) :
    TypeEnvWF env := by
  match h with
  | .decl _ _ _ _ _ _ _ _ ents acts reqty sk hreg hsk hents hacts =>
  have hinv := hsk.inv
  have hE := hents.ok hinv
  have hA := hacts.ok hinv
  simp only [id] at hE hA
  have hmem : ∀ x, x ∈ sk.ks ∨ x ∈ sk.ats →
      x ∈ ents.map Prod.fst ∨ x ∈ (acts.map Prod.fst).map (·.ty) := fun x hx => by
    rw [hE.1, hA.1, ← hinv.ats_eq]; exact hx
  have hwf : ∀ x, x ∈ sk.ks ∨ x ∈ sk.ats → EntityTypeWF (Map.mk ents) (Map.mk acts) x :=
    fun x hx => entityTypeWF_of_mem (hmem x hx)
  have hentsSorted : KeysSorted ents := keysSorted_of_map_fst (by rw [hE.1]; exact hinv.ks_sorted rfl)
  have hactsSorted : KeysSorted acts := keysSorted_of_map_fst (by rw [hA.1]; exact hinv.uids_sorted rfl)
  refine .mk _ _ _ (.mk _ _ ents hentsSorted ?_) (.mk _ _ acts hactsSorted ?_ ?_ ?_) ?_
  · -- entity entries
    refine entityEntriesWF_iff.mpr fun p hp => ?_
    obtain ⟨hshape, hdecl, hsorted⟩ := hE.2 p hp
    obtain ⟨x, entry⟩ := p
    cases entry with
    | standard se =>
      obtain ⟨⟨ancs⟩, attrs, tags⟩ := se
      obtain ⟨ha, ht⟩ := hshape
      have hattrs := ha.tyF.cedarTypeWF hwf
      refine .standard _ _ _ (.mk _ _ ancs attrs tags (hsorted rfl) ?_ hattrs.1 hattrs.2 ?_)
      · refine entityAncestorsWF_iff.mpr fun y hy => ?_
        have hy := hdecl rfl y hy
        rw [← hE.1] at hy
        obtain ⟨v, hv⟩ := mem_keys_iff.mp hy
        exact Map.contains_iff_some_find?.mp
          (map_contains_iff_mapContains.mpr ⟨_, mem_toList_mapContains (m := Map.mk ents) hv⟩)
      · cases ht
        case none => exact .none _ _
        case some h => have := h.cedarTypeWF hwf; exact .some _ _ _ this.1 this.2
    | enum eids =>
      obtain ⟨l⟩ := eids
      cases hshape
      case mk raw h₁ h₂ =>
        cases h₁ with
        | consT =>
          have hne := h₂.ne_nil
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
          exact .enum _ _ _ _ h₂.sorted
  · -- action entries
    refine actionEntriesWF_iff.mpr fun p hp => ⟨?_, ?_⟩
    · have hu : p.1 ∈ sk.uids := by rw [← hA.1]; exact List.mem_map.mpr ⟨_, hp, rfl⟩
      have hty := hinv.uids_ty p.1 hu
      have hnot : NotInIf true p.1.ty sk.ks := by cases hty; assumption
      cases hnot
      case strict hnot =>
        refine mapNotContainsKey_find? (mapNotContainsKey_of_absent fun v hv => ?_)
        have : p.1.ty ∈ ents.map Prod.fst := List.mem_map.mpr ⟨_, hv, rfl⟩
        rw [hE.1] at this
        exact notInET_iff.mp hnot this
    · obtain ⟨⟨hps, hpss, hrs, hrss, hctx⟩, hdecl, hasorted⟩ := hA.2.2.1 p hp
      obtain ⟨u, ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ctx⟩⟩ := p
      have hc := hctx.tyF.cedarTypeWF hwf
      refine .mk _ _ ps rs ancs ctx (hpss rfl) (hrss rfl) (hasorted rfl)
        (entityTypesWF_iff.mpr fun y hy => hwf _ (hps y hy).mem)
        (entityTypesWF_iff.mpr fun y hy => hwf _ (hrs y hy).mem) ?_ hc.1 hc.2
      refine actionAncestorsWF_iff.mpr fun y hy => ?_
      have hy := hdecl rfl y hy
      rw [← hA.1] at hy
      obtain ⟨v, hv⟩ := mem_keys_iff.mp hy
      exact map_contains_iff_mapContains.mpr ⟨_, mem_toList_mapContains (m := Map.mk acts) hv⟩
  · -- acyclic
    refine .mk _ (actionsIrreflexive_iff.mpr fun p hp => ?_)
    exact (irreflB_iff actAncs acts).mp (hA.2.2.2.2 trivial).2 p hp
  · -- transitive
    refine .mk _ (actionsTransitive_iff.mpr fun p hp => actionsTransitiveFrom_iff.mpr ?_)
    intro q hq hqp x hx
    exact (closedB_iff actAncs acts).mp (hA.2.2.2.2 trivial).1 p hp q hq hqp x hx
  · -- the request
    obtain ⟨p, u, res, ctx⟩ := reqty
    obtain ⟨en, hen, hp, hr, hctx⟩ := hA.2.2.2.1
    obtain ⟨⟨ps⟩, ⟨rs⟩, ancs, ctx'⟩ := en
    simp only at hctx hp hr
    subst hctx
    have hwfm : (Map.mk acts).WellFormed := Map.mk_wf (keysSorted_iff_sortedBy.mp hactsSorted)
    exact .mk _ _ _ _ _ _ _ _ (mapFind_iff_find?.mpr (Map.mem_toList_find? hwfm hen))
      (setContains_mk_iff_mem.mpr hp) (setContains_mk_iff_mem.mpr hr)

end Cedar.Validation.Relational.SchemaGen

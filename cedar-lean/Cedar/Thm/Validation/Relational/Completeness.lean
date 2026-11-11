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

public import Cedar.Thm.Validation.Relational.CapsCongr
public import Cedar.Thm.Validation.Relational.Flags
import Batteries.Data.List.Lemmas
import all Cedar.Data.List -- unfolds `mapM₂`
import all Cedar.Data.Map -- unfolds `contains`, `empty`, `find`, …
import all Cedar.Data.Set -- unfolds `all`, `any`, `contains`, …
import all Cedar.Spec.Entities -- unfolds `ancestors`, `attrs`, `tags`
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.Subtyping -- unfolds `lub`, `lubBool`, `lubQualifiedType`, …
import all Cedar.Validation.Typechecker -- unfolds `Capabilities`, `actionUID`, `entityUID`, …
import all Cedar.Validation.TypedExpr -- unfolds `typeOf`
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `QualifiedType`, …
import all Cedar.Validation.Validator -- unfolds `checkEntities`, `environment`, `environments`

/-! # Completeness of the relational typing spec

Every successful run of `typeOf` is witnessed by `HasType false false` (`typeOf_complete`), giving
`hasType_iff_typeOf_ok` with `hasType_sound`. -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Reverse bridges (functional lookup ⇒ relational witness) -/

/-- List membership ⇒ `MapContains`. -/
theorem mem_mapContains {α β : Type} {k : α} {v : β} {l : List (α × β)} (h : (k, v) ∈ l) :
    MapContains k v (Map.mk l) := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact MapContains.here _ _ _
    · exact MapContains.there _ _ _ _ _ (ih h)

/-- `Map.find? = some` ⇒ `MapContains` (reverse of `mapContains_find?_nodup`). -/
theorem find?_mapContains {α β : Type} [LT α] [DecidableLT α] [DecidableEq α]
    {m : Map α β} {k : α} {v : β} (h : m.find? k = some v) : MapContains k v m := by
  obtain ⟨l⟩ := m
  exact mem_mapContains (Map.find?_mem_toList h)

/-- `MapContains` on an `EntityUID` key ⇒ `MapContainsPairKey` (some entry, possibly a
    duplicate-key head). Proved by induction on the membership witness. -/
theorem mapContainsPairKey_of_mapContains {v : Type} {ety : EntityType} {eid : String}
    {entry : v} {acts : Map EntityUID v} (h : MapContains ⟨ety, eid⟩ entry acts) :
    ∃ e, MapContainsPairKey ety eid e acts := by
  induction h with
  | here => exact ⟨entry, MapContainsPairKey.here⟩
  | there k' _ _ _ ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨a', b'⟩ := k'
    by_cases ha : ety = a'
    · by_cases hb : eid = b'
      · subst ha; subst hb; exact ⟨_, MapContainsPairKey.here⟩
      · exact ⟨e, MapContainsPairKey.nextB hb he⟩
    · exact ⟨e, MapContainsPairKey.nextA ha he⟩

/-- Reverse of `mapContainsPairKey_actionType?`: an `actionType?` type has *some* action UID. -/
theorem actionType?_mapContainsPairKey {ety : EntityType} {acts : ActionSchema}
    (h : ActionSchema.actionType? acts ety = true) :
    ∃ eid entry, MapContainsPairKey ety eid entry acts := by
  simp only [ActionSchema.actionType?, Set.any, Map.keys, Map.toList, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨u, hmem, hty⟩ := h
  obtain ⟨⟨u', entry⟩, hpair_mem, hpair_fst⟩ := List.mem_map.mp hmem
  subst hpair_fst
  obtain ⟨ety', eid'⟩ := u'
  subst hty
  obtain ⟨e, hpk⟩ := mapContainsPairKey_of_mapContains (mem_toList_mapContains hpair_mem)
  exact ⟨eid', e, hpk⟩

/-- `EntitySchema.isValidEntityUID` ⇒ `ValidEntityUID` (standard/enum witnesses). -/
theorem validEntityUID_of_isValid {ets : EntitySchema} {acts : ActionSchema} {uid : EntityUID}
    (h : ets.isValidEntityUID uid = true) :
    ValidEntityUID uid.ty uid.eid ets acts := by
  simp only [EntitySchema.isValidEntityUID] at h
  split at h
  · rename_i entry hfind
    have hmc := find?_mapContains hfind
    cases entry with
    | standard s => exact ValidEntityUID.standard _ _ _ _ _ hmc
    | enum eids =>
      simp only [EntitySchemaEntry.isValidEntityEID] at h
      exact ValidEntityUID.enum _ _ _ _ _ hmc ((setContains_iff_contains).mpr h)
  · simp at h

/-- The entity-literal validity test of `typeOfLit` and `checkEntities` gives `ValidEntityUID`. -/
theorem validEntityUID_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} (h : (ets.isValidEntityUID uid || acts.contains uid) = true) :
    ValidEntityUID uid.ty uid.eid ets acts := by
  rcases Bool.or_eq_true_iff.mp h with hv | hc
  · exact validEntityUID_of_isValid hv
  · simp only [ActionSchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨entry, hfind⟩ := hc
    obtain ⟨e, hpk⟩ := mapContainsPairKey_of_mapContains (find?_mapContains hfind)
    exact ValidEntityUID.action uid.ty uid.eid ets acts e hpk

/-- `≠` on `BoolType` ⇒ `BoolTypeNeq` (reverse of `boolTypeNeq_ne`). -/
theorem boolTypeNeq_of_ne {b₁ b₂ : BoolType} (h : b₁ ≠ b₂) : BoolTypeNeq b₁ b₂ := by
  cases b₁ <;> cases b₂ <;> first | exact absurd rfl h | constructor

/-- `lub? = some` ⇒ `Lub` (reverse of `lub_sound`), with the `LubQualified`/`LubRecord`
    reverses proved simultaneously by functional induction on `lub?`. -/
theorem lub?_lub (ty₁ ty₂ : CedarType) : ∀ {t}, lub? ty₁ ty₂ = some t → Lub ty₁ ty₂ t := by
  induction ty₁, ty₂ using lub?.induct
    (motive_1 := fun q₁ q₂ => ∀ {q}, lubQualifiedType q₁ q₂ = some q → LubQualified q₁ q₂ q)
    (motive_3 := fun r₁ r₂ => ∀ {r}, lubRecordType r₁ r₂ = some r → LubRecord r₁ r₂ r) with
  | case1 b₁ b₂ =>
    intro t h; simp only [lub?, Option.some.injEq] at h; subst h
    by_cases hb : b₁ = b₂
    · subst hb; simp only [lubBool]; exact Lub.boolSame _
    · rw [show lubBool b₁ b₂ = .anyBool from by simp only [lubBool, ite_eq_right hb]]
      exact Lub.boolDiff _ _ (boolTypeNeq_of_ne hb)
  | case2 s₁ s₂ ih =>
    intro t h; simp only [lub?] at h
    cases hs : s₁ ⊔ s₂ with
    | none => rw [hs] at h; simp at h
    | some s =>
      rw [hs] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact Lub.set _ _ _ (ih hs)
  | case3 r₁ r₂ ih3 =>
    intro t h; simp only [lub?] at h
    cases hr : lubRecordType r₁ r₂ with
    | none => rw [hr] at h; simp at h
    | some r =>
      rw [hr] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact Lub.record _ _ _ (ih3 hr)
  | case4 ty₂ hb hs hr =>
    intro t h
    rw [Cedar.Thm.lub_refl] at h; simp only [Option.some.injEq] at h; subst h
    cases ty₂ with
    | int => exact Lub.int
    | string => exact Lub.string
    | entity ety => exact Lub.entity ety
    | ext xty => exact Lub.ext xty
    | bool b => exact (hb b b rfl rfl).elim
    | set s => exact (hs s s rfl rfl).elim
    | record m => obtain ⟨kvs⟩ := m; exact (hr kvs kvs rfl rfl).elim
  | case5 a ty₂ hne _ _ _ => intro t h; simp only [lub?] at h; split at h <;> simp_all
  | case6 => rename_i r h; simp only [lubRecordType, Option.some.injEq] at h; subst h; exact LubRecord.nil
  | case7 k₁ v₁ r₁ k₂ v₂ r₂ hbne => rename_i r h; simp [lubRecordType, hbne] at h
  | case8 k₁ v₁ r₁ k₂ v₂ r₂ hbne ihq ihr =>
    rename_i r h
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
        exact LubRecord.cons _ _ _ _ _ _ _ (ihq hty) (ihr htys)
  | case9 t ty₂ _ _ => rename_i r h; simp [lubRecordType] at h
  | case10 ty₁ ty₂ ih =>
    rename_i q h; simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact LubQualified.optional _ _ _ (ih hlub)
  | case11 ty₁ ty₂ ih =>
    rename_i q h; simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact LubQualified.required _ _ _ (ih hlub)
  | case12 t q₂ _ _ => rename_i q h; simp [lubQualifiedType] at h

/-! ## Entity-type declaredness invariant -/

open Schema (WfCedarType WfAttrs WfEntitiesGo WfEntitySchema WfActionsGo WfActionSchema
  RequestFromAction DefinedEntityType WfPrincipalTypes WfResourceTypes)

/-- A valid entity UID's type is a declared entity type. -/
theorem validEntityUID_validType {ety eid ets acts} (h : ValidEntityUID ety eid ets acts) :
    ValidEntityType ety ets acts := by
  cases h with
  | standard => exact ValidEntityType.inSchema _ _ _ _ (by assumption)
  | enum => exact ValidEntityType.inSchema _ _ _ _ (by assumption)
  | action => exact ValidEntityType.isAction _ _ _ _ _ (by assumption)

/-- `DefinedEntityType allNames` splits as membership in the accumulated `names` or a
    key of the built entries. -/
theorem wfEntitiesGo_names {built names allNames entries ety}
    (h : WfEntitiesGo built names allNames entries) :
    DefinedEntityType allNames ety →
      DefinedEntityType names ety ∨ ∃ v, MapContains ety v (Map.mk entries) := by
  induction h with
  | nil built names => intro hd; exact Or.inl hd
  | standard built names et ancestors attrs tags allNames rest hni hpick hwa hwt hgo ih =>
    intro hd
    rcases ih hd with hn | ⟨v, hmc⟩
    · cases hn with
      | here => exact Or.inr ⟨_, MapContains.here _ _ _⟩
      | there _ _ _ _ hd' => exact Or.inl hd'
    · exact Or.inr ⟨v, MapContains.there _ _ _ _ _ hmc⟩
  | enum built names et eids allNames rest hni hgo ih =>
    intro hd
    rcases ih hd with hn | ⟨v, hmc⟩
    · cases hn with
      | here => exact Or.inr ⟨_, MapContains.here _ _ _⟩
      | there _ _ _ _ hd' => exact Or.inl hd'
    · exact Or.inr ⟨v, MapContains.there _ _ _ _ _ hmc⟩

/-- The accumulated `names` are all in `allNames`. -/
theorem wfEntitiesGo_names_mono {built names allNames entries}
    (h : WfEntitiesGo built names allNames entries) :
    ∀ e, DefinedEntityType names e → DefinedEntityType allNames e := by
  induction h with
  | nil built names => intro e he; exact he
  | standard built names et ancestors attrs tags allNames rest hni hpick hwa hwt hrest ih =>
    intro e he; refine ih e ?_
    by_cases hee : e = et
    · subst hee; exact DefinedEntityType.here _ _
    · exact DefinedEntityType.there _ _ _ hee he
  | enum built names et eids allNames rest hni hrest ih =>
    intro e he; refine ih e ?_
    by_cases hee : e = et
    · subst hee; exact DefinedEntityType.here _ _
    · exact DefinedEntityType.there _ _ _ hee he

/-- Entity types declared in a well-formed entity schema are `ValidEntityType`. -/
theorem definedEntityType_valid {allNames entries acts ety}
    (h : WfEntitySchema allNames entries) (hd : DefinedEntityType allNames ety) :
    ValidEntityType ety (Map.mk entries) acts := by
  cases h with
  | mk hgo =>
    rcases wfEntitiesGo_names hgo hd with hn | ⟨v, hmc⟩
    · cases hn
    · exact ValidEntityType.inSchema ety v (Map.mk entries) acts hmc

/-- A `WfCedarType` over declared names is `TypeValid` (given the names→declared bridge). -/
theorem wfCedarType_typeValid {env : TypeEnv} :
    ∀ {names ty}, WfCedarType names ty →
      (∀ e, DefinedEntityType names e → ValidEntityType e env.ets env.acts) → TypeValid env ty := by
  intro names ty h
  induction h using WfCedarType.rec
    (motive_2 := fun _lb names attrs _ =>
      (∀ e, DefinedEntityType names e → ValidEntityType e env.ets env.acts) →
        ∀ p ∈ attrs, TypeValid env p.2.getType) with
  | bool => intro _; exact TypeValid.bool _
  | int => intro _; exact TypeValid.int
  | string => intro _; exact TypeValid.string
  | entity ets ety hdef => intro hbr; exact TypeValid.entity ety (hbr ety hdef)
  | set ets ty hwf ih => intro hbr; exact TypeValid.set _ (ih hbr)
  | record ets attrs hwa ih => intro hbr; exact TypeValid.record _ (ih hbr)
  | extDecimal => intro _; exact TypeValid.ext _
  | extIPAddr => intro _; exact TypeValid.ext _
  | extDatetime => intro _; exact TypeValid.ext _
  | extDuration => intro _; exact TypeValid.ext _
  | nil lb ets => rename_i hbr p hp; simp at hp
  | consRequired lb ets attr ty rest hka hwf hrest ihty ihrest =>
    rename_i hbr p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ihty hbr
    · exact ihrest hbr p hmem
  | consOptional lb ets attr ty rest hka hwf hrest ihty ihrest =>
    rename_i hbr p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ihty hbr
    · exact ihrest hbr p hmem

/-- Each entry's attribute record in a well-formed entity schema is `TypeValid`. -/
theorem wfEntitiesGo_attrs_typeValid {env : TypeEnv} {allNames entries built names}
    (h : WfEntitiesGo built names allNames entries) :
    (∀ e, DefinedEntityType allNames e → ValidEntityType e env.ets env.acts) →
    (∀ e, DefinedEntityType names e → DefinedEntityType allNames e) →
      ∀ ety entry, (ety, entry) ∈ entries → TypeValid env (.record entry.attrs) := by
  induction h with
  | nil built names => intro _ _ ety entry hmem; simp at hmem
  | standard built names et ancestors attrs tags allNames rest hni hpick hwa hwt hrest ih =>
    intro hbridge hsub ety entry hmem
    have hsub' : ∀ e, DefinedEntityType (et :: names) e → DefinedEntityType allNames e := by
      intro e he'
      cases he' with
      | here => exact wfEntitiesGo_names_mono hrest et (DefinedEntityType.here _ _)
      | there _ _ _ _ hd => exact hsub e hd
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp only [EntitySchemaEntry.attrs]
      exact wfCedarType_typeValid (WfCedarType.record (et :: names) attrs hwa)
        (fun e hd => hbridge e (hsub' e hd))
    · exact ih hbridge hsub' ety entry hmem
  | enum built names et eids allNames rest hni hrest ih =>
    intro hbridge hsub ety entry hmem
    have hsub' : ∀ e, DefinedEntityType (et :: names) e → DefinedEntityType allNames e := by
      intro e he'
      cases he' with
      | here => exact wfEntitiesGo_names_mono hrest et (DefinedEntityType.here _ _)
      | there _ _ _ _ hd => exact hsub e hd
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp only [EntitySchemaEntry.attrs]
      exact TypeValid.record [] (by intro p hp; simp at hp)
    · exact ih hbridge hsub' ety entry hmem

/-- Each entry's tag type in a well-formed entity schema is `TypeValid`. -/
theorem wfEntitiesGo_tags_typeValid {env : TypeEnv} {allNames entries built names}
    (h : WfEntitiesGo built names allNames entries) :
    (∀ e, DefinedEntityType allNames e → ValidEntityType e env.ets env.acts) →
    (∀ e, DefinedEntityType names e → DefinedEntityType allNames e) →
      ∀ ety entry ty, (ety, entry) ∈ entries → entry.tags? = some ty → TypeValid env ty := by
  induction h with
  | nil built names => intro _ _ ety entry ty hmem _; simp at hmem
  | standard built names et ancestors attrs tags allNames rest hni hpick hwa hwt hrest ih =>
    intro hbridge hsub ety entry ty hmem htag
    have hsub' : ∀ e, DefinedEntityType (et :: names) e → DefinedEntityType allNames e := by
      intro e he'
      cases he' with
      | here => exact wfEntitiesGo_names_mono hrest et (DefinedEntityType.here _ _)
      | there _ _ _ _ hd => exact hsub e hd
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp only [EntitySchemaEntry.tags?] at htag
      cases hwt with
      | none => simp at htag
      | some ty' hwct =>
        simp only [Option.some.injEq] at htag; subst htag
        exact wfCedarType_typeValid hwct (fun e hd => hbridge e (hsub' e hd))
    · exact ih hbridge hsub' ety entry ty hmem htag
  | enum built names et eids allNames rest hni hrest ih =>
    intro hbridge hsub ety entry ty hmem htag
    have hsub' : ∀ e, DefinedEntityType (et :: names) e → DefinedEntityType allNames e := by
      intro e he'
      cases he' with
      | here => exact wfEntitiesGo_names_mono hrest et (DefinedEntityType.here _ _)
      | there _ _ _ _ hd => exact hsub e hd
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq; subst he
      simp [EntitySchemaEntry.tags?] at htag
    · exact ih hbridge hsub' ety entry ty hmem htag

/-- Attributes looked up in a well-formed schema form a `TypeValid` record. -/
theorem wfTypeEnv_attrs?_typeValid {env : TypeEnv} (hwf : Schema.WfTypeEnv env) {ety rty}
    (hattr : EntitySchema.attrs? env.ets ety = some rty) : TypeValid env (.record rty) := by
  cases hwf with
  | mk entityTypes entityEntries actionEntries reqty hes has hrfa =>
    simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattr
    obtain ⟨entry, hfind, hea⟩ := hattr
    have hmem := Map.find?_mem_toList hfind
    cases hes with
    | mk hgo =>
      have hbridge : ∀ e, DefinedEntityType entityTypes e →
          ValidEntityType e (Map.mk entityEntries) (Map.mk actionEntries) :=
        fun e hd => definedEntityType_valid (WfEntitySchema.mk _ _ hgo) hd
      rw [← hea]
      exact wfEntitiesGo_attrs_typeValid hgo hbridge (fun _ h => by cases h) _ entry hmem

/-- A tag type looked up in a well-formed schema is `TypeValid`. -/
theorem wfTypeEnv_tags?_typeValid {env : TypeEnv} (hwf : Schema.WfTypeEnv env) {ety ty}
    (htag : EntitySchema.tags? env.ets ety = some (some ty)) : TypeValid env ty := by
  cases hwf with
  | mk entityTypes entityEntries actionEntries reqty hes has hrfa =>
    simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htag
    obtain ⟨entry, hfind, hea⟩ := htag
    have hmem := Map.find?_mem_toList hfind
    cases hes with
    | mk hgo =>
      have hbridge : ∀ e, DefinedEntityType entityTypes e →
          ValidEntityType e (Map.mk entityEntries) (Map.mk actionEntries) :=
        fun e hd => definedEntityType_valid (WfEntitySchema.mk _ _ hgo) hd
      exact wfEntitiesGo_tags_typeValid hgo hbridge (fun _ h => by cases h) _ entry ty hmem hea

/-! ### Request-type declaredness (reqty entity components come from the action schema) -/

theorem definedEntityType_setContains {l : List EntityType} {x : EntityType}
    (h : DefinedEntityType l x) : SetContains x (Set.mk l) := by
  induction h with
  | here et rest => exact SetContains.here _ _
  | there et et' rest _ _ ih => exact SetContains.there _ _ _ ih

theorem wfPrincipalTypes_defined {ets principals p} (h : WfPrincipalTypes ets principals)
    (hmem : SetContains p (Set.mk principals)) : DefinedEntityType ets p := by
  induction h with
  | nil => cases hmem
  | cons p' rest hdef hrest ih =>
    cases hmem with
    | here => exact hdef
    | there _ _ hm => exact ih hm

theorem wfResourceTypes_defined {ets resources r} (h : WfResourceTypes ets resources)
    (hmem : SetContains r (Set.mk resources)) : DefinedEntityType ets r := by
  induction h with
  | nil => cases hmem
  | cons r' rest hdef hrest ih =>
    cases hmem with
    | here => exact hdef
    | there _ _ hm => exact ih hm

theorem wfActionsGo_mem_principals {ets built avail entries}
    (h : WfActionsGo ets built avail entries) :
    ∀ {uid principals r a ctx}, (uid, ActionSchemaEntry.mk (Set.mk principals) r a ctx) ∈ entries →
      WfPrincipalTypes ets principals := by
  induction h with
  | nil => intro uid principals r a ctx hmem; simp at hmem
  | cons built avail avail' eid ancestors principals resources context rest
      hsel hpick hwp hwr hwa hrest ih =>
    intro uid principals' r a ctx hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq
      injection he with hp _ _ _; injection hp with hpp; subst hpp; exact hwp
    · exact ih hmem

theorem wfActionsGo_mem_resources {ets built avail entries}
    (h : WfActionsGo ets built avail entries) :
    ∀ {uid p resources a ctx}, (uid, ActionSchemaEntry.mk p (Set.mk resources) a ctx) ∈ entries →
      WfResourceTypes ets resources := by
  induction h with
  | nil => intro uid p resources a ctx hmem; simp at hmem
  | cons built avail avail' eid ancestors principals resources context rest
      hsel hpick hwp hwr hwa hrest ih =>
    intro uid p resources' a ctx hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq; obtain ⟨_, he⟩ := heq
      injection he with _ hr _ _; injection hr with hrr; subst hrr; exact hwr
    · exact ih hmem

theorem requestFromAction_mem {ets acts reqty} (h : RequestFromAction ets acts reqty) :
    ∃ entry, (reqty.action, entry) ∈ acts ∧
      SetContains reqty.principal entry.appliesToPrincipal ∧
      SetContains reqty.resource entry.appliesToResource := by
  induction h with
  | here acts uid principals resources ancestors context principal resource hp hr =>
    exact ⟨ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context),
      by simp, definedEntityType_setContains hp, definedEntityType_setContains hr⟩
  | there act acts reqty hrfa ih =>
    obtain ⟨entry, hmem, hp, hr⟩ := ih
    exact ⟨entry, by simp [hmem], hp, hr⟩

/-- The request type's principal/resource/action entity types are declared, and its
    context is a `TypeValid` record. -/
theorem wfTypeEnv_reqty_valid {env : TypeEnv} (hwf : Schema.WfTypeEnv env) :
    ValidEntityType env.reqty.principal env.ets env.acts ∧
    ValidEntityType env.reqty.resource env.ets env.acts ∧
    ValidEntityType env.reqty.action.ty env.ets env.acts ∧
    TypeValid env (.record env.reqty.context) := by
  cases hwf with
  | mk entityTypes entityEntries actionEntries reqty hes has hrfa =>
    obtain ⟨entry, hmem, hp, hr⟩ := requestFromAction_mem hrfa
    have hbridge : ∀ e, DefinedEntityType entityTypes e →
        ValidEntityType e (Map.mk entityEntries) (Map.mk actionEntries) :=
      fun e hd => definedEntityType_valid hes hd
    cases has with
    | mk hgo =>
      obtain ⟨aprin, ares, aanc, actx⟩ := entry
      obtain ⟨pl⟩ := aprin; obtain ⟨rl⟩ := ares
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hbridge _ (wfPrincipalTypes_defined (wfActionsGo_mem_principals hgo hmem) hp)
      · exact hbridge _ (wfResourceTypes_defined (wfActionsGo_mem_resources hgo hmem) hr)
      · obtain ⟨e', hpk⟩ := mapContainsPairKey_of_mapContains (mem_mapContains hmem)
        exact ValidEntityType.isAction _ _ _ _ _ hpk
      · obtain ⟨uid, p, r, a, ctx, hc, hcmem⟩ := requestFromAction_ctx_mem hrfa
        rw [hc]
        exact wfCedarType_typeValid
          (WfCedarType.record entityTypes ctx (wfActionsGo_mem_ctx_wf hgo hcmem)) hbridge

/-! ### `lub?` preserves `TypeValid` -/

theorem lub?_typeValid {env : TypeEnv} (ty₁ ty₂ : CedarType) :
    ∀ {t}, lub? ty₁ ty₂ = some t → TypeValid env ty₁ → TypeValid env ty₂ → TypeValid env t := by
  induction ty₁, ty₂ using lub?.induct
    (motive_1 := fun q₁ q₂ => ∀ {q}, lubQualifiedType q₁ q₂ = some q →
      TypeValid env q₁.getType → TypeValid env q₂.getType → TypeValid env q.getType)
    (motive_3 := fun r₁ r₂ => ∀ {r}, lubRecordType r₁ r₂ = some r →
      TypeValid env (.record (Map.mk r₁)) → TypeValid env (.record (Map.mk r₂)) →
        TypeValid env (.record (Map.mk r))) with
  | case1 b₁ b₂ => intro t h _ _; simp only [lub?, Option.some.injEq] at h; subst h; exact TypeValid.bool _
  | case2 s₁ s₂ ih =>
    intro t h hv1 hv2; simp only [lub?] at h
    cases hs : s₁ ⊔ s₂ with
    | none => rw [hs] at h; simp at h
    | some s =>
      rw [hs] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      cases hv1 with | set _ hv1' => cases hv2 with | set _ hv2' => exact TypeValid.set _ (ih hs hv1' hv2')
  | case3 r₁ r₂ ih3 =>
    intro t h hv1 hv2; simp only [lub?] at h
    cases hr : lubRecordType r₁ r₂ with
    | none => rw [hr] at h; simp at h
    | some r =>
      rw [hr] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact ih3 hr hv1 hv2
  | case4 ty₂ hb hs hr =>
    intro t h _ hv2; rw [Cedar.Thm.lub_refl] at h; simp only [Option.some.injEq] at h; subst h; exact hv2
  | case5 a ty₂ hne _ _ _ => intro t h _ _; simp only [lub?] at h; split at h <;> simp_all
  | case6 => rename_i r h _ _; simp only [lubRecordType, Option.some.injEq] at h; subst h; exact TypeValid.record [] (by simp)
  | case7 k₁ v₁ r₁ k₂ v₂ r₂ hbne => rename_i r h _ _; simp [lubRecordType, hbne] at h
  | case8 k₁ v₁ r₁ k₂ v₂ r₂ hbne ihq ihr =>
    rename_i r h hvr1 hvr2
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
        cases hvr1 with | record _ hc1 => cases hvr2 with | record _ hc2 =>
          refine TypeValid.record _ ?_
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hpm
          · exact ihq hty (hc1 (k₁, v₁) (by simp)) (hc2 (k₁, v₂) (by simp))
          · have hrec := ihr htys (TypeValid.record _ (fun q hq => hc1 q (by simp [hq])))
              (TypeValid.record _ (fun q hq => hc2 q (by simp [hq])))
            cases hrec with | record _ hct => exact hct p hpm
  | case9 t ty₂ _ _ => rename_i r h _ _; simp [lubRecordType] at h
  | case10 ty₁ ty₂ ih =>
    rename_i q h hv1 hv2; simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact ih hlub hv1 hv2
  | case11 ty₁ ty₂ ih =>
    rename_i q h hv1 hv2; simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact ih hlub hv1 hv2
  | case12 t q₂ _ _ => rename_i q h _ _; simp [lubQualifiedType] at h

/-! ### `typeOf`-helper `TypeValid` lemmas (result-type validity) -/

/-- `getAttrInRecord` returns a `TypeValid` type when the receiver record is `TypeValid`. -/
theorem getAttrInRecord_typeValid {env : TypeEnv} {ty rty x a c aty ac}
    (hrec : TypeValid env (.record rty)) (hg : getAttrInRecord ty rty x a c = .ok (aty, ac)) :
    TypeValid env aty := by
  simp only [getAttrInRecord] at hg
  cases hrec with
  | record rts hcomp =>
    split at hg
    · rename_i qty hfind
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hg; obtain ⟨rfl, _⟩ := hg
      have := hcomp _ (Map.find?_mem_toList hfind); simpa [Qualified.getType] using this
    · rename_i aty' hfind
      split at hg
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hg; obtain ⟨rfl, _⟩ := hg
        have := hcomp _ (Map.find?_mem_toList hfind); simpa [Qualified.getType] using this
      · simp only [err, reduceCtorEq] at hg
    · simp only [err, reduceCtorEq] at hg

/-- `hasAttrInRecord` always returns a boolean type. -/
theorem hasAttrInRecord_typeValid {env : TypeEnv} {rty x a c k ty c'}
    (h : hasAttrInRecord rty x a c k = .ok (ty, c')) : TypeValid env ty := by
  simp only [hasAttrInRecord] at h
  split at h
  · split at h <;> (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact TypeValid.bool _)
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact TypeValid.bool _

/-- `typeOfEq` always returns a boolean type. -/
theorem typeOfEq_typeValid {env : TypeEnv} {ty₁ ty₂ : TypedExpr} {x₁ x₂ tx c'}
    (h : typeOfEq ty₁ ty₂ x₁ x₂ = .ok (tx, c')) : TypeValid env tx.typeOf := by
  simp only [typeOfEq] at h
  split at h
  · split at h <;>
      (simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.bool _)
  · split at h
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.bool _
    · split at h
      · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.bool _
      · simp only [err, reduceCtorEq] at h

/-- `typeOfHasTag` always returns a boolean type. -/
theorem typeOfHasTag_typeValid {env : TypeEnv} {ety x₁ x₂ c ty c'}
    (h : typeOfHasTag ety x₁ x₂ c env = .ok (ty, c')) : TypeValid env ty := by
  simp only [typeOfHasTag] at h
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact TypeValid.bool _
  · split at h <;> (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact TypeValid.bool _)
  · split at h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact TypeValid.bool _
    · simp only [err, reduceCtorEq] at h

/-- `typeOfGetTag` returns a `TypeValid` tag type (the schema tag type is declared). -/
theorem typeOfGetTag_typeValid {env : TypeEnv} (hwf : EnvAssumptions env) {ety x₁ x₂ c ty c'}
    (h : typeOfGetTag ety x₁ x₂ c env = .ok (ty, c')) : TypeValid env ty := by
  simp only [typeOfGetTag] at h
  split at h
  · simp only [err, reduceCtorEq] at h
  · rename_i tagTy htags
    split at h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h
      exact hwf.tags_typeValid htags
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-- An extension constructor returns the (given, `TypeValid`) type. -/
theorem typeOfConstructor_typeValid {α : Type} {env : TypeEnv} {mk : String → Option α} {xs ty t c'}
    (hty : TypeValid env ty) (h : typeOfConstructor mk xs ty = .ok (t, c')) : TypeValid env t := by
  simp only [typeOfConstructor] at h
  split at h
  · split at h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact hty
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-- Folding `lub?` over `TypeValid` element types yields a `TypeValid` type. -/
theorem foldlM_lub?_typeValid {env : TypeEnv} :
    ∀ (l : List CedarType) (acc res : CedarType), TypeValid env acc →
      (∀ t ∈ l, TypeValid env t) → l.foldlM lub? acc = some res → TypeValid env res := by
  intro l
  induction l with
  | nil =>
    intro acc res hacc _ h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; exact h ▸ hacc
  | cons hd tl ih =>
    intro acc res hacc hall h
    simp only [List.foldlM_cons] at h
    cases hlub : lub? acc hd with
    | none => rw [hlub] at h; simp at h
    | some m =>
      rw [hlub] at h; simp only [Option.bind_some_fun] at h
      exact ih m res (lub?_typeValid acc hd hlub hacc (hall hd (by simp)))
        (fun t ht => hall t (by simp [ht])) h

/-- `justType` success reflects to a `typeOf` success (recovering the discarded caps). -/
theorem justType_ok {x : Expr} {c : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h : justType (typeOf x c env) = .ok tx) : ∃ cc, typeOf x c env = .ok (tx, cc) := by
  cases hx : typeOf x c env with
  | error e => rw [hx] at h; simp [justType, Except.map] at h
  | ok v =>
    obtain ⟨t, cc⟩ := v
    rw [hx] at h; simp only [justType, Except.map, Except.ok.injEq] at h; subst h
    exact ⟨cc, rfl⟩

/-- Every element type produced by `mapM`-ing `typeOf` over a list is `TypeValid`. -/
theorem mapM_all_typeValid {env : TypeEnv} {c : Capabilities} :
    ∀ {xs' : List Expr} {ttl : List TypedExpr},
      (∀ x ∈ xs', ∀ {tx cc}, typeOf x c env = .ok (tx, cc) → TypeValid env tx.typeOf) →
      xs'.mapM (fun x => justType (typeOf x c env)) = .ok ttl →
      ∀ t ∈ ttl.map TypedExpr.typeOf, TypeValid env t := by
  intro xs'
  induction xs' with
  | nil =>
    intro ttl _ hm t ht
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm; subst hm; simp at ht
  | cons x₀ xs'' ih =>
    intro ttl hall hm t ht
    simp only [List.mapM_cons] at hm
    cases hx0 : justType (typeOf x₀ c env) with
    | error e => rw [hx0] at hm; simp at hm
    | ok thd =>
      rw [hx0] at hm; simp only [Except.bind_ok] at hm
      cases hxs : xs''.mapM (fun x => justType (typeOf x c env)) with
      | error e => rw [hxs] at hm; simp at hm
      | ok ttl' =>
        rw [hxs] at hm; simp only [pure, Except.pure, Except.bind_ok, Except.ok.injEq] at hm
        subst hm
        simp only [List.map_cons, List.mem_cons] at ht
        obtain ⟨cc0, hx02⟩ := justType_ok hx0
        rcases ht with rfl | ht
        · exact hall x₀ (by simp) hx02
        · exact ih (fun x hx => hall x (by simp [hx])) hxs t ht

/-- Every value type produced by `mapM₂`-ing `typeOf` over a record's fields is `TypeValid`. -/
theorem mapM₂_all_typeValid {env : TypeEnv} {c : Capabilities} :
    ∀ {axs : List (Attr × Expr)} {atys : List (Attr × TypedExpr)},
      (∀ ax ∈ axs, ∀ {tx cc}, typeOf ax.2 c env = .ok (tx, cc) → TypeValid env tx.typeOf) →
      axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) = .ok atys →
      ∀ p ∈ atys, TypeValid env p.2.typeOf := by
  intro axs
  induction axs with
  | nil =>
    intro atys _ hm p hp
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm; subst hm; simp at hp
  | cons ax₀ axs'' ih =>
    intro atys hall hm p hp
    simp only [List.mapM_cons] at hm
    cases ha0 : (typeOf ax₀.2 c env).map (fun r => (ax₀.1, r.1)) with
    | error e => rw [ha0] at hm; simp at hm
    | ok ahd =>
      rw [ha0] at hm; simp only [Except.bind_ok] at hm
      cases has : axs''.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
      | error e => rw [has] at hm; simp at hm
      | ok atys' =>
        rw [has] at hm; simp only [pure, Except.pure, Except.bind_ok, Except.ok.injEq] at hm; subst hm
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · cases hx0 : typeOf ax₀.2 c env with
          | error e => rw [hx0] at ha0; simp [Except.map] at ha0
          | ok r =>
            obtain ⟨thd, cc⟩ := r; rw [hx0] at ha0
            simp only [Except.map, Except.ok.injEq] at ha0; subst ha0
            exact hall ax₀ (by simp) hx0
        · exact ih (fun ax hax => hall ax (by simp [hax])) has p hp

/-- **Type validity of `typeOf`.** On an environment satisfying `EnvAssumptions`, every type
    `typeOf` produces has all its entity components declared. The analogue of Cedar's
    `typechecked_has_well_formed_type`, tracking only entity-declaredness (so it needs no map
    sortedness). -/
theorem typeOf_type_valid {env : TypeEnv} (hwf : EnvAssumptions env) :
    ∀ {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      typeOf x c env = .ok (tx, c') → TypeValid env tx.typeOf := by
  intro x c
  induction x, c using typeOf.induct with
  | case1 c p =>
    intro tx c' h
    obtain ⟨ets, acts, reqty⟩ := env
    simp only [typeOf, typeOfLit] at h
    split at h
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.bool _
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.bool _
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.int
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.string
    · split at h
      · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rename_i uid hcond
        exact TypeValid.entity _ (validEntityUID_validType (validEntityUID_of_checkEntities hcond))
      · simp only [err, reduceCtorEq] at h
  | case2 c v =>
    intro tx c' h
    obtain ⟨hp, hr, ha, hctx⟩ := hwf.reqty_valid
    simp only [typeOf, typeOfVar] at h
    split at h <;>
      (simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h)
    · exact TypeValid.entity _ hp
    · exact TypeValid.entity _ ha
    · exact TypeValid.entity _ hr
    · exact hctx
  | case3 c x₁ x₂ x₃ ih1 ih2 ih3 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok, typeOfIf] at h
      split at h
      · cases h2 : typeOf x₂ (c ∪ cc1) env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h
          simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          simp only [TypedExpr.typeOf]; exact ih2 cc1 h2
      · cases h3 : typeOf x₃ c env with
        | error e => rw [h3] at h; simp at h
        | ok r3 =>
          obtain ⟨ty3, cc3⟩ := r3; rw [h3] at h
          simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          simp only [TypedExpr.typeOf]; exact ih3 h3
      · cases h2 : typeOf x₂ (c ∪ cc1) env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h; simp only [Except.bind_ok] at h
          cases h3 : typeOf x₃ c env with
          | error e => rw [h3] at h; simp at h
          | ok r3 =>
            obtain ⟨ty3, cc3⟩ := r3; rw [h3] at h; simp only [Except.bind_ok] at h
            split at h
            · rename_i lubTy hlub
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              simp only [TypedExpr.typeOf]; exact lub?_typeValid _ _ hlub (ih2 cc1 h2) (ih3 h3)
            · simp only [err, reduceCtorEq] at h
      · simp only [err, reduceCtorEq] at h
  | case4 c x₁ x₂ ih1 ih2 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok, typeOfAnd] at h
      split at h
      · rename_i heq; simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rw [heq]; exact TypeValid.bool _
      · cases h2 : typeOf x₂ (c ∪ cc1) env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h; simp only [Except.bind_ok] at h
          split at h <;>
            first
            | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl⟩ := h
               exact TypeValid.bool _)
            | (simp only [err, reduceCtorEq] at h)
      · simp only [err, reduceCtorEq] at h
  | case5 c x₁ x₂ ih1 ih2 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok, typeOfOr] at h
      split at h
      · rename_i heq; simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rw [heq]; exact TypeValid.bool _
      · cases h2 : typeOf x₂ c env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h; simp only [Except.bind_ok] at h
          split at h
          · rename_i heq2; simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            simp only [TypedExpr.typeOf]; exact ih2 h2
          · simp only [err, reduceCtorEq] at h
      · cases h2 : typeOf x₂ c env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h; simp only [Except.bind_ok] at h
          split at h <;>
            first
            | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl⟩ := h
               exact TypeValid.bool _)
            | (simp only [err, reduceCtorEq] at h)
      · simp only [err, reduceCtorEq] at h
  | case6 c op₁ x₁ ih1 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok, typeOfUnaryApp] at h
      split at h <;>
        first
        | (simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h
           simp only [TypedExpr.typeOf]
           first | exact TypeValid.bool _ | exact TypeValid.int)
        | (simp only [err, reduceCtorEq] at h)
  | case7 c op₂ x₁ x₂ ih1 ih2 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok] at h
      cases h2 : typeOf x₂ c env with
      | error e => rw [h2] at h; simp at h
      | ok r2 =>
        obtain ⟨ty2, cc2⟩ := r2; rw [h2] at h; simp only [Except.bind_ok, typeOfBinaryApp] at h
        split at h <;>
          first
          | exact typeOfEq_typeValid h
          | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
             first | exact TypeValid.bool _ | exact TypeValid.int)
          | (rename_i ety _ _
             cases hgt : typeOfGetTag ety x₁ x₂ c env with
             | error e => rw [hgt] at h; simp at h
             | ok r => obtain ⟨tgy, tgc⟩ := r; rw [hgt] at h;
                       simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h;
                       obtain ⟨rfl, rfl⟩ := h; exact typeOfGetTag_typeValid hwf hgt)
          | (rename_i ety _ _
             cases hht : typeOfHasTag ety x₁ x₂ c env with
             | error e => rw [hht] at h; simp at h
             | ok r => obtain ⟨thy, thc⟩ := r; rw [hht] at h;
                       simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h;
                       obtain ⟨rfl, rfl⟩ := h; exact typeOfHasTag_typeValid hht)
          | (simp only [ifLubThenBool] at h; split at h <;>
             first
             | (simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact TypeValid.bool _)
             | (simp [err] at h))
          | (simp only [err, reduceCtorEq] at h)
  | case8 c x₁ a ih1 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok, typeOfHasAttr] at h
      split at h <;>
        first
        | (cases hh : hasAttrInRecord _ x₁ a c _ with
           | error e => rw [hh] at h; simp at h
           | ok r => obtain ⟨hy, hcc⟩ := r; rw [hh] at h;
                     simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h;
                     obtain ⟨rfl, rfl⟩ := h; exact hasAttrInRecord_typeValid hh)
        | (split at h <;>
           first
           | (cases hh : hasAttrInRecord _ x₁ a c _ with
              | error e => rw [hh] at h; simp at h
              | ok r => obtain ⟨hy, hcc⟩ := r; rw [hh] at h;
                        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h;
                        obtain ⟨rfl, rfl⟩ := h; exact hasAttrInRecord_typeValid hh)
           | (split at h <;>
              first
              | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact TypeValid.bool _)
              | (simp only [err, reduceCtorEq] at h)))
        | (simp only [err, reduceCtorEq] at h)
  | case9 c x₁ a as ih1 =>
    intro tx c' h
    simp only [typeOf] at h
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
        exact TypeValid.bool _
  | case10 c x₁ a ih1 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1; rw [h1] at h; simp only [Except.bind_ok, typeOfGetAttr] at h
      split at h
      · rename_i rty heqty
        cases hg : getAttrInRecord ty1.typeOf rty x₁ a c with
        | error e => rw [hg] at h; simp at h
        | ok r => obtain ⟨aty, ac⟩ := r; rw [hg] at h;
                  simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                  simp only [TypedExpr.typeOf]; exact getAttrInRecord_typeValid (heqty ▸ ih1 h1) hg
      · rename_i ety heqty
        split at h
        · rename_i rty hattr
          cases hg : getAttrInRecord ty1.typeOf rty x₁ a c with
          | error e => rw [hg] at h; simp at h
          | ok r => obtain ⟨aty, ac⟩ := r; rw [hg] at h;
                    simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                    simp only [TypedExpr.typeOf]
                    exact getAttrInRecord_typeValid (hwf.attrs_typeValid hattr) hg
        · simp only [err, reduceCtorEq] at h
      · simp only [err, reduceCtorEq] at h
  | case11 c xs ih =>
    intro tx c' h
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases xs with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, bind, Except.bind, typeOfSet, err, reduceCtorEq] at h
    | cons x₀ xs' =>
      simp only [List.mapM_cons] at h
      cases hx0 : justType (typeOf x₀ c env) with
      | error e => rw [hx0] at h; simp at h
      | ok thd =>
        rw [hx0] at h; simp only [Except.bind_ok] at h
        cases hxs' : xs'.mapM (fun x => justType (typeOf x c env)) with
        | error e => rw [hxs'] at h; simp at h
        | ok ttl =>
          rw [hxs'] at h; simp only [pure, Except.pure, bind, Except.bind, typeOfSet] at h
          split at h
          · rename_i lubty hfold
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            simp only [TypedExpr.typeOf]
            obtain ⟨cc0, hx02⟩ := justType_ok hx0
            refine TypeValid.set _ (foldlM_lub?_typeValid _ thd.typeOf lubty (ih x₀ (by simp) hx02) ?_ hfold)
            exact mapM_all_typeValid (fun x hx => ih x (by simp [hx])) hxs'
          · simp only [err, reduceCtorEq] at h
  | case12 c axs ih =>
    intro tx c' h
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1)))] at h
    cases hm : axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
    | error e => rw [hm] at h; simp at h
    | ok atys =>
      rw [hm] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hcomp : ∀ p ∈ atys, TypeValid env p.2.typeOf := by
        refine mapM₂_all_typeValid ?_ hm
        intro ax hax tx cc htyp
        have hsz : sizeOf (ax.1, ax.2).snd < 1 + sizeOf axs := by
          have hlt := List.sizeOf_lt_of_mem hax
          obtain ⟨a, x⟩ := ax
          simp only [sizeOf, Prod._sizeOf_1] at *
          omega
        exact ih ax.1 ax.2 hsz htyp
      simp only [TypedExpr.typeOf]
      refine TypeValid.record _ ?_
      intro q hq
      have hqL := Map.mem_make_mem_list hq
      simp only [List.mem_map] at hqL
      obtain ⟨p, hp, rfl⟩ := hqL
      simp only [Qualified.getType]; exact hcomp p hp
  | case13 c xfn xs ih =>
    intro tx c' h
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
    | error e => rw [hm] at h; simp at h
    | ok tys =>
      rw [hm] at h; simp only [Except.bind_ok, typeOfCall] at h
      split at h <;>
        first
        | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           first | exact TypeValid.bool _ | exact TypeValid.int | exact TypeValid.ext _)
        | (cases hcon : typeOfConstructor _ xs _ with
           | error e => rw [hcon] at h; simp at h
           | ok r => obtain ⟨cy, cc⟩ := r; rw [hcon] at h;
                     simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h;
                     obtain ⟨rfl, rfl⟩ := h; exact typeOfConstructor_typeValid (TypeValid.ext _) hcon)
        | (simp only [err, reduceCtorEq] at h)
        | (simp only [typeOfIsInRange] at h
           split at h
           · split at h
             · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
               exact TypeValid.bool _
             · simp only [err, reduceCtorEq] at h
           · simp only [err, reduceCtorEq] at h)

/-- **Entity-type declaredness.** A successful `typeOf` under `EnvAssumptions` only produces
    entity types declared in the schema (standard/enum in `ets`, or an action in `acts`). -/
theorem typeOf_entityType_declared {env : TypeEnv} (hwf : EnvAssumptions env)
    {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities} {ety : EntityType}
    (hty : typeOf x c env = .ok (tx, c')) (hety : tx.typeOf = .entity ety) :
    ValidEntityType ety env.ets env.acts := by
  have hv := typeOf_type_valid hwf hty
  rw [hety] at hv
  cases hv with | entity _ hvet => exact hvet

/-- The set-element analogue of `typeOf_entityType_declared`: a successful `typeOf`
    producing `.set (.entity ety)` has its element type `ety` declared. -/
theorem typeOf_setElem_entityType_declared {env : TypeEnv} (hwf : EnvAssumptions env)
    {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities} {ety : EntityType}
    (hty : typeOf x c env = .ok (tx, c')) (hety : tx.typeOf = .set (.entity ety)) :
    ValidEntityType ety env.ets env.acts := by
  have hv := typeOf_type_valid hwf hty
  rw [hety] at hv
  cases hv with | set _ hv2 => cases hv2 with | entity _ hvet => exact hvet

/-! ## Reverse bridges for the list/set/record/call cases -/

/-- Reverse of `allLub_foldlM`: a successful `foldlM lub?` yields an `AllLub` witness. -/
theorem allLub_of_foldlM {acc : CedarType} {l : List CedarType} {result : CedarType}
    (h : l.foldlM lub? acc = some result) : AllLub acc l result := by
  induction l generalizing acc with
  | nil => simp only [List.foldlM_nil, pure, Option.some.injEq] at h; subst h; exact AllLub.nil acc
  | cons hd tl ih =>
    simp only [List.foldlM_cons] at h
    cases hl : lub? acc hd with
    | none => rw [hl] at h; simp at h
    | some m =>
      rw [hl] at h; simp only [Option.bind_some_fun] at h
      exact AllLub.cons acc hd tl m result (lub?_lub acc hd hl) (ih h)

/-- Reverse of the `set`/`call` element pass: a successful `mapM (justType ∘ typeOf)`,
    with a per-element `HasType` witness, yields a `HasTypeList`. -/
theorem hasTypeList_of_mapM {xs : List Expr} {c : Capabilities} {env : TypeEnv}
    (hty : ∀ x ∈ xs, ∀ {tx : TypedExpr} {cc : Capabilities},
      typeOf x c env = .ok (tx, cc) → ∃ cout, HasType false false x c env tx.typeOf cout)
    {tys : List TypedExpr}
    (hm : xs.mapM (fun x => justType (typeOf x c env)) = .ok tys) :
    HasTypeList false false xs c env (tys.map TypedExpr.typeOf) := by
  induction xs generalizing tys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm; subst hm
    exact HasTypeList.nil c env
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
        simp only [List.map_cons]
        obtain ⟨cc, hhd2⟩ := justType_ok hhd
        obtain ⟨cout, hHT⟩ := hty hd List.mem_cons_self hhd2
        exact HasTypeList.cons hd tl c env thd.typeOf (ttl.map TypedExpr.typeOf) hHT
          (ih2 (fun x hx => hty x (List.mem_cons_of_mem _ hx)) htl)

/-- Reverse of the `record` element pass: a successful `mapM` over the attributes, with
    per-attribute `HasType` witnesses, yields a `HasTypeFields` in source order. -/
theorem hasTypeFields_of_mapM {axs : List (Attr × Expr)} {c : Capabilities} {env : TypeEnv}
    (hty : ∀ ax ∈ axs, ∀ {tx : TypedExpr} {cc : Capabilities},
      typeOf ax.2 c env = .ok (tx, cc) → ∃ cout, HasType false false ax.2 c env tx.typeOf cout)
    {atys : List (Attr × TypedExpr)}
    (hm : axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) = .ok atys) :
    HasTypeFields false false axs c env
      (atys.map (fun p => (p.1, Qualified.required p.2.typeOf))) := by
  induction axs generalizing atys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm; subst hm
    exact HasTypeFields.nil c env
  | cons hd tl ih2 =>
    obtain ⟨a, x⟩ := hd
    simp only [List.mapM_cons] at hm
    cases hx : (typeOf x c env).map (fun r => (a, r.1)) with
    | error e => rw [hx] at hm; simp at hm
    | ok qhd =>
      rw [hx] at hm; simp only [Except.bind_ok] at hm
      cases htl : tl.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
      | error e => rw [htl] at hm; simp at hm
      | ok qtl =>
        rw [htl] at hm
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at hm
        subst hm
        cases hx2 : typeOf x c env with
        | error e => rw [hx2] at hx; simp [Except.map] at hx
        | ok v =>
          obtain ⟨tx, cc⟩ := v
          rw [hx2] at hx; simp only [Except.map, Except.ok.injEq] at hx; subst hx
          obtain ⟨cout, hHT⟩ := hty (a, x) List.mem_cons_self hx2
          simp only [List.map_cons]
          exact HasTypeFields.cons a x tl c env tx.typeOf _ hHT
            (ih2 (fun ax hax => hty ax (List.mem_cons_of_mem _ hax)) htl)

/-- Reverse of `typeOfConstructor`: a successful run pins the argument to a single
    string literal whose parse succeeds, and returns the declared type / empty caps. -/
theorem validX_of_typeOfConstructor {α} {mk : String → Option α} {xs : List Expr}
    {ty rty : CedarType} {c' : Capabilities}
    (h : typeOfConstructor mk xs ty = .ok (rty, c')) :
    ∃ s d, xs = [.lit (.string s)] ∧ mk s = some d ∧ rty = ty ∧ c' = [] := by
  simp only [typeOfConstructor] at h
  split at h
  · rename_i s
    split at h
    · rename_i d hmk
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s, d, rfl, hmk, rfl, rfl⟩
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

theorem ipAddrTypes_of_all : ∀ {t : CedarType} {ts : List CedarType},
    (t :: ts).all (· == .ext .ipAddr) = true → IpAddrTypes (t :: ts)
  | t, [], h => by
    simp only [List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at h; subst h; exact .one
  | t, t' :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h'⟩ := h
    refine .cons _ (ipAddrTypes_of_all ?_)
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]; exact h'

/-- Reverse of the `call` typing: a successful `typeOfCall`, with the argument
    expressions typed by a `HasTypeList`, yields a `HasTypeExtCall` witness (and the
    call produces empty capabilities). -/
theorem hasTypeExtCall_of_typeOfCall {xfn : ExtFun} {xs : List Expr} {c : Capabilities}
    {env : TypeEnv} {tys : List TypedExpr} {tx : TypedExpr} {c' : Capabilities}
    (hlist : HasTypeList false false xs c env (tys.map TypedExpr.typeOf))
    (h : typeOfCall xfn tys xs = .ok (tx, c')) :
    HasTypeExtCall false false xfn xs c env tx.typeOf ∧ c' = [] := by
  simp only [typeOfCall] at h
  split at h
  all_goals first
    | -- methods with fixed argument types
      (rename_i heq
       simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       rw [heq] at hlist
       refine ⟨?_, rfl⟩
       rcases hlist with _ | ⟨_, _, _, _, _, _, h₁, _ | ⟨_, _, _, _, _, _, h₂, _ | _⟩⟩
       constructor <;> assumption)
    | -- constructors
      (have ⟨⟨_, _⟩, hc, h⟩ := do_eq_ok.mp h
       obtain ⟨s, d, rfl, hmk, rfl, rfl⟩ := validX_of_typeOfConstructor hc
       simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨by constructor; exact .mk _ _ hmk, rfl⟩)
    | (simp only [err, reduceCtorEq] at h)
    | skip
  -- `isInRange`
  simp only [typeOfIsInRange] at h
  split at h
  · rename_i t ts heq
    split at h
    · rename_i hall
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [heq] at hlist
      cases hlist with
      | cons a _ _ _ _ _ hHTa hrest =>
        refine ⟨?_, rfl⟩; simp only [TypedExpr.typeOf]
        exact HasTypeExtCall.isInRange a _ c env _ hHTa (ipAddrTypes_of_all hall) hrest
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-! ## Reverse bridges for the binaryApp case -/

/-- `≠` on `Prim` ⇒ `PrimNeq` (reverse of `primNeq_ne`). -/
theorem primNeq_of_ne {p₁ p₂ : Prim} (h : p₁ ≠ p₂) : PrimNeq p₁ p₂ := by
  cases p₁ <;> cases p₂ <;>
    first
      | (constructor; done)
      | (constructor; intro heq; subst heq; exact h rfl)

/- `Lub` ⇒ `LubCompat` (compatibility is implied by the existence of a lub). -/
mutual
theorem lubCompat_of_lub {t₁ t₂ t : CedarType} (h : Lub t₁ t₂ t) : LubCompat t₁ t₂ := by
  cases h with
  | boolSame b => exact LubCompat.bool b b
  | boolDiff b₁ b₂ _ => exact LubCompat.bool b₁ b₂
  | int => exact LubCompat.int
  | string => exact LubCompat.string
  | entity ety => exact LubCompat.entity ety
  | ext xty => exact LubCompat.ext xty
  | set s₁ s₂ s hs => exact LubCompat.set s₁ s₂ (lubCompat_of_lub hs)
  | record r₁ r₂ r hr => exact LubCompat.record r₁ r₂ (lubCompatRecord_of_lubRecord hr)
theorem lubCompatRecord_of_lubRecord {r₁ r₂ r : List (Attr × QualifiedType)}
    (h : LubRecord r₁ r₂ r) : LubCompatRecord r₁ r₂ := by
  cases h with
  | nil => exact LubCompatRecord.nil
  | cons k v₁ v₂ v r₁ r₂ r hq hr =>
    cases hq with
    | optional t₁ t₂ t ht =>
      exact LubCompatRecord.consOpt k t₁ t₂ r₁ r₂ (lubCompat_of_lub ht)
        (lubCompatRecord_of_lubRecord hr)
    | required t₁ t₂ t ht =>
      exact LubCompatRecord.consReq k t₁ t₂ r₁ r₂ (lubCompat_of_lub ht)
        (lubCompatRecord_of_lubRecord hr)
end

/-- `lub? = some` ⇒ `LubCompat`. -/
theorem lubCompat_of_lub? {t₁ t₂ t : CedarType} (h : lub? t₁ t₂ = some t) : LubCompat t₁ t₂ :=
  lubCompat_of_lub (lub?_lub t₁ t₂ h)

/-- `MapContains` of a standard entry ⇒ `MapContainsAncestors`. -/
theorem mapContainsAncestors_of_standard {ety : EntityType} {ancs : Set EntityType}
    {attrs : RecordType} {tags : Option CedarType} {ets : EntitySchema}
    (h : MapContains ety (.standard ⟨ancs, attrs, tags⟩) ets) : MapContainsAncestors ety ancs ets := by
  induction h with
  | here => exact MapContainsAncestors.here _ _ _ _ _
  | there k' v' rest hmc ih => exact MapContainsAncestors.there _ _ _ _ _ ih

/-- `MapContains` of a standard entry with a tag type ⇒ `MapContainsTagType`. -/
theorem mapContainsTagType_of_standard {ety : EntityType} {ancs : Set EntityType}
    {attrs : RecordType} {ty : CedarType} {ets : EntitySchema}
    (h : MapContains ety (.standard ⟨ancs, attrs, some ty⟩) ets) : MapContainsTagType ety ty ets := by
  induction h with
  | here => exact MapContainsTagType.here _ _ _ _ _
  | there k' v' rest hmc ih => exact MapContainsTagType.there _ _ _ _ _ ih

/-- `MapContains` of a standard entry with no tags ⇒ `MapContainsNoTags`. -/
theorem mapContainsNoTags_of_standard {ety : EntityType} {ancs : Set EntityType}
    {attrs : RecordType} {ets : EntitySchema}
    (h : MapContains ety (.standard ⟨ancs, attrs, none⟩) ets) : MapContainsNoTags ety ets := by
  induction h with
  | here => exact MapContainsNoTags.here _ _ _ _
  | there k' v' rest hmc ih => exact MapContainsNoTags.there _ _ _ _ ih

/-- `EntitySchema.tags? = some (some ty)` ⇒ `HasTagSchema` (the entry is necessarily standard). -/
theorem hasTagSchema_of_tags? {ets : EntitySchema} {ety : EntityType} {ty : CedarType}
    (h : EntitySchema.tags? ets ety = some (some ty)) : HasTagSchema ets ety ty := by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h
  obtain ⟨entry, hfind, hea⟩ := h
  have hmc := find?_mapContains hfind
  cases entry with
  | standard s =>
    obtain ⟨ancs, attrs, tags⟩ := s
    simp only [EntitySchemaEntry.tags?] at hea; subst hea
    exact HasTagSchema.mk ets ety ty (mapContainsTagType_of_standard hmc)
  | enum eids => simp only [EntitySchemaEntry.tags?, reduceCtorEq] at hea

/-- The `typeOf` of an entity literal is `.entity uid.ty`. -/
theorem litEntity_typeOf {uid : EntityUID} {c : Capabilities} {env : TypeEnv}
    {ty : TypedExpr} {cc : Capabilities}
    (h : typeOf (.lit (.entityUID uid)) c env = .ok (ty, cc)) : ty.typeOf = .entity uid.ty := by
  simp only [typeOf, typeOfLit] at h
  split at h
  · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; rfl
  · simp only [err, reduceCtorEq] at h

/-- `MapContains` (on a distinct-keyed store) ⇒ `Map.contains = true`. -/
theorem mapContains_contains {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] [BEq α]
    [LawfulBEq α] {k : α} {v : β} {m : Map α β} (hnd : (m.toList.map Prod.fst).Nodup)
    (h : MapContains k v m) : Map.contains m k = true := by
  simp only [Map.contains, mapContains_find?_nodup h hnd, Option.isSome_some]

/-- `TypeEnv.descendentOf = true` for an operand type that is a *declared entity* (in `ets`) ⇒
    `DescendentOf` (refl, or an `ets`-ancestor edge). -/
theorem descendentOf_of_true_inSchema {ets : EntitySchema} {acts : ActionSchema}
    {reqty : RequestType} {ety₁ ety₂ : EntityType} {entry : EntitySchemaEntry}
    (hnd : (ets.toList.map Prod.fst).Nodup) (hmc : MapContains ety₁ entry ets)
    (h : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = true) :
    DescendentOf ets acts ety₁ ety₂ := by
  simp only [TypeEnv.descendentOf] at h
  split at h
  · rename_i he; subst he; exact DescendentOf.refl ets acts ety₁
  · rename_i he
    simp only [mapContains_find?_nodup hmc hnd] at h
    cases entry with
    | standard s =>
      obtain ⟨ancs, attrs, tags⟩ := s
      simp only [EntitySchemaEntry.ancestors] at h
      exact DescendentOf.ancestor ets acts ety₁ ety₂ ancs (mapContainsAncestors_of_standard hmc)
        ((setContains_iff_contains).mpr h)
    | enum eids => simp [EntitySchemaEntry.ancestors, Set.contains, Set.empty, Set.elts] at h

/-- `TypeEnv.descendentOf = false` for a *standard* operand type ⇒ `NotDescendentOf`. -/
theorem notDescendentOf_of_false_standard {ets : EntitySchema} {acts : ActionSchema}
    {reqty : RequestType} {ety₁ ety₂ : EntityType} {ancs : Set EntityType} {attrs : RecordType}
    {tags : Option CedarType} (hnd : (ets.toList.map Prod.fst).Nodup)
    (hmc : MapContains ety₁ (.standard ⟨ancs, attrs, tags⟩) ets) (hne : ety₁ ≠ ety₂)
    (h : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = false) :
    NotDescendentOf ets acts ety₁ ety₂ := by
  simp only [TypeEnv.descendentOf, ite_eq_right hne, mapContains_find?_nodup hmc hnd,
    EntitySchemaEntry.ancestors] at h
  exact NotDescendentOf.diff ets acts ety₁ ety₂ ancs hne (mapContainsAncestors_of_standard hmc)
    (fun hsc => by simp [(setContains_iff_contains).mp hsc] at h)

/-- `ActionSchema.descendentOf = false` (with the source action present, distinct target) ⇒
    `NotActionDescendentOf`. -/
theorem notActionDescendentOf_of_false {acts : ActionSchema} {uid₁ uid₂ : EntityUID}
    {entry : ActionSchemaEntry} (hnd : (acts.toList.map Prod.fst).Nodup)
    (hmc : MapContains uid₁ entry acts) (hne : uid₁ ≠ uid₂)
    (h : acts.descendentOf uid₁ uid₂ = false) : NotActionDescendentOf acts uid₁ uid₂ := by
  simp only [ActionSchema.descendentOf, beq_iff_eq, ite_eq_right hne,
    mapContains_find?_nodup hmc hnd] at h
  exact NotActionDescendentOf.diff acts uid₁ uid₂ entry hne hmc
    (fun hsc => by simp [(setContains_iff_contains).mp hsc] at h)

/-! ## Reverse bridges for the getAttr/hasAttr cases -/

/-- List-level: if no `(k, v)` occurs, the key is absent (`MapNotContainsKey`). -/
theorem mapNotContainsKey_of_absent {α β} [DecidableEq α] {k : α} {l : List (α × β)}
    (habs : ∀ v, ¬ (k, v) ∈ l) : MapNotContainsKey k (Map.mk l) := by
  induction l with
  | nil => exact MapNotContainsKey.empty k
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    have hkne : k ≠ k' := fun heq => habs v' (by subst heq; exact List.mem_cons_self)
    exact MapNotContainsKey.skip k k' v' tl hkne (ih (fun v hv => habs v (List.mem_cons_of_mem _ hv)))

/-- `Map.find? = none` ⇒ `MapNotContainsKey` (reverse of `mapNotContainsKey_find?`). -/
theorem mapNotContainsKey_of_find?_none {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {k : α} {m : Map α β} (h : m.find? k = none) : MapNotContainsKey k m := by
  obtain ⟨l⟩ := m
  exact mapNotContainsKey_of_absent (by simpa only [Map.toList] using Map.find?_none_all_absent h)

/-- `TypeEnv.descendentOf = true` for an operand type absent from `ets` (an action type) and a
    distinct target ⇒ `DescendentOf.action`: the lookup falls through to `maybeDescendentOf`. -/
theorem descendentOf_of_true_absent {ets : EntitySchema} {acts : ActionSchema}
    {reqty : RequestType} {ety₁ ety₂ : EntityType} (hne : ety₁ ≠ ety₂)
    (hf : ets.find? ety₁ = none) (h : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = true) :
    DescendentOf ets acts ety₁ ety₂ := by
  simp only [TypeEnv.descendentOf, hne, ↓reduceIte, hf] at h
  exact .action _ _ _ _ (mapNotContainsKey_of_find?_none hf) (maybeActionDescendentOf_iff.mpr h)

/-- `TypeEnv.descendentOf = false` for an operand type absent from `ets` ⇒ no action of that
    type has an ancestor of the target type. -/
theorem not_maybeActionDescendentOf_of_false {ets : EntitySchema} {acts : ActionSchema}
    {reqty : RequestType} {ety₁ ety₂ : EntityType} (hne : ety₁ ≠ ety₂)
    (hf : ets.find? ety₁ = none) (h : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = false) :
    ¬ MaybeActionDescendentOf acts ety₁ ety₂ := by
  simp only [TypeEnv.descendentOf, hne, ↓reduceIte, hf] at h
  intro hmd
  simp [maybeActionDescendentOf_iff.mp hmd] at h

/-- `MapContains` of a standard entry ⇒ `MapContainsAttrs` (reverse extractor). -/
theorem mapContainsAttrs_of_standard {ety : EntityType} {ancs : Set EntityType} {attrs : RecordType}
    {tags : Option CedarType} {ets : EntitySchema}
    (h : MapContains ety (.standard ⟨ancs, attrs, tags⟩) ets) : MapContainsAttrs ety attrs ets := by
  induction h with
  | here => exact MapContainsAttrs.here _ _ _ _ _
  | there k' v' rest hmc ih => exact MapContainsAttrs.there _ _ _ _ _ ih

/-- `MapContains` of an enum entry (on a distinct-keyed store) ⇒ `MapContainsEnum`. -/
theorem mapContainsEnum_of_mapContains {ety : EntityType} {eids : Set String} {ets : EntitySchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) (h : MapContains ety (.enum eids) ets) :
    MapContainsEnum ety eids ets := by
  induction h with
  | here => exact MapContainsEnum.here _ _ _
  | there k' v' rest hmc ih =>
    simp only [Map.toList, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    have hkne : k' ≠ ety := fun heq => by
      subst heq; exact hnotin (List.mem_map.mpr ⟨(k', .enum eids), mapContains_mem hmc, rfl⟩)
    exact MapContainsEnum.there ety eids k' v' rest hkne (ih hnd')

/-- Reverse of `getAttrInRecord`: a successful lookup yields a `GetAttrInRecord` witness
    (and empty output capabilities). -/
theorem getAttrInRecord_of_ok {ty : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c : Capabilities} {aty : CedarType} {ac : Capabilities}
    (h : getAttrInRecord ty rty x a c = .ok (aty, ac)) : GetAttrInRecord rty x a c aty ∧ ac = ∅ := by
  simp only [getAttrInRecord] at h
  split at h
  · rename_i aty' heqf
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, hcap⟩ := h
    exact ⟨GetAttrInRecord.required rty x a c _ (find?_mapContains heqf), hcap.symm⟩
  · rename_i aty' heqf
    split at h
    · rename_i hcap
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, hac⟩ := h
      exact ⟨GetAttrInRecord.optional rty x a c _ (capAttrMem_iff.mpr hcap) (find?_mapContains heqf),
        hac.symm⟩
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-- Reverse of `hasAttrInRecord` on a *found* attribute: yields a `HasAttrInRecord` witness. -/
theorem hasAttrInRecord_found_of_ok {rty : RecordType} {x : Expr} {a : Attr} {c : Capabilities}
    {k : Bool} {ty : CedarType} {caps : Capabilities} {qty : QualifiedType}
    (hfind : rty.find? a = some qty) (h : hasAttrInRecord rty x a c k = .ok (ty, caps)) :
    HasAttrInRecord rty x a c k ty caps := by
  have hmc : MapContains a qty rty := find?_mapContains hfind
  simp only [hasAttrInRecord, hfind] at h
  split at h
  · rename_i hcond
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    rcases Bool.or_eq_true_iff.mp hcond with hcap | hreq
    · exact HasAttrInRecord.found_in_caps rty x a c k qty
        (capAttrMem_iff.mpr (by simpa using hcap)) (by simpa using hmc)
    · simp only [Bool.and_eq_true] at hreq
      obtain ⟨hqreq, hk⟩ := hreq
      subst hk
      cases qty with
      | required ty' => exact HasAttrInRecord.found_required_known rty x a c ty' hmc
      | optional ty' => simp only [Qualified.isRequired, reduceCtorEq] at hqreq
  · rename_i hcond
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hcond
    obtain ⟨hncapd, hnrq⟩ := hcond
    have hncap' : ¬ CapAttrMem x a c := fun hm => of_decide_eq_false hncapd (capAttrMem_iff.mp hm)
    cases k with
    | false => exact HasAttrInRecord.found_not_known rty x a c qty hmc hncap'
    | true =>
      cases qty with
      | optional ty' => exact HasAttrInRecord.found_optional_known rty x a c ty' hmc hncap'
      | required ty' => simp [Qualified.isRequired] at hnrq

/-- `c ∪ c₁` as a `CapMerge` witness, up to `CapsEquiv`. -/
theorem capsEquiv_union_append {c cc₁ cout₁ : Capabilities} (hce₁ : CapsEquiv cout₁ cc₁) :
    CapsEquiv (c ∪ cc₁) (c ++ cout₁) :=
  (CapsEquiv.union (CapsEquiv.refl c) hce₁.symm).trans
    (capMerge_capsEquiv_union (capMerge_append c cout₁)).symm

/-! ## Completeness of the extended `has` chain -/

/-- A successful `typeOfHasAttr` on a receiver of type `tx.typeOf` is a `HasAttrOn` step. -/
theorem hasAttrOn_complete {env : TypeEnv} (hwf : EnvAssumptions env) {tx : TypedExpr}
    {x : Expr} {a : Attr} {c : Capabilities} {tyHas : TypedExpr} {ci : Capabilities}
    (htw : TyWf tx.typeOf) (h : typeOfHasAttr tx x a c env = .ok (tyHas, ci)) :
    ∃ b, tyHas.typeOf = .bool b ∧ HasAttrOn env tx.typeOf x a c b ci := by
  obtain ⟨ets, acts, reqty⟩ := env
  simp only [typeOfHasAttr] at h
  split at h
  · rename_i rty heqty
    rw [heqty] at htw ⊢
    have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
    cases hfa : rty.find? a with
    | some qty =>
      cases hha : hasAttrInRecord rty x a c true with
      | error e => rw [hha] at h; simp at h
      | ok r =>
        obtain ⟨ty', caps⟩ := r
        rw [hha] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨b, rfl⟩ := hasAttrInRecord_bool hha
        exact ⟨b, rfl, HasAttrOn.record _ _ _ _ _ _ _ (hasAttrInRecord_found_of_ok hfa hha)⟩
    | none =>
      rw [show hasAttrInRecord rty x a c true = ok (.bool .ff) from by
        simp only [hasAttrInRecord, hfa]] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rtyList⟩ := rty
      exact ⟨.ff, rfl, HasAttrOn.recordNotFound _ rtyList _ _ _ (mapNotContainsKey_of_find?_none hfa)⟩
  · rename_i ety heqty
    rw [heqty]
    split at h
    · rename_i rty hattr
      have hnd : (rty.toList.map Prod.fst).Nodup := by
        cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
      have hattr2 := hattr
      simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattr2
      obtain ⟨entry, hfind, hea⟩ := hattr2
      have hmc := find?_mapContains hfind
      cases entry with
      | standard s =>
        obtain ⟨ancs, attrs, tags⟩ := s
        simp only [EntitySchemaEntry.attrs] at hea
        have hmca : MapContainsAttrs ety rty ets := hea ▸ mapContainsAttrs_of_standard hmc
        cases hfa : rty.find? a with
        | some qty =>
          cases hha : hasAttrInRecord rty x a c false with
          | error e => rw [hha] at h; simp at h
          | ok r =>
            obtain ⟨ty', caps⟩ := r
            rw [hha] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨b, rfl⟩ := hasAttrInRecord_bool hha
            exact ⟨b, rfl, HasAttrOn.entity _ _ _ _ _ _ _ _ _ _ hmca
              (hasAttrInRecord_found_of_ok hfa hha)⟩
        | none =>
          rw [show hasAttrInRecord rty x a c false = ok (.bool .ff) from by
            simp only [hasAttrInRecord, hfa]] at h
          simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨.ff, rfl, HasAttrOn.entityNotFound _ _ _ _ _ _ _ _ hmca
            (mapNotContainsKey_of_find?_none hfa)⟩
      | enum eids =>
        simp only [EntitySchemaEntry.attrs] at hea
        have hmce : MapContainsEnum ety eids ets :=
          mapContainsEnum_of_mapContains hwf.ets_keys_nodup hmc
        rw [show hasAttrInRecord rty x a c false = ok (.bool .ff) from by
          rw [← hea]; simp only [hasAttrInRecord, show (Map.empty : RecordType).find? a = none from rfl]] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.ff, rfl, HasAttrOn.enum _ _ _ _ _ _ _ _ hmce⟩
    · rename_i hattrn
      split at h
      · rename_i hact
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        have hfnone : ets.find? ety = none := by
          simp only [EntitySchema.attrs?, Option.map_eq_none_iff] at hattrn; exact hattrn
        obtain ⟨eid, entry, hpk⟩ := actionType?_mapContainsPairKey hact
        exact ⟨.ff, rfl, HasAttrOn.action _ _ _ _ _ _ _ _ _ (mapNotContainsKey_of_find?_none hfnone) hpk⟩
      · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-- A successful `typeOfGetAttr` on a receiver of type `tx.typeOf` is a `GetAttrOn` step. -/
theorem getAttrOn_complete {env : TypeEnv} (hwf : EnvAssumptions env) {tx : TypedExpr}
    {x : Expr} {a : Attr} {c : Capabilities} {tyG : TypedExpr} {cg : Capabilities}
    (htw : TyWf tx.typeOf) (h : typeOfGetAttr tx x a c env = .ok (tyG, cg)) :
    GetAttrOn env tx.typeOf x a c tyG.typeOf ∧ cg = ∅ := by
  obtain ⟨ets, acts, reqty⟩ := env
  simp only [typeOfGetAttr] at h
  split at h
  · rename_i rty heqty
    rw [heqty] at htw ⊢
    cases hg : getAttrInRecord tx.typeOf rty x a c with
    | error e => rw [hg] at h; simp at h
    | ok r =>
      obtain ⟨aty, ac⟩ := r
      rw [hg] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
      obtain ⟨hgar, rfl⟩ := getAttrInRecord_of_ok hg
      exact ⟨GetAttrOn.record _ _ _ _ _ _ hgar, rfl⟩
  · rename_i ety heqty
    rw [heqty]
    split at h
    · rename_i rty hattr
      cases hg : getAttrInRecord tx.typeOf rty x a c with
      | error e => rw [hg] at h; simp at h
      | ok r =>
        obtain ⟨aty, ac⟩ := r
        rw [hg] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hnd : (rty.toList.map Prod.fst).Nodup := by
          cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
        simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattr
        obtain ⟨entry, hfind, hea⟩ := hattr
        have hmc := find?_mapContains hfind
        cases entry with
        | standard s =>
          obtain ⟨ancs, attrs, tags⟩ := s
          simp only [EntitySchemaEntry.attrs] at hea
          obtain ⟨hgar, rfl⟩ := getAttrInRecord_of_ok hg
          exact ⟨GetAttrOn.entity _ _ _ _ _ _ _ _ _ (hea ▸ mapContainsAttrs_of_standard hmc) hgar, rfl⟩
        | enum eids =>
          simp only [EntitySchemaEntry.attrs] at hea
          rw [← hea] at hg
          simp only [getAttrInRecord, show (Map.empty : RecordType).find? a = none from rfl,
            err, reduceCtorEq] at hg
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-- A successful `typeOfExtHasAttr` on `a :: as` is witnessed by `ExtHasAttrChain`. -/
theorem extHasAttrChain_complete {env : TypeEnv} (hwf : EnvAssumptions env) :
    ∀ (as : List Attr) {tx : TypedExpr} {x : Expr} {a : Attr} {c : Capabilities}
      {b : BoolType} {c' : Capabilities},
      TyWf tx.typeOf → typeOfExtHasAttr tx x (a :: as) c env = .ok (b, c') →
      ∃ cout, ExtHasAttrChain env tx.typeOf x a as c b cout ∧ CapsEquiv cout c'
  | [], tx, x, a, c, b, c', htw, h => by
    simp only [typeOfExtHasAttr] at h
    cases hha : typeOfHasAttr tx x a c env with
    | error e => rw [hha] at h; simp at h
    | ok r =>
      obtain ⟨tyHas, ci⟩ := r
      rw [hha] at h; simp only [Except.bind_ok] at h
      obtain ⟨bh, hbh, hon⟩ := hasAttrOn_complete hwf htw hha
      rw [hbh] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ci, ExtHasAttrChain.last _ _ _ _ _ _ _ hon, CapsEquiv.refl _⟩
  | a' :: as, tx, x, a, c, b, c', htw, h => by
    simp only [typeOfExtHasAttr] at h
    cases hha : typeOfHasAttr tx x a c env with
    | error e => rw [hha] at h; simp at h
    | ok r =>
      obtain ⟨tyHas, ci⟩ := r
      rw [hha] at h; simp only [Except.bind_ok] at h
      obtain ⟨bh, hbh, hon⟩ := hasAttrOn_complete hwf htw hha
      rw [hbh] at h
      -- The attribute is maybe present: type `x.a` and the rest of the chain under `c ∪ ci`,
      -- then move both onto the relational witness `c ++ ci`.
      have rest : NotFf bh → ∃ cout, ExtHasAttrChain env tx.typeOf x a (a' :: as) c b cout ∧
          CapsEquiv cout c' := by
        intro hnf
        have hce : CapsEquiv (c ∪ ci) (c ++ ci) := capsEquiv_union_append (CapsEquiv.refl ci)
        cases hnf <;> (
          simp only at h
          cases hg : typeOfGetAttr tx x a (c ∪ ci) env with
          | error e => rw [hg] at h; simp at h
          | ok r =>
            obtain ⟨tyNext, cgn⟩ := r
            rw [hg] at h; simp only [Except.bind_ok] at h
            obtain ⟨hga, _⟩ := getAttrOn_complete hwf htw hg
            have htwN := typeOfGetAttr_tyWf hwf htw hg
            cases hr : typeOfExtHasAttr tyNext (x.getAttr a) (a' :: as) (c ∪ ci) env with
            | error e => rw [hr] at h; simp at h
            | ok r2 =>
              obtain ⟨bty, cr⟩ := r2
              rw [hr] at h; simp only [Except.bind_ok] at h
              rw [typeOfExtHasAttr_capsEquiv hce] at hr
              obtain ⟨coutR, hch, hceR⟩ := extHasAttrChain_complete hwf as htwN hr
              have hgaC := getAttrOn_congr hga hce
              cases bty with
              | ff =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨[], ExtHasAttrChain.restFf _ _ _ _ _ _ _ _ _ _ _ _ hon (by constructor)
                  (capMerge_append c ci) hgaC hch, CapsEquiv.refl _⟩
              | tt =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨ci ++ coutR, ExtHasAttrChain.restTt _ _ _ _ _ _ _ _ _ _ _ _ _ hon
                  (by constructor) (capMerge_append c ci) hgaC hch (capMerge_append ci coutR),
                  (capsEquiv_union_append hceR).symm⟩
              | anyBool =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨ci ++ coutR, ExtHasAttrChain.restAnyBool _ _ _ _ _ _ _ _ _ _ _ _ _ hon
                  (by constructor) (capMerge_append c ci) hgaC hch (capMerge_append ci coutR),
                  (capsEquiv_union_append hceR).symm⟩)
      cases bh with
      | ff =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨ci, ExtHasAttrChain.absent _ _ _ _ _ _ _ _ hon, CapsEquiv.refl _⟩
      | tt => exact rest NotFf.tt
      | anyBool => exact rest NotFf.anyBool

/-- **Completeness of `HasType`** (converse of `hasType_sound`): on an environment satisfying
    `EnvAssumptions`, any successful `typeOf` run is witnessed by a `HasType false false`
    derivation with a capability-equivalent output. -/
theorem typeOf_complete {env : TypeEnv} (hwf : EnvAssumptions env) :
    ∀ {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      typeOf x c env = .ok (tx, c') →
      ∃ cout, HasType false false x c env tx.typeOf cout ∧ CapsEquiv cout c' := by
  intro x c
  induction x, c using typeOf.induct with
  | case1 c p =>
    intro tx c' h
    obtain ⟨ets, acts, reqty⟩ := env
    simp only [typeOf, typeOfLit] at h
    split at h
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litBoolTrue _ _ _ _, fun _ => Iff.rfl⟩
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litBoolFalse _ _ _ _, fun _ => Iff.rfl⟩
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litInt _ _ _ _ _, fun _ => Iff.rfl⟩
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litString _ _ _ _ _, fun _ => Iff.rfl⟩
    · split at h
      · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rename_i uid hcond
        exact ⟨[], HasType.litEntity uid.ty uid.eid c ets acts reqty
          (validEntityUID_of_checkEntities hcond), fun _ => Iff.rfl⟩
      · simp only [err, reduceCtorEq] at h
  | case2 c v =>
    intro tx c' h
    obtain ⟨ets, acts, princ, ⟨actionTy, actionEid⟩, resource, ctx⟩ := env
    simp only [typeOf, typeOfVar] at h
    split at h <;>
      (simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h)
    · exact ⟨[], HasType.varPrincipal _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
    · exact ⟨[], HasType.varAction _ _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
    · exact ⟨[], HasType.varResource _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
    · exact ⟨[], HasType.varContext _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
  | case3 c x₁ x₂ x₃ ih1 ih2 ih3 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
      simp only [typeOfIf] at h
      split at h
      · -- ty1.typeOf = .bool tt → iteTt (x₃ untaken)
        rename_i heq
        cases h2 : typeOf x₂ (c ∪ cc1) env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2
          rw [h2] at h; simp only [Except.bind_ok] at h
          obtain ⟨cout2, hHT2, hce2⟩ := ih2 cc1 h2
          obtain ⟨cout2', hHT2', hce2'⟩ := hasType_capsCongr hHT2 (capsEquiv_union_append hce1)
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨cout1 ++ cout2', ?_, ?_⟩
          · simp only [TypedExpr.typeOf]
            exact HasType.iteTt x₁ x₂ x₃ c env cout1 _ ty2.typeOf cout2' _ (heq ▸ hHT1)
              (capMerge_append c cout1) hHT2' (capMerge_append cout1 cout2') (DeadOperand.lax _ _)
          · exact (capMerge_capsEquiv_union (capMerge_append cout1 cout2')).trans
              (CapsEquiv.union hce1 (hce2'.symm.trans hce2))
      · -- ty1.typeOf = .bool ff → iteFf (x₂ untaken)
        rename_i heq
        cases h3 : typeOf x₃ c env with
        | error e => rw [h3] at h; simp at h
        | ok r3 =>
          obtain ⟨ty3, cc3⟩ := r3
          rw [h3] at h; simp only [Except.bind_ok] at h
          obtain ⟨cout3, hHT3, hce3⟩ := ih3 h3
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨cout3, ?_, hce3⟩
          simp only [TypedExpr.typeOf]
          exact HasType.iteFf x₁ x₂ x₃ c env cout1 ty3.typeOf cout3 (heq ▸ hHT1) hHT3
            (DeadOperand.lax _ _)
      · -- ty1.typeOf = .bool anyBool → iteAnyBool
        rename_i heq
        cases h2 : typeOf x₂ (c ∪ cc1) env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2
          rw [h2] at h; simp only [Except.bind_ok] at h
          obtain ⟨cout2, hHT2, hce2⟩ := ih2 cc1 h2
          obtain ⟨cout2', hHT2', hce2'⟩ := hasType_capsCongr hHT2 (capsEquiv_union_append hce1)
          cases h3 : typeOf x₃ c env with
          | error e => rw [h3] at h; simp at h
          | ok r3 =>
            obtain ⟨ty3, cc3⟩ := r3
            rw [h3] at h; simp only [Except.bind_ok] at h
            obtain ⟨cout3, hHT3, hce3⟩ := ih3 h3
            split at h
            · -- ty2.typeOf ⊔ ty3.typeOf = some lubTy → iteAnyBool
              rename_i lubTy hlub
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨capIntersect (cout1 ++ cout2') cout3, ?_, ?_⟩
              · simp only [TypedExpr.typeOf]
                exact HasType.iteAnyBool x₁ x₂ x₃ c env cout1 _ ty2.typeOf cout2' ty3.typeOf cout3
                  lubTy _ (heq ▸ hHT1) (capMerge_append c cout1) hHT2' hHT3 (lub?_lub _ _ hlub)
                  (capMerge_append cout1 cout2')
              · exact (capIntersect_capsEquiv_inter _ _).trans (CapsEquiv.inter
                  ((capMerge_capsEquiv_union (capMerge_append cout1 cout2')).trans
                    (CapsEquiv.union hce1 (hce2'.symm.trans hce2))) hce3)
            · -- lub = none → err
              simp only [err, reduceCtorEq] at h
      · -- ty1.typeOf non-bool → err
        simp only [err, reduceCtorEq] at h
  | case4 c x₁ x₂ ih1 ih2 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
      simp only [typeOfAnd] at h
      split at h
      · -- ty1.typeOf = .bool .ff → andShort (short-circuit)
        rename_i heq
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        rw [heq]
        exact HasType.andShort x₁ x₂ c env cout1 (heq ▸ hHT1) (DeadOperand.lax _ _)
      · -- ty1.typeOf = .bool ty₁ (ty₁ ∈ {tt, anyBool}); x₂ typed at c ∪ cc1
        rename_i _ ty₁ hne heq
        cases h2 : typeOf x₂ (c ∪ cc1) env with
        | error e => rw [h2] at h; simp at h
        | ok r2 =>
          obtain ⟨ty2, cc2⟩ := r2
          rw [h2] at h; simp only [Except.bind_ok] at h
          obtain ⟨cout2, hHT2, hce2⟩ := ih2 cc1 h2
          -- transport the branch IH from (c ∪ cc1) onto the CapMerge witness (c ++ cout1)
          obtain ⟨cout2', hHT2', hce2'⟩ := hasType_capsCongr hHT2 (capsEquiv_union_append hce1)
          have hm₁ : CapMerge c cout1 (c ++ cout1) := capMerge_append c cout1
          have hm₂ : CapMerge cout1 cout2' (cout1 ++ cout2') := capMerge_append cout1 cout2'
          have hout : CapsEquiv (cout1 ++ cout2') (cc1 ∪ cc2) :=
            (capMerge_capsEquiv_union hm₂).trans (CapsEquiv.union hce1 (hce2'.symm.trans hce2))
          split at h
          · -- ty2 = .bool ff → (.bool ff, ∅): andTtFf / andAnyFf
            rename_i heq2
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨[], ?_, fun _ => Iff.rfl⟩
            simp only [TypedExpr.typeOf]
            cases ty₁ with
            | ff => exact absurd rfl hne
            | tt => exact HasType.andTtFf x₁ x₂ c env cout1 _ cout2' (heq ▸ hHT1) hm₁ (heq2 ▸ hHT2')
            | anyBool => exact HasType.andAnyFf x₁ x₂ c env cout1 _ cout2' (heq ▸ hHT1) hm₁ (heq2 ▸ hHT2')
          · -- ty2 = .bool tt → (.bool ty₁, cc1 ∪ cc2): andTtTt / andAnyTt
            rename_i heq2
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨cout1 ++ cout2', ?_, hout⟩
            simp only [TypedExpr.typeOf]
            cases ty₁ with
            | ff => exact absurd rfl hne
            | tt => exact HasType.andTtTt x₁ x₂ c env cout1 _ cout2' _ (heq ▸ hHT1) hm₁ (heq2 ▸ hHT2') hm₂
            | anyBool => exact HasType.andAnyTt x₁ x₂ c env cout1 _ cout2' _ (heq ▸ hHT1) hm₁ (heq2 ▸ hHT2') hm₂
          · -- ty2 = .bool bty (anyBool) → (.bool anyBool, cc1 ∪ cc2): andTtAny / andAnyAny
            rename_i _ bty2 hnt2 hnf2 heq2
            have hany2 : bty2 = BoolType.anyBool := by
              cases bty2 <;> first | rfl | exact absurd rfl hnt2 | exact absurd rfl hnf2
            subst hany2
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨cout1 ++ cout2', ?_, hout⟩
            simp only [TypedExpr.typeOf]
            cases ty₁ with
            | ff => exact absurd rfl hne
            | tt => exact HasType.andTtAny x₁ x₂ c env cout1 _ cout2' _ (heq ▸ hHT1) hm₁ (heq2 ▸ hHT2') hm₂
            | anyBool => exact HasType.andAnyAny x₁ x₂ c env cout1 _ cout2' _ (heq ▸ hHT1) hm₁ (heq2 ▸ hHT2') hm₂
          · -- ty2 non-bool → err
            simp only [err, reduceCtorEq] at h
      · -- ty1.typeOf non-bool → err
        simp only [err, reduceCtorEq] at h
  | case5 c x₁ x₂ ih1 ih2 =>
    intro tx c' h
    · simp only [typeOf] at h
      cases h1 : typeOf x₁ c env with
      | error e => rw [h1] at h; simp at h
      | ok r1 =>
        obtain ⟨ty1, cc1⟩ := r1
        rw [h1] at h; simp only [Except.bind_ok] at h
        obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
        simp only [typeOfOr] at h
        split at h
        · rename_i heq
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          rw [heq]; exact HasType.orShort x₁ x₂ c env cout1 (heq ▸ hHT1) (DeadOperand.lax _ _)
        · rename_i heq
          cases h2 : typeOf x₂ c env with
          | error e => rw [h2] at h; simp at h
          | ok r2 =>
            obtain ⟨ty2, cc2⟩ := r2
            rw [h2] at h; simp only [Except.bind_ok] at h
            obtain ⟨cout2, hHT2, hce2⟩ := ih2 h2
            split at h
            · rename_i heq2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨cout2, ?_, hce2⟩
              rw [heq2]
              exact HasType.orFfThen x₁ x₂ c env cout1 _ cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
            · simp only [err, reduceCtorEq] at h
        · -- outer `.bool _`: reached only for `anyBool` (tt/ff handled above)
          rename_i _ bty hnt hnf heq
          have hany : bty = BoolType.anyBool := by
            cases bty <;> first | rfl | exact absurd rfl hnt | exact absurd rfl hnf
          subst hany
          cases h2 : typeOf x₂ c env with
          | error e => rw [h2] at h; simp at h
          | ok r2 =>
            obtain ⟨ty2, cc2⟩ := r2
            rw [h2] at h; simp only [Except.bind_ok] at h
            obtain ⟨cout2, hHT2, hce2⟩ := ih2 h2
            split at h
            · rename_i heq2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              simp only [TypedExpr.typeOf]
              exact HasType.orAnyTt x₁ x₂ c env cout1 cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
            · rename_i heq2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨cout1, ?_, hce1⟩
              simp only [TypedExpr.typeOf]
              exact HasType.orAnyFf x₁ x₂ c env cout1 cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
            · -- inner `.bool _`: reached only for `anyBool`
              rename_i _ bty2 hnt2 hnf2 heq2
              have hany2 : bty2 = BoolType.anyBool := by
                cases bty2 <;> first | rfl | exact absurd rfl hnt2 | exact absurd rfl hnf2
              subst hany2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨capIntersect cout1 cout2, ?_, ?_⟩
              · simp only [TypedExpr.typeOf]
                exact HasType.orAnyAny x₁ x₂ c env cout1 cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
              · exact (capIntersect_capsEquiv_inter cout1 cout2).trans (CapsEquiv.inter hce1 hce2)
            · simp only [err, reduceCtorEq] at h
        · simp only [err, reduceCtorEq] at h
  | case6 c op₁ x₁ ih1 =>
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
      simp only [typeOfUnaryApp] at h
      split at h
      · -- `.not`, `.bool bx`: pick not-rule by the operand's bool subtype
        rename_i _ _ bx heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        cases bx <;>
          first
            | exact HasType.unaryAppNotTt x₁ c env (heq ▸ hHT1)
            | exact HasType.unaryAppNotFf x₁ c env (heq ▸ hHT1)
            | exact HasType.unaryAppNotAny x₁ c env (heq ▸ hHT1)
      · -- `.neg`, `.int`
        rename_i _ _ heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        exact HasType.unaryAppNeg x₁ c env (heq ▸ hHT1)
      · -- `.isEmpty`, `.set elemTy`
        rename_i _ _ elemTy heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        exact HasType.unaryAppIsEmpty x₁ c env elemTy (heq ▸ hHT1)
      · -- `.like pat`, `.string`
        rename_i _ _ _ heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        exact HasType.unaryAppLike _ x₁ c env (heq ▸ hHT1)
      · -- `.is ety₁`, `.entity ety₂`
        rename_i _ _ ety₁ ety₂ heq
        split at h
        · -- ety₁ = ety₂ → `.tt`
          rename_i hEq
          simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          subst hEq
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          simp only [TypedExpr.typeOf]
          exact HasType.unaryAppIsTrue ety₁ x₁ c env (IsTargetOf.lax _ _) (heq ▸ hHT1)
        · -- ety₁ ≠ ety₂ → `.ff`
          rename_i hNe
          simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          simp only [TypedExpr.typeOf]
          -- Operand type `ety₂` is declared, by the entity-type declaredness invariant.
          have hvet₂ : ValidEntityType ety₂ env.ets env.acts :=
            typeOf_entityType_declared hwf h1 heq
          exact HasType.unaryAppIsFalse ety₁ ety₂ x₁ c env hvet₂ (IsTargetOf.lax _ _) hNe
            (heq ▸ hHT1)
      · -- err (unexpected operand type)
        simp only [err, reduceCtorEq] at h
  | case7 c op₂ x₁ x₂ ih1 ih2 =>
    intro tx c' h
    obtain ⟨ets, acts, reqty⟩ := env
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c ⟨ets, acts, reqty⟩ with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      cases h2 : typeOf x₂ c ⟨ets, acts, reqty⟩ with
      | error e => rw [h2] at h; simp at h
      | ok r2 =>
        obtain ⟨ty2, cc2⟩ := r2
        rw [h2] at h; simp only [Except.bind_ok] at h
        obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
        obtain ⟨cout2, hHT2, hce2⟩ := ih2 h2
        simp only [typeOfBinaryApp] at h
        split at h
        · -- eq
          simp only [typeOfEq] at h
          split at h
          · -- both operands are literals
            split at h
            · -- p₁ == p₂  →  `.bool .tt`
              rename_i p₁ p₂ hbeq
              simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hpe : p₁ = p₂ := by simpa using hbeq
              subst hpe
              exact ⟨[], HasType.binaryAppEqLitSame p₁ c ⟨ets, acts, reqty⟩ ty1.typeOf hHT1,
                fun _ => Iff.rfl⟩
            · -- p₁ ≠ p₂  →  `.bool .ff`
              rename_i p₁ p₂ hbeq
              simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hpne : p₁ ≠ p₂ := fun he => hbeq (beq_iff_eq.mpr he)
              exact ⟨[], HasType.binaryAppEqLitDiff p₁ p₂ c ⟨ets, acts, reqty⟩ ty1.typeOf ty2.typeOf
                (primNeq_of_ne hpne) hHT1 hHT2, fun _ => Iff.rfl⟩
          · -- not both literals
            split at h
            · -- lub exists  →  `.bool .anyBool`
              rename_i hnotlit _ lubTy heqlub
              simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              refine HasType.binaryAppEqNonLitLub x₁ x₂ c ⟨ets, acts, reqty⟩ ty1.typeOf ty2.typeOf
                lubTy (lub?_lub _ _ heqlub) hHT1 hHT2 ?_
              intro hbl; cases hbl with | mk p₁ p₂ => exact hnotlit p₁ p₂ rfl rfl
            · -- no lub
              split at h
              · -- both entity types (necessarily distinct)  →  `.bool .ff`
                rename_i hnotlit _ hlubnone _ _ ety₁ ety₂ heq1 heq2
                simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hv1 := typeOf_entityType_declared hwf h1 heq1
                have hv2 := typeOf_entityType_declared hwf h2 heq2
                have hne : ety₁ ≠ ety₂ := by
                  intro he; rw [heq1, heq2, he] at hlubnone; simp [lub?] at hlubnone
                refine ⟨[], ?_, fun _ => Iff.rfl⟩
                refine HasType.binaryAppEqEntityDiff x₁ x₂ c ⟨ets, acts, reqty⟩ ety₁ ety₂ hv1 hv2 hne
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2) ?_
                intro hbl; cases hbl with | mk p₁ p₂ => exact hnotlit p₁ p₂ rfl rfl
              · simp only [err, reduceCtorEq] at h
        · -- mem, entity/entity
          rename_i ety₁ ety₂ heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          have hnd := hwf.ets_keys_nodup
          have hnda := hwf.acts_keys_nodup
          by_cases hal : IsActionLitMem x₁ x₂ acts
          · -- action-literal membership
            cases hal with
            | mk uid₁ uid₂ _ entry hmcA =>
              have hty1 := litEntity_typeOf h1
              have hty2 := litEntity_typeOf h2
              have hc1 : acts.contains uid₁ = true := mapContains_contains hnda hmcA
              have htype : typeOfInₑ ety₁ ety₂ (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))
                  ⟨ets, acts, reqty⟩ = (if acts.descendentOf uid₁ uid₂ then BoolType.tt else .ff) := by
                simp [typeOfInₑ, actionUID?, entityUID?, hc1]
              rw [htype]
              by_cases hdesc : acts.descendentOf uid₁ uid₂ = true
              · rw [ite_eq_left hdesc]
                exact ⟨[], HasType.binaryAppMemActionLitTt uid₁ uid₂ c ets acts reqty
                  (descendentOf_actionDescendentOf hmcA hnda hdesc) (hty1 ▸ hHT1) (hty2 ▸ hHT2),
                  fun _ => Iff.rfl⟩
              · rw [ite_eq_right hdesc]
                have hne : uid₁ ≠ uid₂ := fun he => by subst he; simp [ActionSchema.descendentOf] at hdesc
                exact ⟨[], HasType.binaryAppMemActionLitFf uid₁ uid₂ c ets acts reqty
                  (notActionDescendentOf_of_false hnda hmcA hne (by simpa using hdesc))
                  (hty1 ▸ hHT1) (hty2 ▸ hHT2), fun _ => Iff.rfl⟩
          · -- generic membership: split on `ets.find? ety₁` (the shape `descendentOf` reads),
            -- not on the `ValidEntityType` witness — this covers action operands (`none`) and
            -- `ets` operands (`some`) uniformly.
            rw [typeOfInₑ_fallback hal]
            have hv1 := typeOf_entityType_declared hwf h1 heq1
            by_cases hdesc : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = true
            · rw [ite_eq_left hdesc]
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              by_cases heqe : ety₁ = ety₂
              · subst heqe
                exact HasType.binaryAppMemEntitySame x₁ x₂ c ets acts reqty ety₁ hv1 hal
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2)
              · cases hf : ets.find? ety₁ with
                | none =>
                  exact HasType.binaryAppMemEntityEntity x₁ x₂ c ets acts reqty ety₁ ety₂ hv1
                    (descendentOf_of_true_absent heqe hf hdesc) hal (heq1 ▸ hHT1) (heq2 ▸ hHT2)
                | some entry =>
                  exact HasType.binaryAppMemEntityEntity x₁ x₂ c ets acts reqty ety₁ ety₂ hv1
                    (descendentOf_of_true_inSchema hnd (find?_mapContains hf) hdesc) hal
                    (heq1 ▸ hHT1) (heq2 ▸ hHT2)
            · rw [ite_eq_right (by simpa using hdesc)]
              have hne : ety₁ ≠ ety₂ := fun he => by subst he; simp [TypeEnv.descendentOf] at hdesc
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              cases hf : ets.find? ety₁ with
              | none =>
                exact HasType.binaryAppMemActionEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂
                  (mapNotContainsKey_of_find?_none hf) hne
                  (not_maybeActionDescendentOf_of_false hne hf (by simpa using hdesc)) hal
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2)
              | some entry =>
                have hv2 := typeOf_entityType_declared hwf h2 heq2
                have hmc := find?_mapContains hf
                cases entry with
                | standard s =>
                  obtain ⟨ancs, attrs, tags⟩ := s
                  exact HasType.binaryAppMemEntityEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ hv1 hv2
                    (notDescendentOf_of_false_standard hnd hmc hne (by simpa using hdesc)) hal
                    (heq1 ▸ hHT1) (heq2 ▸ hHT2)
                | enum eids =>
                  exact HasType.binaryAppMemEntityEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ hv1 hv2
                    (NotDescendentOf.enum ets acts ety₁ ety₂ eids hne
                      (mapContainsEnum_of_mapContains hnd hmc)) hal (heq1 ▸ hHT1) (heq2 ▸ hHT2)
        · -- mem, entity/set entity
          rename_i ety₁ ety₂ heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          have hnd := hwf.ets_keys_nodup
          have hnda := hwf.acts_keys_nodup
          by_cases hal : IsActionLitMemSet x₁ x₂ acts
          · -- action-literal set membership
            cases hal with
            | mk uid₁ xs _ entry hmcA hall =>
              have hty1 := litEntity_typeOf h1
              have hc1 : acts.contains uid₁ = true := mapContains_contains hnda hmcA
              obtain ⟨uids, huids⟩ := mapM_entityUID?_all_lits hall
              have htype : typeOfInₛ ety₁ ety₂ (.lit (.entityUID uid₁)) (.set xs) ⟨ets, acts, reqty⟩
                  = (if uids.any (fun u => acts.descendentOf uid₁ u) then BoolType.tt else .ff) := by
                simp [typeOfInₛ, actionUID?, entityUID?, entityUIDs?, hc1, huids]
              rw [htype]
              by_cases hany : uids.any (fun u => acts.descendentOf uid₁ u) = true
              · rw [ite_eq_left hany]
                simp only [List.any_eq_true] at hany
                obtain ⟨u, hu_mem, hu_desc⟩ := hany
                have hais := actionInSet_of_mem huids hu_mem
                  (descendentOf_actionDescendentOf hmcA hnda hu_desc)
                exact ⟨[], HasType.binaryAppMemActionLitSetTt uid₁ xs c ets acts reqty ety₂
                  (IsActionLitMemSet.mk uid₁ xs acts entry hmcA hall) hais
                  (hty1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
              · rw [ite_eq_right hany]
                have hnais : ¬ ActionInSet acts uid₁ xs :=
                  fun ha => hany (actionInSet_any ha huids hnda)
                exact ⟨[], HasType.binaryAppMemActionLitSetFf uid₁ xs c ets acts reqty ety₂
                  (IsActionLitMemSet.mk uid₁ xs acts entry hmcA hall) hnais
                  (hty1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
          · -- generic set membership: mirror the entity/entity case — split on `ets.find? ety₁`
            rw [typeOfInₛ_fallback hal]
            have hv1 := typeOf_entityType_declared hwf h1 heq1
            by_cases hdesc : TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = true
            · rw [ite_eq_left hdesc]
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              by_cases heqe : ety₁ = ety₂
              · subst heqe
                exact HasType.binaryAppMemEntitySetSame x₁ x₂ c ets acts reqty ety₁ hv1 hal
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2)
              · cases hf : ets.find? ety₁ with
                | none =>
                  exact HasType.binaryAppMemEntitySet x₁ x₂ c ets acts reqty ety₁ ety₂ hv1
                    (descendentOf_of_true_absent heqe hf hdesc) hal (heq1 ▸ hHT1) (heq2 ▸ hHT2)
                | some entry =>
                  exact HasType.binaryAppMemEntitySet x₁ x₂ c ets acts reqty ety₁ ety₂ hv1
                    (descendentOf_of_true_inSchema hnd (find?_mapContains hf) hdesc) hal
                    (heq1 ▸ hHT1) (heq2 ▸ hHT2)
            · rw [ite_eq_right (by simpa using hdesc)]
              have hne : ety₁ ≠ ety₂ := fun he => by subst he; simp [TypeEnv.descendentOf] at hdesc
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              cases hf : ets.find? ety₁ with
              | none =>
                exact HasType.binaryAppMemActionSetFf x₁ x₂ c ets acts reqty ety₁ ety₂
                  (mapNotContainsKey_of_find?_none hf) hne
                  (not_maybeActionDescendentOf_of_false hne hf (by simpa using hdesc)) hal
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2)
              | some entry =>
                have hv2 := typeOf_setElem_entityType_declared hwf h2 heq2
                have hmc := find?_mapContains hf
                cases entry with
                | standard s =>
                  obtain ⟨ancs, attrs, tags⟩ := s
                  exact HasType.binaryAppMemEntitySetFf x₁ x₂ c ets acts reqty ety₁ ety₂ hv1 hv2
                    (notDescendentOf_of_false_standard hnd hmc hne (by simpa using hdesc)) hal
                    (heq1 ▸ hHT1) (heq2 ▸ hHT2)
                | enum eids =>
                  exact HasType.binaryAppMemEntitySetFf x₁ x₂ c ets acts reqty ety₁ ety₂ hv1 hv2
                    (NotDescendentOf.enum ets acts ety₁ ety₂ eids hne
                      (mapContainsEnum_of_mapContains hnd hmc)) hal (heq1 ▸ hHT1) (heq2 ▸ hHT2)
        · -- hasTag
          rename_i ety₁ heq1 heq2
          cases hht : typeOfHasTag ety₁ x₁ x₂ c ⟨ets, acts, reqty⟩ with
          | error e => rw [hht] at h; simp at h
          | ok r =>
            obtain ⟨rty, rc⟩ := r; rw [hht] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [typeOfHasTag] at hht
            split at hht
            · -- tags? = some none  →  `.bool .ff`
              rename_i htags
              -- a standard entry without tags, or an enum
              simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htags
              obtain ⟨entry, hfind, hea⟩ := htags
              have hmc := find?_mapContains hfind
              cases entry with
              | standard s =>
                obtain ⟨ancs, attrs, tags⟩ := s
                simp only [EntitySchemaEntry.tags?] at hea; subst hea
                simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht; obtain ⟨rfl, rfl⟩ := hht
                exact ⟨[], HasType.hasTagFf x₁ x₂ c ets acts reqty ety₁
                  (NoTags.none ets ety₁ (mapContainsNoTags_of_standard hmc))
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
              | enum eids =>
                simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht; obtain ⟨rfl, rfl⟩ := hht
                exact ⟨[], HasType.hasTagFf x₁ x₂ c ets acts reqty ety₁
                  (NoTags.enum ets ety₁ eids
                    (mapContainsEnum_of_mapContains (hwf.ets_keys_nodup) hmc))
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
            · -- tags? = some (some ty)
              rename_i ty htags
              have hhs := hasTagSchema_of_tags? htags
              split at hht
              · -- cap present  →  `.bool .tt`
                rename_i hcap
                simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht; obtain ⟨rfl, rfl⟩ := hht
                exact ⟨[], HasType.hasTagTt x₁ x₂ c ets acts reqty ety₁ ty
                  (capTagMem_iff.mpr hcap) hhs (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
              · -- cap absent  →  `.bool .anyBool`, `[(x₁, .tag x₂)]`
                rename_i hcap
                simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht; obtain ⟨rfl, rfl⟩ := hht
                refine ⟨[(x₁, .tag x₂)], ?_, fun _ => Iff.rfl⟩
                exact HasType.hasTagAnyBool x₁ x₂ c ets acts reqty ety₁ ty hhs
                  (fun hm => hcap (capTagMem_iff.mp hm)) (heq1 ▸ hHT1) (heq2 ▸ hHT2)
            · -- tags? = none
              rename_i htagsn
              split at hht
              · -- actionType? ety₁ = true  →  `.bool .ff`.
                rename_i hact
                simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht; obtain ⟨rfl, rfl⟩ := hht
                have hfnone : ets.find? ety₁ = none := by
                  simp only [EntitySchema.tags?, Option.map_eq_none_iff] at htagsn; exact htagsn
                obtain ⟨eid, entry, hpk⟩ := actionType?_mapContainsPairKey hact
                exact ⟨[], HasType.hasTagActionFf x₁ x₂ c ets acts reqty ety₁ eid entry
                  (mapNotContainsKey_of_find?_none hfnone) hpk
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
              · simp only [err, reduceCtorEq] at hht
        · -- getTag
          rename_i ety₁ heq1 heq2
          cases hgt : typeOfGetTag ety₁ x₁ x₂ c ⟨ets, acts, reqty⟩ with
          | error e => rw [hgt] at h; simp at h
          | ok r =>
            obtain ⟨rty, rc⟩ := r; rw [hgt] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [typeOfGetTag] at hgt
            split at hgt
            · simp only [err, reduceCtorEq] at hgt
            · rename_i ty htags
              split at hgt
              · rename_i hcap
                simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hgt; obtain ⟨rfl, rfl⟩ := hgt
                exact ⟨[], HasType.getTag x₁ x₂ c ets acts reqty ety₁ ty
                  (capTagMem_iff.mpr hcap) (hasTagSchema_of_tags? htags)
                  (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
              · simp only [err, reduceCtorEq] at hgt
            · simp only [err, reduceCtorEq] at hgt
        · -- less int/int
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppLessInt x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1) (heq2 ▸ hHT2),
            fun _ => Iff.rfl⟩
        · -- less datetime/datetime
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppLessDatetime x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1)
            (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
        · -- less duration/duration
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppLessDuration x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1)
            (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
        · -- lessEq int/int
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppLessEqInt x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1)
            (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
        · -- lessEq datetime/datetime
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppLessEqDatetime x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1)
            (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
        · -- lessEq duration/duration
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppLessEqDuration x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1)
            (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
        · -- add
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppAdd x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1) (heq2 ▸ hHT2),
            fun _ => Iff.rfl⟩
        · -- sub
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppSub x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1) (heq2 ▸ hHT2),
            fun _ => Iff.rfl⟩
        · -- mul
          rename_i heq1 heq2
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], HasType.binaryAppMul x₁ x₂ c ⟨ets, acts, reqty⟩ (heq1 ▸ hHT1) (heq2 ▸ hHT2),
            fun _ => Iff.rfl⟩
        · -- contains
          rename_i ty₃ heq3
          cases hlub : ifLubThenBool ty2.typeOf ty₃ with
          | error e => rw [hlub] at h; simp at h
          | ok r =>
            obtain ⟨rt, rc⟩ := r; rw [hlub] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [ifLubThenBool] at hlub
            split at hlub
            · rename_i lt hlt
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hlub; obtain ⟨rfl, rfl⟩ := hlub
              exact ⟨[], HasType.binaryAppContains x₁ x₂ c ⟨ets, acts, reqty⟩ ty2.typeOf ty₃
                (lubCompat_of_lub? hlt) (heq3 ▸ hHT1) hHT2, fun _ => Iff.rfl⟩
            · simp only [err, reduceCtorEq] at hlub
        · -- containsAll
          rename_i ty₃ ty₄ heq1 heq2
          cases hlub : ifLubThenBool ty₃ ty₄ with
          | error e => rw [hlub] at h; simp at h
          | ok r =>
            obtain ⟨rt, rc⟩ := r; rw [hlub] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [ifLubThenBool] at hlub
            split at hlub
            · rename_i lt hlt
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hlub; obtain ⟨rfl, rfl⟩ := hlub
              exact ⟨[], HasType.binaryAppContainsAll x₁ x₂ c ⟨ets, acts, reqty⟩ ty₃ ty₄
                (lubCompat_of_lub? hlt) (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
            · simp only [err, reduceCtorEq] at hlub
        · -- containsAny
          rename_i ty₃ ty₄ heq1 heq2
          cases hlub : ifLubThenBool ty₃ ty₄ with
          | error e => rw [hlub] at h; simp at h
          | ok r =>
            obtain ⟨rt, rc⟩ := r; rw [hlub] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [ifLubThenBool] at hlub
            split at hlub
            · rename_i lt hlt
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hlub; obtain ⟨rfl, rfl⟩ := hlub
              exact ⟨[], HasType.binaryAppContainsAny x₁ x₂ c ⟨ets, acts, reqty⟩ ty₃ ty₄
                (lubCompat_of_lub? hlt) (heq1 ▸ hHT1) (heq2 ▸ hHT2), fun _ => Iff.rfl⟩
            · simp only [err, reduceCtorEq] at hlub
        · -- fallthrough (unexpected operand types)
          simp only [err, reduceCtorEq] at h
  | case8 c x₁ a ih1 =>
    -- hasAttr
    intro tx c' h
    obtain ⟨ets, acts, reqty⟩ := env
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c ⟨ets, acts, reqty⟩ with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
      simp only [typeOfHasAttr] at h
      split at h
      · -- receiver is a record
        rename_i rty heqty
        cases hfa : rty.find? a with
        | some qty =>
          cases hha : hasAttrInRecord rty x₁ a c true with
          | error e => rw [hha] at h; simp at h
          | ok r =>
            obtain ⟨ty', caps⟩ := r
            rw [hha] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have htw := typeOf_tyWf hwf h1; rw [heqty] at htw
            have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
            refine ⟨caps, ?_, fun _ => Iff.rfl⟩
            show HasType false false (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ ty' caps
            exact HasType.hasAttrRecord x₁ a c ⟨ets, acts, reqty⟩ rty ty' caps (heqty ▸ hHT1)
              (hasAttrInRecord_found_of_ok hfa hha)
        | none =>
          rw [show hasAttrInRecord rty x₁ a c true = ok (.bool .ff) from by
            simp only [hasAttrInRecord, hfa]] at h
          simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨rtyList⟩ := rty
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          show HasType false false (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []
          exact HasType.hasAttrRecordNotFound x₁ a c ⟨ets, acts, reqty⟩ rtyList (heqty ▸ hHT1)
            (mapNotContainsKey_of_find?_none hfa)
      · -- receiver is an entity
        rename_i ety heqty
        split at h
        · -- attrs? ety = some rty
          rename_i rty hattr
          have hnd : (rty.toList.map Prod.fst).Nodup := by
            cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
          have hattr2 := hattr
          simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattr2
          obtain ⟨entry, hfind, hea⟩ := hattr2
          have hmc := find?_mapContains hfind
          cases entry with
          | standard s =>
            obtain ⟨ancs, attrs, tags⟩ := s
            simp only [EntitySchemaEntry.attrs] at hea
            have hmca : MapContainsAttrs ety rty ets := hea ▸ mapContainsAttrs_of_standard hmc
            cases hfa : rty.find? a with
            | some qty =>
              cases hha : hasAttrInRecord rty x₁ a c false with
              | error e => rw [hha] at h; simp at h
              | ok r =>
                obtain ⟨ty', caps⟩ := r
                rw [hha] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨caps, ?_, fun _ => Iff.rfl⟩
                show HasType false false (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ ty' caps
                exact HasType.hasAttrEntity x₁ a c ets acts reqty ety ty' caps rty hmca
                  (heqty ▸ hHT1) (hasAttrInRecord_found_of_ok hfa hha)
            | none =>
              rw [show hasAttrInRecord rty x₁ a c false = ok (.bool .ff) from by
                simp only [hasAttrInRecord, hfa]] at h
              simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              show HasType false false (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []
              exact HasType.hasAttrEntityNotFound x₁ a c ets acts reqty ety rty hmca
                (heqty ▸ hHT1) (mapNotContainsKey_of_find?_none hfa)
          | enum eids =>
            simp only [EntitySchemaEntry.attrs] at hea
            have hmce : MapContainsEnum ety eids ets :=
              mapContainsEnum_of_mapContains (hwf.ets_keys_nodup) hmc
            rw [show hasAttrInRecord rty x₁ a c false = ok (.bool .ff) from by
              rw [← hea]; simp only [hasAttrInRecord, show (Map.empty : RecordType).find? a = none from rfl]] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨[], ?_, fun _ => Iff.rfl⟩
            show HasType false false (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []
            exact HasType.hasAttrEnum x₁ a c ets acts reqty ety eids hmce (heqty ▸ hHT1)
        · -- attrs? ety = none
          rename_i hattrn
          split at h
          · -- actionType? ety = true → `.bool .ff`.
            rename_i hact
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            have hfnone : ets.find? ety = none := by
              simp only [EntitySchema.attrs?, Option.map_eq_none_iff] at hattrn; exact hattrn
            obtain ⟨eid, entry, hpk⟩ := actionType?_mapContainsPairKey hact
            refine ⟨[], ?_, fun _ => Iff.rfl⟩
            show HasType false false (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []
            exact HasType.hasAttrActionFf x₁ a c ets acts reqty ety eid entry
              (mapNotContainsKey_of_find?_none hfnone) hpk (heqty ▸ hHT1)
          · simp only [err, reduceCtorEq] at h
      · simp only [err, reduceCtorEq] at h
  | case9 c x₁ a as ih1 =>
    -- extHasAttr
    intro tx c' h
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, _⟩ := ih1 h1
      cases hc : typeOfExtHasAttr ty1 x₁ (a :: as) c env with
      | error e => rw [hc] at h; simp at h
      | ok r2 =>
        obtain ⟨bty, cc2⟩ := r2
        rw [hc] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cout, hch, hce⟩ := extHasAttrChain_complete hwf as (typeOf_tyWf hwf h1) hc
        exact ⟨cout, HasType.extHasAttr _ _ _ _ _ _ _ _ _ hHT1 hch (.no _ _), hce⟩
  | case10 c x₁ a ih1 =>
    -- getAttr
    intro tx c' h
    obtain ⟨ets, acts, reqty⟩ := env
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c ⟨ets, acts, reqty⟩ with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, hce1⟩ := ih1 h1
      simp only [typeOfGetAttr] at h
      split at h
      · -- receiver is a record
        rename_i rty heqty
        cases hg : getAttrInRecord ty1.typeOf rty x₁ a c with
        | error e => rw [hg] at h; simp at h
        | ok r =>
          obtain ⟨aty, ac⟩ := r
          rw [hg] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have htw := typeOf_tyWf hwf h1; rw [heqty] at htw
          have hnd : (rty.toList.map Prod.fst).Nodup := by cases htw with | record _ hn _ => exact hn
          obtain ⟨hgar, rfl⟩ := getAttrInRecord_of_ok hg
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          show HasType false false (.getAttr x₁ a) c ⟨ets, acts, reqty⟩ aty []
          exact HasType.getAttrRecord x₁ a c ⟨ets, acts, reqty⟩ rty aty (heqty ▸ hHT1) hgar
      · -- receiver is an entity
        rename_i ety heqty
        split at h
        · -- attrs? ety = some rty
          rename_i rty hattr
          cases hg : getAttrInRecord ty1.typeOf rty x₁ a c with
          | error e => rw [hg] at h; simp at h
          | ok r =>
            obtain ⟨aty, ac⟩ := r
            rw [hg] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hnd : (rty.toList.map Prod.fst).Nodup := by
              cases hwf.attrs_tyWf hattr with | record _ hn _ => exact hn
            simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattr
            obtain ⟨entry, hfind, hea⟩ := hattr
            have hmc := find?_mapContains hfind
            cases entry with
            | standard s =>
              obtain ⟨ancs, attrs, tags⟩ := s
              simp only [EntitySchemaEntry.attrs] at hea
              have hmca := mapContainsAttrs_of_standard hmc
              obtain ⟨hgar, rfl⟩ := getAttrInRecord_of_ok hg
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              show HasType false false (.getAttr x₁ a) c ⟨ets, acts, reqty⟩ aty []
              exact HasType.getAttrEntity x₁ a c ets acts reqty ety aty rty (hea ▸ hmca)
                (heqty ▸ hHT1) hgar
            | enum eids =>
              simp only [EntitySchemaEntry.attrs] at hea
              rw [← hea] at hg
              simp only [getAttrInRecord, show (Map.empty : RecordType).find? a = none from rfl,
                err, reduceCtorEq] at hg
        · simp only [err, reduceCtorEq] at h
      · simp only [err, reduceCtorEq] at h
  | case11 c xs ih =>
    intro tx c' h
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases xs with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, bind, Except.bind, typeOfSet, err,
        reduceCtorEq] at h
    | cons x₀ xs' =>
      simp only [List.mapM_cons] at h
      cases hx0 : justType (typeOf x₀ c env) with
      | error e => rw [hx0] at h; simp at h
      | ok thd =>
        rw [hx0] at h; simp only [Except.bind_ok] at h
        cases hxs' : xs'.mapM (fun x => justType (typeOf x c env)) with
        | error e => rw [hxs'] at h; simp at h
        | ok ttl =>
          rw [hxs'] at h
          simp only [pure, Except.pure, bind, Except.bind, typeOfSet] at h
          split at h
          · rename_i lubty hfold
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨cc0, hx02⟩ := justType_ok hx0
            obtain ⟨cout0, hHT0, _⟩ :=
              ih x₀ List.mem_cons_self hx02
            have hty' : ∀ x ∈ xs', ∀ {tx : TypedExpr} {cc : Capabilities},
                typeOf x c env = .ok (tx, cc) → ∃ cout, HasType false false x c env tx.typeOf cout := by
              intro x hx tx cc htyp
              obtain ⟨cout, hHT, _⟩ :=
                ih x (List.mem_cons_of_mem _ hx) htyp
              exact ⟨cout, hHT⟩
            have hlist := hasTypeList_of_mapM hty' hxs'
            have hallub := allLub_of_foldlM hfold
            refine ⟨[], ?_, fun _ => Iff.rfl⟩
            simp only [TypedExpr.typeOf]
            exact HasType.set x₀ xs' c env thd.typeOf (ttl.map TypedExpr.typeOf) lubty
              hHT0 hlist hallub
          · simp only [err, reduceCtorEq] at h
  | case12 c axs ih =>
    intro tx c' h
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1)))] at h
    cases hm : axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
    | error e => rw [hm] at h; simp at h
    | ok atys =>
      rw [hm] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hty' : ∀ ax ∈ axs, ∀ {tx : TypedExpr} {cc : Capabilities},
          typeOf ax.2 c env = .ok (tx, cc) → ∃ cout, HasType false false ax.2 c env tx.typeOf cout := by
        intro ax hax tx cc htyp
        have hsz : sizeOf (ax.1, ax.2).snd < 1 + sizeOf axs := by
          have hlt := List.sizeOf_lt_of_mem hax
          obtain ⟨a, x⟩ := ax
          simp only [sizeOf, Prod._sizeOf_1] at *
          omega
        obtain ⟨cout, hHT, _⟩ := ih ax.1 ax.2 hsz htyp
        exact ⟨cout, hHT⟩
      exact ⟨[], HasType.record axs c env _ (RecordTypeOf.lax _ _ _ _ (hasTypeFields_of_mapM hty' hm)),
        fun _ => Iff.rfl⟩
  | case13 c xfn xs ih =>
    intro tx c' h
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
    | error e => rw [hm] at h; simp at h
    | ok tys =>
      rw [hm] at h; simp only [Except.bind_ok] at h
      have hty' : ∀ x ∈ xs, ∀ {tx : TypedExpr} {cc : Capabilities},
          typeOf x c env = .ok (tx, cc) → ∃ cout, HasType false false x c env tx.typeOf cout := by
        intro x hx tx cc htyp
        obtain ⟨cout, hHT, _⟩ := ih x hx htyp
        exact ⟨cout, hHT⟩
      have hlist := hasTypeList_of_mapM hty' hm
      obtain ⟨hExt, rfl⟩ := hasTypeExtCall_of_typeOfCall hlist h
      exact ⟨[], HasType.callExt xfn xs c env tx.typeOf hExt, fun _ => Iff.rfl⟩

/-- Every environment described by the relational schema spec (`Schema.WfTypeEnv`)
    satisfies `EnvAssumptions`. -/
theorem Schema.WfTypeEnv.envAssumptions {env : TypeEnv} (hwf : Schema.WfTypeEnv env) :
    EnvAssumptions env where
  ets_keys_nodup := wfTypeEnv_ets_nodup hwf
  acts_keys_nodup := wfTypeEnv_acts_nodup hwf
  attrs_tyWf := wfTypeEnv_attrs?_tyWf hwf
  tags_tyWf := wfTypeEnv_tags?_tyWf hwf
  context_tyWf := wfTypeEnv_context_tyWf hwf
  attrs_typeValid := wfTypeEnv_attrs?_typeValid hwf
  tags_typeValid := wfTypeEnv_tags?_typeValid hwf
  reqty_valid := wfTypeEnv_reqty_valid hwf

/-- `HasType false false` characterizes the typechecker: on an environment satisfying
    `EnvAssumptions`, the relation derives type `ty` for `x` exactly when `typeOf` succeeds with
    a typed expression of type `ty`. Output capabilities agree up to `CapsEquiv` (see
    `hasType_sound` and `typeOf_complete`). -/
theorem hasType_iff_typeOf_ok {env : TypeEnv} (hwf : EnvAssumptions env)
    {x : Expr} {c : Capabilities} {ty : CedarType} :
    (∃ cout, HasType false false x c env ty cout) ↔
      (∃ tx c', typeOf x c env = .ok (tx, c') ∧ tx.typeOf = ty) := by
  constructor
  · rintro ⟨cout, hHT⟩
    obtain ⟨tx, c', hok, hty, _⟩ := hasType_sound hwf hHT
    exact ⟨tx, c', hok, hty⟩
  · rintro ⟨tx, c', hok, hty⟩
    obtain ⟨cout, hHT, _⟩ := typeOf_complete hwf hok
    exact ⟨cout, hty ▸ hHT⟩

/-- **Strict completeness.** On an environment satisfying `EnvAssumptions`, every successful run
    of `typeOf` on an expression with declared entities, in the parser's image, is witnessed by
    a `HasType true true` derivation (up to `CapsEquiv` on the output capabilities). -/
theorem typeOf_complete_strict {env : TypeEnv} (hwf : EnvAssumptions env) {x : Expr}
    {c : Capabilities} {tx : TypedExpr} {c' : Capabilities} (hok : typeOf x c env = .ok (tx, c'))
    (hd : EntitiesDeclared env.ets env.acts x) (hk : ParserImage x) :
    ∃ cout, HasType true true x c env tx.typeOf cout ∧ CapsEquiv cout c' := by
  obtain ⟨cout, hHT, hc⟩ := typeOf_complete hwf hok
  exact ⟨cout, hHT.strengthen hd hk, hc⟩

/-- `HasType true true` characterizes the typechecker on expressions meeting the syntactic
    conditions: on an environment satisfying `EnvAssumptions`, the relation derives type `ty`
    for `x` exactly when `typeOf` succeeds with a typed expression of type `ty` and `x` has
    declared entities and is in the parser's image (`ParserImage`). -/
theorem hasType_strict_iff_typeOf_ok {env : TypeEnv} (hwf : EnvAssumptions env)
    {x : Expr} {c : Capabilities} {ty : CedarType} :
    (∃ cout, HasType true true x c env ty cout) ↔
      (∃ tx c', typeOf x c env = .ok (tx, c') ∧ tx.typeOf = ty) ∧
        EntitiesDeclared env.ets env.acts x ∧ ParserImage x := by
  constructor
  · rintro ⟨cout, hHT⟩
    exact ⟨(hasType_iff_typeOf_ok hwf).mp ⟨cout, hHT.weaken⟩, hHT.strict_syntax⟩
  · rintro ⟨⟨tx, c', hok, hty⟩, hd, hk⟩
    obtain ⟨cout, hHT, _⟩ := typeOf_complete_strict hwf hok hd hk
    exact ⟨cout, hty ▸ hHT⟩

end Cedar.Validation.Relational

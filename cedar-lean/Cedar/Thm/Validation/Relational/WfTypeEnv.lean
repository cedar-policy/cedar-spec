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

public import Cedar.Thm.Validation.Relational.EnvironmentValidation
import Batteries.Data.List.Lemmas
import all Cedar.Data.Map -- unfolds `contains`, `empty`, `find`, …
import all Cedar.Data.Set -- unfolds `all`, `any`, `contains`, …
import all Cedar.Spec.Entities -- unfolds `ancestors`, `attrs`, `tags`
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.EnvironmentValidator -- unfolds `validateWellFormed`
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `QualifiedType`, …
import all Cedar.Validation.Validator -- unfolds `environment`, `environments`

/-! # The generator-shaped `WfTypeEnv` and `validateWellFormed`

`wfTypeEnv_typeEnvWF_iff`: a `WfTypeEnv` environment is well-formed iff it meets the conditions
`WfTypeEnvGaps` collects. -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## The conditions `WfTypeEnv` leaves open -/

/-- The set-shape conditions on an entity entry: a standard entry's ancestors are sorted, an
enumeration is non-empty and sorted. -/
def EntityEntrySetsSorted : EntitySchemaEntry → Prop
  | .standard entry => EltsSorted entry.ancestors.elts
  | .enum eids => eids.elts ≠ [] ∧ EltsSorted eids.elts

/-- The set-shape conditions on an action entry: its principal, resource and ancestor sets are
sorted. -/
def ActionEntrySetsSorted (entry : ActionSchemaEntry) : Prop :=
  EltsSorted entry.appliesToPrincipal.elts ∧ EltsSorted entry.appliesToResource.elts ∧
    EltsSorted entry.ancestors.elts

/-- The well-formedness conditions that `Schema.WfTypeEnv` does not guarantee: both maps are
sorted, every set is sorted, enumerations are non-empty, and no action's entity type is
declared in the entity schema. -/
def WfTypeEnvGaps (env : TypeEnv) : Prop :=
  KeysSorted env.ets.toList ∧
  KeysSorted env.acts.toList ∧
  (∀ p ∈ env.ets.toList, EntityEntrySetsSorted p.2) ∧
  (∀ p ∈ env.acts.toList, ActionEntrySetsSorted p.2) ∧
  (∀ p ∈ env.acts.toList, env.ets.find? p.1.ty = none)

/-- Every well-formed environment satisfies `WfTypeEnvGaps`. -/
theorem typeEnvWF_gaps {env : TypeEnv} (h : TypeEnvWF env) : WfTypeEnvGaps env := by
  obtain ⟨⟨el⟩, ⟨al⟩, reqty⟩ := env
  match h with
  | .mk _ _ _ he ha _ =>
  match he, ha with
  | .mk _ _ _ hes hee, .mk _ _ _ has hae _ _ =>
  refine ⟨hes, has, fun ⟨_, entry⟩ hp => ?_, fun ⟨_, entry⟩ hp => ?_, fun p hp => ?_⟩
  · match entry, entityEntriesWF_iff.mp hee _ hp with
    | _, .standard _ _ _ (.mk _ _ _ _ _ hs _ _ _ _) => exact hs
    | _, .enum _ _ _ _ hs => exact ⟨List.cons_ne_nil _ _, hs⟩
  · match entry, (actionEntriesWF_iff.mp hae _ hp).2 with
    | _, .mk _ _ _ _ _ _ hp hr ha _ _ _ _ _ => exact ⟨hp, hr, ha⟩
  · exact (actionEntriesWF_iff.mp hae _ hp).1

/-! ## Generator invariants -/

theorem definedEntityType_mem {l : List EntityType} {x : EntityType}
    (h : Schema.DefinedEntityType l x) : x ∈ l := by
  induction h <;> simp_all

theorem keysSorted_cons_of_above {attr : Attr} {v : QualifiedType}
    {rest : List (Attr × QualifiedType)} (hs : KeysSorted rest)
    (ha : ∀ a q r, rest = (a, q) :: r → Schema.KeyAbove (some attr) a) :
    KeysSorted ((attr, v) :: rest) := by
  match rest, hs, ha with
  | [], _, _ => exact .single _ _
  | (a, q) :: r, hs, ha =>
    match ha a q r rfl with
    | .some _ _ hlt => exact .cons _ _ _ _ _ hlt hs

mutual

theorem wfCedarType_cedarTypeWF {ets : EntitySchema} {acts : ActionSchema}
    {names : List EntityType} {ty : CedarType} (hd : ∀ x ∈ names, EntityTypeWF ets acts x) :
    Schema.WfCedarType names ty → CedarTypeWF ets acts ty ∧ CedarTypeLifted ty
  | .bool _ => ⟨.bool _ _ _, .bool⟩
  | .int _ => ⟨.int _ _, .int⟩
  | .string _ => ⟨.string _ _, .string⟩
  | .entity _ _ h => ⟨.entity _ _ _ (hd _ (definedEntityType_mem h)), .entity _⟩
  | .set _ _ h =>
    have ih := wfCedarType_cedarTypeWF hd h
    ⟨.set _ _ _ ih.1, .set _ ih.2⟩
  | .record _ _ h =>
    have ih := wfAttrs_attrsWF hd h
    ⟨.record _ _ _ ih.2.2.1 ih.1, .record _ ih.2.1⟩
  | .extDecimal _ => ⟨.ext _ _ _, .ext _⟩
  | .extIPAddr _ => ⟨.ext _ _ _, .ext _⟩
  | .extDatetime _ => ⟨.ext _ _ _, .ext _⟩
  | .extDuration _ => ⟨.ext _ _ _, .ext _⟩

theorem wfAttrs_attrsWF {ets : EntitySchema} {acts : ActionSchema}
    {names : List EntityType} {lb : Option Attr} {l : List (Attr × QualifiedType)}
    (hd : ∀ x ∈ names, EntityTypeWF ets acts x) :
    Schema.WfAttrs lb names l →
      AttrsWF ets acts l ∧ AttrsLifted l ∧ KeysSorted l ∧
        ∀ a q r, l = (a, q) :: r → Schema.KeyAbove lb a
  | .nil _ _ => ⟨.nil _ _, .nil, .nil, fun _ _ _ h => nomatch h⟩
  | .consRequired _ _ _ _ _ hka hty hrest =>
    have iht := wfCedarType_cedarTypeWF hd hty
    have ihr := wfAttrs_attrsWF hd hrest
    ⟨.cons _ _ _ _ _ (.required _ _ _ iht.1) ihr.1, .cons _ _ _ (.required _ iht.2) ihr.2.1,
      keysSorted_cons_of_above ihr.2.2.1 ihr.2.2.2, fun _ _ _ h => by cases h; exact hka⟩
  | .consOptional _ _ _ _ _ hka hty hrest =>
    have iht := wfCedarType_cedarTypeWF hd hty
    have ihr := wfAttrs_attrsWF hd hrest
    ⟨.cons _ _ _ _ _ (.optional _ _ _ iht.1) ihr.1, .cons _ _ _ (.optional _ iht.2) ihr.2.1,
      keysSorted_cons_of_above ihr.2.2.1 ihr.2.2.2, fun _ _ _ h => by cases h; exact hka⟩

end

theorem wfAttrs_record {ets : EntitySchema} {acts : ActionSchema} {names : List EntityType}
    {l : List (Attr × QualifiedType)} (hd : ∀ x ∈ names, EntityTypeWF ets acts x)
    (h : Schema.WfAttrs none names l) :
    CedarTypeWF ets acts (.record (.mk l)) ∧ CedarTypeLifted (.record (.mk l)) :=
  have h := wfAttrs_attrsWF hd h
  ⟨.record _ _ _ h.2.2.1 h.1, .record _ h.2.1⟩

theorem wfPrincipalTypes_entityTypesWF {ets : EntitySchema} {acts : ActionSchema}
    {names l : List EntityType} (hd : ∀ x ∈ names, EntityTypeWF ets acts x)
    (h : Schema.WfPrincipalTypes names l) : EntityTypesWF ets acts l := by
  induction h with
  | nil => exact .nil _ _
  | cons _ _ hp _ ih => exact .cons _ _ _ _ (hd _ (definedEntityType_mem hp)) ih

theorem wfResourceTypes_entityTypesWF {ets : EntitySchema} {acts : ActionSchema}
    {names l : List EntityType} (hd : ∀ x ∈ names, EntityTypeWF ets acts x)
    (h : Schema.WfResourceTypes names l) : EntityTypesWF ets acts l := by
  induction h with
  | nil => exact .nil _ _
  | cons _ _ hp _ ih => exact .cons _ _ _ _ (hd _ (definedEntityType_mem hp)) ih

theorem wfTags_tagsWF {ets : EntitySchema} {acts : ActionSchema} {names : List EntityType}
    {tags : Option CedarType} (hd : ∀ x ∈ names, EntityTypeWF ets acts x)
    (h : Schema.WfTags names tags) : TagsWF ets acts tags := by
  cases h with
  | none => exact .none _ _
  | some _ h =>
    have h := wfCedarType_cedarTypeWF hd h
    exact .some _ _ _ h.1 h.2

/-! ### Entity schema -/

theorem appendET_eq {xs ys zs : List EntityType} (h : Schema.AppendET xs ys zs) :
    zs = xs ++ ys := by
  induction h <;> simp_all

theorem pickClosedAncestors_mem {built : List (EntityType × List EntityType)}
    {chosen : List EntityType} (h : Schema.PickClosedAncestors built chosen) :
    ∀ x ∈ chosen, ∃ p ∈ built, x = p.1 ∨ x ∈ p.2 := by
  induction h with
  | none => simp
  | skip p pset built chosen _ ih =>
    intro x hx
    obtain ⟨q, hq, hx⟩ := ih x hx
    exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩
  | pick p pset built chosen merged _ happ ih =>
    intro x hx
    rw [appendET_eq happ] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨(x, pset), List.mem_cons_self, .inl rfl⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(p, pset), List.mem_cons_self, .inr hx⟩
    · obtain ⟨q, hq, hx⟩ := ih x hx
      exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩

theorem wfEntitiesGo_names_mem {built : List (EntityType × List EntityType)}
    {names allNames : List EntityType} {entries : List (EntityType × EntitySchemaEntry)}
    (h : Schema.WfEntitiesGo built names allNames entries) : ∀ x ∈ names, x ∈ allNames := by
  induction h with
  | nil => exact fun _ hx => hx
  | standard _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact fun x hx => ih x (List.mem_cons_of_mem _ hx)
  | enum _ _ _ _ _ _ _ _ ih => exact fun x hx => ih x (List.mem_cons_of_mem _ hx)

theorem wfEntitiesGo_allNames_mem {built : List (EntityType × List EntityType)}
    {names allNames : List EntityType} {entries : List (EntityType × EntitySchemaEntry)}
    (h : Schema.WfEntitiesGo built names allNames entries) :
    ∀ x ∈ allNames, x ∈ names ∨ ∃ e, (x, e) ∈ entries := by
  induction h with
  | nil => exact fun _ hx => .inl hx
  | standard _ _ et _ _ _ _ _ _ _ _ _ _ ih =>
    intro x hx
    rcases ih x hx with hx | ⟨e, he⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr ⟨_, List.mem_cons_self⟩
      · exact .inl hx
    · exact .inr ⟨e, List.mem_cons_of_mem _ he⟩
  | enum _ _ et _ _ _ _ _ ih =>
    intro x hx
    rcases ih x hx with hx | ⟨e, he⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr ⟨_, List.mem_cons_self⟩
      · exact .inl hx
    · exact .inr ⟨e, List.mem_cons_of_mem _ he⟩

theorem wfEntitiesGo_entityEntriesWF {ets : EntitySchema} {acts : ActionSchema}
    {built : List (EntityType × List EntityType)} {names allNames : List EntityType}
    {entries : List (EntityType × EntitySchemaEntry)}
    (h : Schema.WfEntitiesGo built names allNames entries)
    (hb : ∀ p ∈ built, ∀ x, (x = p.1 ∨ x ∈ p.2) → x ∈ names)
    (hk : ∀ x ∈ allNames, ∃ e, MapContains x e ets)
    (hs : ∀ p ∈ entries, EntityEntrySetsSorted p.2) :
    EntityEntriesWF ets acts entries := by
  induction h with
  | nil => exact .nil _ _
  | standard built names et ancestors attrs tags allNames rest _ hpick hattrs htags hgo ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hs
    have hnames := wfEntitiesGo_names_mem hgo
    have hd : ∀ x ∈ et :: names, EntityTypeWF ets acts x := fun x hx =>
      have ⟨e, he⟩ := hk x (hnames x hx)
      .entity _ _ _ e he
    have hanc : ∀ x ∈ ancestors, x ∈ names := fun x hx =>
      have ⟨p, hp, hx⟩ := pickClosedAncestors_mem hpick x hx
      hb p hp x hx
    have hrec := wfAttrs_record hd hattrs
    refine .cons _ _ _ _ _ (.standard _ _ _ (.mk _ _ _ _ _ hs.1 ?_ hrec.1 hrec.2
      (wfTags_tagsWF hd htags))) (ih ?_ hk hs.2)
    · exact entityAncestorsWF_iff.mpr fun x hx =>
        map_find?_isSome_iff_mapContains.mpr (hk x (hnames x (List.mem_cons_of_mem _ (hanc x hx))))
    · intro p hp x hx
      rcases List.mem_cons.mp hp with rfl | hp
      · rcases hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hanc x hx)
      · exact List.mem_cons_of_mem _ (hb p hp x hx)
  | enum built names et eids allNames rest _ hgo ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hs
    obtain ⟨⟨hne, hsorted⟩, hs⟩ := hs
    refine .cons _ _ _ _ _ ?_ (ih (fun p hp x hx => List.mem_cons_of_mem _ (hb p hp x hx)) hk hs)
    match eids, hne, hsorted with
    | _ :: _, _, hsorted => exact .enum _ _ _ _ hsorted

/-! ### Action schema -/

/-- `built` is closed: each recorded ancestor list contains, with every action, that action's
own (earlier recorded) ancestor list. -/
inductive ClosedBuilt : List (EntityUID × List EntityUID) → Prop where
  | nil : ClosedBuilt []
  | cons : ∀ p pset rest,
      (∀ q ∈ pset, ∃ qset, (q, qset) ∈ rest ∧ ∀ y ∈ qset, y ∈ pset) →
      ClosedBuilt rest → ClosedBuilt ((p, pset) :: rest)

theorem appendUID_eq {xs ys zs : List EntityUID} (h : Schema.AppendUID xs ys zs) :
    zs = xs ++ ys := by
  induction h <;> simp_all

theorem pickClosedActionAncestors_closed {built : List (EntityUID × List EntityUID)}
    {chosen : List EntityUID} (h : Schema.PickClosedActionAncestors built chosen)
    (hc : ClosedBuilt built) :
    ∀ x ∈ chosen, ∃ xset, (x, xset) ∈ built ∧ ∀ y ∈ xset, y ∈ chosen := by
  induction h with
  | none => simp
  | skip p pset built chosen _ ih =>
    cases hc with
    | cons _ _ _ _ hc =>
      intro x hx
      obtain ⟨xs, hm, hs⟩ := ih hc x hx
      exact ⟨xs, List.mem_cons_of_mem _ hm, hs⟩
  | pick p pset built chosen merged _ happ ih =>
    cases hc with
    | cons _ _ _ hhead hc =>
      rw [appendUID_eq happ]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨pset, List.mem_cons_self,
          fun y hy => List.mem_cons_of_mem _ (List.mem_append_left _ hy)⟩
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨xs, hm, hs⟩ := hhead x hx
        exact ⟨xs, List.mem_cons_of_mem _ hm,
          fun y hy => List.mem_cons_of_mem _ (List.mem_append_left _ (hs y hy))⟩
      · obtain ⟨xs, hm, hs⟩ := ih hc x hx
        exact ⟨xs, List.mem_cons_of_mem _ hm,
          fun y hy => List.mem_cons_of_mem _ (List.mem_append_right _ (hs y hy))⟩

/-- What `WfActionsGo` guarantees about each generated action, relative to the actions `pre`
generated before it: its shape, its components' generator relations, and that its ancestors
are earlier actions whose own ancestors it inherits. -/
theorem wfActionsGo_entries {names : List EntityType}
    {built : List (EntityUID × List EntityUID)} {avail : List String}
    {entries : List (EntityUID × ActionSchemaEntry)}
    (h : Schema.WfActionsGo names built avail entries) :
    ∀ {pre : List (EntityUID × ActionSchemaEntry)}, ClosedBuilt built →
      (∀ p ∈ built, ∃ e, (p.1, e) ∈ pre ∧ e.ancestors = Set.mk p.2) →
      ((pre ++ entries).map Prod.fst).Nodup →
      ∀ q ∈ entries, ∃ principals resources ancestors context,
        q.2 = ⟨Set.mk principals, Set.mk resources, Set.mk ancestors, Map.mk context⟩ ∧
        Schema.WfPrincipalTypes names principals ∧ Schema.WfResourceTypes names resources ∧
        Schema.WfAttrs none names context ∧
        q.1 ∉ ancestors ∧
        ∀ x ∈ ancestors, ∃ e, (x, e) ∈ pre ++ entries ∧ ∀ y ∈ e.ancestors.elts, y ∈ ancestors := by
  induction h with
  | nil => intro _ _ _ _ q hq; exact absurd hq List.not_mem_nil
  | cons built avail avail' eid ancestors principals resources context rest
      _ hpick hwp hwr hwa _ ih =>
    intro pre hc hbp hnd q hq
    have hcl := pickClosedActionAncestors_closed hpick hc
    have hanc : ∀ x ∈ ancestors, ∃ e, (x, e) ∈ pre ∧ ∀ y ∈ e.ancestors.elts, y ∈ ancestors := by
      intro x hx
      obtain ⟨xset, hxm, hxs⟩ := hcl x hx
      obtain ⟨e, he, hea⟩ := hbp _ hxm
      exact ⟨e, he, by simpa only [hea] using hxs⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · refine ⟨principals, resources, ancestors, context, rfl, hwp, hwr, hwa, fun hm => ?_,
        fun x hx => have ⟨e, he, hs⟩ := hanc x hx; ⟨e, List.mem_append_left _ he, hs⟩⟩
      obtain ⟨e, he, _⟩ := hanc _ hm
      rw [List.map_append, List.nodup_append] at hnd
      exact hnd.2.2 _ (List.mem_map_of_mem (f := Prod.fst) he) _ (by simp) rfl
    · have := ih (pre := pre ++ [(⟨Schema.actionEntityType, eid⟩,
          ⟨Set.mk principals, Set.mk resources, Set.mk ancestors, Map.mk context⟩)])
        (.cons _ _ _ hcl hc) ?_ (by simpa only [List.append_assoc, List.singleton_append]) q hq
      · simpa only [List.append_assoc, List.singleton_append] using this
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
        · obtain ⟨e, he, hea⟩ := hbp p hp
          exact ⟨e, List.mem_append_left _ he, hea⟩

/-! ### Request type -/

theorem requestFromAction_entry {names : List EntityType}
    {entries : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    (h : Schema.RequestFromAction names entries reqty) :
    ∃ principals resources ancestors context,
      (reqty.action, ⟨Set.mk principals, Set.mk resources, Set.mk ancestors, Map.mk context⟩) ∈
        entries ∧
      reqty.principal ∈ principals ∧ reqty.resource ∈ resources ∧
      reqty.context = Map.mk context := by
  induction h with
  | here _ _ principals resources ancestors context _ _ hp hr =>
    exact ⟨principals, resources, ancestors, context, List.mem_cons_self,
      definedEntityType_mem hp, definedEntityType_mem hr, rfl⟩
  | there _ _ _ _ ih =>
    obtain ⟨ps, rs, ancs, ctx, hm, hp, hr, hc⟩ := ih
    exact ⟨ps, rs, ancs, ctx, List.mem_cons_of_mem _ hm, hp, hr, hc⟩

/-! ## `WfTypeEnv` is well-formed exactly up to `WfTypeEnvGaps` -/

/-- A generated environment satisfying `WfTypeEnvGaps` is well-formed. -/
theorem wfTypeEnv_typeEnvWF {env : TypeEnv} (h : Schema.WfTypeEnv env)
    (hg : WfTypeEnvGaps env) : TypeEnvWF env := by
  match h with
  | .mk names ents acts reqty hes has hreq =>
  obtain ⟨hks, hka, hse, hsa, hdis⟩ := hg
  simp only [Map.toList_mk_id] at hks hka hse hsa hdis
  have hgo : Schema.WfEntitiesGo [] [] names ents := match hes with | .mk _ _ h => h
  have hago : Schema.WfActionsGo names [] Schema.actionEidPool acts :=
    match has with | .mk _ _ h => h
  have hnames : ∀ x ∈ names, ∃ e, MapContains x e (Map.mk ents) := fun x hx =>
    match wfEntitiesGo_allNames_mem hgo x hx with
    | .inl h => absurd h List.not_mem_nil
    | .inr ⟨e, he⟩ => ⟨e, mem_mapContains he⟩
  have hd : ∀ x ∈ names, EntityTypeWF (Map.mk ents) (Map.mk acts) x := fun x hx =>
    have ⟨e, he⟩ := hnames x hx
    .entity _ _ _ e he
  have hawf : (Map.mk acts).WellFormed := map_wf_iff_keysSorted.mpr hka
  have hnd : (acts.map Prod.fst).Nodup := sortedBy_map_nodup (keysSorted_iff_sortedBy.mp hka)
  have hgood := wfActionsGo_entries hago (pre := []) .nil (fun _ hp => absurd hp List.not_mem_nil)
    (by simpa only [List.nil_append] using hnd)
  simp only [List.nil_append] at hgood
  refine .mk _ _ _ (.mk _ _ _ hks (wfEntitiesGo_entityEntriesWF hgo
      (fun _ hp => absurd hp List.not_mem_nil) hnames hse)) (.mk _ _ _ hka ?_ ?_ ?_) ?_
  · refine actionEntriesWF_iff.mpr fun q hq => ⟨hdis q hq, ?_⟩
    obtain ⟨ps, rs, ancs, ctx, heq, hp, hr, ha, _, hanc⟩ := hgood q hq
    obtain ⟨hsp, hsr, hsan⟩ := hsa q hq
    rw [heq] at hsp hsr hsan ⊢
    have hctx := wfAttrs_record hd ha
    exact .mk _ _ _ _ _ _ hsp hsr hsan (wfPrincipalTypes_entityTypesWF hd hp)
      (wfResourceTypes_entityTypesWF hd hr)
      (actionAncestorsWF_iff.mpr fun x hx =>
        have ⟨_, he, _⟩ := hanc x hx
        map_contains_of_mem he)
      hctx.1 hctx.2
  · refine .mk _ (actionsIrreflexive_iff.mpr fun q hq => ?_)
    obtain ⟨ps, rs, ancs, ctx, heq, _, _, _, hni, _⟩ := hgood q hq
    rw [heq]
    exact hni
  · refine .mk _ (actionsTransitive_iff.mpr fun q₁ hq₁ =>
      actionsTransitiveFrom_iff.mpr fun q₂ hq₂ hm => ?_)
    obtain ⟨ps, rs, ancs, ctx, heq, _, _, _, _, hanc⟩ := hgood q₁ hq₁
    rw [heq] at hm ⊢
    obtain ⟨e, he, hs⟩ := hanc q₂.1 hm
    have : e = q₂.2 := Option.some.inj
      ((Map.mem_toList_find? hawf he).symm.trans (Map.mem_toList_find? hawf hq₂))
    subst this
    exact hs
  · obtain ⟨ps, rs, ancs, ctx, hm, hp, hr, hc⟩ := requestFromAction_entry hreq
    obtain ⟨p, a, r, c⟩ := reqty
    simp only at hm hp hr hc
    subst hc
    exact .mk _ _ _ _ _ _ _ _ (mapFind_iff_find?.mpr (Map.mem_toList_find? hawf hm))
      (setContains_iff_mem.mpr hp) (setContains_iff_mem.mpr hr)

/-- A generated environment (`Schema.WfTypeEnv`) is well-formed iff it satisfies
`WfTypeEnvGaps`. Every conjunct of `WfTypeEnvGaps` is checked by `validateWellFormed` and none
is implied by `WfTypeEnv`, so this is the weakest side condition. -/
theorem wfTypeEnv_typeEnvWF_iff {env : TypeEnv} (h : Schema.WfTypeEnv env) :
    TypeEnvWF env ↔ WfTypeEnvGaps env :=
  ⟨typeEnvWF_gaps, wfTypeEnv_typeEnvWF h⟩

/-- A generated environment passes `validateWellFormed` iff it satisfies `WfTypeEnvGaps`. -/
theorem wfTypeEnv_validateWellFormed_iff {env : TypeEnv} (h : Schema.WfTypeEnv env) :
    env.validateWellFormed = .ok () ↔ WfTypeEnvGaps env :=
  typeEnvWF_iff_validateWellFormed.symm.trans (wfTypeEnv_typeEnvWF_iff h)

end Cedar.Validation.Relational

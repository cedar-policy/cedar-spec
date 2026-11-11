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

public import Cedar.Thm.Validation.EnvironmentValidation
public import Cedar.Thm.Validation.Relational.Completeness
public import Cedar.Validation.Relational.WellFormed
import Batteries.Data.List.Lemmas
import all Cedar.Data.Map -- unfolds `contains`, `empty`, `find`, …
import all Cedar.Data.Set -- unfolds `all`, `contains`, `elts`, …
import all Cedar.Spec.Entities -- unfolds `ancestors`, `attrs`, `tags`
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.EnvironmentValidator -- unfolds `validateAcyclicActionHierarchy`, `validateAttrsWellFormed`, `validateLifted`, …
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `QualifiedType`, …
import all Cedar.Validation.Validator -- unfolds `environment`, `environments`

/-! # The relational schema well-formedness check agrees with `validateWellFormed` -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Structural helpers -/

theorem eltsSorted_iff_sorted {α} [LT α] {l : List α} : EltsSorted l ↔ l.Sorted := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | single => exact .cons_nil
    | cons _ _ _ hlt _ ih => exact .cons_cons hlt ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons_nil => exact .single _
    | cons_cons hlt _ ih => exact .cons _ _ _ hlt ih

theorem keysSorted_iff_sortedBy {α β} [LT α] {l : List (α × β)} :
    KeysSorted l ↔ l.SortedBy Prod.fst := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | single => exact .cons_nil
    | cons _ _ _ _ _ hlt _ ih => exact .cons_cons hlt ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons_nil => exact .single _ _
    | cons_cons hlt _ ih => exact .cons _ _ _ _ _ hlt ih

theorem set_wf_iff_eltsSorted {α} [LT α] [DecidableLT α] [StrictLT α] {l : List α} :
    (Set.mk l).WellFormed ↔ EltsSorted l :=
  (Set.wf_iff_sorted _).trans eltsSorted_iff_sorted.symm

theorem set_wellFormed_iff_eltsSorted {α} [LT α] [DecidableLT α] [StrictLT α] {l : List α} :
    (Set.mk l).wellFormed = true ↔ EltsSorted l :=
  Set.wellFormed_correct.trans set_wf_iff_eltsSorted

theorem map_wf_iff_keysSorted {α β} [LT α] [DecidableLT α] [StrictLT α] {l : List (α × β)} :
    (Map.mk l).WellFormed ↔ KeysSorted l :=
  Map.wf_iff_sorted.trans keysSorted_iff_sortedBy.symm

theorem map_wellFormed_iff_keysSorted {α β} [LT α] [DecidableLT α] [StrictLT α]
    {l : List (α × β)} : (Map.mk l).wellFormed = true ↔ KeysSorted l :=
  Map.wellFormed_correct.trans map_wf_iff_keysSorted

theorem setContains_iff_mem {α} {x : α} {s : Set α} : SetContains x s ↔ x ∈ s.elts := by
  refine ⟨fun h => ?_, mem_elts_setContains⟩
  induction h with
  | here => simp [Set.elts]
  | there _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem setNotContains_iff_not_mem {α} {x : α} {s : Set α} :
    SetNotContains x s ↔ x ∉ s.elts := by
  constructor
  · intro h
    induction h with
    | empty => simp [Set.elts]
    | skip _ _ hne _ ih => simp_all [Set.elts]
  · obtain ⟨l⟩ := s
    intro h
    induction l with
    | nil => exact .empty _
    | cons y rest ih =>
      simp only [Set.elts, List.mem_cons, not_or] at h ih
      exact .skip _ _ _ h.1 (ih h.2)

theorem eltsSubset_iff {α} {l : List α} {s : Set α} :
    EltsSubset l s ↔ ∀ x ∈ l, x ∈ s.elts := by
  constructor
  · intro h
    induction h with
    | nil => simp
    | cons _ _ _ hx _ ih =>
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨setContains_iff_mem.mp hx, ih⟩
  · intro h
    induction l with
    | nil => exact .nil _
    | cons x rest ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      exact .cons _ _ _ (setContains_iff_mem.mpr h.1) (ih h.2)

theorem mapFind_iff_find? {α β : Type} [BEq α] [LawfulBEq α] {k : α} {v : β} {m : Map α β} :
    MapFind k v m ↔ m.find? k = some v := by
  obtain ⟨l⟩ := m
  induction l with
  | nil =>
    simp only [Map.find?, Map.toList, List.find?_nil, reduceCtorEq, iff_false]
    intro h
    cases h
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases hk : k' = k
    · subst hk
      simp only [Map.find?, Map.toList, List.find?_cons, beq_self_eq_true, Option.some.injEq]
      constructor
      · intro h
        cases h with
        | here => rfl
        | there _ _ _ hne _ => exact absurd rfl hne
      · rintro rfl
        exact .here _ _ _
    · have hne : (k' == k) = false := beq_eq_false_iff_ne.mpr hk
      have ih' : MapFind k v (Map.mk tl) ↔ (Map.mk tl).find? k = some v := ih
      simp only [Map.find?, Map.toList, List.find?_cons, hne] at ih' ⊢
      rw [← ih']
      constructor
      · intro h
        cases h with
        | here => exact absurd rfl hk
        | there _ _ _ _ h => exact h
      · exact .there _ _ _ _ _ (Ne.symm hk)

theorem map_contains_of_mem {α β : Type} [BEq α] [LawfulBEq α] {m : Map α β} {k : α} {v : β}
    (h : (k, v) ∈ m.toList) : m.contains k = true := by
  have hsome : (m.toList.find? (fun x => x.fst == k)).isSome :=
    List.find?_isSome.mpr ⟨(k, v), h, by simp⟩
  simp only [Map.contains, Map.find?]
  split
  · rfl
  · rename_i hnone
    obtain ⟨⟨k'', v''⟩, hfind⟩ := Option.isSome_iff_exists.mp hsome
    exact absurd hfind (by simpa using hnone k'' v'')

theorem map_contains_iff_mapContains {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    [StrictLT α] {m : Map α β} {k : α} : m.contains k = true ↔ ∃ v, MapContains k v m :=
  ⟨contains_mapContains, fun ⟨_, h⟩ => map_contains_of_mem (mapContains_mem h)⟩

theorem map_find?_isSome_iff_mapContains {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    [StrictLT α] {m : Map α β} {k : α} : (∃ v, m.find? k = some v) ↔ ∃ v, MapContains k v m :=
  Map.contains_iff_some_find?.symm.trans map_contains_iff_mapContains

theorem mapNotContainsKey_iff_find?_none {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
    [StrictLT α] {m : Map α β} {k : α} : MapNotContainsKey k m ↔ m.find? k = none :=
  ⟨mapNotContainsKey_find?, mapNotContainsKey_of_find?_none⟩

theorem forM_ok_iff {α ε : Type} {l : List α} {f : α → Except ε Unit} :
    l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok () :=
  ⟨List.forM_ok_implies_all_ok', List.all_ok_implies_forM_ok _ _⟩

/-! ## Types -/

theorem entityTypeWF_iff_wellFormed {env : TypeEnv} {ety : EntityType} :
    EntityTypeWF env.ets env.acts ety ↔ EntityType.WellFormed env ety := by
  constructor
  · intro h
    cases h with
    | entity entry h => exact .inl (map_contains_of_mem (mapContains_mem h))
    | action eid entry h => exact .inr ⟨_, map_contains_of_mem (mapContains_mem h), rfl⟩
  · rintro (h | ⟨uid, h, rfl⟩)
    · obtain ⟨entry, h⟩ := contains_mapContains h
      exact .entity _ _ _ entry h
    · obtain ⟨entry, h⟩ := contains_mapContains (m := env.acts) h
      exact .action _ _ _ uid.eid entry h

/-- `EntityTypeWF` is `EntityType.validateWellFormed`. -/
theorem entityTypeWF_iff_validateWellFormed {env : TypeEnv} {ety : EntityType} :
    EntityTypeWF env.ets env.acts ety ↔ EntityType.validateWellFormed env ety = .ok () :=
  entityTypeWF_iff_wellFormed.trans
    ⟨Thm.entity_type_validate_well_formed_is_complete,
      Thm.entity_type_validate_well_formed_is_sound⟩

mutual

theorem cedarTypeWF_wellFormed {ets : EntitySchema} {acts : ActionSchema} {reqty : RequestType}
    {ty : CedarType} :
    CedarTypeWF ets acts ty → CedarType.WellFormed { ets, acts, reqty } ty
  | .bool .. => .bool_wf
  | .int .. => .int_wf
  | .string .. => .string_wf
  | .entity _ _ _ h => .entity_wf (entityTypeWF_iff_wellFormed (env := { ets, acts, reqty }).mp h)
  | .set _ _ _ h => .set_wf (cedarTypeWF_wellFormed h)
  | .record _ _ _ hs ha => .record_wf (map_wf_iff_keysSorted.mpr hs)
      (fun _ _ hf => attrsWF_wellFormed ha (Map.find?_mem_toList hf))
  | .ext .. => .ext_wf

theorem qualifiedTypeWF_wellFormed {ets : EntitySchema} {acts : ActionSchema}
    {reqty : RequestType} {qty : QualifiedType} :
    QualifiedTypeWF ets acts qty → QualifiedType.WellFormed { ets, acts, reqty } qty
  | .optional _ _ _ h => .optional_wf (cedarTypeWF_wellFormed h)
  | .required _ _ _ h => .required_wf (cedarTypeWF_wellFormed h)

theorem attrsWF_wellFormed {ets : EntitySchema} {acts : ActionSchema} {reqty : RequestType}
    {l : List (Attr × QualifiedType)} :
    AttrsWF ets acts l → ∀ {a qty}, (a, qty) ∈ l → QualifiedType.WellFormed { ets, acts, reqty } qty
  | .nil .., _, _, h => absurd h List.not_mem_nil
  | .cons _ _ _ _ _ hq hr, _, _, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact qualifiedTypeWF_wellFormed hq
    · exact attrsWF_wellFormed hr h

end

theorem attrsWF_of_forall {ets : EntitySchema} {acts : ActionSchema}
    {l : List (Attr × QualifiedType)} (h : ∀ p ∈ l, QualifiedTypeWF ets acts p.2) :
    AttrsWF ets acts l := by
  induction l with
  | nil => exact .nil _ _
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    exact .cons _ _ _ _ _ h.1 (ih h.2)

mutual

theorem wellFormed_cedarTypeWF {env : TypeEnv} {ty : CedarType} :
    CedarType.WellFormed env ty → CedarTypeWF env.ets env.acts ty
  | .bool_wf => .bool _ _ _
  | .int_wf => .int _ _
  | .string_wf => .string _ _
  | .entity_wf h => .entity _ _ _ (entityTypeWF_iff_wellFormed.mpr h)
  | .set_wf h => .set _ _ _ (wellFormed_cedarTypeWF h)
  | .record_wf (rty := ⟨rts⟩) h₁ h₂ => .record _ _ rts (map_wf_iff_keysSorted.mp h₁)
      (attrsWF_of_forall fun p hp =>
        wellFormed_qualifiedTypeWF (h₂ p.1 p.2 (Map.mem_toList_find? h₁ hp)))
  | .ext_wf => .ext _ _ _

theorem wellFormed_qualifiedTypeWF {env : TypeEnv} {qty : QualifiedType} :
    QualifiedType.WellFormed env qty → QualifiedTypeWF env.ets env.acts qty
  | .optional_wf h => .optional _ _ _ (wellFormed_cedarTypeWF h)
  | .required_wf h => .required _ _ _ (wellFormed_cedarTypeWF h)

end

theorem cedarTypeWF_iff_wellFormed {env : TypeEnv} {ty : CedarType} :
    CedarTypeWF env.ets env.acts ty ↔ CedarType.WellFormed env ty :=
  ⟨cedarTypeWF_wellFormed, wellFormed_cedarTypeWF⟩

/-- `CedarTypeWF` is `CedarType.validateWellFormed`. -/
theorem cedarTypeWF_iff_validateWellFormed {env : TypeEnv} {ty : CedarType} :
    CedarTypeWF env.ets env.acts ty ↔ ty.validateWellFormed env = .ok () :=
  cedarTypeWF_iff_wellFormed.trans
    ⟨Thm.type_validate_well_formed_is_complete, Thm.type_validate_well_formed_is_sound⟩

/-- `QualifiedTypeWF` is `QualifiedType.validateWellFormed`. -/
theorem qualifiedTypeWF_iff_validateWellFormed {env : TypeEnv} {qty : QualifiedType} :
    QualifiedTypeWF env.ets env.acts qty ↔ qty.validateWellFormed env = .ok () := by
  cases qty with
  | optional ty =>
    simp only [QualifiedType.validateWellFormed, ← cedarTypeWF_iff_validateWellFormed]
    exact ⟨fun | .optional _ _ _ h => h, .optional _ _ _⟩
  | required ty =>
    simp only [QualifiedType.validateWellFormed, ← cedarTypeWF_iff_validateWellFormed]
    exact ⟨fun | .required _ _ _ h => h, .required _ _ _⟩

/-- `AttrsWF` is `validateAttrsWellFormed`. -/
theorem attrsWF_iff_validateAttrsWellFormed {env : TypeEnv} {l : List (Attr × QualifiedType)} :
    AttrsWF env.ets env.acts l ↔ validateAttrsWellFormed env l = .ok () := by
  induction l with
  | nil => simp only [validateAttrsWellFormed, iff_true]; exact .nil _ _
  | cons hd tl ih =>
    obtain ⟨a, qty⟩ := hd
    rw [validateAttrsWellFormed]
    cases hq : qty.validateWellFormed env with
    | error e =>
      simp only [Except.bind_err, reduceCtorEq, iff_false]
      intro h
      cases h
      rename_i h _
      exact absurd (qualifiedTypeWF_iff_validateWellFormed.mp h) (by simp [hq])
    | ok u =>
      simp only [Except.bind_ok, ← ih]
      refine ⟨fun | .cons _ _ _ _ _ _ h => h, fun h => .cons _ _ _ _ _ ?_ h⟩
      exact qualifiedTypeWF_iff_validateWellFormed.mpr hq

/-! ## Lifted types -/

mutual

theorem cedarTypeLifted_isLifted {ty : CedarType} : CedarTypeLifted ty → CedarType.IsLifted ty
  | .bool => .bool_lifted
  | .int => .int_lifted
  | .string => .string_lifted
  | .entity _ => .entity_lifted
  | .set _ h => .set_lifted (cedarTypeLifted_isLifted h)
  | .record _ h => .record_lifted (fun _ _ hm => attrsLifted_isLifted h hm)
  | .ext _ => .ext_lifted

theorem qualifiedTypeLifted_isLifted {qty : QualifiedType} :
    QualifiedTypeLifted qty → QualifiedType.IsLifted qty
  | .optional _ h => .optional_lifted (cedarTypeLifted_isLifted h)
  | .required _ h => .required_lifted (cedarTypeLifted_isLifted h)

theorem attrsLifted_isLifted {l : List (Attr × QualifiedType)} :
    AttrsLifted l → ∀ {a qty}, (a, qty) ∈ l → QualifiedType.IsLifted qty
  | .nil, _, _, h => absurd h List.not_mem_nil
  | .cons _ _ _ hq hr, _, _, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact qualifiedTypeLifted_isLifted hq
    · exact attrsLifted_isLifted hr h

end

theorem attrsLifted_of_forall {l : List (Attr × QualifiedType)}
    (h : ∀ p ∈ l, QualifiedTypeLifted p.2) : AttrsLifted l := by
  induction l with
  | nil => exact .nil
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    exact .cons _ _ _ h.1 (ih h.2)

mutual

theorem isLifted_cedarTypeLifted {ty : CedarType} : CedarType.IsLifted ty → CedarTypeLifted ty
  | .bool_lifted => .bool
  | .int_lifted => .int
  | .string_lifted => .string
  | .entity_lifted => .entity _
  | .set_lifted h => .set _ (isLifted_cedarTypeLifted h)
  | .record_lifted (rty := ⟨rts⟩) h => .record rts
      (attrsLifted_of_forall fun p hp => isLifted_qualifiedTypeLifted (h p.1 p.2 hp))
  | .ext_lifted => .ext _

theorem isLifted_qualifiedTypeLifted {qty : QualifiedType} :
    QualifiedType.IsLifted qty → QualifiedTypeLifted qty
  | .optional_lifted h => .optional _ (isLifted_cedarTypeLifted h)
  | .required_lifted h => .required _ (isLifted_cedarTypeLifted h)

end

theorem cedarTypeLifted_iff_isLifted {ty : CedarType} : CedarTypeLifted ty ↔ ty.IsLifted :=
  ⟨cedarTypeLifted_isLifted, isLifted_cedarTypeLifted⟩

/-- `CedarTypeLifted` is `CedarType.validateLifted`. -/
theorem cedarTypeLifted_iff_validateLifted {ty : CedarType} :
    CedarTypeLifted ty ↔ ty.validateLifted = .ok () :=
  cedarTypeLifted_iff_isLifted.trans
    ⟨Thm.type_validate_lifted_is_complete, Thm.type_validate_lifted_is_sound⟩

/-! ## Entity schema -/

theorem set_contains_iff_mem_elts {α} [DecidableEq α] {s : Set α} {x : α} :
    s.contains x = true ↔ x ∈ s.elts :=
  Set.contains_prop_bool_equiv.trans (Set.mem_elts_iff_mem_set _ _).symm

theorem tagsWF_iff {env : TypeEnv} {tags : Option CedarType} :
    TagsWF env.ets env.acts tags ↔
      ∀ ty, tags = .some ty → CedarType.WellFormed env ty ∧ ty.IsLifted := by
  cases tags with
  | none => simp only [reduceCtorEq, false_implies, implies_true, iff_true]; exact .none _ _
  | some ty =>
    simp only [Option.some.injEq, forall_eq', ← cedarTypeWF_iff_wellFormed,
      ← cedarTypeLifted_iff_isLifted]
    exact ⟨fun | .some _ _ _ h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .some _ _ _ h₁ h₂⟩

theorem entityAncestorsWF_iff {ets : EntitySchema} {l : List EntityType} :
    EntityAncestorsWF ets l ↔ ∀ x ∈ l, ∃ entry, ets.find? x = some entry := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _
  | cons x rest ih =>
    constructor
    · intro h
      cases h
      rename_i hc hr
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact map_find?_isSome_iff_mapContains.mpr ⟨_, hc⟩
      · exact ih.mp hr y hy
    · intro h
      obtain ⟨_, hc⟩ := map_find?_isSome_iff_mapContains.mp (h x List.mem_cons_self)
      exact .cons _ _ _ _ hc (ih.mpr fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem standardEntryWF_iff_wellFormed {env : TypeEnv} {entry : StandardSchemaEntry} :
    StandardEntryWF env.ets env.acts entry ↔ StandardSchemaEntry.WellFormed env entry := by
  obtain ⟨⟨ancs⟩, attrs, tags⟩ := entry
  constructor
  · intro h
    cases h
    rename_i hs ha hwf hl ht
    exact ⟨set_wf_iff_eltsSorted.mpr hs,
      fun anc hm => entityAncestorsWF_iff.mp ha anc ((Set.mem_elts_iff_mem_set _ _).mpr hm),
      cedarTypeWF_iff_wellFormed.mp hwf, cedarTypeLifted_isLifted hl, tagsWF_iff.mp ht⟩
  · rintro ⟨hs, ha, hwf, hl, ht⟩
    exact .mk _ _ _ _ _ (set_wf_iff_eltsSorted.mp hs)
      (entityAncestorsWF_iff.mpr fun x hx => ha x ((Set.mem_elts_iff_mem_set _ _).mp hx))
      (cedarTypeWF_iff_wellFormed.mpr hwf) (isLifted_cedarTypeLifted hl) (tagsWF_iff.mpr ht)

/-- `StandardEntryWF` is `StandardSchemaEntry.validateWellFormed`. -/
theorem standardEntryWF_iff_validateWellFormed {env : TypeEnv} {entry : StandardSchemaEntry} :
    StandardEntryWF env.ets env.acts entry ↔ entry.validateWellFormed env = .ok () :=
  standardEntryWF_iff_wellFormed.trans
    ⟨Thm.standard_schema_entry_validate_well_formed_is_complete,
      Thm.standard_schema_entry_validate_well_formed_is_sound⟩

theorem entityEntryWF_iff_wellFormed {env : TypeEnv} {entry : EntitySchemaEntry} :
    EntityEntryWF env.ets env.acts entry ↔ EntitySchemaEntry.WellFormed env entry := by
  cases entry with
  | standard entry =>
    simp only [EntitySchemaEntry.WellFormed, ← standardEntryWF_iff_wellFormed]
    exact ⟨fun | .standard _ _ _ h => h, .standard _ _ _⟩
  | enum es =>
    obtain ⟨l⟩ := es
    cases l with
    | nil =>
      simp only [EntitySchemaEntry.WellFormed, Set.isEmpty, Set.empty, beq_self_eq_true,
        not_true_eq_false, and_false, iff_false]
      intro h
      cases h
    | cons eid eids =>
      simp only [EntitySchemaEntry.WellFormed, set_wf_iff_eltsSorted]
      exact ⟨fun | .enum _ _ _ _ h => ⟨h, by simp [Set.isEmpty, Set.empty]⟩,
        fun ⟨h, _⟩ => .enum _ _ _ _ h⟩

/-- `EntityEntryWF` is `EntitySchemaEntry.validateWellFormed`. -/
theorem entityEntryWF_iff_validateWellFormed {env : TypeEnv} {entry : EntitySchemaEntry} :
    EntityEntryWF env.ets env.acts entry ↔ entry.validateWellFormed env = .ok () :=
  entityEntryWF_iff_wellFormed.trans
    ⟨Thm.entity_schema_entry_validate_well_formed_is_complete,
      Thm.entity_schema_entry_validate_well_formed_is_sound⟩

theorem entityEntriesWF_iff {ets : EntitySchema} {acts : ActionSchema}
    {l : List (EntityType × EntitySchemaEntry)} :
    EntityEntriesWF ets acts l ↔ ∀ p ∈ l, EntityEntryWF ets acts p.2 := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _ _
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp, ← ih]
    exact ⟨fun | .cons _ _ _ _ _ h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .cons _ _ _ _ _ h₁ h₂⟩

theorem entitySchemaWF_iff_wellFormed {env : TypeEnv} {ets : EntitySchema} :
    EntitySchemaWF env.ets env.acts ets ↔ EntitySchema.WellFormed env ets := by
  obtain ⟨l⟩ := ets
  constructor
  · intro h
    cases h
    rename_i hs he
    exact ⟨map_wf_iff_keysSorted.mpr hs, fun ety entry hf => entityEntryWF_iff_wellFormed.mp
      (entityEntriesWF_iff.mp he (ety, entry) (Map.find?_mem_toList hf))⟩
  · rintro ⟨hwf, he⟩
    exact .mk _ _ _ (map_wf_iff_keysSorted.mp hwf) (entityEntriesWF_iff.mpr fun p hp =>
      entityEntryWF_iff_wellFormed.mpr (he p.1 p.2 (Map.mem_toList_find? hwf hp)))

/-- `EntitySchemaWF` is `EntitySchema.validateWellFormed`. -/
theorem entitySchemaWF_iff_validateWellFormed {env : TypeEnv} {ets : EntitySchema} :
    EntitySchemaWF env.ets env.acts ets ↔ ets.validateWellFormed env = .ok () :=
  entitySchemaWF_iff_wellFormed.trans
    ⟨Thm.entity_schema_validate_well_formed_is_complete,
      Thm.entity_schema_validate_well_formed_is_sound⟩

/-! ## Action schema -/

theorem entityTypesWF_iff {ets : EntitySchema} {acts : ActionSchema} {l : List EntityType} :
    EntityTypesWF ets acts l ↔ ∀ x ∈ l, EntityTypeWF ets acts x := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _ _
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp, ← ih]
    exact ⟨fun | .cons _ _ _ _ h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .cons _ _ _ _ h₁ h₂⟩

theorem actionAncestorsWF_iff {acts : ActionSchema} {l : List EntityUID} :
    ActionAncestorsWF acts l ↔ ∀ x ∈ l, acts.contains x = true := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _
  | cons x rest ih =>
    constructor
    · intro h
      cases h
      rename_i hc hr
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact map_contains_iff_mapContains.mpr ⟨_, hc⟩
      · exact ih.mp hr y hy
    · intro h
      obtain ⟨_, hc⟩ := map_contains_iff_mapContains.mp (h x List.mem_cons_self)
      exact .cons _ _ _ _ hc (ih.mpr fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem actionEntryWF_iff_wellFormed {env : TypeEnv} {entry : ActionSchemaEntry} :
    ActionEntryWF env.ets env.acts entry ↔ ActionSchemaEntry.WellFormed env entry := by
  obtain ⟨⟨ps⟩, ⟨rs⟩, ⟨ancs⟩, ctx⟩ := entry
  constructor
  · intro h
    match h with
    | .mk _ _ _ _ _ _ hps hrs has hp hr ha hc hl =>
    exact ⟨set_wf_iff_eltsSorted.mpr hps, set_wf_iff_eltsSorted.mpr hrs,
      set_wf_iff_eltsSorted.mpr has,
      fun ety h => entityTypeWF_iff_wellFormed.mp
        (entityTypesWF_iff.mp hp ety (set_contains_iff_mem_elts.mp h)),
      fun ety h => entityTypeWF_iff_wellFormed.mp
        (entityTypesWF_iff.mp hr ety (set_contains_iff_mem_elts.mp h)),
      fun uid hu => actionAncestorsWF_iff.mp ha uid ((Set.mem_elts_iff_mem_set _ _).mpr hu),
      cedarTypeWF_iff_wellFormed.mp hc, cedarTypeLifted_isLifted hl⟩
  · rintro ⟨hps, hrs, has, hp, hr, ha, hc, hl⟩
    exact .mk _ _ _ _ _ _ (set_wf_iff_eltsSorted.mp hps) (set_wf_iff_eltsSorted.mp hrs)
      (set_wf_iff_eltsSorted.mp has)
      (entityTypesWF_iff.mpr fun x hx =>
        entityTypeWF_iff_wellFormed.mpr (hp x (set_contains_iff_mem_elts.mpr hx)))
      (entityTypesWF_iff.mpr fun x hx =>
        entityTypeWF_iff_wellFormed.mpr (hr x (set_contains_iff_mem_elts.mpr hx)))
      (actionAncestorsWF_iff.mpr fun x hx => ha x ((Set.mem_elts_iff_mem_set _ _).mp hx))
      (cedarTypeWF_iff_wellFormed.mpr hc) (isLifted_cedarTypeLifted hl)

/-- `ActionEntryWF` is `ActionSchemaEntry.validateWellFormed`. -/
theorem actionEntryWF_iff_validateWellFormed {env : TypeEnv} {entry : ActionSchemaEntry} :
    ActionEntryWF env.ets env.acts entry ↔ entry.validateWellFormed env = .ok () :=
  actionEntryWF_iff_wellFormed.trans
    ⟨Thm.action_schema_entry_validate_well_formed_is_complete,
      Thm.action_schema_entry_validate_well_formed_is_sound⟩

theorem actionsIrreflexive_iff {l : List (EntityUID × ActionSchemaEntry)} :
    ActionsIrreflexive l ↔ ∀ p ∈ l, p.1 ∉ p.2.ancestors.elts := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil
  | cons hd tl ih =>
    obtain ⟨uid, ⟨ps, rs, ancs, ctx⟩⟩ := hd
    rw [List.forall_mem_cons, ← ih]
    simp only [← setNotContains_iff_not_mem]
    exact ⟨fun | .cons _ _ _ _ _ _ h₁ h₂ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => .cons _ _ _ _ _ _ h₁ h₂⟩

/-- `ActionHierarchyAcyclic` is `ActionSchema.validateAcyclicActionHierarchy`. -/
theorem actionHierarchyAcyclic_iff_validate {acts : ActionSchema} :
    ActionHierarchyAcyclic acts ↔ acts.validateAcyclicActionHierarchy = .ok () := by
  obtain ⟨l⟩ := acts
  simp only [ActionSchema.validateAcyclicActionHierarchy, forM_ok_iff, Map.toList]
  have hacyc : ActionHierarchyAcyclic (Map.mk l) ↔ ActionsIrreflexive l :=
    ⟨fun | .mk _ h => h, .mk _⟩
  rw [hacyc, actionsIrreflexive_iff]
  refine forall_congr' fun ⟨uid, entry⟩ => imp_congr_right fun _ => ?_
  simp only [ite_eq_right_iff, reduceCtorEq, imp_false, set_contains_iff_mem_elts]

theorem actionsTransitiveFrom_iff {ancs₁ : Set EntityUID} {l : List (EntityUID × ActionSchemaEntry)} :
    ActionsTransitiveFrom ancs₁ l ↔
      ∀ p ∈ l, p.1 ∈ ancs₁.elts → ∀ x ∈ p.2.ancestors.elts, x ∈ ancs₁.elts := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _
  | cons hd tl ih =>
    obtain ⟨uid₂, ⟨ps, rs, ⟨ancs₂⟩, ctx⟩⟩ := hd
    simp only [List.mem_cons, forall_eq_or_imp, ← ih]
    constructor
    · intro h
      cases h
      next hn hr => exact ⟨fun hm => absurd hm (setNotContains_iff_not_mem.mp hn), hr⟩
      next hs hr => exact ⟨fun _ => eltsSubset_iff.mp hs, hr⟩
    · rintro ⟨h₁, h₂⟩
      by_cases hm : uid₂ ∈ ancs₁.elts
      · exact .ancestor _ _ _ _ _ _ _ (setContains_iff_mem.mpr hm) (eltsSubset_iff.mpr (h₁ hm)) h₂
      · exact .notAncestor _ _ _ _ (setNotContains_iff_not_mem.mpr hm) h₂

theorem actionsTransitive_iff {all l : List (EntityUID × ActionSchemaEntry)} :
    ActionsTransitive all l ↔ ∀ p ∈ l, ActionsTransitiveFrom p.2.ancestors all := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _
  | cons hd tl ih =>
    obtain ⟨uid, ⟨ps, rs, ancs, ctx⟩⟩ := hd
    simp only [List.mem_cons, forall_eq_or_imp, ← ih]
    exact ⟨fun | .cons _ _ _ _ _ _ _ h₁ h₂ => ⟨h₁, h₂⟩,
      fun ⟨h₁, h₂⟩ => .cons _ _ _ _ _ _ _ h₁ h₂⟩

/-- `ActionHierarchyTransitive` is `ActionSchema.validateTransitiveActionHierarchy`. -/
theorem actionHierarchyTransitive_iff_validate {acts : ActionSchema} :
    ActionHierarchyTransitive acts ↔ acts.validateTransitiveActionHierarchy = .ok () := by
  obtain ⟨l⟩ := acts
  simp only [ActionSchema.validateTransitiveActionHierarchy, forM_ok_iff, Map.toList]
  have htrans : ActionHierarchyTransitive (Map.mk l) ↔ ActionsTransitive l l :=
    ⟨fun | .mk _ h => h, .mk _⟩
  rw [htrans, actionsTransitive_iff]
  refine forall_congr' fun ⟨uid₁, entry₁⟩ => imp_congr_right fun _ => ?_
  rw [actionsTransitiveFrom_iff]
  refine forall_congr' fun ⟨uid₂, entry₂⟩ => imp_congr_right fun _ => ?_
  simp only [Set.subset, List.all_eq_true, set_contains_iff_mem_elts]
  split <;> (try split) <;> simp_all

theorem actionEntriesWF_iff {ets : EntitySchema} {acts : ActionSchema}
    {l : List (EntityUID × ActionSchemaEntry)} :
    ActionEntriesWF ets acts l ↔ ∀ p ∈ l, ets.find? p.1.ty = none ∧ ActionEntryWF ets acts p.2 := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, iff_true]; exact .nil _ _
  | cons hd tl ih =>
    obtain ⟨⟨ety, eid⟩, entry⟩ := hd
    rw [List.forall_mem_cons, ← ih]
    simp only [← mapNotContainsKey_iff_find?_none]
    exact ⟨fun | .cons _ _ _ _ _ _ h₁ h₂ h₃ => ⟨⟨h₁, h₂⟩, h₃⟩,
      fun ⟨⟨h₁, h₂⟩, h₃⟩ => .cons _ _ _ _ _ _ h₁ h₂ h₃⟩

theorem actionSchemaWF_iff_wellFormed {env : TypeEnv} {acts : ActionSchema} :
    ActionSchemaWF env.ets env.acts acts ↔ ActionSchema.WellFormed env acts := by
  obtain ⟨l⟩ := acts
  constructor
  · intro h
    cases h
    rename_i hs he hac htr
    have hwf := map_wf_iff_keysSorted.mpr hs
    refine ⟨hwf, fun uid entry hf => ?_, fun uid hc => ?_,
      Thm.action_schema_validate_acyclic_action_hierarchy_is_sound
        (actionHierarchyAcyclic_iff_validate.mp hac),
      Thm.action_schema_validate_transitive_action_hierarchy_is_sound
        (actionHierarchyTransitive_iff_validate.mp htr)⟩
    · exact actionEntryWF_iff_wellFormed.mp
        (actionEntriesWF_iff.mp he (uid, entry) (Map.find?_mem_toList hf)).2
    · obtain ⟨entry, hf⟩ := Map.contains_iff_some_find?.mp hc
      have hnone : env.ets.find? uid.ty = none :=
        (actionEntriesWF_iff.mp he (uid, entry) (Map.find?_mem_toList hf)).1
      simp [EntitySchema.contains, hnone]
  · rintro ⟨hwf, hent, hdis, hac, htr⟩
    refine .mk _ _ _ (map_wf_iff_keysSorted.mp hwf) (actionEntriesWF_iff.mpr fun p hp => ?_)
      (actionHierarchyAcyclic_iff_validate.mpr
        (Thm.action_schema_validate_acyclic_action_hierarchy_is_complete hwf hac))
      (actionHierarchyTransitive_iff_validate.mpr
        (Thm.action_schema_validate_transitive_action_hierarchy_is_complete hwf htr))
    have hf := Map.mem_toList_find? hwf hp
    have hnc := hdis p.1 (Map.contains_iff_some_find?.mpr ⟨_, hf⟩)
    refine ⟨?_, actionEntryWF_iff_wellFormed.mpr (hent p.1 p.2 hf)⟩
    cases hfe : env.ets.find? p.1.ty with
    | none => rfl
    | some _ => simp [EntitySchema.contains, hfe] at hnc

/-- `ActionSchemaWF` is `ActionSchema.validateWellFormed`. -/
theorem actionSchemaWF_iff_validateWellFormed {env : TypeEnv} {acts : ActionSchema} :
    ActionSchemaWF env.ets env.acts acts ↔ acts.validateWellFormed env = .ok () :=
  actionSchemaWF_iff_wellFormed.trans
    ⟨Thm.action_schema_validate_well_formed_is_complete,
      Thm.action_schema_validate_well_formed_is_sound⟩

/-! ## Request type, type environment and schema -/

theorem requestTypeWF_iff_wellFormed {env : TypeEnv} {reqty : RequestType} :
    RequestTypeWF env.acts reqty ↔ RequestType.WellFormed env reqty := by
  obtain ⟨p, a, r, ctx⟩ := reqty
  constructor
  · intro h
    match h with
    | .mk _ _ _ _ _ _ _ _ hf hp hr =>
    exact ⟨_, mapFind_iff_find?.mp hf,
      (Set.mem_elts_iff_mem_set _ _).mp (setContains_iff_mem.mp hp),
      (Set.mem_elts_iff_mem_set _ _).mp (setContains_iff_mem.mp hr), rfl⟩
  · rintro ⟨⟨ps, rs, ancs, ctx'⟩, hf, hp, hr, hc⟩
    obtain rfl : ctx = ctx' := hc
    exact .mk _ _ _ _ _ _ _ _ (mapFind_iff_find?.mpr hf)
      (setContains_iff_mem.mpr ((Set.mem_elts_iff_mem_set _ _).mpr hp))
      (setContains_iff_mem.mpr ((Set.mem_elts_iff_mem_set _ _).mpr hr))

/-- `RequestTypeWF` is `RequestType.validateWellFormed`. -/
theorem requestTypeWF_iff_validateWellFormed {env : TypeEnv} {reqty : RequestType} :
    RequestTypeWF env.acts reqty ↔ reqty.validateWellFormed env = .ok () :=
  requestTypeWF_iff_wellFormed.trans
    ⟨Thm.request_type_validate_well_formed_is_complete,
      Thm.request_type_validate_well_formed_is_sound⟩

/-- The relational check `TypeEnvWF` is Cedar's well-formedness proposition `TypeEnv.WellFormed`. -/
theorem typeEnvWF_iff_wellFormed {env : TypeEnv} : TypeEnvWF env ↔ TypeEnv.WellFormed env := by
  obtain ⟨ets, acts, reqty⟩ := env
  constructor
  · intro h
    cases h
    rename_i he ha hr
    exact ⟨entitySchemaWF_iff_wellFormed.mp he, actionSchemaWF_iff_wellFormed.mp ha,
      requestTypeWF_iff_wellFormed.mp hr⟩
  · rintro ⟨he, ha, hr⟩
    exact .mk _ _ _ (entitySchemaWF_iff_wellFormed.mpr he) (actionSchemaWF_iff_wellFormed.mpr ha)
      (requestTypeWF_iff_wellFormed.mpr hr)

/-- The relational check `TypeEnvWF` is exactly `TypeEnv.validateWellFormed`. -/
theorem typeEnvWF_iff_validateWellFormed {env : TypeEnv} :
    TypeEnvWF env ↔ env.validateWellFormed = .ok () :=
  typeEnvWF_iff_wellFormed.trans
    ⟨Thm.env_validate_well_formed_is_complete, Thm.env_validate_well_formed_is_sound⟩

/-- `SchemaEnvironment` is membership in `Schema.environments`. -/
theorem schemaEnvironment_iff_mem {schema : Schema} {env : TypeEnv} :
    SchemaEnvironment schema env ↔ env ∈ schema.environments := by
  constructor
  · intro h
    match h with
    | .mk ets acts action ps rs ancs ctx p r hm hp hr =>
    simp only [Schema.environments, List.mem_map, List.mem_flatMap, TypeEnv.mk.injEq, true_and,
      exists_eq_right]
    refine ⟨(action, ⟨ps, rs, ancs, ctx⟩), mapContains_mem hm, ?_⟩
    show _ ∈ (ps.toList.product rs.toList).map _
    simp only [List.mem_map, Prod.exists, List.pair_mem_product]
    exact ⟨p, r, ⟨setContains_iff_mem.mp hp, setContains_iff_mem.mp hr⟩, rfl⟩
  · intro h
    obtain ⟨hets, hacts, ⟨ps, rs, ancs, ctx⟩, hm, hp, hr, hc⟩ := Thm.mem_environments h
    obtain ⟨ets, acts, ⟨p, a, r, ctx'⟩⟩ := env
    obtain ⟨sets, sacts⟩ := schema
    simp only at hets hacts hm hp hr hc
    subst hets hacts hc
    exact .mk _ _ _ _ _ _ _ _ _ (mem_toList_mapContains hm)
      (setContains_iff_mem.mpr ((Set.mem_elts_iff_mem_set _ _).mpr hp))
      (setContains_iff_mem.mpr ((Set.mem_elts_iff_mem_set _ _).mpr hr))

/-- The relational check `SchemaWF` is exactly `Schema.validateWellFormed`. -/
theorem schemaWF_iff_validateWellFormed {schema : Schema} :
    SchemaWF schema ↔ schema.validateWellFormed = .ok () := by
  simp only [SchemaWF, Schema.validateWellFormed, forM_ok_iff, schemaEnvironment_iff_mem,
    typeEnvWF_iff_validateWellFormed]

end Cedar.Validation.Relational

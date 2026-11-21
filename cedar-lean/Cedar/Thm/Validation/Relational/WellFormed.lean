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

public import Cedar.Thm.Validation.Relational.Completeness
public import Cedar.Thm.Validation.Typechecker.WF
import Batteries.Data.List.Lemmas
import all Cedar.Data.Map -- unfolds `empty`, `find`, `toList`
import all Cedar.Data.Set -- unfolds `empty`, `map`, `toList`
import all Cedar.Spec.Entities -- unfolds `attrs`, `tags`
import all Cedar.Spec.Value -- unfolds `EntityType`
import all Cedar.Validation.Types -- unfolds `EntitySchema`, `QualifiedType`, `RecordType`, …
import all Cedar.Validation.Validator -- unfolds `environment`, `environments`

/-! # Cedar's well-formed type environments satisfy `EnvAssumptions`

`TypeEnv.WellFormed` gives every property in `EnvAssumptions`. -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

theorem map_wf_keys_nodup {α β} [LT α] [DecidableLT α] [StrictLT α] {m : Map α β}
    (h : m.WellFormed) : (m.toList.map Prod.fst).Nodup :=
  sortedBy_map_nodup (Map.wf_iff_sorted.mp h)

theorem entityType_wf_validEntityType {env : TypeEnv} {ety : EntityType}
    (h : EntityType.WellFormed env ety) : ValidEntityType ety env.ets env.acts := by
  rcases h with hc | ⟨uid, hc, rfl⟩
  · obtain ⟨entry, hf⟩ := Map.contains_iff_some_find?.mp hc
    exact ValidEntityType.inSchema _ _ _ _ (find?_mapContains hf)
  · obtain ⟨entry, hf⟩ := Map.contains_iff_some_find?.mp hc
    obtain ⟨e, he⟩ := mapContainsPairKey_of_mapContains (find?_mapContains hf)
    exact ValidEntityType.isAction _ _ _ _ _ he

mutual
theorem cedarType_wf_tyWf {env : TypeEnv} {ty : CedarType} :
    CedarType.WellFormed env ty → TyWf ty
  | .bool_wf => .bool _
  | .int_wf => .int
  | .string_wf => .string
  | .entity_wf _ => .entity _
  | .set_wf h => .set _ (cedarType_wf_tyWf h)
  | .record_wf h₁ h₂ => .record _ (map_wf_keys_nodup h₁) (fun q hq => by
      obtain ⟨⟨a, q'⟩, hmem, rfl⟩ := List.mem_map.mp hq
      exact qualifiedType_wf_tyWfQ (h₂ a q' (Map.mem_toList_find? h₁ hmem)))
  | .ext_wf => .ext _
theorem qualifiedType_wf_tyWfQ {env : TypeEnv} {qty : QualifiedType} :
    QualifiedType.WellFormed env qty → TyWfQ qty
  | .optional_wf h => .optional _ (cedarType_wf_tyWf h)
  | .required_wf h => .required _ (cedarType_wf_tyWf h)
end

mutual
theorem cedarType_wf_typeValid {env : TypeEnv} {ty : CedarType} :
    CedarType.WellFormed env ty → TypeValid env ty
  | .bool_wf => .bool _
  | .int_wf => .int
  | .string_wf => .string
  | .entity_wf h => .entity _ (entityType_wf_validEntityType h)
  | .set_wf h => .set _ (cedarType_wf_typeValid h)
  | .record_wf (rty := ⟨rts⟩) h₁ h₂ => .record rts (fun p hp =>
      qualifiedType_wf_typeValid (h₂ p.1 p.2 (Map.mem_toList_find? h₁ hp)))
  | .ext_wf => .ext _
theorem qualifiedType_wf_typeValid {env : TypeEnv} {qty : QualifiedType} :
    QualifiedType.WellFormed env qty → TypeValid env qty.getType
  | .optional_wf h => cedarType_wf_typeValid h
  | .required_wf h => cedarType_wf_typeValid h
end

/-- The empty record type satisfies both record invariants. -/
private theorem empty_record_tyWf : TyWf (.record (Map.empty : RecordType)) :=
  .record _ (by simp [Map.empty, Map.toList]) (by simp [Map.empty, Map.toList])

private theorem empty_record_typeValid {env : TypeEnv} :
    TypeValid env (.record (Map.empty : RecordType)) :=
  .record [] (by simp)

/-- An entity entry in a well-formed environment: its attribute and tag types are well formed. -/
private theorem entry_attrs_tags_wf {env : TypeEnv} (hwf : TypeEnv.WellFormed env)
    {ety : EntityType} {entry : EntitySchemaEntry} (hf : env.ets.find? ety = some entry) :
    (CedarType.record entry.attrs).WellFormed env ∨ entry.attrs = Map.empty := by
  have hentry := hwf.1.2 ety entry hf
  cases entry with
  | standard se =>
    simp only [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry
    exact .inl hentry.2.2.1
  | enum es => exact .inr rfl

private theorem entry_tags_wf {env : TypeEnv} (hwf : TypeEnv.WellFormed env)
    {ety : EntityType} {entry : EntitySchemaEntry} {ty : CedarType}
    (hf : env.ets.find? ety = some entry) (ht : entry.tags? = some ty) :
    CedarType.WellFormed env ty := by
  have hentry := hwf.1.2 ety entry hf
  cases entry with
  | standard se =>
    simp only [EntitySchemaEntry.WellFormed, StandardSchemaEntry.WellFormed] at hentry
    exact (hentry.2.2.2.2 ty ht).1
  | enum es => simp [EntitySchemaEntry.tags?] at ht

/-- The request's action entry in a well-formed environment, and what it gives. -/
private theorem reqty_entry {env : TypeEnv} (hwf : TypeEnv.WellFormed env) :
    ∃ entry, env.acts.find? env.reqty.action = some entry ∧
      EntityType.WellFormed env env.reqty.principal ∧
      EntityType.WellFormed env env.reqty.resource ∧
      (CedarType.record env.reqty.context).WellFormed env := by
  obtain ⟨entry, hf, hp, hr, hc⟩ := hwf.2.2
  have hentry := hwf.2.1.2.1 _ entry hf
  simp only [ActionSchemaEntry.WellFormed] at hentry
  refine ⟨entry, hf, hentry.2.2.2.1 _ ?_, hentry.2.2.2.2.1 _ ?_, hc ▸ hentry.2.2.2.2.2.2.1⟩
  · exact Set.contains_prop_bool_equiv.mpr hp
  · exact Set.contains_prop_bool_equiv.mpr hr

/-- Cedar's well-formed type environments satisfy `EnvAssumptions`. -/
theorem TypeEnv.WellFormed.envAssumptions {env : TypeEnv} (hwf : TypeEnv.WellFormed env) :
    EnvAssumptions env where
  ets_keys_nodup := map_wf_keys_nodup hwf.1.1
  acts_keys_nodup := map_wf_keys_nodup hwf.2.1.1
  attrs_tyWf := by
    intro ety rty h
    simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h
    obtain ⟨entry, hf, rfl⟩ := h
    rcases entry_attrs_tags_wf hwf hf with hw | he
    · exact cedarType_wf_tyWf hw
    · rw [he]; exact empty_record_tyWf
  tags_tyWf := by
    intro ety ty h
    simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h
    obtain ⟨entry, hf, ht⟩ := h
    exact cedarType_wf_tyWf (entry_tags_wf hwf hf ht)
  context_tyWf := by
    obtain ⟨_, _, _, _, hc⟩ := reqty_entry hwf
    exact cedarType_wf_tyWf hc
  attrs_typeValid := by
    intro ety rty h
    simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h
    obtain ⟨entry, hf, rfl⟩ := h
    rcases entry_attrs_tags_wf hwf hf with hw | he
    · exact cedarType_wf_typeValid hw
    · rw [he]; exact empty_record_typeValid
  tags_typeValid := by
    intro ety ty h
    simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h
    obtain ⟨entry, hf, ht⟩ := h
    exact cedarType_wf_typeValid (entry_tags_wf hwf hf ht)
  reqty_valid := by
    obtain ⟨entry, hf, hp, hr, hc⟩ := reqty_entry hwf
    obtain ⟨e, he⟩ := mapContainsPairKey_of_mapContains (find?_mapContains hf)
    exact ⟨entityType_wf_validEntityType hp, entityType_wf_validEntityType hr,
      ValidEntityType.isAction _ _ _ _ _ he, cedarType_wf_typeValid hc⟩

end Cedar.Validation.Relational

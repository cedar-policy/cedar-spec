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

import Cedar.Spec
import Cedar.Validation

/-!
This file contains the definition of well-formedness of `Environment`
and related definitions.
--/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Validation
open Cedar.Spec

----- Well-formedness of environment -----

def ActionSchema.IsActionEntityType (acts : ActionSchema) (ety : EntityType) : Prop :=
  ∃ uid, acts.contains uid ∧ uid.ty = ety

/--
Either a non-action entity type in `env.ets`,
or an action entity type in `env.acts`.
-/
def EntityType.WellFormed (env : Environment) (ety : EntityType) : Prop :=
  env.ets.contains ety ∨ env.acts.IsActionEntityType ety

mutual
inductive QualifiedType.WellFormed (env : Environment) : Qualified CedarType → Prop where
  | optional_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    QualifiedType.WellFormed env (.optional ty)
  | required_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    QualifiedType.WellFormed env (.required ty)

/--
Defines when a `CedarType` is well-formed in an `Environment`.
-/
inductive CedarType.WellFormed (env : Environment) : CedarType → Prop where
  | bool_wf {bty : BoolType} : CedarType.WellFormed env (.bool bty)
  | int_wf : CedarType.WellFormed env .int
  | string_wf : CedarType.WellFormed env .string
  | entity_wf {ety : EntityType}
    (h : EntityType.WellFormed env ety) :
    CedarType.WellFormed env (.entity ety)
  | set_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    CedarType.WellFormed env (.set ty)
  | record_wf {rty : RecordType}
    -- Well-formed as a `Map`
    (h₁ : rty.WellFormed)
    -- Each attribute type is well-formed
    (h₂ : ∀ attr qty, rty.find? attr = some qty → QualifiedType.WellFormed env qty) :
    CedarType.WellFormed env (.record rty)
  | ext_wf {xty : ExtType} : CedarType.WellFormed env (.ext xty)
end

def StandardSchemaEntry.WellFormed (env : Environment) (entry : StandardSchemaEntry) : Prop :=
  -- Well-formed as `Map`/`Set`s
  entry.ancestors.WellFormed ∧
  -- Each ancestor entity type must be a well-formed,
  -- non-action, non-enum entity type
  (∀ anc ∈ entry.ancestors,
    ∃ entry, env.ets.find? anc = some entry ∧ entry.isStandard) ∧
  -- The attribute types are well-formed
  (CedarType.record entry.attrs).WellFormed env ∧
  -- The tag type is well-formed
  (∀ ty, entry.tags = .some ty → CedarType.WellFormed env ty)

def EntitySchemaEntry.WellFormed (env : Environment) (entry : EntitySchemaEntry) : Prop :=
  match entry with
  | standard entry => entry.WellFormed env
  | enum es => es.WellFormed ∧ ¬es.isEmpty

def EntitySchema.WellFormed (env : Environment) (ets : EntitySchema) : Prop :=
  Map.WellFormed ets ∧
  ∀ ety entry, ets.find? ety = some entry → entry.WellFormed env

def EntityUID.WellFormed (env : Environment) (uid : EntityUID) : Prop :=
  env.ets.isValidEntityUID uid ∨ env.acts.contains uid

def ActionSchemaEntry.WellFormed (env : Environment) (entry : ActionSchemaEntry) : Prop :=
  -- Well-formed as `Map`/`Set`s
  entry.appliesToPrincipal.WellFormed ∧
  entry.appliesToResource.WellFormed ∧
  entry.ancestors.WellFormed ∧
  -- Each principal/resource entity type is well-formed
  (∀ ety, entry.appliesToPrincipal.contains ety → EntityType.WellFormed env ety) ∧
  (∀ ety, entry.appliesToResource.contains ety → EntityType.WellFormed env ety) ∧
  -- Ancestors of each action entity must also be an action entity
  (∀ uid ∈ entry.ancestors, env.acts.contains uid) ∧
  -- Context is a well-formed `RecordType`
  (CedarType.record entry.context).WellFormed env

def ActionSchema.AcyclicActionHierarchy (acts : ActionSchema) : Prop :=
  ∀ uid entry, acts.find? uid = .some entry → uid ∉ entry.ancestors

def ActionSchema.TransitiveActionHierarchy (acts : ActionSchema) : Prop :=
  ∀ uid₁ entry₁ uid₂ entry₂,
    acts.find? uid₁ = .some entry₁ →
    acts.find? uid₂ = .some entry₂ →
    uid₂ ∈ entry₁.ancestors →
    entry₂.ancestors ⊆ entry₁.ancestors

def ActionSchema.WellFormed (env : Environment) (acts : ActionSchema) : Prop :=
  Map.WellFormed acts ∧
  (∀ uid entry, acts.find? uid = some entry → entry.WellFormed env) ∧
  (∀ uid, acts.contains uid → ¬env.ets.contains uid.ty) ∧
  acts.AcyclicActionHierarchy ∧
  acts.TransitiveActionHierarchy

def RequestType.WellFormed (env : Environment) (reqty : RequestType) : Prop :=
  ∃ entry, env.acts.find? reqty.action = some entry ∧
    -- Enforce that principal/resource/context are valid for the action
    reqty.principal ∈ entry.appliesToPrincipal ∧
    reqty.resource ∈ entry.appliesToResource ∧
    reqty.context = entry.context
  -- Other properties, such as the well-formedness of principal/resource/context
  -- follows from the above and the well-formedness of `env.ets` and `env.acts`.

def Environment.WellFormed (env : Environment) : Prop :=
  env.ets.WellFormed env ∧
  env.acts.WellFormed env ∧
  env.reqty.WellFormed env

----- Some lemmas -----

theorem qty_wf_implies_type_of_wf {env : Environment} {qty : Qualified CedarType}
  (h : QualifiedType.WellFormed env qty) :
  CedarType.WellFormed env qty.getType
:= by
  cases h with
  | optional_wf hwf => simp [Qualified.getType, hwf]
  | required_wf hwf => simp [Qualified.getType, hwf]

theorem wf_record_type_cons {env : Environment}
  {hd : (Attr × Qualified CedarType)}
  {tl : List (Attr × Qualified CedarType)}
  (hwf : CedarType.WellFormed env (.record (Map.mk (hd :: tl)))) :
  CedarType.WellFormed env hd.snd.getType ∧
  CedarType.WellFormed env (.record (Map.mk tl))
:= by
  cases hwf
  rename_i hwf_map hwf_tys
  simp only [Map.WellFormed] at hwf_map
  constructor
  · have := hwf_tys hd.fst hd.snd
    simp only [Map.find?, List.find?, BEq.rfl, forall_const] at this
    cases e : hd.snd
    all_goals
      simp only [e] at *
      cases this
      simp only [Qualified.getType]
      assumption
  · constructor
    · simp only [Map.WellFormed]
      apply Eq.symm
      apply Map.make_eq_mk.mp
      have := Map.make_eq_mk.mpr (Eq.symm hwf_map)
      cases this with
      | cons_nil => constructor
      | cons_cons =>
        simp only [Map.toList, Map.kvs]
        assumption
    · intros attr qty hfound
      have hfound := Map.find?_mem_toList hfound
      simp only [Map.toList, Map.kvs] at hfound
      have : (Map.mk (hd :: tl)).find? attr = some qty := by
        apply (Map.in_list_iff_find?_some ?_).mp
        · simp [Map.kvs, hfound]
        · simp only [Map.WellFormed]
          assumption
      exact hwf_tys attr qty this

theorem wf_record_implies_wf_attr {env : Environment} {rty : RecordType} {attr : Attr} {qty : QualifiedType}
  (hwf : CedarType.WellFormed env (.record rty))
  (hqty : rty.find? attr = some qty) :
  QualifiedType.WellFormed env qty
:= by
  cases hwf with
  | record_wf _ hattr =>
    exact hattr attr qty hqty

theorem wf_env_implies_wf_entity_schema_entry {env : Environment} {ety : EntityType} {entry : EntitySchemaEntry}
  (hwf : env.WellFormed)
  (hets : env.ets.find? ety = some entry) :
  entry.WellFormed env
:= by
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  exact hwf_ets ety entry hets

theorem wf_env_implies_wf_tag_type {env : Environment} {ety : EntityType} {ty : CedarType}
  (hwf : env.WellFormed)
  (hety : env.ets.tags? ety = .some (.some ty)) :
  CedarType.WellFormed env ty
:= by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at hety
  have ⟨entry, hentry, htags⟩ := hety
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  have hwf_entry := hwf_ets ety entry hentry
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  split at hwf_entry
  · have ⟨_, _, _, hwf_tag⟩ := hwf_entry
    simp only [EntitySchemaEntry.tags?] at htags
    exact hwf_tag ty htags
  · simp [EntitySchemaEntry.tags?] at htags

theorem wf_env_implies_wf_attrs {env : Environment} {ety : EntityType} {attrs : RecordType}
  (hwf : env.WellFormed)
  (hattrs : env.ets.attrs? ety = .some attrs) :
  CedarType.WellFormed env (.record attrs)
:= by
  simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hattrs
  have ⟨entry, hentry, hattrs⟩ := hattrs
  have ⟨⟨_, hwf_ets⟩, _⟩ := hwf
  have hwf_entry := hwf_ets ety entry hentry
  simp only [EntitySchemaEntry.WellFormed] at hwf_entry
  split at hwf_entry
  · have ⟨_, _, hwf_attrs, _⟩ := hwf_entry
    simp only [← hattrs]
    exact hwf_attrs
  · simp only [EntitySchemaEntry.attrs] at hattrs
    simp only [← hattrs, Map.empty]
    constructor
    . simp [Map.WellFormed, Map.toList, Map.kvs, Map.make, List.canonicalize]
    · simp [Map.find?, List.find?]

theorem wf_env_implies_action_wf {env : Environment}
  (hwf : env.WellFormed) :
  EntityUID.WellFormed env env.reqty.action
:= by
  have ⟨_, _, hwf_req⟩ := hwf
  have ⟨_, hact, _⟩ := hwf_req
  apply Or.inr
  simp [EntityUID.WellFormed, ActionSchema.contains, hact]

theorem wf_env_disjoint_ets_acts
  {env : Environment} {uid : EntityUID}
  {ets_entry : EntitySchemaEntry}
  {acts_entry : ActionSchemaEntry}
  (hwf : env.WellFormed)
  (hets : env.ets.find? uid.ty = some ets_entry)
  (hacts : env.acts.find? uid = some acts_entry) :
  False
:= by
  have ⟨_, ⟨_, _, hdisj, _⟩, _⟩ := hwf
  have := hdisj uid
  apply this
  · simp [ActionSchema.contains, hacts]
  · simp [EntitySchema.contains, hets]

/--
More well-formedness properties of `env.reqty`.
-/
theorem wf_env_implies_wf_request
  {env : Environment}
  (hwf : env.WellFormed) :
  EntityType.WellFormed env env.reqty.principal ∧
  env.acts.contains env.reqty.action ∧
  EntityType.WellFormed env env.reqty.resource ∧
  (CedarType.record env.reqty.context).WellFormed env
:= by
  have ⟨_, hwf_acts, ⟨entry, hwf_act, hwf_princ, hwf_res, hwf_ctx⟩⟩ := hwf
  have ⟨_, hwf_acts, _⟩ := hwf_acts
  have hwf_act_entry := hwf_acts env.reqty.action entry hwf_act
  have ⟨_, _, _, hwf_app_to_princ, hwf_app_to_res, _, hwf_ctx_ty⟩ := hwf_act_entry
  and_intros
  · apply hwf_app_to_princ
    simp only [Membership.mem] at hwf_princ
    simp [Set.contains, hwf_princ, Membership.mem]
  · simp [ActionSchema.contains, hwf_act]
  · apply hwf_app_to_res
    simp only [Membership.mem] at hwf_res
    simp [Set.contains, hwf_res, Membership.mem]
  · simp [hwf_ctx, hwf_ctx_ty]

end Cedar.Validation

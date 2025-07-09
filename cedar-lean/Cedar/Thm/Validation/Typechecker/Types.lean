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
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Set
import Cedar.Thm.Validation.Typechecker.LUB
import Cedar.Thm.Validation.Typechecker.WF

/-!
This file contains useful definitions and lemmas about Cedar types.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

----- Definitions -----

def BoolType.AdmitsBool : BoolType → Bool → Prop
  | .tt,     true  => True
  | .ff,     false => True
  | .anyBool, _    => True
  | _, _           => False

def Environment.AdmitsUIDOfEntityType (env : Environment) (e : EntityUID) (ety: EntityType) : Prop :=
  ety = e.ty ∧ EntityUID.WellFormed env e

def ExtType.AdmitsExt : ExtType → Ext → Prop
  | .decimal,  .decimal _  => True
  | .ipAddr,   .ipaddr _   => True
  | .datetime, .datetime _ => True
  | .duration, .duration _ => True
  | _, _                   => False

inductive Environment.AdmitsValueOfType (env : Environment) : Value → CedarType → Prop where
  | instance_of_bool (b : Bool) (bty : BoolType)
      (h₁ : bty.AdmitsBool b) :
      env.AdmitsValueOfType (.prim (.bool b)) (.bool bty)
  | instance_of_int :
      env.AdmitsValueOfType (.prim (.int _)) .int
  | instance_of_string :
      env.AdmitsValueOfType (.prim (.string _)) .string
  | instance_of_entity (e : EntityUID) (ety: EntityType)
      (h₁ : env.AdmitsUIDOfEntityType e ety) :
      env.AdmitsValueOfType (.prim (.entityUID e)) (.entity ety)
  | instance_of_set (s : Set Value) (ty : CedarType)
      (h₁ : ∀ v, v ∈ s → env.AdmitsValueOfType v ty) :
      env.AdmitsValueOfType (.set s) (.set ty)
  | instance_of_record (r : Map Attr Value) (rty : RecordType)
      -- if an attribute is present in the record, then it is present in the type
      (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      -- if an attribute is present, then it has the expected type
      (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
        r.find? k = some v → rty.find? k = some qty → env.AdmitsValueOfType v qty.getType)
      -- required attributes are present
      (h₃ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      env.AdmitsValueOfType (.record r) (.record rty)
  | instance_of_ext (x : Ext) (xty : ExtType)
      (h₁ : xty.AdmitsExt x) :
      env.AdmitsValueOfType (.ext x) (.ext xty)

def Environment.AdmitsRequest (env : Environment) (request : Request) : Prop :=
  env.AdmitsUIDOfEntityType request.principal env.reqty.principal ∧
  request.action = env.reqty.action ∧
  env.AdmitsUIDOfEntityType request.resource env.reqty.resource ∧
  env.AdmitsValueOfType request.context (.record env.reqty.context)

def Environment.AdmitsEntityTags (env : Environment) (data : EntityData) (entry : EntitySchemaEntry) : Prop :=
  match entry.tags? with
  | .some tty => ∀ v ∈ data.tags.values, env.AdmitsValueOfType v tty
  | .none     => data.tags = Map.empty

def EntitySchemaEntry.AdmitsEID (entry: EntitySchemaEntry) (eid: String) : Prop :=
  match entry with
  | .standard _ => True
  | .enum eids => eid ∈ eids

/--
For every entity `(uid, data)` in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
4. The entity's tags' types are consistent with the tags information in the type store.
-/
def Environment.AdmitsOrdinaryEntityData (env : Environment) (uid : EntityUID) (data : EntityData) : Prop :=
  ∃ entry, env.ets.find? uid.ty = some entry ∧
    entry.AdmitsEID uid.eid ∧
    env.AdmitsValueOfType data.attrs (.record entry.attrs) ∧
    (∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ entry.ancestors) ∧
    env.AdmitsEntityTags data entry

/--
Similar to `WellFormedEntityData`, but a special case for action entities
since they are stored disjoint from `ets`
-/
def Environment.AdmitsActionEntityData (env : Environment) (uid : EntityUID) (data : EntityData) : Prop :=
  -- Action entities cannot have attributes or tags
  data.attrs = .empty ∧
  data.tags = .empty ∧
  ∃ entry,
    env.acts.find? uid = some entry ∧
    data.ancestors = entry.ancestors

def Environment.AdmitsEntityData (env : Environment) (uid : EntityUID) (data : EntityData) : Prop :=
  env.AdmitsOrdinaryEntityData uid data ∨
  env.AdmitsActionEntityData uid data

/--
Each entry in the store is valid
-/
def Environment.AdmitsEntities (env : Environment) (entities : Entities) : Prop :=
  -- Each entity data is valid
  (∀ (uid : EntityUID) (data : EntityData),
    entities.find? uid = some data → env.AdmitsEntityData uid data) ∧
  -- Each action in the schema exists
  (∀ (uid : EntityUID) (entry : ActionSchemaEntry),
    env.acts.find? uid = some entry → ∃ data, entities.find? uid = some data)

def Environment.WellFormedForRequestEntities (env : Environment) (request : Request) (entities : Entities) : Prop :=
  env.WellFormed ∧
  env.AdmitsRequest request ∧
  env.AdmitsEntities entities

end Cedar.Validation

----- Theorems -----

namespace Cedar.Thm

open Cedar.Validation

theorem false_is_instance_of_ff {env : Environment} :
  InstanceOfType env (Value.prim (Prim.bool false)) (CedarType.bool BoolType.ff)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem true_is_instance_of_tt {env : Environment} :
  InstanceOfType env (Value.prim (Prim.bool true)) (CedarType.bool BoolType.tt)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem bool_is_instance_of_anyBool {env : Environment} (b : Bool) :
  InstanceOfType env (Value.prim (Prim.bool b)) (CedarType.bool BoolType.anyBool)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem instance_of_bool_is_bool {env : Environment} {v₁ : Value} {bty : BoolType} :
  InstanceOfType env v₁ (CedarType.bool bty) →
  ∃ b, v₁ = .prim (.bool b)
:= by
  intro h₁
  rcases h₁ with ⟨b, _, _⟩
  exists b

theorem instance_of_ff_is_false {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.bool BoolType.ff) →
  v₁ = .prim (.bool false)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_tt_is_true {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.bool BoolType.tt) →
  v₁ = .prim (.bool true)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_anyBool_is_bool {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.bool BoolType.anyBool) →
  ∃ b, v₁ = .prim (.bool b)
:= instance_of_bool_is_bool

theorem instance_of_int_is_int {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ CedarType.int →
  ∃ i, v₁ = .prim (.int i)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_string_is_string {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ CedarType.string →
  ∃ s, v₁ = .prim (.string s)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_entity_type_is_entity {env : Environment} {ety : EntityType} :
  InstanceOfType env v₁ (.entity ety) →
  ∃ euid, euid.ty = ety ∧ v₁ = .prim (.entityUID euid)
:= by
  intro h₁
  cases h₁
  rename_i euid h₁
  simp only [InstanceOfEntityType] at h₁
  exists euid
  simp [h₁]

theorem instance_of_decimal_type_is_decimal {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.decimal) →
  ∃ d, v₁ = .ext (.decimal d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_ipAddr_type_is_ipAddr {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.ipAddr) →
  ∃ d, v₁ = .ext (.ipaddr d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i ip _
  exists ip

theorem instance_of_datetime_type_is_datetime {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.datetime) →
  ∃ d, v₁ = .ext (.datetime d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_duration_type_is_duration {env : Environment} {v₁ : Value} :
  InstanceOfType env v₁ (CedarType.ext ExtType.duration) →
  ∃ d, v₁ = .ext (.duration d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp only [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_set_type_is_set {env : Environment} {v : Value} {ty : CedarType} :
  InstanceOfType env v (.set ty) →
  ∃ s, v = .set s
:= by
  intro h₁
  cases h₁
  rename_i s h₁
  exists s

theorem instance_of_record_type_is_record {env : Environment} {v : Value} {rty : RecordType} :
  InstanceOfType env v (.record rty) →
  ∃ r, v = .record r
:= by
  intro h₁
  cases h₁
  rename_i r _ _ _
  exists r

theorem instance_of_attribute_type {env : Environment} {r : Map Attr Value} {v : Value} {rty : RecordType} {a : Attr} {aty : CedarType} {qaty : QualifiedType}
  (h₁ : InstanceOfType env (.record r) (.record rty))
  (h₂ : rty.find? a = .some qaty)
  (h₃ : qaty.getType = aty)
  (h₄ : r.find? a = .some v) :
  InstanceOfType env v aty
:= by
  cases h₁
  rename_i _ h₅ _
  rw [←h₃]
  apply h₅ a v qaty h₄ h₂

theorem absent_attribute_is_absent {env : Environment} {r : Map Attr Value} {rty : RecordType} {a : Attr}
  (h₁ : InstanceOfType env (.record r) (.record rty))
  (h₂ : rty.find? a = .none) :
  r.find? a = .none
:= by
  cases h₁
  case instance_of_record h₃ _ _ =>
    by_contra h₄
    simp [Option.ne_none_iff_exists', ←Map.contains_iff_some_find?] at h₄
    specialize h₃ a h₄
    simp [Map.contains_iff_some_find?, h₂] at h₃

theorem required_attribute_is_present {env : Environment} {r : Map Attr Value} {rty : RecordType} {a : Attr} {aty : CedarType}
  (h₁ : InstanceOfType env (.record r) (.record rty))
  (h₂ : rty.find? a = .some (Qualified.required aty)) :
  ∃ v, r.find? a = .some v
:= by
  cases h₁
  rename_i h₃
  rw [←Map.contains_iff_some_find?]
  apply h₃ _ _ h₂
  simp [Qualified.isRequired]

theorem well_typed_entity_attributes
  {env : Environment} {request : Request} {entities : Entities}
  {uid: EntityUID} {d: EntityData} {rty : RecordType}
  (h₁ : InstanceOfWellFormedEnvironment request entities env)
  (h₂ : Map.find? entities uid = some d)
  (h₃ : EntitySchema.attrs? env.ets uid.ty = some rty) :
  InstanceOfType env d.attrs (.record rty)
:= by
  have ⟨_, _, h₁, _⟩ := h₁
  simp [InstanceOfSchemaEntry] at h₁
  specialize h₁ uid d h₂
  cases h₁ with
  | inl h₁ =>
    have ⟨entry, h₁₂, _, h₁, _⟩ := h₁
    unfold EntitySchema.attrs? at h₃
    simp [h₁₂] at h₃
    subst h₃
    exact h₁
  | inr h₁ =>
    have ⟨h₁, _, _, ⟨_, hentry⟩⟩ := h₁
    simp only [EntitySchema.attrs?, Option.map, h₁] at h₃
    split at h₃
    · apply False.elim
      apply wf_env_disjoint_ets_acts
      all_goals assumption
    · contradiction

theorem instance_of_type_bool_is_bool {env : Environment} (v : Value) (ty : CedarType) :
  InstanceOfType env v ty →
  ty ⊑ .bool .anyBool →
  ∃ b, v = .prim (.bool b)
:= by
  intro h₀ h₁
  cases v <;> cases ty <;> try cases h₀ <;>
  try simp [subty, lub?] at h₁
  case instance_of_bool b bty =>
    exists b

theorem bool_type_is_inhabited (bty : BoolType) :
  ∃ b, InstanceOfBoolType b bty
:= by
  simp [InstanceOfBoolType]
  cases bty
  case tt => simp only [or_true]
  case ff => simp only [or_false]
  case anyBool => simp only [or_self]

theorem entity_type_is_inhabited {env : Environment} {ety : EntityType}
  (hwf_env : env.WellFormed)
  (hwf : EntityType.WellFormed env ety) :
  ∃ euid, InstanceOfEntityType euid ety env
:= by
  cases hwf
  -- Non-action entity
  case inl hwf_ets =>
    simp only [EntitySchema.contains, Option.isSome] at hwf_ets
    split at hwf_ets
    case _ entry hentry =>
      have hwf_entry := wf_env_implies_wf_entity_schema_entry hwf_env hentry
      cases entry with
      | standard entry =>
        exists (EntityUID.mk ety default)
        simp only [InstanceOfEntityType, EntityUID.WellFormed, true_and]
        apply Or.inl
        simp [
          EntitySchema.isValidEntityUID,
          hentry,
          EntitySchemaEntry.isValidEntityEID,
          Set.contains, Membership.mem,
        ]
      | enum eids =>
        have ⟨_, hnon_empty⟩ := hwf_entry
        have ⟨eid, heid⟩ := (Set.non_empty_iff_exists eids).mp hnon_empty
        exists (EntityUID.mk ety eid)
        simp only [InstanceOfEntityType, EntityUID.WellFormed, true_and]
        apply Or.inl
        simp only [Membership.mem] at heid
        simp [
          EntitySchema.isValidEntityUID,
          hentry,
          EntitySchemaEntry.isValidEntityEID,
          Set.contains, Membership.mem, heid,
        ]
    case _ => contradiction
  -- Action entity
  case inr hwf_acts =>
    have ⟨act, hwf_act, hty_act⟩ := hwf_acts
    exists act
    simp only [InstanceOfEntityType, hty_act, true_and]
    apply Or.inr
    exact hwf_act

theorem ext_type_is_inhabited (xty : ExtType) :
  ∃ x, InstanceOfExtType x xty
:= by
  simp [InstanceOfExtType]
  cases xty
  case ipAddr  => exists (Ext.ipaddr (default : IPAddr))
  case decimal => exists (Ext.decimal (default : Ext.Decimal))
  case datetime => exists (Ext.datetime (default : Ext.Datetime))
  case duration => exists (Ext.duration (default : Ext.Datetime.Duration))

theorem instance_of_record_nil {env : Environment} :
  InstanceOfType env (Value.record (Map.mk [])) (CedarType.record (Map.mk []))
:= by
  apply InstanceOfType.instance_of_record <;>
  simp [Map.contains, Map.find?, Map.kvs, List.find?]

theorem instance_of_record_cons {env : Environment} {hd : Attr × Qualified CedarType} {tl : List (Attr × Qualified CedarType)} {rhd : Value} {rtl : List (Attr × Value)}
  (h₁ : InstanceOfType env rhd (Qualified.getType hd.snd))
  (h₂ : InstanceOfType env (Value.record (Map.mk rtl)) (CedarType.record (Map.mk tl))) :
  InstanceOfType env (Value.record (Map.mk ((hd.fst, rhd) :: rtl))) (CedarType.record (Map.mk (hd :: tl)))
:= by
  cases h₂ ; rename_i h₂ h₃ h₄
  apply InstanceOfType.instance_of_record
  case h₁ =>
    intro a
    specialize h₂ a
    simp [Map.contains, Map.find?, Map.kvs, List.find?]
    simp [Map.contains, Map.find?, Map.kvs, List.find?] at h₂
    cases h₅ : hd.fst == a <;> simp [h₅]
    exact h₂
  case h₂ =>
    intro a v qty
    specialize h₃ a v qty
    simp [Map.contains, Map.find?, Map.kvs, List.find?]
    simp [Map.contains, Map.find?, Map.kvs, List.find?] at h₃
    cases h₅ : hd.fst == a <;> simp [h₅]
    case false => exact h₃
    case true =>
      intro h₆ h₇
      subst h₆ h₇
      exact h₁
  case h₃ =>
    intro a qty
    specialize h₄ a qty
    simp [Map.contains, Map.find?, Map.kvs, List.find?]
    simp [Map.contains, Map.find?, Map.kvs, List.find?] at h₄
    cases h₅ : hd.fst == a <;> simp [h₅]
    exact h₄


theorem sizeOf_attribute_lt_sizeOf_qualified (aqty : Attr × Qualified CedarType) :
  sizeOf (Qualified.getType aqty.snd) < sizeOf aqty
:= by
  simp [Qualified.getType]
  split
  all_goals {
    rename_i aty h
    apply @Nat.lt_trans _ (sizeOf aqty.snd)
    case h₁ => simp [h, ←Nat.succ_eq_one_add]
    case a =>
      cases aqty ; simp [Prod.snd]
      omega
  }

theorem type_is_inhabited {env : Environment} {ty : CedarType}
  (hwf_env : env.WellFormed)
  (hwf : ty.WellFormed env) :
  ∃ v, InstanceOfType env v ty
:= by
  match ty with
  | .bool bty =>
    have ⟨b, h₁⟩ := bool_type_is_inhabited bty
    exists (.prim (.bool b))
    apply InstanceOfType.instance_of_bool _ _ h₁
  | .int =>
    exists (.prim (.int default))
    apply InstanceOfType.instance_of_int
  | .string =>
    exists (.prim (.string default))
    apply InstanceOfType.instance_of_string
  | .entity ety =>
    cases hwf with | entity_wf hwf_ety =>
    have ⟨euid, h₁⟩ := entity_type_is_inhabited hwf_env hwf_ety
    exists (.prim (.entityUID euid))
    apply InstanceOfType.instance_of_entity _ _ h₁
  | .set ty₁ =>
    exists (.set Set.empty)
    apply InstanceOfType.instance_of_set
    intro v₁ h₁
    have h₂ := Set.in_set_means_list_non_empty v₁ Set.empty h₁
    simp [Set.empty, Set.elts] at h₂
  | .ext xty =>
    have ⟨x, h₁⟩ := ext_type_is_inhabited xty
    exists (.ext x)
    apply InstanceOfType.instance_of_ext _ _ h₁
  | .record (Map.mk rty) =>
    cases rty
    case nil =>
      exists (.record (Map.mk []))
      exact instance_of_record_nil
    case cons hd tl =>
      have _ : sizeOf hd.snd.getType < 1 + (1 + (1 + sizeOf hd + sizeOf tl)) := by -- termination
        apply @Nat.lt_trans _ (1 + (1 + sizeOf hd + sizeOf tl)) <;>
        try { simp [←Nat.succ_eq_one_add] }
        apply @Nat.lt_trans _ (1 + sizeOf hd + sizeOf tl) <;>
        try { simp [←Nat.succ_eq_one_add] }
        apply @Nat.lt_trans _ (sizeOf hd + sizeOf tl)
        case h₁ =>
          apply Nat.lt_add_right
          apply sizeOf_attribute_lt_sizeOf_qualified
        case a =>
          simp [Nat.add_assoc]
      have ⟨hwf_hd, hwf_tl⟩ := wf_record_type_cons hwf
      have ⟨rhd, h₂⟩ := type_is_inhabited hwf_env hwf_hd
      have ⟨vtl, h₃⟩ := type_is_inhabited hwf_env hwf_tl
      have ⟨mtl, h₄⟩ := instance_of_record_type_is_record h₃
      subst h₄ ; cases mtl ; rename_i rtl
      exists (.record (Map.mk ((hd.fst, rhd) :: rtl)))
      exact instance_of_record_cons h₂ h₃

theorem type_is_inhabited_bool {env : Environment} {bty : BoolType} :
  ∃ v, InstanceOfType env v (.bool bty)
:= by
  have ⟨v, h⟩ := bool_type_is_inhabited bty
  exists v
  constructor
  assumption

theorem type_is_inhabited_int {env : Environment} :
  ∃ v, InstanceOfType env v CedarType.int
:= by
  exists (.prim (.int default))
  apply InstanceOfType.instance_of_int

theorem type_is_inhabited_set {env : Environment} {ty : CedarType} :
  ∃ v, InstanceOfType env v (.set ty)
:= by
  exists (.set Set.empty)
  apply InstanceOfType.instance_of_set
  intro v₁ h₁
  have h₂ := Set.in_set_means_list_non_empty v₁ Set.empty h₁
  simp [Set.empty, Set.elts] at h₂

theorem type_is_inhabited_ext {env : Environment} {xty : ExtType} :
  ∃ v, InstanceOfType env v (.ext xty)
:= by
  have ⟨x, h₁⟩ := ext_type_is_inhabited xty
  exists (.ext x)
  apply InstanceOfType.instance_of_ext _ _ h₁

theorem instance_of_lubBool_left {env : Environment} {v : Value} {bty₁ bty₂ : BoolType} :
  InstanceOfType env v (CedarType.bool bty₁) →
  InstanceOfType env v (CedarType.bool (lubBool bty₁ bty₂))
:= by
  intro h₁ ; cases h₁
  simp [lubBool]
  split <;> rename_i b h₁ h₂
  · subst h₂
    apply InstanceOfType.instance_of_bool b bty₁ h₁
  · exact bool_is_instance_of_anyBool b

theorem instance_of_lubBool {env : Environment} {v : Value} {bty₁ bty₂ : BoolType} :
  (InstanceOfType env v (CedarType.bool bty₁) ∨ InstanceOfType env v (CedarType.bool bty₂)) →
  InstanceOfType env v (CedarType.bool (lubBool bty₁ bty₂))
:= by
  intro h₁ ; cases h₁ <;> rename_i h₂
  · exact instance_of_lubBool_left h₂
  · rw [lubBool_comm]
    exact instance_of_lubBool_left h₂

theorem sizeOf_attr_type_lt_sizeOf_record_type {a : Attr} {qty : QualifiedType } {rty : List (Attr × Qualified CedarType) }
  (h₁ : CedarType.record (Map.mk rty) = ty)
  (h₂ : Map.find? (Map.mk rty) a = .some qty) :
  sizeOf qty.getType < sizeOf ty
:= by
  subst h₁
  apply @Nat.lt_trans _ (sizeOf qty)
  case h₁ =>
    simp [Qualified.getType]
    split <;> simp [←Nat.succ_eq_one_add]
  case a =>
    apply @Nat.lt_trans _ (sizeOf (Map.mk rty))
    case h₁ =>
      apply @Nat.lt_trans _ (sizeOf rty)
      case h₁ =>
        simp [Map.find?, Map.kvs] at h₂
        split at h₂ <;> simp at h₂
        rename_i a' qty' h₃ ; rw [eq_comm] at h₂ ; subst h₂
        have h₄ := List.mem_of_find?_eq_some h₃
        apply @Nat.lt_trans _ (sizeOf (a', qty))
        case h₁ =>
          simp only [Prod.mk.sizeOf_spec]
          omega
        case a => exact List.sizeOf_lt_of_mem h₄
      case a => simp [←Nat.succ_eq_one_add]
    case a => simp [←Nat.succ_eq_one_add]


theorem instance_of_lub_left {env : Environment} {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType env v ty₁) :
  InstanceOfType env v ty
:= by
  unfold lub? at h₁
  -- Generalizing here lets us retain hypotheses of the form ty₁ = CedarType.set
  -- s₁ after the split.  We need these for the termination proof.
  generalize hty₁ : ty₁ = ty₁'
  generalize hty₂ : ty₂ = ty₂'
  simp [hty₁, hty₂] at h₂
  split at h₁
  case h_1 =>
    simp at h₁ ; subst h₁ hty₁ hty₂
    exact instance_of_lubBool_left h₂
  case h_2 _ _ sty₁ sty₂ =>
    cases h₃ : sty₁ ⊔ sty₂ <;> simp [h₃] at h₁
    rename_i sty
    subst h₁ ; simp [←hty₁, ←hty₂] at h₂
    cases h₂ ; rename_i h₄
    apply InstanceOfType.instance_of_set
    intro w h₅
    specialize h₄ w h₅
    apply instance_of_lub_left h₃ (by simp [h₄])
  case h_3 _ _ rty₁ rty₂ =>
    cases h₃ : lubRecordType rty₁ rty₂ <;> simp [h₃] at h₁
    rename_i rty
    have hl := lubRecordType_is_lub_of_record_types h₃
    subst h₁ ; simp [←hty₁] at h₂
    cases h₂ ; rename_i r h₄ h₅ h₆
    apply InstanceOfType.instance_of_record
    case h₁ =>
      intro a h₇
      specialize h₄ a h₇
      exact lubRecord_contains_left hl h₄
    case h₂ =>
      intro a v qty h₇ h₈
      have ⟨qty₁, qty₂, h₉, _, h₁₁⟩ := lubRecord_find_implies_find hl h₈
      specialize h₅ a v qty₁ h₇ h₉
      have h₁₂ := lubQualified_is_lub_of_getType h₁₁
      have _ : sizeOf qty₁.getType < sizeOf ty₁' :=  -- termination
        sizeOf_attr_type_lt_sizeOf_record_type hty₁ h₉
      apply instance_of_lub_left h₁₂ h₅
    case h₃ =>
      intro a qty h₇ h₈
      have ⟨qty₁, h₉, h₁₀⟩ := lubRecord_find_implies_find_left hl h₇
      apply h₆ a qty₁ h₉
      simp [h₁₀, h₈]
  case h_4 =>
    split at h₁ <;> simp at h₁
    rename_i h₃
    subst h₁ h₃ hty₁ hty₂
    exact h₂
termination_by (sizeOf ty₁, sizeOf ty₂)

theorem instance_of_lub {env : Environment} {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType env v ty₁ ∨ InstanceOfType env v ty₂) :
  InstanceOfType env v ty
:= by
  cases h₂ <;> rename_i h₃
  · exact instance_of_lub_left h₁ h₃
  · rw [lub_comm] at h₁
    exact instance_of_lub_left h₁ h₃

/--
TODO: move this back to Cedar/Thm/Validation/Typechecker/LitVar.lean
after we fix the proof.
-/
theorem type_of_lit_inversion {p : Prim} {c₁ c₂ : Capabilities} {tx : TypedExpr} {env : Environment}
  (h₁ : (typeOf (.lit p) c₁ env) = .ok (tx, c₂)) :
  ∃ ty, tx = .lit p ty
:= by
  simp only [typeOf, typeOfLit, ok, err, Function.comp_apply] at h₁
  (split at h₁ <;> try split at h₁) <;> first
  | simp only [reduceCtorEq] at h₁
  | injections h₁ h₁ ; simp [←h₁]

/--
Obtains the fact of well-formed environment from `InstanceOfWellFormedEnvironment`.
-/
theorem InstanceOfWellFormedEnvironment.wf_env
  {env : Environment} {request : Request} {entities : Entities}
  (h : InstanceOfWellFormedEnvironment request entities env):
  env.WellFormed
:= by
  have ⟨h, _, _,⟩ := h
  exact h

theorem InstanceOfWellFormedEnvironment.instance_of_schema_entry
  {env : Environment} {request : Request} {entities : Entities}
  {uid : EntityUID} {data : EntityData}
  (h : InstanceOfWellFormedEnvironment request entities env)
  (hentry : entities.find? uid = some data) :
  InstanceOfSchemaEntry uid data env
:= by
  have ⟨_, _, hsch⟩ := h
  exact hsch.1 uid data hentry

theorem InstanceOfWellFormedEnvironment.instance_of_schema
  {env : Environment} {request : Request} {entities : Entities}
  (h : InstanceOfWellFormedEnvironment request entities env) :
  InstanceOfSchema entities env
:= by
  have ⟨_, _, hsch⟩ := h
  exact hsch

theorem InstanceOfWellFormedEnvironment.wf_action_data
  {env : Environment} {request : Request} {entities : Entities}
  {uid : EntityUID} {entry : ActionSchemaEntry}
  (h : InstanceOfWellFormedEnvironment request entities env)
  (hacts : Map.find? env.acts uid = some entry) :
  ∃ data,
    Map.find? entities uid = some data ∧
    data.ancestors = entry.ancestors
:= by
  have ⟨hwf, _, hsch⟩ := h
  have ⟨data, hdata⟩ := hsch.2 uid entry hacts
  exists data
  simp only [hdata, true_and]
  cases hsch.1 uid data hdata with
  | inl hets =>
    have ⟨_, hets, _⟩ := hets
    apply False.elim
    apply wf_env_disjoint_ets_acts hwf
    all_goals assumption
  | inr hacts2 =>
    have ⟨_, _, ⟨entry, hacts2, hanc⟩⟩ := hacts2
    simp only [hacts2, Option.some.injEq] at hacts
    simp [hacts, hanc]

end Cedar.Thm

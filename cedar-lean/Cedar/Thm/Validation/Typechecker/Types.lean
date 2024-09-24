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

/-!
This file contains useful definitions and lemmas about Cedar types.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

----- Definitions -----

def InstanceOfBoolType : Bool → BoolType → Prop
  | true,  .tt      => True
  | false, .ff      => True
  | _,     .anyBool => True
  | _, _            => False

def InstanceOfEntityType (e : EntityUID) (ety: EntityType) : Prop :=
  ety = e.ty

def InstanceOfExtType : Ext → ExtType → Prop
  | .decimal _, .decimal => True
  | .ipaddr _,  .ipAddr  => True
  | _, _                 => False

inductive InstanceOfType : Value → CedarType → Prop :=
  | instance_of_bool (b : Bool) (bty : BoolType)
      (h₁ : InstanceOfBoolType b bty) :
      InstanceOfType (.prim (.bool b)) (.bool bty)
  | instance_of_int :
      InstanceOfType (.prim (.int _)) .int
  | instance_of_string :
      InstanceOfType (.prim (.string _)) .string
  | instance_of_entity (e : EntityUID) (ety: EntityType) (l : Level)
      (h₁ : InstanceOfEntityType e ety) :
      InstanceOfType (.prim (.entityUID e)) (.entity ety l)
  | instance_of_set (s : Set Value) (ty : CedarType)
      (h₁ : forall v, v ∈ s → InstanceOfType v ty) :
      InstanceOfType (.set s) (.set ty)
  | instance_of_record (r : Map Attr Value) (rty : RecordType)
      -- if an attribute is present in the record, then it is present in the type
      (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      -- if an attribute is present, then it has the expected type
      (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
        r.find? k = some v → rty.find? k = some qty → InstanceOfType v qty.getType)
      -- required attributes are present
      (h₃ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      InstanceOfType (.record r) (.record rty)
  | instance_of_ext (x : Ext) (xty : ExtType)
      (h₁ : InstanceOfExtType x xty) :
      InstanceOfType (.ext x) (.ext xty)

def InstanceOfRequestType (request : Request) (reqty : RequestType) : Prop :=
  InstanceOfEntityType request.principal reqty.principal.fst ∧
  request.action = reqty.action.fst ∧
  InstanceOfEntityType request.resource reqty.resource.fst ∧
  InstanceOfType request.context (.record reqty.context)

def InstanceOfRequestTypeLevel (request : Request) (reqty : RequestType) (l : Level) : Prop :=
  InstanceOfEntityType request.principal reqty.principal.fst ∧
  reqty.principal.snd = l ∧
  reqty.action.snd = l ∧
  reqty.resource.snd = l ∧
  request.action = reqty.action.fst ∧
  InstanceOfEntityType request.resource reqty.resource.fst ∧
  InstanceOfType request.context (.record reqty.context)


section
set_option hygiene false

notation:10 μ " ⊢ " e " : " τ => WellFormed μ e τ

inductive WellFormed : Entities → Value → CedarType → Prop :=
  | bool (μ : Entities) (b : Bool) (bty : BoolType)
      (h₁ : InstanceOfBoolType b bty) :
      μ  ⊢ .prim (.bool b) : .bool bty
  | int (μ : Entities) :
    μ ⊢ .prim (.int _) : .int
  | string (μ : Entities) :
    μ ⊢ .prim (.string _) : .string
  | set (μ : Entities) (s : Cedar.Data.Set Value) (ty : CedarType)
    (h₁ : forall v, v ∈ s → (μ ⊢ v : ty)) :
    μ ⊢ .set s : .set ty
  | record (μ : Entities) (r : Cedar.Data.Map Attr Value) (rty : RecordType)
      -- if an attribute is present in the record, then it is present in the type
      (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      -- if an attribute is present, then it has the expected type
      (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
        r.find? k = some v → rty.find? k = some qty → (μ ⊢ v : qty.getType))
      -- required attributes are present
      (h₃ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      μ ⊢ .record r : .record rty
  | ext (μ : Entities) (x : Ext) (xty : ExtType)
      (h₁ : InstanceOfExtType x xty) :
      μ ⊢ .ext x : .ext xty
  -- Now for the wacky cases: Entities
  -- Any entity is well formed at level 0
  | entity₀ (μ : Entities) (e : EntityUID) (ety: EntityType)
    (h₁ : InstanceOfEntityType e ety) :
    μ ⊢ .prim (.entityUID e) : .entity ety (.finite 0)
  -- Entities can be given `n` as long as all entities in the attributes can be given a level bounded from below by `n - 1`
  | entityₙ (μ : Entities) (e : EntityUID) (ety : EntityType) (attrs : Cedar.Data.Map Attr Value) {l : Level}
    (h₁ : InstanceOfEntityType e ety)
    (h₂ : μ.attrs e = .ok attrs)
    -- All attributes must be well formed
    (h₃ : ∀ k v t',
      (k,v) ∈ attrs.kvs →
      (μ ⊢ v : t')
    )
    -- All attributes must be bounded by `l - 1`
    (h₄ : ∀ k v t',
      (k,v) ∈ attrs.kvs →
      level t' ≥ l.sub1
    ) :
    μ ⊢ .prim (.entityUID e) : .entity ety l

end


theorem WellFormed_is_instanceOf (μ : Entities) (v : Value) (t : CedarType) :
  (μ ⊢ v : t) →
  InstanceOfType v t
  := by
  intros h
  cases v  <;> cases h
  case _ =>
    apply InstanceOfType.instance_of_bool
    assumption
  case _ =>
    apply InstanceOfType.instance_of_int
  case _ =>
    apply InstanceOfType.instance_of_string
  case _ =>
    apply InstanceOfType.instance_of_entity
    assumption
  case _ =>
    apply InstanceOfType.instance_of_entity
    assumption
  case _ =>
    apply InstanceOfType.instance_of_set
    rename_i s ty h₁
    intros v h₂
    have h_v_wf := h₁ v h₂
    apply WellFormed_is_instanceOf
    apply h_v_wf
  case _ =>
    rename_i attrs rty h₁ h₂ h₃
    apply InstanceOfType.instance_of_record <;> try assumption
    intros k v qty h₄ h₅
    have h_v_wf := h₃ k v qty h₄ h₅
    apply WellFormed_is_instanceOf
    assumption
  case _ =>
    apply InstanceOfType.instance_of_ext
    assumption
termination_by sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ =>
    rename_i heq _ _ _ _ _ _ _ _ _ _ _ _
    subst heq
    rename_i s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    simp
    have hsize : sizeOf v < sizeOf s := by
      apply Set.sizeOf_lt_of_mem
      assumption
    omega
  case _ =>
    rename_i m heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq]
    simp
    have hsize : sizeOf v < sizeOf m := by
      have h₁ : sizeOf (k,v) < sizeOf m.kvs := by
        apply List.sizeOf_lt_of_mem
        apply Map.find_means_mem
        assumption
      have h₂ : sizeOf v < sizeOf (k,v) := by
        simp
        omega
      have h₃ : sizeOf m.kvs < sizeOf m := by
        apply Map.sizeOf_lt_of_kvs
      omega
    omega



/--
For every entity in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
-/
def InstanceOfEntitySchema (entities : Entities) (ets: EntitySchema) : Prop :=
  ∀ uid data, entities.find? uid = some data →
    ∃ entry, ets.find? uid.ty = some entry ∧
      InstanceOfType data.attrs (.record entry.attrs) ∧
      ∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ entry.ancestors

/--
For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
def InstanceOfActionSchema (entities : Entities) (as: ActionSchema) : Prop :=
  ∀ (uid : EntityUID) (entry : ActionSchemaEntry),
  Map.find? as uid = some entry →
  ∃ data,
    Map.find? entities uid = some data ∧
    data.ancestors = entry.ancestors

def RequestAndEntitiesMatchEnvironment (env : Environment) (request : Request) (entities : Entities) : Prop :=
  InstanceOfRequestType request env.reqty ∧
  InstanceOfEntitySchema entities env.ets ∧
  InstanceOfActionSchema entities env.acts

def RequestAndEntitiesMatchEnvironmentLeveled (env : Environment) (request : Request) (entities : Entities) (l : Level) : Prop :=
  InstanceOfRequestTypeLevel request env.reqty l ∧
  InstanceOfEntitySchema entities env.ets ∧
  InstanceOfActionSchema entities env.acts ∧
  (entities ⊢ request.principal : .entity env.reqty.principal.fst env.reqty.principal.snd) ∧
  (entities ⊢ request.resource : .entity env.reqty.resource.fst env.reqty.resource.snd) ∧
  (entities ⊢ request.action : .entity env.reqty.action.fst.ty env.reqty.action.snd) ∧
  (entities ⊢ request.context : .record env.reqty.context)

----- Theorems -----

theorem false_is_instance_of_ff :
  InstanceOfType (Value.prim (Prim.bool false)) (CedarType.bool BoolType.ff)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem true_is_instance_of_tt :
  InstanceOfType (Value.prim (Prim.bool true)) (CedarType.bool BoolType.tt)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem bool_is_instance_of_anyBool (b : Bool) :
  InstanceOfType (Value.prim (Prim.bool b)) (CedarType.bool BoolType.anyBool)
:= by
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]

theorem instance_of_bool_is_bool {v₁ : Value} {bty : BoolType} :
  InstanceOfType v₁ (CedarType.bool bty) →
  ∃ b, v₁ = .prim (.bool b)
:= by
  intro h₁
  rcases h₁ with ⟨b, _, _⟩
  exists b

theorem instance_of_ff_is_false {v₁ : Value} :
  InstanceOfType v₁ (CedarType.bool BoolType.ff) →
  v₁ = .prim (.bool false)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_tt_is_true {v₁ : Value} :
  InstanceOfType v₁ (CedarType.bool BoolType.tt) →
  v₁ = .prim (.bool true)
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    simp [InstanceOfBoolType] at h₁
    cases b <;> simp at h₁
    rfl

theorem instance_of_anyBool_is_bool {v₁ : Value} :
  InstanceOfType v₁ (CedarType.bool BoolType.anyBool) →
  ∃ b, v₁ = .prim (.bool b)
:= instance_of_bool_is_bool

theorem instance_of_int_is_int {v₁ : Value} :
  InstanceOfType v₁ CedarType.int →
  ∃ i, v₁ = .prim (.int i)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_string_is_string {v₁ : Value} :
  InstanceOfType v₁ CedarType.string →
  ∃ s, v₁ = .prim (.string s)
:= by
  intro h₁
  cases h₁
  rename_i y
  exists y

theorem instance_of_entity_type_is_entity {ety : EntityType} :
  InstanceOfType v₁ (.entity ety l) →
  ∃ euid, euid.ty = ety ∧ v₁ = .prim (.entityUID euid)
:= by
  intro h₁
  cases h₁
  rename_i euid h₁
  simp [InstanceOfEntityType] at h₁
  exists euid
  simp [h₁]

theorem instance_of_decimal_type_is_decimal {v₁ : Value} :
  InstanceOfType v₁ (CedarType.ext ExtType.decimal) →
  ∃ d, v₁ = .ext (.decimal d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i d _
  exists d

theorem instance_of_ipAddr_type_is_ipAddr {v₁ : Value} :
  InstanceOfType v₁ (CedarType.ext ExtType.ipAddr) →
  ∃ d, v₁ = .ext (.ipaddr d)
:= by
  intro h₁
  cases h₁
  rename_i x h₁
  simp [InstanceOfExtType] at h₁
  split at h₁ <;> try { contradiction }
  rename_i ip _
  exists ip

theorem instance_of_set_type_is_set {v : Value} {ty : CedarType} :
  InstanceOfType v (.set ty) →
  ∃ s, v = .set s
:= by
  intro h₁
  cases h₁
  rename_i s h₁
  exists s

theorem instance_of_record_type_is_record {v : Value} {rty : RecordType} :
  InstanceOfType v (.record rty) →
  ∃ r, v = .record r
:= by
  intro h₁
  cases h₁
  rename_i r _ _ _
  exists r

theorem instance_of_attribute_type {r : Map Attr Value} {v : Value} {rty : RecordType} {a : Attr} {aty : CedarType} {qaty : QualifiedType}
  (h₁ : InstanceOfType (.record r) (.record rty))
  (h₂ : rty.find? a = .some qaty)
  (h₃ : qaty.getType = aty)
  (h₄ : r.find? a = .some v) :
  InstanceOfType v aty
:= by
  cases h₁
  rename_i _ h₅ _
  rw [←h₃]
  apply h₅ a v qaty h₄ h₂

theorem absent_attribute_is_absent {r : Map Attr Value} {rty : RecordType} {a : Attr}
  (h₁ : InstanceOfType (.record r) (.record rty))
  (h₂ : rty.find? a = .none) :
  r.find? a = .none
:= by
  cases h₁
  case instance_of_record h₃ _ _ =>
    by_contra h₄
    simp [Option.ne_none_iff_exists', ←Map.contains_iff_some_find?] at h₄
    specialize h₃ a h₄
    simp [Map.contains_iff_some_find?, h₂] at h₃

theorem required_attribute_is_present {r : Map Attr Value} {rty : RecordType} {a : Attr} {aty : CedarType}
  (h₁ : InstanceOfType (.record r) (.record rty))
  (h₂ : rty.find? a = .some (Qualified.required aty)) :
  ∃ v, r.find? a = .some v
:= by
  cases h₁
  rename_i h₃
  rw [←Map.contains_iff_some_find?]
  apply h₃ _ _ h₂
  simp [Qualified.isRequired]

theorem well_typed_entity_attributes {env : Environment} {request : Request} {entities : Entities} {uid: EntityUID} {d: EntityData} {rty : RecordType}
  (h₁ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₂ : Map.find? entities uid = some d)
  (h₃ : EntitySchema.attrs? env.ets uid.ty = some rty) :
  InstanceOfType d.attrs (.record rty)
:= by
  have ⟨_, h₁, _⟩ := h₁
  simp [InstanceOfEntitySchema] at h₁
  specialize h₁ uid d h₂
  have ⟨entry, h₁₂, h₁, _⟩ := h₁
  unfold EntitySchema.attrs? at h₃
  simp [h₁₂] at h₃
  subst h₃
  exact h₁

theorem instance_of_type_bool_is_bool (v : Value) (ty : CedarType) :
  InstanceOfType v ty →
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
  case tt => exists true
  all_goals { exists false }

theorem entity_type_is_inhabited (ety : EntityType) :
  ∃ euid, InstanceOfEntityType euid ety
:= by
  simp [InstanceOfEntityType]
  exists (EntityUID.mk ety default)

theorem ext_type_is_inhabited (xty : ExtType) :
  ∃ x, InstanceOfExtType x xty
:= by
  simp [InstanceOfExtType]
  cases xty
  case ipAddr  => exists (Ext.ipaddr (default : IPAddr))
  case decimal => exists (Ext.decimal (default : Ext.Decimal))

theorem instance_of_record_nil :
  InstanceOfType (Value.record (Map.mk [])) (CedarType.record (Map.mk []))
:= by
  apply InstanceOfType.instance_of_record <;>
  simp [Map.contains, Map.find?, Map.kvs, List.find?]

theorem instance_of_record_cons {hd : Attr × Qualified CedarType} {tl : List (Attr × Qualified CedarType)} {rhd : Value} {rtl : List (Attr × Value)}
  (h₁ : InstanceOfType rhd (Qualified.getType hd.snd))
  (h₂ : InstanceOfType (Value.record (Map.mk rtl)) (CedarType.record (Map.mk tl))) :
  InstanceOfType (Value.record (Map.mk ((hd.fst, rhd) :: rtl))) (CedarType.record (Map.mk (hd :: tl)))
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

theorem type_is_inhabited (ty : CedarType) :
  ∃ v, InstanceOfType v ty
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
  | .entity ety l =>
    have ⟨euid, h₁⟩ := entity_type_is_inhabited ety
    exists (.prim (.entityUID euid))
    apply InstanceOfType.instance_of_entity _ _ _ h₁
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
          simp [←Nat.succ_eq_one_add]
      have ⟨rhd, h₂⟩ := type_is_inhabited hd.snd.getType
      have ⟨vtl, h₃⟩ := type_is_inhabited (.record (Map.mk tl))
      have ⟨mtl, h₄⟩ := instance_of_record_type_is_record h₃
      subst h₄ ; cases mtl ; rename_i rtl
      exists (.record (Map.mk ((hd.fst, rhd) :: rtl)))
      exact instance_of_record_cons h₂ h₃

theorem instance_of_lubBool_left {v : Value} {bty₁ bty₂ : BoolType} :
  InstanceOfType v (CedarType.bool bty₁) →
  InstanceOfType v (CedarType.bool (lubBool bty₁ bty₂))
:= by
  intro h₁ ; cases h₁
  simp [lubBool]
  split <;> rename_i b h₁ h₂
  · subst h₂
    apply InstanceOfType.instance_of_bool b bty₁ h₁
  · exact bool_is_instance_of_anyBool b

theorem instance_of_lubBool {v : Value} {bty₁ bty₂ : BoolType} :
  (InstanceOfType v (CedarType.bool bty₁) ∨ InstanceOfType v (CedarType.bool bty₂)) →
  InstanceOfType v (CedarType.bool (lubBool bty₁ bty₂))
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


theorem instance_of_lub_left {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType v ty₁) :
  InstanceOfType v ty
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
  case h_3 ety₁ l₁ ety₂ l₂ =>
    cases heq : decide (ety₁ = ety₂) <;> simp at heq
    case false =>
      rw [if_neg] at  h₁
      contradiction
      simp
      apply heq
    case true =>
      rw [if_pos] at h₁
      simp at h₁
      cases ty₁' <;> simp at hty₁
      rename_i ety' l'
      have ⟨h₃, _h₄⟩ := hty₁
      cases ty <;> simp at h₁
      cases h₂
      apply InstanceOfType.instance_of_entity
      have ⟨h₁, _h₂ ⟩ := h₁
      rename_i h
      rw [← h₁]
      rw [h₃]
      apply h
      rw [heq]
      simp
  case h_4 _ _ rty₁ rty₂ =>
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
  case h_5 =>
    split at h₁ <;> simp at h₁
    rename_i h₃
    subst h₁ h₃ hty₁ hty₂
    exact h₂
termination_by (sizeOf ty₁, sizeOf ty₂)

theorem instance_of_lub {v : Value} {ty ty₁ ty₂ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = .some ty)
  (h₂ : InstanceOfType v ty₁ ∨ InstanceOfType v ty₂) :
  InstanceOfType v ty
:= by
  cases h₂ <;> rename_i h₃
  · exact instance_of_lub_left h₁ h₃
  · rw [lub_comm] at h₁
    exact instance_of_lub_left h₁ h₃

theorem request_leveled_instance_implies_instance {request : Request} {reqty : RequestType} {l : Level} :
  InstanceOfRequestTypeLevel request reqty l →
  InstanceOfRequestType request reqty
  := by
  intros h
  unfold InstanceOfRequestType
  unfold InstanceOfRequestTypeLevel at h
  simp [h]

theorem request_and_entity_match_level_implies_regular {env : Environment} {request : Request} {entities : Entities} {l : Level} :
  RequestAndEntitiesMatchEnvironmentLeveled env request entities l →
  RequestAndEntitiesMatchEnvironment env request entities
  := by
  intros h
  unfold RequestAndEntitiesMatchEnvironment
  unfold RequestAndEntitiesMatchEnvironmentLeveled at h
  simp [h]
  apply request_leveled_instance_implies_instance
  have ⟨h₁, _⟩ := h
  apply h₁



end Cedar.Thm

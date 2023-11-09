/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Thm.Lemmas.Std
import Cedar.Validation

/-!
This file contains useful definitions and lemmas about Cedar types.

todo: fill in `sorry`s.
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
  | instance_of_entity (e : EntityUID) (ety: EntityType)
      (h₁ : InstanceOfEntityType e ety) :
      InstanceOfType (.prim (.entityUID e)) (.entity ety)
  | instance_of_set (s : Set Value) (ty : CedarType)
      (h₁ : forall v, v ∈ s → InstanceOfType v ty) :
      InstanceOfType (.set s) (.set ty)
  | instance_of_record (r : Map Attr Value) (rty : RecordType)
      -- if an attribute is present, then it has the expected type
      (h₁ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
        rty.find? k = some qty → r.find? k = some v → InstanceOfType v qty.getType)
      -- required attributes are present
      (h₂ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      InstanceOfType (.record r) (.record rty)
  | instance_of_ext (x : Ext) (xty : ExtType)
      (h₁ : InstanceOfExtType x xty) :
      InstanceOfType (.ext x) (.ext xty)

def InstanceOfRequestType (request : Request) (reqty : RequestType) : Prop :=
  InstanceOfEntityType request.principal reqty.principal ∧
  request.action = reqty.action ∧
  InstanceOfEntityType request.resource reqty.resource ∧
  InstanceOfType request.context (.record reqty.context)

/--
For every entity in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
-/
def InstanceOfEntityTypeStore (entities : Entities) (ets: EntityTypeStore) : Prop :=
  ∀ uid data, entities.find? uid = some data →
    ∃ attrTys ancestorTys, ets.find? uid.ty = some (attrTys, ancestorTys) ∧
      InstanceOfType data.attrs (.record attrTys) ∧
      ∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ ancestorTys

/--
For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
def InstanceOfActionStore (entities : Entities) (as: ActionStore) : Prop :=
  ∀ uid data, entities.find? uid = some data → as.contains uid →
    ∃ ancestors, as.find? uid = some ancestors →
      ∀ ancestor, ancestor ∈ data.ancestors → ancestor ∈ ancestors

def RequestAndEntitiesMatchEnvironment (env : Environment) (request : Request) (entities : Entities) : Prop :=
  InstanceOfRequestType request env.reqty ∧
  InstanceOfEntityTypeStore entities env.ets ∧
  InstanceOfActionStore entities env.acts

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
:= by
  intro h₁
  cases h₁ with
  | instance_of_bool b _ h₁ =>
    apply Exists.intro b
    rfl

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
  case tt => apply Exists.intro true; simp only
  all_goals {
    apply Exists.intro false; simp only
  }

theorem entity_type_is_inhabited (ety : EntityType) :
  ∃ euid, InstanceOfEntityType euid ety
:= by
  simp [InstanceOfEntityType]
  apply Exists.intro (EntityUID.mk ety default)
  simp only

theorem ext_type_is_inhabited (xty : ExtType) :
  ∃ x, InstanceOfExtType x xty
:= by
  simp [InstanceOfExtType]
  cases xty
  case ipAddr =>
    apply Exists.intro (Ext.ipaddr (default : IPAddr))
    simp only
  case decimal =>
    apply Exists.intro (Ext.decimal (default : Ext.Decimal))
    simp only

mutual
theorem type_is_inhabited (ty : CedarType) :
  ∃ v, InstanceOfType v ty
:= by
  match ty with
  | .bool bty =>
    rcases (bool_type_is_inhabited bty) with ⟨b, h₁⟩
    apply Exists.intro (.prim (.bool b))
    apply InstanceOfType.instance_of_bool _ _ h₁
  | .int =>
    apply Exists.intro (.prim (.int default))
    apply InstanceOfType.instance_of_int
  | .string =>
    apply Exists.intro (.prim (.string default))
    apply InstanceOfType.instance_of_string
  | .entity ety =>
    rcases (entity_type_is_inhabited ety) with ⟨euid, h₁⟩
    apply Exists.intro (.prim (.entityUID euid))
    apply InstanceOfType.instance_of_entity _ _ h₁
  | .set ty₁ =>
    apply Exists.intro (.set Set.empty)
    apply InstanceOfType.instance_of_set
    intro v₁ h₁
    rcases (Set.in_set_means_list_non_empty v₁ Set.empty h₁) with h₂
    simp [Set.empty] at h₂
  | .ext xty =>
    rcases (ext_type_is_inhabited xty) with ⟨x, h₁⟩
    apply Exists.intro (.ext x)
    apply InstanceOfType.instance_of_ext _ _ h₁
  | .record rty =>
    rcases (record_type_is_inhabited rty) with ⟨r, h₁, h₂⟩
    apply Exists.intro (.record r)
    apply InstanceOfType.instance_of_record _ _ h₁ h₂

theorem record_type_is_inhabited (rty : RecordType) :
  ∃ (r : Map Attr Value),
    (∀ (k : Attr) (v : Value) (qty : QualifiedType),
      rty.find? k = some qty → r.find? k = some v → InstanceOfType v qty.getType) ∧
    (∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k)
:= by sorry

end

end Cedar.Thm

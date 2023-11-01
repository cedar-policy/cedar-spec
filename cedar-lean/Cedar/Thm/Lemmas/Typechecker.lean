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
import Cedar.Validation

/-!
This file contains useful definitions and lemmas about the `Typechecker` functions.

todo: fill in `sorry`s. Some invariants may need to be adjusted. The current
definitions are an informed guess based on the corresponding Dafny proof.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

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
3. The entity's ancestors' types are defined in the type store, and the ancestor
   relationship is consistent with the descendants information in the type store.
-/
def InstanceOfEntityTypeStore (entities : Entities) (ets: EntityTypeStore) : Prop :=
  ∀ uid data, entities.find? uid = some data →
    ∃ attrTys descendantTys, ets.find? uid.ty = some (attrTys, descendantTys) ∧
      InstanceOfType data.attrs (.record attrTys) ∧
      ∀ ancestor, ancestor ∈ data.ancestors →
        ∃ descendants, ets.find? ancestor.ty = some descendants ∧ uid.ty ∈ descendantTys

/--
For every action in the entity store, the action's ancestors are defined in the
action store, and the ancestor relationships in the entity store are consistent
with the descendants information in the action store.
-/
def InstanceOfActionStore (entities : Entities) (as: ActionStore) : Prop :=
  ∀ uid data, entities.find? uid = some data → isAction uid as →
    ∀ ancestor, ancestor ∈ data.ancestors →
      ∃ descendants, as.find? ancestor = some descendants ∧ uid ∈ descendants

def RequestAndEntitiesMatchEnvironment (env : Environment) (request : Request) (entities : Entities) : Prop :=
  InstanceOfRequestType request env.reqty ∧
  InstanceOfEntityTypeStore entities env.ets ∧
  InstanceOfActionStore entities env.acts

/--
The type soundness property says that if the typechecker assigns a type to an
expression, then it must be the case that the expression `EvaluatesTo` a value
of that type. The `EvaluatesTo` predicate covers the (obvious) case where evaluation
has no errors, but it also allows for errors of type `entityDoesNotExist` and
`extensionError`.

The typechecker cannot protect against these errors because they depend on runtime
information (i.e., the entities passed into the authorization request, and
extension function applications on authorization-time data). All other errors
(`attrDoesNotExist` and `typeError`) can be prevented statically.

_Note_: Currently, `extensionError`s can also be ruled out at validation time
because the only extension functions that can error are constructors, and all
constructors are required to be applied to string literals, meaning that they
can be fully evaluated during validation. This is not guaranteed to be the case
in the future.
-/
def EvaluatesTo (e: Expr) (request : Request) (entities : Entities) (v : Value) : Prop :=
  evaluate e request entities = .error .entityDoesNotExist ∨
  evaluate e request entities = .error .extensionError ∨
  evaluate e request entities = .ok v

/--
On input to the typechecking function, for any (e,k) in the Capabilities,
e is a record- or entity-typed expression that has key k.
-/
def CapabilitiesInvariant (c : Capabilities) (request : Request) (entities : Entities) : Prop :=
  ∀ (e : Expr) (k : Attr), (e, k) ∈ c → EvaluatesTo (.hasAttr e k) request entities true

/--
The Capabilities output by the typechecking function will satisfy
`CapabilitiesInvariant` provided that the input expression evaluates to true.
-/
def GuardedCapabilitiesInvariant (e: Expr) (c: Capabilities) (request : Request) (entities : Entities) : Prop :=
  evaluate e request entities = .ok true →
  CapabilitiesInvariant c request entities

-- Easy property: the empty capability set satisifies the invariant
theorem empty_CapabilitiesInvariant (request : Request) (entities : Entities) :
  CapabilitiesInvariant ∅ request entities
:= by
  intro e k h
  contradiction

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

/--
If an expression is well-typed according to the typechecker, and the input
environment and capabilities satisfy some invariants, then either (1) evaluation
produces a value of the returned type or (2) it returns an error of type
`entityDoesNotExist` or `extensionError`. Both options are encoded in the
`EvaluatesTo` predicate.
-/
theorem typeOf_is_sound (e : Expr) (c₁ c₂ : Capabilities) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (t, c₂) →
  GuardedCapabilitiesInvariant e c₂ request entities ∧
  ∃ (v : Value), EvaluatesTo e request entities v ∧ InstanceOfType v t
:= by
  sorry

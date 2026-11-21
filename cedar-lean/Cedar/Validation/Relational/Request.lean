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

public import Cedar.Validation.Relational.WellFormed
public import Cedar.Validation.RequestEntityValidator

@[expose] public section

/-! # Relational specification of request validation

`ValidRequest schema req` holds when `validateRequest` accepts `req`. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Values as instances of types (`instanceOfType`) -/

/-- `instanceOfBoolType`. -/
inductive InstanceOfBoolType : Bool → BoolType → Prop where
  | tt : InstanceOfBoolType true .tt
  | ff : InstanceOfBoolType false .ff
  | anyBool : ∀ b, InstanceOfBoolType b .anyBool

/-- `instanceOfExtType`. -/
inductive InstanceOfExtType : Ext → ExtType → Prop where
  | decimal : ∀ d, InstanceOfExtType (.decimal d) .decimal
  | ipaddr : ∀ ip, InstanceOfExtType (.ipaddr ip) .ipAddr
  | datetime : ∀ dt, InstanceOfExtType (.datetime dt) .datetime
  | duration : ∀ dur, InstanceOfExtType (.duration dur) .duration

/-- Every required attribute of a record type is present in the record value's attributes
    `avs` (the third conjunct of `instanceOfType` on records). -/
inductive RequiredAttrsPresent : List (Attr × Value) → List (Attr × QualifiedType) → Prop where
  | nil : ∀ avs, RequiredAttrsPresent avs []
  | optional : ∀ avs a ty rty, RequiredAttrsPresent avs rty →
      RequiredAttrsPresent avs ((a, .optional ty) :: rty)
  | required : ∀ avs a v ty rty, MapContains a v (.mk avs) → RequiredAttrsPresent avs rty →
      RequiredAttrsPresent avs ((a, .required ty) :: rty)

mutual
/-- `instanceOfType v ty ⟨ets, acts⟩`. -/
inductive InstanceOfType : EntitySchema → ActionSchema → Value → CedarType → Prop where
  | bool : ∀ ets acts b bty, InstanceOfBoolType b bty →
      InstanceOfType ets acts (.prim (.bool b)) (.bool bty)
  | int : ∀ ets acts i, InstanceOfType ets acts (.prim (.int i)) .int
  | string : ∀ ets acts s, InstanceOfType ets acts (.prim (.string s)) .string
  | entity : ∀ ets acts ety eid, ValidEntityUID ety eid ets acts →
      InstanceOfType ets acts (.prim (.entityUID ⟨ety, eid⟩)) (.entity ety)
  | set : ∀ ets acts vs ty, InstanceOfTypeList ets acts vs ty →
      InstanceOfType ets acts (.set (.mk vs)) (.set ty)
  | record : ∀ ets acts avs rty, InstanceOfRecordEntries ets acts avs rty →
      RequiredAttrsPresent avs rty →
      InstanceOfType ets acts (.record (.mk avs)) (.record (.mk rty))
  | ext : ∀ ets acts x xty, InstanceOfExtType x xty → InstanceOfType ets acts (.ext x) (.ext xty)

/-- Every element of a set value is an instance of the element type. -/
inductive InstanceOfTypeList : EntitySchema → ActionSchema → List Value → CedarType → Prop where
  | nil : ∀ ets acts ty, InstanceOfTypeList ets acts [] ty
  | cons : ∀ ets acts v vs ty, InstanceOfType ets acts v ty → InstanceOfTypeList ets acts vs ty →
      InstanceOfTypeList ets acts (v :: vs) ty

/-- Every attribute of a record value is declared by the record type `rty`, with a value of
    the declared type (the first two conjuncts of `instanceOfType` on records). -/
inductive InstanceOfRecordEntries : EntitySchema → ActionSchema → List (Attr × Value) →
    List (Attr × QualifiedType) → Prop where
  | nil : ∀ ets acts rty, InstanceOfRecordEntries ets acts [] rty
  | cons : ∀ ets acts a v avs qty rty, MapContains a qty (.mk rty) →
      InstanceOfType ets acts v qty.getType → InstanceOfRecordEntries ets acts avs rty →
      InstanceOfRecordEntries ets acts ((a, v) :: avs) rty
end

/-! ## Requests -/

/-- `instanceOfRequestType req env`: the principal and resource are valid entities of the
    request type's principal and resource types, the action is the request type's action, and
    the context is an instance of its context type. -/
inductive InstanceOfRequestType : TypeEnv → Request → Prop where
  | mk : ∀ ets acts pty peid act rty reid ctx ctxty,
      ValidEntityUID pty peid ets acts →
      ValidEntityUID rty reid ets acts →
      InstanceOfType ets acts (.record ctx) (.record ctxty) →
      InstanceOfRequestType ⟨ets, acts, ⟨pty, act, rty, ctxty⟩⟩ ⟨⟨pty, peid⟩, act, ⟨rty, reid⟩, ctx⟩

/-- `validateRequest schema req` succeeds: `req` is an instance of the request type of some
    environment of `schema`. -/
inductive ValidRequest : Schema → Request → Prop where
  | mk : ∀ schema env req, SchemaEnvironment schema env → InstanceOfRequestType env req →
      ValidRequest schema req

end Cedar.Validation.Relational

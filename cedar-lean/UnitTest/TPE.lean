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

import Cedar.TPE.Evaluator
import Cedar.Spec.Expr
import Cedar.Validation.Types
import Cedar.Data.Map

namespace UnitTest.TPE.Basic

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-
entity User;

entity Document  = {
  "isPublic": Bool,
  "owner": User
};

action View appliesTo {
  principal: [User],
  resource: [Document],
  context: {
    "hasMFA": Bool,
  }
};

action Delete appliesTo {
  principal: [User],
  resource: [Document],
  context: {
    "hasMFA": Bool,
    "srcIP": ipaddr
  }
};
-/

def ActionType : EntityType :=
  ⟨"Action", []⟩

def UserType : EntityType :=
  ⟨"User", []⟩

def DocumentType : EntityType :=
  ⟨"Document", []⟩

def schema : Schema :=
  ⟨Map.mk [
  (
     ActionType,
     .standard ⟨default, default, default⟩
  ),
  (
     UserType,
     .standard ⟨default, default, default⟩
  ),
  (
     DocumentType,
     .standard ⟨
          default,
          Map.mk [
               ("isPublic", (.required (.bool .anyBool))),
               ("owner", (.required (.entity UserType)))
          ],
          default⟩
  )
  ],
  Map.mk [
     (⟨ActionType, "View"⟩, ⟨
          Set.mk [UserType],
          Set.mk [DocumentType],
          default,
          Map.mk [("hasMFA", (.required (.bool .anyBool)))]
      ⟩),
      (⟨ActionType, "Delete"⟩, ⟨
          Set.mk [UserType],
          Set.mk [DocumentType],
          default,
          Map.mk [
               ("hasMFA", (.required (.bool .anyBool))),
               ("srcIP", (.required (.ext .ipAddr)))]
      ⟩)
  ]⟩

/-
// Users can view public documents.
permit (
  principal,
  action == Action::"View",
  resource
) when {
  resource.isPublic
};
-/

def policy₁ : Policy :=
  ⟨ "1",
  .permit,
  .principalScope .any,
  .actionScope (.eq ⟨ActionType, "View"⟩),
  .resourceScope .any,
  [
     ⟨.when,
     (.getAttr (.var .resource) "isPublic")⟩
  ]⟩

/-
// Users can view owned documents if they are mfa-authenticated.
permit (
  principal,
  action == Action::"View",
  resource
) when {
  context.hasMFA &&
  resource.owner == principal
};
-/

def policy₂ : Policy :=
  ⟨ "2",
  .permit,
  .principalScope .any,
  .actionScope (.eq ⟨ActionType, "View"⟩),
  .resourceScope .any,
  [
     ⟨.when,
     (.and
       (.getAttr (.var .context) "hasMFA")
       (.binaryApp .eq (.getAttr (.var .resource) "owner") (.var .principal))
       )⟩
  ]⟩

/-
// Users can delete owned documents if they are mfa-authenticated
// and on the company network.
permit (
  principal,
  action == Action::"Delete",
  resource
) when {
  context.hasMFA &&
  resource.owner == principal &&
  context.srcIP.isInRange(ip("1.1.1.0/24"))
};
-/

def policy₃ : Policy :=
  ⟨ "2",
  .permit,
  .principalScope .any,
  .actionScope (.eq ⟨ActionType, "Delete"⟩),
  .resourceScope .any,
  [
     ⟨.when,
     (.and
       (.getAttr (.var .context) "hasMFA")
       (.binaryApp .eq (.getAttr (.var .resource) "owner") (.var .principal))
       )⟩
  ]⟩

/-
// Typed partial request, with an unknown resource of type Document.
// In this example syntax, we omit the `id` field of the `resource`
// paramater to indicate that it is unknown.
{
    "principal": { "type": "User", "id": "Alice" },
    "action":    { "type": "Action", "id": "View" },
    "resource":  { "type": "Document" },
    "context":   { "hasMFA": true }
}

// Entity data for Alice.
[
  {
    "uid": { "type": "User", "id": "Alice" },
    "attrs": { },
    "parents": [ ]
  }
]
-/

def req : PartialRequest :=
  ⟨
     ⟨UserType, "Alice"⟩,
     ⟨ActionType, "View"⟩,
     ⟨DocumentType, default⟩,
     .some $ Map.mk [("hasMFA", true)]
  ⟩

def es : PartialEntities :=
  Map.mk [
     (⟨ActionType, "View"⟩, ⟨.some default, .some default, .some default⟩),
     (⟨ActionType, "Delete"⟩, ⟨.some default, .some default, .some default⟩),
     (⟨UserType, "Alice"⟩, ⟨.some default, .some default, default⟩)
  ]

#eval (tpePolicy schema policy₁ req es)
#eval (tpePolicy schema policy₂ req es)
#eval (tpePolicy schema policy₃ req es)

end UnitTest.TPE.Basic

namespace UnitTest.TPE.Motivation

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-
// Schema
type Address = {
   street: String,
   zip?: String,
};

entity User {
  address: Address
};

entity Package {
  address: Address
};

action PickUp appliesTo {
  principal: [User],
  resource: [Package],
  context: {}
};
-/
def ActionType : EntityType :=
  ⟨"Action", []⟩

def AddressType : RecordType :=
  Map.mk [
     ("street", (.required .string)),
     ("zip", (.optional .string))
  ]

def UserType : EntityType :=
  ⟨"User", []⟩

def PackageType : EntityType :=
  ⟨"Package", []⟩

def schema : Schema :=
  ⟨Map.mk [
  (
     ActionType,
     .standard ⟨default, default, default⟩
  ),
  (
     UserType,
     .standard ⟨
          default,
          Map.mk [
               ("address", (.required (.record AddressType)))
          ],
          default⟩
  ),
    (
     PackageType,
     .standard ⟨
          default,
          Map.mk [
               ("address", (.required (.record AddressType)))
          ],
          default⟩
  ),
  ],
  Map.mk [
     (⟨ActionType, "PickUp"⟩, ⟨
          Set.mk [UserType],
          Set.mk [PackageType],
          default,
          default
      ⟩)
  ]⟩

/-
// Policy
permit(principal, action == Action::"PickUp", resource)
when {
  principal.address == resource.address
}
-/

def policy : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope (.eq ⟨ActionType, "PickUp"⟩),
  .resourceScope .any,
  [
     ⟨.when,
       (.binaryApp .eq
       (.getAttr (.var .principal) "address")
       (.getAttr (.var .resource) "address"))⟩
  ]⟩

/-
* principal is User::"Alice" with the address of { "street": "Sesame Street"},
* action is Action::"PickUp, and
* resource is unknown("pkg").
-/

def req : PartialRequest :=
  ⟨
     ⟨UserType, "Alice"⟩,
     ⟨ActionType, "PickUp"⟩,
     ⟨PackageType, default⟩,
     .some $ default
  ⟩

def es : PartialEntities :=
  Map.mk [
     (⟨ActionType, "PickUp"⟩, ⟨.some default, .some default, .some default⟩),
     (⟨UserType, "Alice"⟩, ⟨.some $ Map.mk [("address", .record $ Map.mk [("street", "Sesame Street")])], .some default, default⟩)
  ]

#eval tpePolicy schema policy req es
end UnitTest.TPE.Motivation

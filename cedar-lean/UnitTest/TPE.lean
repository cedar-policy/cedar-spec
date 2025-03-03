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
import UnitTest.Run

namespace UnitTest.TPE

open Cedar.Spec
open Cedar.TPE
open Cedar.Validation

def ActionType : EntityType := ⟨"Action", []⟩

def testResult (p : Policy) (schema : Schema) (req : PartialRequest) (es : PartialEntities) (r : Residual) : TestCase IO :=
  test s!"policy {p.id}" ⟨λ _ => checkEq (evaluatePolicy schema p req es) (.ok r)⟩

namespace UnitTest.TPE.Basic

open Cedar.Spec
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

def UserType : EntityType :=
  ⟨"User", []⟩

def DocumentType : EntityType :=
  ⟨"Document", []⟩

def schema : Schema :=
  ⟨Map.make [
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
          Map.make [
               ("isPublic", (.required (.bool .anyBool))),
               ("owner", (.required (.entity UserType)))
          ],
          default⟩
  )
  ],
  Map.make [
     (⟨ActionType, "View"⟩, ⟨
          Set.singleton UserType,
          Set.singleton DocumentType,
          default,
          Map.make [("hasMFA", (.required (.bool .anyBool)))]
      ⟩),
      (⟨ActionType, "Delete"⟩, ⟨
          Set.singleton UserType,
          Set.singleton DocumentType,
          default,
          Map.make [
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
     .some $ Map.make [("hasMFA", true)]
  ⟩

def es : PartialEntities :=
  Map.make [
     (⟨ActionType, "View"⟩, ⟨.some default, .some default, .some default⟩),
     (⟨ActionType, "Delete"⟩, ⟨.some default, .some default, .some default⟩),
     (⟨UserType, "Alice"⟩, ⟨.some default, .some default, default⟩)
  ]

def tests :=
  suite "TPE results for the RFC basic example"
  [
    testResult policy₁ schema req es
      (.getAttr (.var .resource (.entity { id := "Document", path := [] }))
        "isPublic"
      (.bool .anyBool)),
    testResult policy₂ schema req es
      (.binaryApp
        .eq
        (.getAttr
          (.var .resource (.entity { id := "Document", path := [] }))
          "owner"
          (.entity { id := "User", path := [] }))
          (.val
            (.prim (.entityUID { ty := { id := "User", path := [] }, eid := "Alice" }))
            (.entity { id := "User", path := [] }))
        (.bool .anyBool)),
    testResult policy₃ schema req es (.val false (.bool .ff))
  ]
--#eval TestSuite.runAll [tests]

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

def AddressType : RecordType :=
  Map.make [
     ("street", (.required .string)),
     ("zip", (.optional .string))
  ]

def UserType : EntityType :=
  ⟨"User", []⟩

def PackageType : EntityType :=
  ⟨"Package", []⟩

def schema : Schema :=
  ⟨Map.make [
  (
     ActionType,
     .standard ⟨default, default, default⟩
  ),
  (
     UserType,
     .standard ⟨
          default,
          Map.make [
               ("address", (.required (.record AddressType)))
          ],
          default⟩
  ),
    (
     PackageType,
     .standard ⟨
          default,
          Map.make [
               ("address", (.required (.record AddressType)))
          ],
          default⟩
  ),
  ],
  Map.make [
     (⟨ActionType, "PickUp"⟩, ⟨
          Set.singleton UserType,
          Set.singleton PackageType,
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
  Map.make [
     (⟨ActionType, "PickUp"⟩, ⟨.some default, .some default, .some default⟩),
     (⟨UserType, "Alice"⟩, ⟨.some $ Map.make [("address", .record $ Map.make [("street", "Sesame Street")])], .some default, default⟩)
  ]

def tests :=
  suite "TPE results for the RFC basic example"
  [
    testResult policy schema req es
      (.binaryApp
        .eq
        (.val
          (.record
            (Map.mk [("street", .prim (.string "Sesame Street"))]))
          (.record AddressType))
        (.getAttr
          (.var
            .resource
            (.entity { id := "Package", path := [] }))
          "address"
          (.record AddressType))
      (.bool .anyBool))
  ]
-- #eval TestSuite.runAll [tests]

end UnitTest.TPE.Motivation

namespace UnitTest.TPE.Spec
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data


def schema : Schema :=
  ⟨Map.make [
  (
     ActionType,
     .standard ⟨default, default, default⟩
  ),
  (
     ⟨"A0", []⟩,
     .standard ⟨
          Set.singleton ⟨"A1", []⟩,
          default,
          default⟩
  ),
  (
     ⟨"A1", []⟩,
     .standard ⟨
          default,
          default,
          default⟩
  ),
  ],
  Map.make [
     (⟨ActionType, "a"⟩, ⟨
          Set.singleton ⟨"A0", []⟩,
          Set.singleton ⟨"A1", []⟩,
          default,
          default
      ⟩)
  ]⟩

def es : PartialEntities :=
  Map.make [
     (⟨ActionType, "a"⟩, ⟨.some default, .some default, .some default⟩),
  ]

def req : PartialRequest :=
  ⟨
     ⟨⟨"A0", []⟩, "a0"⟩,
     ⟨ActionType, "a"⟩,
     ⟨⟨"A1", []⟩, "a1"⟩,
     default
  ⟩

def policy₀ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.binaryApp .mem (.var .principal) (.lit (.entityUID ⟨⟨"A0", []⟩, "a0"⟩)))⟩
  ]⟩

def policy₁ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.binaryApp .mem (.var .principal) (.lit (.entityUID ⟨⟨"A0", []⟩, "a00"⟩)))⟩
  ]⟩

def policy₂ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.binaryApp .mem
        (.var .principal)
        (.ite
          (.binaryApp .less (.binaryApp .add (.lit (.int 1)) (.lit (.int 2))) (.lit (.int 5)))
          (.lit (.entityUID ⟨⟨"A0", []⟩, "a0"⟩))
          (.lit (.entityUID ⟨⟨"A0", []⟩, "a00"⟩))
          ))⟩
  ]⟩

def policy₃ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.binaryApp .mem
        (.var .principal)
        (.ite
          (.binaryApp .less (.binaryApp .add (.lit (.int 1)) (.lit (.int 6))) (.lit (.int 5)))
          (.lit (.entityUID ⟨⟨"A0", []⟩, "a0"⟩))
          (.lit (.entityUID ⟨⟨"A0", []⟩, "a00"⟩))
          ))⟩
  ]⟩

def policy₄ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.binaryApp .mem
        (.var .principal)
        (.ite
          (.binaryApp .less (.binaryApp .mul (.lit (.int 9223372036854775807)) (.lit (.int 9223372036854775807))) (.lit (.int 5)))
          (.lit (.entityUID ⟨⟨"A0", []⟩, "a0"⟩))
          (.lit (.entityUID ⟨⟨"A0", []⟩, "a00"⟩))
          ))⟩
  ]⟩

def policy₅ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.and
        (.ite
          (.binaryApp .less (.binaryApp .mul (.lit (.int 9223372036854775807)) (.lit (.int 9223372036854775807))) (.lit (.int 5)))
          (.lit (.bool true))
          (.lit (.bool false))
          )
        (.lit (.bool false)))⟩
  ]⟩

  def policy₆ : Policy :=
  ⟨ "0",
  .permit,
  .principalScope .any,
  .actionScope .any,
  .resourceScope .any,
  [
     ⟨.when,
       (.or
        (.binaryApp .eq
        (.var .principal)
        (.lit (.entityUID ⟨⟨"A0", []⟩, "a00"⟩)))
        (.ite
          (.binaryApp .less (.binaryApp .mul (.lit (.int 9223372036854775807)) (.lit (.int 9223372036854775807))) (.lit (.int 5)))
          (.lit (.bool true))
          (.lit (.bool false))
          )
        )⟩
  ]⟩

def tests :=
  suite "TPE results for the RFC basic example"
  [
    -- x in x -> true
    testResult policy₀ schema req es
    (.val (.prim (.bool true)) (.bool .tt)),
    -- A0::"a0" (LHS) does not exist in the entities and hence is unknown
    testResult policy₁ schema req es
    (.binaryApp .mem
      (.val
        (.prim (.entityUID { ty := { id := "A0", path := [] }, eid := "a0" }))
        (.entity { id := "A0", path := [] }))
      (.val
        (.prim (.entityUID { ty := { id := "A0", path := [] }, eid := "a00" }))
        (.entity { id := "A0", path := [] }))
    (.bool .anyBool)),
    -- A0::"a0" in (if (1 + 2) < 5 then A0::"a0" else A0::"a00")
    testResult policy₂ schema req es
    (.val (.prim (.bool true)) (.bool (.tt))),
    -- A0::"a0" in (if (1 + 6) < 5 then A0::"a0" else A0::"a00")
    testResult policy₃ schema req es
    (.binaryApp .mem
      (.val
        (.prim (.entityUID { ty := { id := "A0", path := [] }, eid := "a0" }))
        (.entity { id := "A0", path := [] }))
      (.val
        (.prim (.entityUID { ty := { id := "A0", path := [] }, eid := "a00" }))
        (.entity { id := "A0", path := [] }))
    (.bool .anyBool)),
    -- integer overflow happens in the condition of ite
    testResult policy₄ schema req es
    (.error (.bool .anyBool)),
    -- and x y -> false where x contains integer overflow
    testResult policy₅ schema req es
    (.error (.bool .ff)),
    -- or x y -> error where x is false and y contains integer overflow
    testResult policy₆ schema req es
    (.error (.bool .anyBool)),
  ]

#eval TestSuite.runAll [tests]
end UnitTest.TPE.Spec

open UnitTest.TPE

def tests := [Basic.tests, Motivation.tests, Spec.tests]

end UnitTest.TPE

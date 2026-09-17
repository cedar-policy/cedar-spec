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
    testResult policy₃ schema req es (.val false (.bool .anyBool))
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
    (.val (.prim (.bool true)) (.bool .anyBool)),
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
    (.val (.prim (.bool true)) (.bool .anyBool)),
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
    (.error (.bool .anyBool)),
    -- or x y -> error where x is false and y contains integer overflow
    testResult policy₆ schema req es
    (.error (.bool .anyBool)),
  ]

#eval TestSuite.runAll [tests]
end UnitTest.TPE.Spec

namespace UnitTest.TPE.ExtHasAttr

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-
// The schema allows testing for different alternations of entity-record in the attribute
// access chain (also with either record/entity type at the root)
// ---
// entity Leaf { value: String };
// entity Middle { info: { "tag": String }, next: Leaf };
// entity Root { child: Middle, data: { "inner": Middle } };
// entity User { profile: { "address": { "city": String } }, manager: Root };
// entity Document;
//
// action Do appliesTo {
//   principal: [User],
//   resource: [Document],
//   context: {
//     "ref": Root,
//     "nested": { "deep": { "leaf": String } },
//     "wrap": { "box": { "target": Middle } }
//   }
// };
-/

def LeafType     : EntityType := ⟨"Leaf", []⟩
def MiddleType   : EntityType := ⟨"Middle", []⟩
def RootType     : EntityType := ⟨"Root", []⟩
def UserType     : EntityType := ⟨"User", []⟩
def DocumentType : EntityType := ⟨"Document", []⟩

def infoRecordType : RecordType :=
  Map.make [("tag", (.required .string))]

def deepRecordType : RecordType :=
  Map.make [("leaf", (.required .string))]

def nestedRecordType : RecordType :=
  Map.make [("deep", (.required (.record deepRecordType)))]

def boxRecordType : RecordType :=
  Map.make [("target", (.required (.entity MiddleType)))]

def wrapRecordType : RecordType :=
  Map.make [("box", (.required (.record boxRecordType)))]

def dataRecordType : RecordType :=
  Map.make [("inner", (.required (.entity MiddleType)))]

def addressRecordType : RecordType :=
  Map.make [("city", (.required .string))]

def profileRecordType : RecordType :=
  Map.make [("address", (.required (.record addressRecordType)))]

def schema : Schema :=
  ⟨Map.make [
    (ActionType, .standard ⟨default, default, default⟩),
    (LeafType, .standard ⟨default, Map.make [("value", (.required .string))], default⟩),
    (MiddleType, .standard ⟨default, Map.make [
      ("info", (.required (.record infoRecordType))),
      ("next", (.required (.entity LeafType)))
    ], default⟩),
    (RootType, .standard ⟨default, Map.make [
      ("child", (.required (.entity MiddleType))),
      ("data", (.required (.record dataRecordType)))
    ], default⟩),
    (UserType, .standard ⟨default, Map.make [
      ("profile", (.required (.record profileRecordType))),
      ("manager", (.required (.entity RootType)))
    ], default⟩),
    (DocumentType, .standard ⟨default, default, default⟩)
  ],
  Map.make [
    (⟨ActionType, "Do"⟩, ⟨
      Set.singleton UserType,
      Set.singleton DocumentType,
      default,
      Map.make [
        ("ref", (.required (.entity RootType))),
        ("nested", (.required (.record nestedRecordType))),
        ("wrap", (.required (.record wrapRecordType)))
      ]
    ⟩)
  ]⟩

/-
Entities:
  User::"alice"  → { profile: {address: {city: "Seattle"}}, manager: Root::"r1" }
  Root::"r1"     → { child: Middle::"m1", data: {inner: Middle::"m2"} }
  Middle::"m1"   → { info: {tag: "hello"}, next: Leaf::"l1" }
  Leaf::"l1"     → { value: "world" }
  Middle::"m2"   — NOT in store (unknown)
-/
def es : PartialEntities :=
  Map.make [
    (⟨ActionType, "Do"⟩, ⟨.some default, .some default, .some default⟩),
    (⟨UserType, "alice"⟩, ⟨.some (Map.make [
      ("profile", .record (Map.make [("address", .record (Map.make [("city", .prim (.string "Seattle"))]))])),
      ("manager", .prim (.entityUID ⟨RootType, "r1"⟩))
    ]), .some default, default⟩),
    (⟨RootType, "r1"⟩, ⟨.some (Map.make [
      ("child", .prim (.entityUID ⟨MiddleType, "m1"⟩)),
      ("data", .record (Map.make [("inner", .prim (.entityUID ⟨MiddleType, "m2"⟩))]))
    ]), .some default, default⟩),
    (⟨MiddleType, "m1"⟩, ⟨.some (Map.make [
      ("info", .record (Map.make [("tag", .prim (.string "hello"))])),
      ("next", .prim (.entityUID ⟨LeafType, "l1"⟩))
    ]), .some default, default⟩),
    (⟨LeafType, "l1"⟩, ⟨.some (Map.make [
      ("value", .prim (.string "world"))
    ]), .some default, default⟩)
  ]

def req : PartialRequest :=
  ⟨
    ⟨UserType, "alice"⟩,
    ⟨ActionType, "Do"⟩,
    ⟨DocumentType, default⟩,
    .some $ Map.make [
      ("ref", .prim (.entityUID ⟨RootType, "r1"⟩)),
      ("nested", .record (Map.make [("deep", .record (Map.make [("leaf", .prim (.string "yes"))]))])),
      ("wrap", .record (Map.make [("box", .record (Map.make [("target", .prim (.entityUID ⟨MiddleType, "m1"⟩))]))]))
    ]
  ⟩

-- Basic tests

-- context has nested.deep.leaf ↝ true
def policyAllRecords : Policy :=
  ⟨ "all-records", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "nested" ["deep", "leaf"])⟩]⟩

-- context has nested.missing.leaf ↝ false (no "missing" in context.nested)
def policyMissing : Policy :=
  ⟨ "missing", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "nested" ["missing", "leaf"])⟩]⟩

-- context has ref ↝ true
def policySingle : Policy :=
  ⟨ "single", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "ref" [])⟩]⟩

/-
Residual tests: the chain hits Middle::"m2" which is not in the entity store,
so TPE produces a residual of the form `X has a` or `X has a.b...`.
-/

-- principal.manager has data.inner.info ↝ Middle::"m2" has info
-- Because: Root::"r1".data.inner = Middle::"m2" (unknown), can't check "info"
def policyResidualERE : Policy :=
  ⟨ "residual-E-R-E", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.getAttr (.var .principal) "manager") "data" ["inner", "info"])⟩]⟩

-- principal.manager has data.inner.next ↝ Middle::"m2" has next
-- Because: same path, different final attr on unknown entity
def policyResidualNext : Policy :=
  ⟨ "residual-next", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.getAttr (.var .principal) "manager") "data" ["inner", "next"])⟩]⟩

-- principal.manager has data.inner.next.value ↝ Middle::"m2" has next.value
-- Because: Middle::"m2" is unknown, remaining chain ["next", "value"] stays as residual
def policyResidualDeep : Policy :=
  ⟨ "residual-deep", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.getAttr (.var .principal) "manager") "data" ["inner", "next", "value"])⟩]⟩

-- principal has manager.child.next.value ↝ true
-- Because: all entities in chain are known, Leaf::"l1" has "value"
def policyResidualFullChain : Policy :=
  ⟨ "full-chain", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .principal) "manager" ["child", "next", "value"])⟩]⟩

-- context has wrap.box.target.next.value ↝ true
-- Because: all entities resolved, Leaf::"l1" has "value"
def policyResidualRRREE : Policy :=
  ⟨ "R-R-R-E-E", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "wrap" ["box", "target", "next", "value"])⟩]⟩

-- context has ref.child.next.value ↝ true
-- Because: Root::"r1" → Middle::"m1" → Leaf::"l1", all known, "value" present
def policyResidualREEE : Policy :=
  ⟨ "R-E-E-E", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "ref" ["child", "next", "value"])⟩]⟩

-- context has ref.child.next.missing ↝ false
-- Because: Leaf::"l1" is known but doesn't have "missing"
def policyResidualMissEnd : Policy :=
  ⟨ "miss-end", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "ref" ["child", "next", "missing"])⟩]⟩

-- Nesting pattern tests

-- context has ref.data.inner ↝ true (R-E-R: record → entity → record → check)
def policyRER : Policy :=
  ⟨ "R-E-R", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "ref" ["data", "inner"])⟩]⟩

-- context has wrap.box.target.info ↝ true (R-R-E: record → record → entity → check)
def policyRRE : Policy :=
  ⟨ "R-R-E", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .context) "wrap" ["box", "target", "info"])⟩]⟩

-- principal has manager.child.info.tag ↝ true (E-E-R: entity → entity → record → check)
def policyEER : Policy :=
  ⟨ "E-E-R", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.var .principal) "manager" ["child", "info", "tag"])⟩]⟩

def tests :=
  suite "TPE extHasAttr"
  [
    -- context has nested.deep.leaf ↝ true
    testResult policyAllRecords schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- context has nested.missing.leaf ↝ false
    testResult policyMissing schema req es
      (.val (.prim (.bool false)) (.bool .anyBool)),
    -- context has ref ↝ true
    testResult policySingle schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- principal.manager has data.inner.info ↝ Middle::"m2" has info
    testResult policyResidualERE schema req es
      (.extHasAttr
        (.val (.prim (.entityUID ⟨MiddleType, "m2"⟩)) (.entity MiddleType))
        "info" []
        (.bool .anyBool)),
    -- principal.manager has data.inner.next ↝ Middle::"m2" has next
    testResult policyResidualNext schema req es
      (.extHasAttr
        (.val (.prim (.entityUID ⟨MiddleType, "m2"⟩)) (.entity MiddleType))
        "next" []
        (.bool .anyBool)),
    -- principal.manager has data.inner.next.value ↝ Middle::"m2" has next.value
    testResult policyResidualDeep schema req es
      (.extHasAttr
        (.val (.prim (.entityUID ⟨MiddleType, "m2"⟩)) (.entity MiddleType))
        "next" ["value"]
        (.bool .anyBool)),
    -- principal has manager.child.next.value ↝ true
    testResult policyResidualFullChain schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- context has wrap.box.target.next.value ↝ true
    testResult policyResidualRRREE schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- context has ref.child.next.value ↝ true
    testResult policyResidualREEE schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- context has ref.child.next.missing ↝ false
    testResult policyResidualMissEnd schema req es
      (.val (.prim (.bool false)) (.bool .anyBool)),
    -- context has ref.data.inner ↝ true (R-E-R)
    testResult policyRER schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- context has wrap.box.target.info ↝ true (R-R-E)
    testResult policyRRE schema req es
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- principal has manager.child.info.tag ↝ true (E-E-R)
    testResult policyEER schema req es
      (.val (.prim (.bool true)) (.bool .anyBool))
  ]

#eval TestSuite.runAll [tests]

end UnitTest.TPE.ExtHasAttr

open UnitTest.TPE

def tests := [Basic.tests, Motivation.tests, Spec.tests, ExtHasAttr.tests]

end UnitTest.TPE

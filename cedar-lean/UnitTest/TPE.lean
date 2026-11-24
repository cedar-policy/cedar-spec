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
     .some $ Map.make [("hasMFA", .value true)]
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
     (⟨UserType, "Alice"⟩, ⟨.some $ Map.make [("address", .value (.record $ Map.make [("street", "Sesame Street")]))], .some default, default⟩)
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
      ("profile", .value (.record (Map.make [("address", .record (Map.make [("city", .prim (.string "Seattle"))]))]))),
      ("manager", .value (.prim (.entityUID ⟨RootType, "r1"⟩)))
    ]), .some default, default⟩),
    (⟨RootType, "r1"⟩, ⟨.some (Map.make [
      ("child", .value (.prim (.entityUID ⟨MiddleType, "m1"⟩))),
      ("data", .value (.record (Map.make [("inner", .prim (.entityUID ⟨MiddleType, "m2"⟩))])))
    ]), .some default, default⟩),
    (⟨MiddleType, "m1"⟩, ⟨.some (Map.make [
      ("info", .value (.record (Map.make [("tag", .prim (.string "hello"))]))),
      ("next", .value (.prim (.entityUID ⟨LeafType, "l1"⟩)))
    ]), .some default, default⟩),
    (⟨LeafType, "l1"⟩, ⟨.some (Map.make [
      ("value", .value (.prim (.string "world")))
    ]), .some default, default⟩)
  ]

def req : PartialRequest :=
  ⟨
    ⟨UserType, "alice"⟩,
    ⟨ActionType, "Do"⟩,
    ⟨DocumentType, default⟩,
    .some $ Map.make [
      ("ref", .value (.prim (.entityUID ⟨RootType, "r1"⟩))),
      ("nested", .value (.record (Map.make [("deep", .record (Map.make [("leaf", .prim (.string "yes"))]))]))),
      ("wrap", .value (.record (Map.make [("box", .record (Map.make [("target", .prim (.entityUID ⟨MiddleType, "m1"⟩))]))])))
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

-- principal.manager has data.inner.nope ↝ false
-- Because: Middle::"m2" is unknown, but the schema says `Middle` has no `nope`
def policySchemaReduced : Policy :=
  ⟨ "schema-reduced", .permit, .principalScope .any, .actionScope (.eq ⟨ActionType, "Do"⟩), .resourceScope .any,
  [⟨.when, (.extHasAttr (.getAttr (.var .principal) "manager") "data" ["inner", "nope"])⟩]⟩

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
      (.val (.prim (.bool true)) (.bool .anyBool)),
    -- principal.manager has data.inner.nope ↝ false, decided by the schema mid-chain
    testResult policySchemaReduced schema req es
      (.val (.prim (.bool false)) (.bool .anyBool))
  ]

#eval TestSuite.runAll [tests]

end UnitTest.TPE.ExtHasAttr

namespace UnitTest.TPE.SchemaInformed
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-!
Tests for the schema-informed reductions of `is`, `==`, `in`, and `hasTag`
-/

def A0 : EntityType := ⟨"A0", []⟩
def A1 : EntityType := ⟨"A1", []⟩

def schema : Schema :=
  ⟨Map.make [
    (ActionType, .standard ⟨default, default, default⟩),
    (A0, .standard ⟨Set.singleton A1, default, default⟩),
    (A1, .standard ⟨default, default, .some (.entity A0)⟩)
  ],
  Map.make [
    (⟨ActionType, "a"⟩, ⟨Set.singleton A0, Set.singleton A1, default, default⟩)
  ]⟩

def es : PartialEntities :=
  Map.make [(⟨ActionType, "a"⟩, ⟨.some default, .some default, .some default⟩)]

def req : PartialRequest :=
  ⟨⟨A0, default⟩, ⟨ActionType, "a"⟩, ⟨A1, default⟩, default⟩

def mkPolicy (x : Expr) : Policy :=
  ⟨"0", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, x⟩]⟩

def boolLit (b : Bool) : Residual := .val (.prim (.bool b)) (.bool .anyBool)

def tests :=
  suite "TPE schema-informed reduction of is/==/in/hasTag/has"
  [
    testResult (mkPolicy (.unaryApp (.is A0) (.var .principal))) schema req es
      (boolLit true),
    testResult (mkPolicy (.unaryApp (.is A1) (.var .principal))) schema req es
      (boolLit false),
    testResult (mkPolicy (.binaryApp .eq (.var .principal) (.var .resource))) schema req es
      (boolLit false),
    testResult (mkPolicy (.binaryApp .mem (.var .resource) (.var .principal))) schema req es
      (boolLit false),
    testResult (mkPolicy (.binaryApp .hasTag (.var .principal) (.lit (.string "x")))) schema req es
      (boolLit false),
    testResult (mkPolicy (.binaryApp .mem (.var .resource) (.set [.var .principal]))) schema req es
      (boolLit false),
    testResult (mkPolicy (.hasAttr (.var .principal) "x")) schema req es
      (boolLit false),
    -- the head of the chain is undeclared, so the whole chain is false
    testResult (mkPolicy (.extHasAttr (.var .principal) "x" ["y"])) schema req es
      (boolLit false),
  ]

end UnitTest.TPE.SchemaInformed

namespace UnitTest.TPE.AttrStates
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-!
Tests for the five attribute states. `E` has a required `req`, an optional `opt`,
and a required record `rec` with a required `inner`.
-/

def E : EntityType := ⟨"E", []⟩

def RecType : RecordType := Map.make [("inner", .required .string)]

def schema : Schema :=
  ⟨Map.make [
    (ActionType, .standard ⟨default, default, default⟩),
    (E, .standard ⟨default,
       Map.make [
         ("req", .required .string),
         ("opt", .optional .string),
         ("rec", .required (.record RecType))
       ],
       .some .string⟩)
  ],
  Map.make [
    (⟨ActionType, "a"⟩, ⟨Set.singleton E, Set.singleton E, default, default⟩)
  ]⟩

def req : PartialRequest :=
  ⟨⟨E, .some "p"⟩, ⟨ActionType, "a"⟩, ⟨E, default⟩, default⟩

/-- `E::"p"` states: `req` unknown (but declared required), `opt` explicitly
absent, `rec` a record we only partly know, and tag `t` present-but-unvalued. -/
def es : PartialEntities :=
  Map.make [
    (⟨ActionType, "a"⟩, ⟨.some default, .some default, .some default⟩),
    (⟨E, "p"⟩, ⟨
      .some (Map.make [
        ("opt", .absent),
        ("rec", .partialRecord (Map.make [("inner", .present)]))
      ]),
      .some default,
      .some (Map.make [("t", .present)])⟩)
  ]

/-- Like `es`, but `rec` is given in partial form yet fully determined: `inner`
has a known value, so the record folds to a concrete value. -/
def esDetermined : PartialEntities :=
  Map.make [
    (⟨ActionType, "a"⟩, ⟨.some default, .some default, .some default⟩),
    (⟨E, "p"⟩, ⟨
      .some (Map.make [
        ("opt", .absent),
        ("rec", .partialRecord (Map.make [("inner", .value (.prim (.string "v")))]))
      ]),
      .some default,
      .some default⟩)
  ]

def mkPolicy (x : Expr) : Policy :=
  ⟨"0", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, x⟩]⟩

def boolLit (b : Bool) : Residual := .val (.prim (.bool b)) (.bool .anyBool)

def principalE : Residual := .val (.prim (.entityUID ⟨E, "p"⟩)) (.entity E)

def tests :=
  suite "TPE attribute states: value/partialRecord/present/absent/unknown"
  [
    -- required-but-unmentioned is recovered as `present`, so `has` is `true`
    testResult (mkPolicy (.hasAttr (.var .principal) "req")) schema req es
      (boolLit true),
    -- explicitly absent, so `has` is `false`
    testResult (mkPolicy (.hasAttr (.var .principal) "opt")) schema req es
      (boolLit false),
    -- a partly-known record still asserts the attribute exists
    testResult (mkPolicy (.hasAttr (.var .principal) "rec")) schema req es
      (boolLit true),
    -- undeclared attributes cannot exist on a closed record type
    testResult (mkPolicy (.hasAttr (.var .principal) "bogus")) schema req es
      (boolLit false),
    -- a tag known to exist without a known value
    testResult (mkPolicy (.binaryApp .hasTag (.var .principal) (.lit (.string "t")))) schema req es
      (boolLit true),
    -- tags have no declared key set, so an unmentioned tag stays unknown
    testResult (mkPolicy (.binaryApp .hasTag (.var .principal) (.lit (.string "u")))) schema req es
      (.binaryApp .hasTag principalE (.val (.prim (.string "u")) .string) (.bool .anyBool)),
    -- the value is not known, so access stays a residual
    testResult (mkPolicy (.binaryApp .eq (.getAttr (.var .principal) "req") (.lit (.string "x"))))
      schema req es
      (.binaryApp .eq (.getAttr principalE "req" .string)
        (.val (.prim (.string "x")) .string) (.bool .anyBool)),
    -- an optional attribute must be guarded to typecheck, and the guard folding
    -- to `false` is what keeps the (erroring) access unreachable
    testResult (mkPolicy (.and (.hasAttr (.var .principal) "opt")
        (.binaryApp .eq (.getAttr (.var .principal) "opt") (.lit (.string "x")))))
      schema req es
      (boolLit false),

    -- Knowledge reaches *through* a partly-known record: `rec` is only partly
    -- known, but it does say `inner` exists.
    testResult (mkPolicy (.hasAttr (.getAttr (.var .principal) "rec") "inner")) schema req es
      (boolLit true),
    -- ... and that `bogus` cannot, since the nested record type is closed
    testResult (mkPolicy (.hasAttr (.getAttr (.var .principal) "rec") "bogus")) schema req es
      (boolLit false),
    -- the nested value itself is not known, so reading it stays a residual
    testResult (mkPolicy (.binaryApp .eq
        (.getAttr (.getAttr (.var .principal) "rec") "inner") (.lit (.string "x"))))
      schema req es
      (.binaryApp .eq
        (.getAttr (.getAttr principalE "rec" (.record RecType)) "inner" .string)
        (.val (.prim (.string "x")) .string) (.bool .anyBool)),

    -- Under conservative error-freedom an attribute access is treated as
    -- possibly-erroring even when the attribute is known to exist, so the
    -- `&& false` fold is blocked and the access is preserved.
    testResult (mkPolicy (.and
        (.binaryApp .eq (.getAttr (.var .principal) "req") (.lit (.string "x")))
        (.lit (.bool false))))
      schema req es
      (.and
        (.binaryApp .eq (.getAttr principalE "req" .string)
          (.val (.prim (.string "x")) .string) (.bool .anyBool))
        (.val (.prim (.bool false)) (.bool .anyBool)) (.bool .anyBool)),
    -- the same for a tag read: it is conservatively possibly-erroring, so the
    -- guarded access is preserved rather than folded away
    testResult (mkPolicy (.and
        (.and (.binaryApp .hasTag (.var .principal) (.lit (.string "t")))
          (.binaryApp .eq (.binaryApp .getTag (.var .principal) (.lit (.string "t")))
            (.lit (.string "x"))))
        (.lit (.bool false))))
      schema req es
      (.and
        (.binaryApp .eq
          (.binaryApp .getTag principalE (.val (.prim (.string "t")) .string) .string)
          (.val (.prim (.string "x")) .string) (.bool .anyBool))
        (.val (.prim (.bool false)) (.bool .anyBool)) (.bool .anyBool)),
    -- A nested record given in partial form but fully determined folds all the
    -- way to a concrete value.
    testResult (mkPolicy (.binaryApp .eq
        (.getAttr (.getAttr (.var .principal) "rec") "inner") (.lit (.string "v"))))
      schema req esDetermined
      (boolLit true),
    -- and the whole nested record folds too, so it can be compared as a value
    testResult (mkPolicy (.binaryApp .eq
        (.getAttr (.var .principal) "rec")
        (.record [("inner", .lit (.string "v"))])))
      schema req esDetermined
      (boolLit true),

    -- but an entity we have no data for at all leaves the access possibly
    -- erroring, so the fold is blocked
    testResult (mkPolicy (.and
        (.binaryApp .eq (.getAttr (.lit (.entityUID ⟨E, "q"⟩)) "req") (.lit (.string "x")))
        (.lit (.bool false))))
      schema req es
      (.and
        (.binaryApp .eq
          (.getAttr (.val (.prim (.entityUID ⟨E, "q"⟩)) (.entity E)) "req" .string)
          (.val (.prim (.string "x")) .string) (.bool .anyBool))
        (.val (.prim (.bool false)) (.bool .anyBool)) (.bool .anyBool)),
  ]

end UnitTest.TPE.AttrStates

namespace UnitTest.TPE.Context
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-!
Tests that partial knowledge of the *context* is reached through the same way
entity data is: `context.rec.inner` resolves from a partly-known context record.
-/

def E : EntityType := ⟨"E", []⟩

def RecType : RecordType := Map.make [("inner", .required .string), ("opt", .optional .string)]

def CtxType : RecordType :=
  Map.make [("rec", .required (.record RecType)), ("flag", .required (.bool .anyBool))]

def schema : Schema :=
  ⟨Map.make [
    (ActionType, .standard ⟨default, default, default⟩),
    (E, .standard ⟨default, default, default⟩)
  ],
  Map.make [
    (⟨ActionType, "a"⟩, ⟨Set.singleton E, Set.singleton E, default, CtxType⟩)
  ]⟩

def es : PartialEntities :=
  Map.make [(⟨ActionType, "a"⟩, ⟨.some default, .some default, .some default⟩)]

/-- The context knows `rec.inner` but neither `rec.opt` nor `flag`. -/
def req : PartialRequest :=
  ⟨⟨E, .some "p"⟩, ⟨ActionType, "a"⟩, ⟨E, default⟩,
   .some (Map.make [
     ("rec", .partialRecord (Map.make [("inner", .value (.prim (.string "v")))]))
   ])⟩

def mkPolicy (x : Expr) : Policy :=
  ⟨"0", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, x⟩]⟩

def boolLit (b : Bool) : Residual := .val (.prim (.bool b)) (.bool .anyBool)

def ctxVar : Residual := .var .context (.record (RecordType.liftBoolTypes CtxType))

def tests :=
  suite "TPE resolution through a partly-known context"
  [
    -- the known nested attribute resolves all the way to its value
    testResult (mkPolicy (.binaryApp .eq
        (.getAttr (.getAttr (.var .context) "rec") "inner") (.lit (.string "v"))))
      schema req es
      (boolLit true),
    -- `rec` is required by the context type, so it must exist
    testResult (mkPolicy (.hasAttr (.getAttr (.var .context) "rec") "inner")) schema req es
      (boolLit true),
    -- `opt` is optional and unmentioned, so its existence is unknown
    testResult (mkPolicy (.hasAttr (.getAttr (.var .context) "rec") "opt")) schema req es
      (.hasAttr (.getAttr ctxVar "rec" (.record RecType)) "opt" (.bool .anyBool)),
    -- an undeclared attribute of the nested record cannot exist
    testResult (mkPolicy (.hasAttr (.getAttr (.var .context) "rec") "bogus")) schema req es
      (boolLit false),
    -- `flag` is required but unmentioned, so `has` is true while the value is unknown
    testResult (mkPolicy (.hasAttr (.var .context) "flag")) schema req es
      (boolLit true),
    testResult (mkPolicy (.getAttr (.var .context) "flag")) schema req es
      (.getAttr ctxVar "flag" (.bool .anyBool)),
    -- ... and although `flag` is known to exist, a read is conservatively
    -- possibly-erroring, so the `&& false` fold is blocked
    testResult (mkPolicy (.and (.getAttr (.var .context) "flag") (.lit (.bool false))))
      schema req es
      (.and (.getAttr ctxVar "flag" (.bool .anyBool))
        (.val (.prim (.bool false)) (.bool .anyBool)) (.bool .anyBool)),
  ]

end UnitTest.TPE.Context

open UnitTest.TPE

def tests := [Basic.tests, Motivation.tests, Spec.tests, ExtHasAttr.tests, SchemaInformed.tests, AttrStates.tests, Context.tests]

end UnitTest.TPE

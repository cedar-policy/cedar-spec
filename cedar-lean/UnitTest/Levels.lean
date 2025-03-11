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

import Cedar.Validation.Levels
import Cedar.Validation.Validator
import UnitTest.Run

namespace UnitTest.Levels

open Cedar.Spec
open Cedar.Validation
open Cedar.Data

def ActionType : EntityType := ⟨"Action", []⟩
def Action : EntityUID := ⟨ActionType, "View"⟩

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
     .standard ⟨
      default,
      Map.make [
        ("manager", (.required (.entity UserType))),
        ("isAdmin", (.required (.bool .anyBool))),
        ("record", (.required (.record (Map.make [("attr", .required (.bool .anyBool))])))),
      ],
      .some (.bool .anyBool)
    ⟩
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
     (Action, ⟨
          Set.singleton UserType,
          Set.singleton DocumentType,
          default,
          Map.make [
            ("hasMFA", (.required (.bool .anyBool))),
            ("otherUser", (.required (.entity UserType)))
          ]
      ⟩)
  ]⟩

def levelCheckExpr (e : Expr) (env : Environment) (n : Nat) : Except String Bool :=
  match typeOf e ∅ env with
  | .ok (tx, _) => pure $ tx.checkLevel env n
  | _           => .error "Typechecking failed, but all tests cases should be well typed"

private def testLevelCheck (msg : String) (e : Expr) (n : Nat) : List (TestCase IO) :=
  (
    test s!"Expected {msg} to check at level {n}" ⟨λ _ => do
      match schema.environment? UserType DocumentType Action with
      | .some env => checkEq (levelCheckExpr e env n) (.ok true)
      | .none => return (.error "Could not find test environment in schema!")⟩
  ) ::
  if n > 0 then
    [test s!"Expected {msg} to fail at level {n - 1}" ⟨λ _ => do
      match schema.environment? UserType DocumentType Action with
      | .some env => checkEq (levelCheckExpr e env (n - 1)) (.ok false)
      | .none => return (.error "Could not find test environment in schema!")⟩]
  else []

def euid := EntityUID.mk UserType "alice"
def euidLit := Expr.lit (.entityUID euid)
def principal := Expr.var .principal
def recordLit := Expr.record [("foo", euidLit), ("bar", principal)]
def recordAccessLit := Expr.getAttr recordLit "foo"
def recordAccessVar := Expr.getAttr recordLit "bar"
def contextAccess := Expr.getAttr (Expr.var .context) "hasMFA"
def ite := Expr.ite (Expr.binaryApp .eq euidLit principal) euidLit principal

def levelZero :=
  let testLevelCheck := (testLevelCheck · · 0)
  suite "Expressions which should check at level 0"
  [
    testLevelCheck "lit" (.lit (.string "foo")),
    testLevelCheck "var" principal,
    testLevelCheck "entityUID" euidLit,
    testLevelCheck "action entityUID" (.lit (.entityUID Action)),
    testLevelCheck "record" recordLit,
    testLevelCheck "getAttr on record lit attr" recordAccessLit,
    testLevelCheck "getAttr on record var attr" recordAccessVar,
    testLevelCheck "getAttr on context" contextAccess,
    testLevelCheck "ite" ite
  ].flatten

def levelOne :=
  let testLevelCheck := (testLevelCheck · · 1)
  suite "Expressions which should check at level 1, but not at level 0"
  [
    testLevelCheck "getAttr on var" (.getAttr principal "manager"),
    testLevelCheck "hasAttr on var" (.hasAttr principal "manager"),
    testLevelCheck "mem on var" (.binaryApp .mem principal euidLit),
    testLevelCheck "mem on action" (.binaryApp .mem (.lit (.entityUID Action)) (.lit (.entityUID Action))),
    testLevelCheck "getTag and hasTag on var" (.and (.binaryApp .hasTag principal (.lit (.string "foo"))) (.binaryApp .getTag principal (.lit (.string "foo")))),
    testLevelCheck "getAttr on var through record" (.getAttr recordAccessVar "manager"),
    testLevelCheck "getAttr on var through record (other attrs contains deref)" (.getAttr (.getAttr (.record [("foo", principal), ("bar", .getAttr principal "isAdmin")]) "foo") "manager"),
    testLevelCheck "getAttr on var through ite" (.getAttr (.ite (.binaryApp .eq euidLit principal) principal principal) "manager"),
    testLevelCheck "getAttr on var through ite (guard contains deref)" (.getAttr (.ite (.getAttr principal "isAdmin") principal principal) "manager"),
    testLevelCheck "getAttr on context attr" (.getAttr (.getAttr (.var .context) "otherUser") "manager"),
    testLevelCheck "getAttr on var record attr" (.getAttr (.getAttr (.var .principal) "record") "attr"),
  ].flatten

def recordFoo (e : Expr) : Expr := .record [("foo", e)]
def getFoo (e : Expr) : Expr := .getAttr e "foo"

def composeN (f : α → α) : Nat → (α → α)
| 0 => id
| n + 1 => f ∘ (composeN f n)

def levelTwo :=
  let testLevelCheck := (testLevelCheck · · 2)
  suite "Expressions which should check at level 2, but not at level 1"
  [
    testLevelCheck "getAttr twice on var" (.getAttr (.getAttr principal "manager") "manager"),
    testLevelCheck "hasAttr on getAttr on var" (.hasAttr (.getAttr principal "manager") "manager"),
    testLevelCheck "hasTag on getAttr on var" (.binaryApp .hasTag (.getAttr principal "manager") (.lit (.string "foo"))),
    testLevelCheck "getAttr inside and outside ite" (.getAttr (.ite (.binaryApp .eq euidLit principal) (.getAttr principal "manager") (.getAttr principal "manager")) "manager"),
    testLevelCheck "getAttr inside and outside record" (.getAttr (getFoo (recordFoo (.getAttr principal "manager"))) "manager"),
    testLevelCheck "lots of intermediate record" (.getAttr (.getAttr (composeN getFoo 10 (composeN recordFoo 5 (composeN getFoo 5 (composeN recordFoo 10 (.getAttr principal "manager"))))) "record") "attr"),
  ].flatten

def levelThree :=
  let testLevelCheck := (testLevelCheck · · 3)
  suite "Expressions which should check at level 3, but not at level 2"
  [
    testLevelCheck "getAttr thrice on var" (.getAttr (.getAttr (.getAttr principal "manager") "manager") "manager"),
  ].flatten

def tests := [levelZero, levelOne, levelTwo, levelThree]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Levels

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

import Cedar.Spec.Evaluator
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec.Expr
import Cedar.Validation.Types
import Cedar.Data.Map
import UnitTest.Run

namespace UnitTest.BatchedEvaluator

open Cedar.Spec
open Cedar.TPE
open Cedar.Validation
open Cedar.Data

def ActionType : EntityType := ⟨"Action", []⟩
def UserType : EntityType := ⟨"User", []⟩
def DocumentType : EntityType := ⟨"Document", []⟩

def entity_schema : EntitySchema :=
  Map.make [
    (ActionType, .standard ⟨default, default, default⟩),
    (UserType, .standard ⟨default, Map.make [("name", .required .string), ("isAdmin", .required (.bool .anyBool))], (.some (.entity UserType))⟩),
    (DocumentType, .standard ⟨default, default, default⟩)
  ]

def action_schema : ActionSchema :=
  Map.make [
    (⟨ActionType, "Read"⟩, ⟨
      Set.singleton UserType,
      Set.singleton DocumentType,
      default,
      default
    ⟩)
  ]

def reqty : RequestType := ⟨UserType, ⟨ActionType, "Read"⟩, DocumentType, Map.empty⟩
def type_env : TypeEnv := ⟨entity_schema, action_schema, reqty⟩

-- Test that evaluate and batched_evaluate produce the same results
def testBatchedEvaluatorEquivalence (name : String) (expr : Expr) (req : Request) (entities : Entities) (loader : EntityLoader) : TestCase IO :=
  test name ⟨λ _ => do
    let regularResult := Cedar.Spec.evaluate expr req entities
    -- Create a minimal TypeEnv for typechecking
    match typeOf expr ∅ type_env with
    | .ok (typedExpr, _) =>
      let batchedResult := batchedEvaluate typedExpr req loader
      match (batchedResult, regularResult) with
      | (.ok br, .ok rr) => checkEq br rr
      | (.error _, .error _) => (.ok (.ok ()))
      | _ => checkEq batchedResult regularResult
    | .error e =>
      .error s!"Type error: {repr e}"
  ⟩

-- Translate the first Rust test: test_simple_entity_manifest
-- Policy: permit(principal, action, resource) when { principal.name == "John" }

def testRequest : Request :=
  ⟨
    ⟨UserType, "oliver"⟩,
    ⟨ActionType, "Read"⟩,
    ⟨DocumentType, "dummy"⟩,
    Map.empty
  ⟩

def testEntities : Entities :=
  Map.make [
    (⟨UserType, "oliver"⟩, ⟨Map.make [("name", "Oliver"), ("isAdmin", true)], Set.empty, Map.mk [⟨"friend", (.prim (.entityUID ⟨UserType, "emina"⟩))⟩]⟩),
    (⟨UserType, "emina"⟩, ⟨Map.make [("name", "emina"), ("isAdmin", true)], Set.empty, Map.empty⟩),
    (⟨ActionType, "Read"⟩, ⟨Map.empty, Set.empty, Map.empty⟩),
    (⟨DocumentType, "dummy"⟩, ⟨Map.empty, Set.empty, Map.empty⟩)
  ]

def testLoader : EntityLoader := entityLoaderFor testEntities

def has_expr_doesnt_eval: Expr := (.binaryApp .hasTag (.lit (.entityUID ⟨UserType, "nonexistent"⟩)) (.lit (.string "randomtag")))
def delayed_friend_string: Expr := (.ite has_expr_doesnt_eval (.lit (.string "friend")) (.lit (.string "friend")))

def oliver: Expr := (.lit (.entityUID ⟨UserType, "oliver"⟩))

def getTag (e: Expr) (t: Expr) : Expr := (.binaryApp .getTag e t)
def hasTag (e: Expr) (t: Expr) : Expr := (.binaryApp .hasTag e t)


def tests :=
  suite "BatchedEvaluator equivalence tests"
  [
    testBatchedEvaluatorEquivalence
      "simple entity manifest - principal.name == \"John\""
      (.binaryApp .eq (.getAttr (.var .principal) "name") (.lit (.string "John")))
      testRequest
      testEntities
      testLoader,
    -- Second test: empty entity manifest (permit with no conditions)
    testBatchedEvaluatorEquivalence
      "empty entity manifest - permit with no conditions"
      (.lit (.bool true))
      testRequest
      testEntities
      testLoader,
    testBatchedEvaluatorEquivalence
     "missing entity - User::\"nonexistent\".name == \"test\""
      (.binaryApp .eq (.getAttr (.lit (.entityUID ⟨UserType, "nonexistent"⟩)) "name") (.lit (.string "test")))
      testRequest
      testEntities
      testLoader,
    -- handling has on entity that isn't there
    testBatchedEvaluatorEquivalence
      "missing entity has attribute"
      (.and (hasTag oliver delayed_friend_string) (
        (.getAttr
          (getTag oliver delayed_friend_string) "isAdmin")))
      testRequest
      testEntities
      testLoader
  ]

#eval do TestSuite.runAll [tests]

end UnitTest.BatchedEvaluator

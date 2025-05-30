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

import Cedar.SymCC.Decoder
import Cedar.SymCC.Encoder
import Cedar.SymCC.Verifier
import UnitTest.Run

/-! This file defines simple utilities for unit testing symbolic evaluation. -/

namespace SymTest

open Cedar Data Spec SymCC Validation
open UnitTest

abbrev Outcome := SymCC.Decision

def Outcome.check (expected : Outcome) (verify : SymEnv → SymCC.Result Asserts) (εnv : SymEnv) : SolverM TestResult := do
  match verify εnv with
  | .ok asserts =>
    let enc ← Encoder.encode asserts εnv (produceModels := true)
    let dec ← Solver.checkSat
    if dec matches .sat then
      let model ← Solver.getModel
      match Decoder.decode model enc with
      | .ok I      => -- validate the model
        for t in asserts do
          if t.interpret I != true then
            throw (IO.userError s!"Model violates assertion {reprStr t}: {model}")
      | .error msg => throw (IO.userError s!"Decoding failed: {msg}\n {model}")
    checkEq dec expected
  | .error err  =>
    throw (IO.userError s!"SymCC failed: {reprStr err}")

def permit (x : Expr) : Policy := {
  id             := "policy",
  effect         := .permit,
  principalScope := .principalScope .any,
  actionScope    := .actionScope .any,
  resourceScope  := .resourceScope .any,
  condition      := [⟨.when, x⟩]
}

def testVerifyNoError (desc : String) (x : Expr) (εnv : SymEnv) (expected : Outcome) : TestCase SolverM :=
  test desc ⟨λ _ => expected.check (verifyNeverErrors (permit x)) εnv⟩

def testVerifyImplies (desc : String) (x₁ x₂ : Expr) (εnv : SymEnv) (expected : Outcome) : TestCase SolverM :=
  test desc ⟨λ _ => expected.check (verifyImplies [(permit x₁)] [(permit x₂)]) εnv⟩

def testVerifyEquivalent (desc : String) (x₁ x₂ : Expr) (εnv : SymEnv) (expected : Outcome) : TestCase SolverM :=
  test desc ⟨λ _ => expected.check (verifyEquivalent [(permit x₁)] [(permit x₂)]) εnv⟩

def testReduce (desc : String) (x : Expr) (εnv : SymEnv) (expected : SymCC.Result Term) : TestCase SolverM :=
  test desc ⟨λ _ => checkEq (compile x εnv) expected⟩

namespace BasicTypes

def principalType : EntityType := ⟨"Principal", []⟩

def resourceType : EntityType := ⟨"Resource", []⟩

def actionType : EntityType := ⟨"Action", []⟩

def action : EntityUID := ⟨actionType, "access"⟩

def actionSchema (context : RecordType) : ActionSchema :=
  let entry : ActionSchemaEntry := {
    appliesToPrincipal := Set.make [principalType],
    appliesToResource := Set.make [resourceType],
    ancestors := Set.empty,
    context := context
  }
  Map.make [(action, entry)]

def requestType (context : RecordType) : RequestType :=
  {
    principal := principalType,
    action := action,
    resource := resourceType,
    context := context
  }

def entitySchema (principalAttrs resourceAttrs : RecordType) (principalTags resourceTags : Option CedarType) : EntitySchema :=
  Map.make [
    (principalType, .standard ⟨Set.empty, principalAttrs, principalTags⟩),
    (resourceType, .standard ⟨Set.empty, resourceAttrs, resourceTags⟩)
  ]

def env (principalAttrs resourceAttrs context : RecordType) (principalTags resourceTags : Option CedarType := none) : Environment :=
  {
    ets   := entitySchema principalAttrs resourceAttrs principalTags resourceTags,
    acts  := actionSchema context,
    reqty := requestType context
  }

end BasicTypes

namespace Photoflash

def userType : EntityType    := ⟨"User", ["Photoflash"]⟩
def groupType : EntityType   := ⟨"Group", ["Photoflash"]⟩
def photoType : EntityType   := ⟨"Photo", ["Photoflash"]⟩
def albumType : EntityType   := ⟨"Album", ["Photoflash"]⟩
def accountType : EntityType := ⟨"Account", ["Photoflash"]⟩

def photoActionType : EntityType   := ⟨"Action", ["Photoflash", "Photo"]⟩
def albumActionType : EntityType   := ⟨"Action", ["Photoflash", "Album"]⟩

def createPhoto : EntityUID := ⟨photoActionType, "createPhoto"⟩
def readPhoto : EntityUID   := ⟨photoActionType, "readPhoto"⟩
def updatePhoto : EntityUID := ⟨photoActionType, "updatePhoto"⟩
def deletePhoto : EntityUID := ⟨photoActionType, "deletePhoto"⟩
def editPhoto : EntityUID   := ⟨photoActionType, "editPhoto"⟩

def shareAlbum : EntityUID := ⟨albumActionType, "shareAlbum"⟩
def viewAlbum : EntityUID  := ⟨albumActionType, "viewAlbum"⟩

def actionSchema (context : RecordType) : ActionSchema :=
  Map.make [
    (createPhoto, photoEntry []),
    (readPhoto, photoEntry [editPhoto]),
    (updatePhoto, photoEntry [editPhoto]),
    (deletePhoto, photoEntry []),
    (editPhoto, photoEntry []),
    (shareAlbum, albumEntry []),
    (viewAlbum, albumEntry []),
  ]
where
  photoEntry (ancs : List EntityUID) : ActionSchemaEntry :=
  {
    appliesToPrincipal := Set.make [userType],
    appliesToResource := Set.make [photoType],
    ancestors := Set.make ancs,
    context := context
  }
  albumEntry (ancs : List EntityUID) : ActionSchemaEntry :=
  {
    appliesToPrincipal := Set.make [userType],
    appliesToResource := Set.make [albumType],
    ancestors := Set.make ancs,
    context := context
  }

def entitySchema : EntitySchema :=
  Map.make [
    (userType, entry
      [groupType]
      [("account", .required (.entity accountType))]),
    (groupType, entry
      [groupType]
      []),
    (photoType, entry
      [albumType, accountType]
      [("tags", .required (.set .string)),
       ("location", .optional .string)]),
    (albumType, entry
      [albumType, accountType]
      []),
    (accountType, entry
      []
      [("owner", .required (.entity userType))])
  ]
where
  entry (ancs : List EntityType) (attrs : List (Attr × QualifiedType)) : EntitySchemaEntry :=
    .standard ⟨Set.make ancs, Map.make attrs, none⟩


def requestType (action : EntityUID) (resourceType : EntityType) (context : RecordType) : RequestType :=
  {
    principal := userType,
    action := action,
    resource := resourceType,
    context := context
  }

deriving instance Inhabited for ActionSchemaEntry

def env (action : EntityUID) (context : RecordType) : Environment :=
  let acts := actionSchema context
  let resourceType := (acts.find? action).get!.appliesToPrincipal.toList.head!
  {
    ets   := entitySchema,
    acts  := acts,
    reqty := requestType action resourceType context
  }

end Photoflash

end SymTest

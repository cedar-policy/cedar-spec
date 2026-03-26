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

import Cedar.SymCC.Compiler
import Cedar.SymCC.Decoder
import Cedar.SymCC.Encoder
public import Cedar.SymCC.Solver
public import Cedar.SymCC.Verifier
public import Cedar.SymCCOpt
import Cedar.SymCCOpt.Verifier
import Cedar.SymCCOpt.CompiledPolicies
public import UnitTest.Run

/-! This file defines simple utilities for unit testing symbolic compilation. -/

namespace SymTest

open Cedar Data Spec SymCC Validation
open UnitTest

public abbrev Outcome := SymCC.Decision

public def Outcome.checkAsserts (expected : Outcome) (asserts : Asserts) (εnv : SymEnv) : SolverM TestResult := do
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

public def Outcome.check (expected : Outcome) (verify : SymEnv → SymCC.Result Asserts) (εnv : SymEnv) : SolverM TestResult := do
  match verify εnv with
  | .ok asserts => Outcome.checkAsserts expected asserts εnv
  | .error err  => throw (IO.userError s!"SymCC failed: {reprStr err}")

private def Policy.permit (x : Expr) : Policy := {
  id             := "policy",
  effect         := .permit,
  principalScope := .principalScope .any,
  actionScope    := .actionScope .any,
  resourceScope  := .resourceScope .any,
  condition      := [⟨.when, x⟩]
}

private def CompiledPolicy.permit (x : Expr) (Γ : Validation.TypeEnv) : Except CompiledPolicyError CompiledPolicy :=
  CompiledPolicy.compile (Policy.permit x) Γ

private def CompiledPolicySet.permit (x : Expr) (Γ : Validation.TypeEnv) : Except CompiledPolicyError CompiledPolicySet :=
  CompiledPolicySet.compile [Policy.permit x] Γ

public def testFailsCompilePolicy (desc : String) (x : Expr) (Γ : Validation.TypeEnv) : TestCase SolverM :=
  let compileResult := CompiledPolicy.compile (Policy.permit x) Γ
  test desc ⟨λ _ => checkMatches (compileResult matches .error _) compileResult⟩

public def testFailsCompilePolicies (desc : String) (x : Expr) (Γ : Validation.TypeEnv) : TestCase SolverM :=
  let compileResult := CompiledPolicySet.compile [Policy.permit x] Γ
  test desc ⟨λ _ => checkMatches (compileResult matches .error _) compileResult⟩

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
public def testVerifyNoError (desc : String) (x : Expr) (Γ : Validation.TypeEnv) (expected : Outcome) : List (TestCase SolverM) :=
  let εnv := SymEnv.ofTypeEnv Γ
  [
    test (desc ++ " (unoptimized)") ⟨λ _ => expected.check (verifyNeverErrors (Policy.permit x)) εnv⟩,
    test (desc ++ " (optimized)") ⟨λ _ => do
      let cp ← CompiledPolicy.permit x Γ |> IO.ofExcept
      expected.checkAsserts (verifyNeverErrorsOpt cp) εnv⟩,
  ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
public def testVerifyImplies (desc : String) (x₁ x₂ : Expr) (Γ : Validation.TypeEnv) (expected : Outcome) : List (TestCase SolverM) :=
  let εnv := SymEnv.ofTypeEnv Γ
  [
    test (desc ++ " (unoptimized)") ⟨λ _ => expected.check (verifyImplies [(Policy.permit x₁)] [(Policy.permit x₂)]) εnv⟩,
    test (desc ++ " (optimized)") ⟨λ _ => do
      let cpset₁ ← CompiledPolicySet.permit x₁ Γ |> IO.ofExcept
      let cpset₂ ← CompiledPolicySet.permit x₂ Γ |> IO.ofExcept
      expected.checkAsserts (verifyImpliesOpt cpset₁ cpset₂) εnv⟩,
  ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
public def testVerifyEquivalent (desc : String) (x₁ x₂ : Expr) (Γ : Validation.TypeEnv) (expected : Outcome) : List (TestCase SolverM) :=
  let εnv := SymEnv.ofTypeEnv Γ
  [
    test (desc ++ " (unoptimized)") ⟨λ _ => expected.check (verifyEquivalent [(Policy.permit x₁)] [(Policy.permit x₂)]) εnv⟩,
    test (desc ++ " (optimized)") ⟨λ _ => do
      let cpset₁ ← CompiledPolicySet.permit x₁ Γ |> IO.ofExcept
      let cpset₂ ← CompiledPolicySet.permit x₂ Γ |> IO.ofExcept
      expected.checkAsserts (verifyEquivalentOpt cpset₁ cpset₂) εnv⟩,
  ]

public def testCompile (desc : String) (x : Expr) (εnv : SymEnv) (expected : SymCC.Result Term) : TestCase SolverM :=
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

public def env (principalAttrs resourceAttrs context : RecordType) (principalTags resourceTags : Option CedarType := none) : TypeEnv :=
  {
    ets   := entitySchema principalAttrs resourceAttrs principalTags resourceTags,
    acts  := actionSchema context,
    reqty := requestType context
  }

end BasicTypes

namespace Photoflash

public def userType : EntityType    := ⟨"User", ["Photoflash"]⟩
public def groupType : EntityType   := ⟨"Group", ["Photoflash"]⟩
public def photoType : EntityType   := ⟨"Photo", ["Photoflash"]⟩
public def albumType : EntityType   := ⟨"Album", ["Photoflash"]⟩
public def accountType : EntityType := ⟨"Account", ["Photoflash"]⟩

public def photoActionType : EntityType   := ⟨"Action", ["Photoflash", "Photo"]⟩
public def albumActionType : EntityType   := ⟨"Action", ["Photoflash", "Album"]⟩

public def createPhoto : EntityUID := ⟨photoActionType, "createPhoto"⟩
public def readPhoto : EntityUID   := ⟨photoActionType, "readPhoto"⟩
public def updatePhoto : EntityUID := ⟨photoActionType, "updatePhoto"⟩
public def deletePhoto : EntityUID := ⟨photoActionType, "deletePhoto"⟩
public def editPhoto : EntityUID   := ⟨photoActionType, "editPhoto"⟩

public def shareAlbum : EntityUID := ⟨albumActionType, "shareAlbum"⟩
public def viewAlbum : EntityUID  := ⟨albumActionType, "viewAlbum"⟩

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

public def env (action : EntityUID) (context : RecordType) : TypeEnv :=
  let acts := actionSchema context
  let resourceType := (acts.find? action).get!.appliesToPrincipal.toList.head!
  {
    ets   := entitySchema,
    acts  := acts,
    reqty := requestType action resourceType context
  }

end Photoflash

end SymTest

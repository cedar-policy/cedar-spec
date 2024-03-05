
import Cedar.Spec
import UnitTest.Run
import Cedar.Data

/-! This file defines unit tests for IPAddr functions. -/

namespace UnitTest.PE

open Cedar.Spec
open Cedar.Data

def simple : TestCase IO :=
  let input : Expr := .call .unknown [.lit (.string "foo")]
  let dummy : UidOrUnknown := .known (EntityUID.mk (Name.mk "foo" []) "bar")
  let req : PartialRequest := PartialRequest.mk dummy dummy dummy (Map.mk [])
  let entities : PartialEntities := Map.mk []
  let result := partialEvaluate input req entities
  let expected : Result PartialValue := .ok $ .residual (.unknown "foo")
  test "simple" ⟨λ _ => checkEq result expected⟩

def name (s : String) : Expr :=
  .lit $ .string s

def unknown (name : String) : Expr :=
  .call .unknown [.lit $ .string name]

def ite : TestCase IO :=

  let input : Expr := .ite (unknown "0") (unknown "1") (unknown "2")

  let dummy : UidOrUnknown := .known (EntityUID.mk (Name.mk "foo" []) "bar")
  let req : PartialRequest := PartialRequest.mk dummy dummy dummy (Map.mk [])
  let entities : PartialEntities := Map.mk []
  let result := partialEvaluate input req entities
  let expected : Result PartialValue := .ok $ .residual (.ite (.unknown "0") (.unknown "1") (.unknown "2"))
  test "ite" ⟨λ _ => checkEq result expected⟩


def failure : TestCase IO :=
  test "failure" ⟨λ _ => checkEq true false⟩

def tests := [suite "PETests" [simple, ite]]

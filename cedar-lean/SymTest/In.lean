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

import SymTest.Util

/-! This file unit tests symbolic compilation of membership operators on entities
and sets of entities: `in`, `contains`, `containsAny`, and `containsAll`. -/

namespace SymTest.In

open Cedar Data Spec SymCC Validation
open UnitTest Photoflash

private def context₁ : RecordType :=
  Map.make [
    ("x", .required (.entity albumType)),
    ("y", .required (.entity albumType)),
    ("z", .required (.entity albumType))
  ]

private def typeEnv₁ := env viewAlbum context₁

private def x : Expr := .getAttr (.var .context) "x"
private def y : Expr := .getAttr (.var .context) "y"
private def z : Expr := .getAttr (.var .context) "z"

private def context₂ : RecordType :=
  Map.make [
    ("x", .required (.entity albumType)),
    ("y", .required (.entity albumType)),
    ("z", .required (.entity albumType)),
    ("xs", .required (.set (.entity albumType))),
    ("ys", .required (.set (.entity albumType))),
    ("zs", .required (.set (.entity albumType)))
  ]

private def typeEnv₂ := env viewAlbum context₂

private def xs : Expr := .getAttr (.var .context) "xs"
private def ys : Expr := .getAttr (.var .context) "ys"
private def zs : Expr := .getAttr (.var .context) "zs"

private def ax : Expr := .lit (.entityUID ⟨albumType, "X"⟩)
private def ay : Expr := .lit (.entityUID ⟨albumType, "Y"⟩)
private def az : Expr := .lit (.entityUID ⟨albumType, "Z"⟩)

private def context₃ : RecordType :=
  Map.make [
    ("photoAct", .required (.entity photoActionType)),
    ("photoActs", .required (.set (.entity photoActionType)))
  ]
private def typeEnv₃ := env readPhoto context₃

private def photoAct : Expr := .getAttr (.var .context) "photoAct"
private def photoActs : Expr := .getAttr (.var .context) "photoActs"



def testsForInOnEntities :=
  suite "In.basic" $ List.flatten
  [
    testVerifyEquivalent s!"False: Album::'X' in Album::'Y' && Album::'Y' in Album::'X' && Album::'X' != Album::'Y'"
      (.and
        (.binaryApp .mem ax ay)
        (.and
          (.binaryApp .mem ay ax)
          (.unaryApp .not (.binaryApp .eq ax ay))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in y && y in x && x != y"
      (.and
        (.binaryApp .mem x y)
        (.and
          (.binaryApp .mem y x)
          (.unaryApp .not (.binaryApp .eq x y))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in y && y in z && x !in z"
      (.and
        (.binaryApp .mem x y)
        (.and
          (.binaryApp .mem y z)
          (.unaryApp .not (.binaryApp .mem x z))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "True: if x in y && y in z then x in z else false"
      (.ite
        (.and
          (.binaryApp .mem x y)
          (.binaryApp .mem y z))
        (.binaryApp .mem x z)
        (.lit (.bool true)))
      (.lit (.bool true))
      typeEnv₁ .unsat,

    testVerifyImplies "Implies: x in (if x in y then z else Album::'Z') ==> x in z || x in Album::'Z'"
      (.binaryApp .mem x (.ite (.binaryApp .mem x y) z az))
      (.or
        (.binaryApp .mem x z)
        (.binaryApp .mem x az))
      typeEnv₁ .unsat,
  ]

def testsForInOnEntitySets :=
  suite "In.set" $ List.flatten
  [
    testVerifyEquivalent "True: x in [z, y, x]"
      (.binaryApp .mem x (.set [z, y, x]))
      (.lit (.bool true))
      typeEnv₁ .unsat,

    testVerifyImplies "Implies: x in (if x in y then z else Album::'Z') ==> x in [z, Album::'Z']"
      (.binaryApp .mem x (.ite (.binaryApp .mem x y) z az))
      (.binaryApp .mem x (.set [z, az]))
      typeEnv₁ .unsat,

    testVerifyEquivalent "True: x in {bar : true, foo : [z, y, x]}.foo"
      (.binaryApp .mem x
        (.getAttr
          (.record [
            ("bar", .lit (.bool true)),
            ("foo", (.set [z, y, x]))])
          "foo"))
      (.lit (.bool true))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in [y] && y in [x] && x != y"
      (.and
        (.binaryApp .mem x (.set [y]))
        (.and
          (.binaryApp .mem y (.set [x]))
          (.unaryApp .not (.binaryApp .eq x y))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in [Album::'X'] && Album::'X' in [x] && x != Album::'X'"
      (.and
        (.binaryApp .mem x (.set [ax]))
        (.and
          (.binaryApp .mem ax (.set [x]))
          (.unaryApp .not (.binaryApp .eq x ax))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in [y] && y in [z] && x !in z"
      (.and
        (.binaryApp .mem x (.set [y]))
        (.and
          (.binaryApp .mem y (.set [z]))
          (.unaryApp .not (.binaryApp .mem x z))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in [y] && y in [z] && x !in [z]"
      (.and
        (.binaryApp .mem x (.set [y]))
        (.and
          (.binaryApp .mem y (.set [z]))
          (.unaryApp .not (.binaryApp .mem x (.set [z])))))
      (.lit (.bool false))
      typeEnv₁ .unsat,

    testVerifyEquivalent "False: x in y && y in ys && x !in ys"
      (.and
        (.binaryApp .mem x y)
        (.and
          (.binaryApp .mem y ys)
          (.unaryApp .not (.binaryApp .mem x ys))))
      (.lit (.bool false))
      typeEnv₂ .unsat,

    testVerifyEquivalent "Equivalent: x in y <==> x in [y]"
      (.binaryApp .mem x y)
      (.binaryApp .mem x (.set [y]))
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.contains(x) ==> x in xs"
      (.binaryApp .contains xs x)
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.contains(x) && ys.contains(x) ==> xs.containsAny(ys)"
      (.and
        (.binaryApp .contains xs x)
        (.binaryApp .contains ys x))
      (.binaryApp .containsAny xs ys)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.containsAll([x]) ==> x in xs"
      (.binaryApp .containsAll xs (.set [x]))
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.containsAll([z, y]) && x in [y, z] ==> x in xs"
      (.and
        (.binaryApp .containsAll xs (.set [z, y]))
        (.binaryApp .mem x (.set [y, z])))
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.containsAll(ys) && x in ys ==> x in xs"
      (.and
        (.binaryApp .containsAll xs ys)
        (.binaryApp .mem x ys))
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.containsAll(ys) && ys.containsAll(zs) && x in zs ==> x in xs"
      (.and
        (.binaryApp .containsAll xs ys)
        (.and
          (.binaryApp .containsAll ys zs)
          (.binaryApp .mem x zs)))
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.containsAny([x]) ==> x in xs"
      (.binaryApp .containsAny xs (.set [x]))
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,

    testVerifyImplies "Implies: xs.containsAny([z, y]) && x in y && x in z ==> x in xs"
      (.and
        (.binaryApp .containsAll xs (.set [z, y]))
        (.and
          (.binaryApp .mem x y)
          (.binaryApp .mem x z)))
      (.binaryApp .mem x xs)
      typeEnv₂ .unsat,
  ]

private def testVerifyActionIn (left right : EntityUID) (outcome : Bool): List (TestCase SolverM) :=
  testVerifyEquivalent s!"{outcome}: {left} in {right}"
    (.binaryApp .mem (.lit (.entityUID left)) (.lit (.entityUID right)))
    (.lit (.bool outcome))
    typeEnv₃ .unsat

def testsForInOnActions :=
  suite "In.action" $ List.flatten
  [
    testVerifyActionIn readPhoto readPhoto true,
    testVerifyActionIn readPhoto editPhoto true,
    testVerifyActionIn updatePhoto editPhoto true,
    testVerifyActionIn readPhoto createPhoto false,
    testVerifyActionIn createPhoto editPhoto false,
    testVerifyActionIn editPhoto editPhoto true,
    testVerifyActionIn shareAlbum editPhoto false,

    testVerifyEquivalent s!"True: action in {readPhoto}"
      (.binaryApp .mem (.var .action) (.lit (.entityUID readPhoto)))
      (.lit (.bool true))
      typeEnv₃ .unsat,

    testVerifyEquivalent s!"True: action in {editPhoto}"
      (.binaryApp .mem (.var .action) (.lit (.entityUID editPhoto)))
      (.lit (.bool true))
      typeEnv₃ .unsat,

    testVerifyEquivalent s!"False: action in {viewAlbum}"
      (.binaryApp .mem (.var .action) (.lit (.entityUID viewAlbum)))
      (.lit (.bool false))
      typeEnv₃ .unsat,

    testVerifyImplies s!"Implies: photoAct in {readPhoto} ==> photoAct in {editPhoto}"
      (.binaryApp .mem photoAct (.lit (.entityUID readPhoto)))
      (.binaryApp .mem photoAct (.lit (.entityUID editPhoto)))
      typeEnv₃ .unsat,

    testVerifyImplies s!"Implies: photoAct in {updatePhoto} ==> photoAct in {editPhoto}"
      (.binaryApp .mem photoAct (.lit (.entityUID updatePhoto)))
      (.binaryApp .mem photoAct (.lit (.entityUID editPhoto)))
      typeEnv₃ .unsat,

    testVerifyImplies s!"Implies: photoAct in {editPhoto} && photoAct != {editPhoto} ==> photoAct in [{readPhoto}, {updatePhoto}]"
      (.and
        (.binaryApp .mem photoAct (.lit (.entityUID editPhoto)))
        (.unaryApp .not (.binaryApp .eq photoAct (.lit (.entityUID editPhoto)))))
      (.binaryApp .mem photoAct
        (.set [
          (.lit (.entityUID readPhoto)),
          (.lit (.entityUID updatePhoto))]))
      typeEnv₃ .unsat,

    testVerifyImplies s!"Implies: photoActs.contains({editPhoto}) ==> {readPhoto} in photoActs"
      (.binaryApp .contains photoActs (.lit (.entityUID editPhoto)))
      (.binaryApp .mem (.lit (.entityUID readPhoto)) photoActs)
      typeEnv₃ .unsat,

    testVerifyImplies s!"Implies: photoActs.contains({editPhoto}) ==> action in photoActs"
      (.binaryApp .contains photoActs (.lit (.entityUID editPhoto)))
      (.binaryApp .mem (.var .action) photoActs)
      typeEnv₃ .unsat,
  ]

def tests := [
  testsForInOnEntities,
  testsForInOnEntitySets,
  testsForInOnActions
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

namespace SymTest.In

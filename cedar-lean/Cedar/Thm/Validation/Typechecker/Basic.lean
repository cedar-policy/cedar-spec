/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Data.Control
import Cedar.Thm.Validation.Typechecker.Types

/-!
This file contains useful definitions and lemmas about the `Typechecker` functions.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
The type soundness property says that if the typechecker assigns a type to an
expression, then it must be the case that the expression `EvaluatesTo` a value
of that type. The `EvaluatesTo` predicate covers the (obvious) case where
evaluation has no errors, but it also allows for errors of type
`entityDoesNotExist`, `extensionError`, and `arithBoundsError`.

The typechecker cannot protect against these errors because they depend on
runtime information (i.e., the entities passed into the authorization request,
extension function applications on authorization-time data, and arithmetic
overflow errors). All other errors (`attrDoesNotExist` and `typeError`) can be
prevented statically.

_Note_: Currently, `extensionError`s can also be ruled out at validation time
because the only extension functions that can error are constructors, and all
constructors are required to be applied to string literals, meaning that they
can be fully evaluated during validation. This is not guaranteed to be the case
in the future.

_Note_: We plan to implement a range analysis that will be able to rule out
`arithBoundsError`s.
-/
def EvaluatesTo (e: Expr) (request : Request) (entities : Entities) (v : Value) : Prop :=
  evaluate e request entities = .error .entityDoesNotExist ∨
  evaluate e request entities = .error .extensionError ∨
  evaluate e request entities = .error .arithBoundsError ∨
  evaluate e request entities = .ok v

/--
On input to the typechecking function, for any (e,k) in the Capabilities,
e is a record- or entity-typed expression that has key k.
-/
def CapabilitiesInvariant (c : Capabilities) (request : Request) (entities : Entities) : Prop :=
  ∀ (e : Expr) (k : Attr), (e, k) ∈ c → EvaluatesTo (.hasAttr e k) request entities true

/--
The Capabilities output by the typechecking function will satisfy
`CapabilitiesInvariant` provided that the input expression evaluates to true.
-/
def GuardedCapabilitiesInvariant (e: Expr) (c: Capabilities) (request : Request) (entities : Entities) : Prop :=
  evaluate e request entities = .ok true →
  CapabilitiesInvariant c request entities

def TypeOfIsSound (x₁ : Expr) : Prop :=
  ∀ {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities},
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironment env request entities →
    typeOf x₁ c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariant x₁ c₂ request entities ∧
    ∃ v, EvaluatesTo x₁ request entities v ∧ InstanceOfType v ty

----- Capability lemmas -----

theorem empty_capabilities_invariant (request : Request) (entities : Entities) :
  CapabilitiesInvariant ∅ request entities
:= by
  intro e k h
  contradiction

theorem empty_guarded_capabilities_invariant {e: Expr} {request : Request} {entities : Entities} :
  GuardedCapabilitiesInvariant e ∅ request entities
:= by
  intro _
  exact empty_capabilities_invariant request entities

theorem capability_implies_record_attribute {x₁ : Expr} {a : Attr} {c₁ : Capabilities} {request : Request} {entities : Entities} {r : Map Attr Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : evaluate x₁ request entities = Except.ok (Value.record r))
  (h₃ : (x₁, a) ∈ c₁) :
  ∃ vₐ, r.find? a = some vₐ
:= by
  simp [CapabilitiesInvariant] at h₁
  specialize h₁ x₁ a h₃
  simp [EvaluatesTo, evaluate, h₂, hasAttr, attrsOf, Map.contains_iff_some_find?] at h₁
  exact h₁

theorem capability_implies_entity_attribute {x₁ : Expr} {a : Attr} {c₁ : Capabilities} {request : Request} {entities : Entities} {uid: EntityUID} {d: EntityData}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (h₃ : Map.find? entities uid = some d)
  (h₄ : (x₁, a) ∈ c₁) :
  ∃ vₐ, d.attrs.find? a = some vₐ
:= by
  simp [CapabilitiesInvariant] at h₁
  specialize h₁ x₁ a h₄
  simp [EvaluatesTo, evaluate, h₂, hasAttr, attrsOf, Entities.attrsOrEmpty, h₃, Map.contains_iff_some_find?] at h₁
  exact h₁

theorem capability_union_invariant {c₁ c₂ : Capabilities} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : CapabilitiesInvariant c₂ request entities) :
  CapabilitiesInvariant (c₁ ∪ c₂) request entities
:= by
  simp [CapabilitiesInvariant] at *
  intro x a h₃
  specialize h₁ x a ; specialize h₂ x a
  cases h₃ <;> rename_i h₃ <;> simp [h₃] at * <;> assumption

theorem capability_intersection_invariant {c₁ c₂ : Capabilities} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities ∨ CapabilitiesInvariant c₂ request entities) :
  CapabilitiesInvariant (c₁ ∩ c₂) request entities
:= by
  simp [CapabilitiesInvariant] at *
  intro x a h₃ h₄
  cases h₁ <;> rename_i h₁ <;> apply h₁ x a <;> assumption

end Cedar.Thm

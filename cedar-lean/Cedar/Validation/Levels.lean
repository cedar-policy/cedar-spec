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

import Cedar.Validation.TypedExpr
import Cedar.Validation.Typechecker
import Cedar.Thm.Data.Map
import Cedar.Spec.Policy

/-!
This file defines a level checking of a type-annotated AST. Level checking
should behave as defined in RFC#76, although the implementation here is
different from what was proposed because this implementation operates over a
type-annotated AST instead of being built into the primary typechecking
algorithm.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

mutual

def checkEntityAccessLevel (tx : TypedExpr) (n nmax : Nat) (path : List Attr) : Bool :=
  match tx, path with
  | .var _ _, _ => true
  | .ite tx₁ tx₂ tx₃ _, _ =>
    checkLevel tx₁ nmax &&
    checkEntityAccessLevel tx₂ n nmax path &&
    checkEntityAccessLevel tx₃ n nmax path
  | .getAttr x₁ a _, _ =>
    match x₁.typeOf with
    | .entity _ =>
      n > 0 &&
      checkEntityAccessLevel x₁ (n - 1) nmax []
    | _ =>
      checkEntityAccessLevel x₁ n nmax (a :: path)
  | .binaryApp .getTag x₁ x₂ _, _ =>
    n > 0 &&
    checkEntityAccessLevel x₁ (n - 1) nmax [] &&
    checkLevel x₂ nmax
  | .record axs _, (a :: path) =>
    match h₁ : (Map.make axs).find? a with
    | some tx' =>
      have : sizeOf tx' < sizeOf axs := by
        replace h₁ := Map.make_mem_list_mem (Map.find?_mem_toList h₁)
        replace h₁ := List.sizeOf_lt_of_mem h₁
        rw [Prod.mk.sizeOf_spec a tx'] at h₁
        omega
      checkEntityAccessLevel tx' n nmax path &&
      axs.attach.all λ e =>
        have : sizeOf e.val.snd < 1 + sizeOf axs := by
          have h₁ := List.sizeOf_lt_of_mem e.property
          rw [Prod.mk.sizeOf_spec e.val.fst e.val.snd] at h₁
          omega
        checkLevel e.val.snd nmax
    | none => false
  | _, _ => false

def checkLevel (tx : TypedExpr) (n : Nat) : Bool :=
  match tx with
  | .lit _ _ => true
  | .var _ _ => true
  | .ite x₁ x₂ x₃ _ =>
    checkLevel x₁ n &&
    checkLevel x₂ n &&
    checkLevel x₃ n
  | .unaryApp _ x₁ _ =>
    checkLevel x₁ n
  | .binaryApp .mem x₁ x₂ _
  | .binaryApp .getTag x₁ x₂ _
  | .binaryApp .hasTag x₁ x₂ _ =>
    n > 0 &&
    checkEntityAccessLevel x₁ (n - 1) n [] &&
    checkLevel x₂ n
  | .and x₁ x₂ _
  | .or x₁ x₂ _
  | .binaryApp _ x₁ x₂ _ =>
    checkLevel x₁ n &&
    checkLevel x₂ n
  | .hasAttr x₁ _ _
  | .getAttr x₁ _ _ =>
    match x₁.typeOf with
    | .entity _ =>
      n > 0 &&
      checkEntityAccessLevel x₁ (n - 1) n []
    | _ => checkLevel x₁ n
  | .call _ xs _
  | .set xs _ =>
    xs.attach.all λ e =>
      have := List.sizeOf_lt_of_mem e.property
      checkLevel e n
  | .record axs _ =>
    axs.attach.all λ e =>
      have : sizeOf e.val.snd < 1 + sizeOf axs := by
        have h₁ := List.sizeOf_lt_of_mem e.property
        rw [Prod.mk.sizeOf_spec e.val.fst e.val.snd] at h₁
        omega
      checkLevel e.val.snd n

 end

def typecheckAtLevel (policy : Policy) (env : Environment) (n : Nat) : Bool :=
  match typeOf policy.toExpr ∅ env with
  | .ok (tx, _) => checkLevel tx n
  | _           => false

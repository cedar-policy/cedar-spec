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

def notEntityLit : TypedExpr → Bool
  | .lit (.entityUID _) _ => false
  | .ite _ x₂ x₃ _ =>
    notEntityLit x₂ && notEntityLit x₃
  | .getAttr x₁ _ _
  | .binaryApp .getTag x₁ _ _ =>
    notEntityLit x₁
  | .record axs _ =>
    axs.attach.all λ e =>
      have : sizeOf e.val.snd < 1 + sizeOf axs := by
        have h₁ := List.sizeOf_lt_of_mem e.property
        rw [Prod.mk.sizeOf_spec e.val.fst e.val.snd] at h₁
        omega
      notEntityLit e.val.snd
  | _ => true

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
    notEntityLit x₁ &&
    n > 0 &&
    checkLevel x₁ (n - 1) &&
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
      notEntityLit x₁ &&
      n > 0 &&
      checkLevel x₁ (n - 1)
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

def typedAtLevel (e : Expr) (c : Capabilities) (env : Environment) (n : Nat) : Bool :=
  match typeOf e c env with
  | .ok (te, _) => checkLevel te n
  | _           => false

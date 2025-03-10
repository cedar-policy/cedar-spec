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

/--
Check that an expression is valid as the argument to an entity dereferencing
expression at a level. This functions assumes that `tx` either evaluates to an
entity value or to a record value containing a entity value via `path`.

Note that this function intentionally returns `false` for entity literals at any
level. This is necessary because entity literals are not one of the "roots" used
by the slicing algorithm.

This functions takes two additional arguments not required by `checkLevel`

- `nmax` specifies the maximum level allowed for any expression. E.g., for an
  `.ite` expression, the maximum level permissible for the guard is independent
  of any `.getAttr` expressions it might be nested inside of.
- `path` is a sequence of attributes specifying an access path through a record
  value, eventually reaching an attribute that has an entity value. This allows
  allows more permissive level checking on record attributes that aren't accessed.
-/
def checkEntityAccessLevel (tx : TypedExpr) (env : Environment) (n nmax : Nat) (path : List Attr) : Bool :=
  match tx, path with
  | .var _ _, _ => true
  | .lit (.entityUID euid) _, _ =>
    euid == env.reqty.action
  | .ite tx₁ tx₂ tx₃ _, _ =>
    checkLevel tx₁ env nmax &&
    checkEntityAccessLevel tx₂ env n nmax path &&
    checkEntityAccessLevel tx₃ env n nmax path
  | .getAttr x₁ a _, _ =>
    match x₁.typeOf with
    | .entity _ =>
      n > 0 &&
      checkEntityAccessLevel x₁ env (n - 1) nmax []
    | _ =>
      checkEntityAccessLevel x₁ env n nmax (a :: path)
  | .binaryApp .getTag x₁ x₂ _, _ =>
    n > 0 &&
    checkEntityAccessLevel x₁ env (n - 1) nmax [] &&
    checkLevel x₂ env nmax
  | .record axs _, (a :: path) =>
    match h₁ : (Map.make axs).find? a with
    | some tx' =>
      have : sizeOf tx' < sizeOf axs := by
        replace h₁ := List.sizeOf_lt_of_mem ∘ Map.make_mem_list_mem ∘ Map.find?_mem_toList $ h₁
        rw [Prod.mk.sizeOf_spec a tx'] at h₁
        omega
      checkEntityAccessLevel tx' env n nmax path &&
      axs.attach₂.all λ e =>
        checkLevel e.val.snd env nmax
    | none => false
  | _, _ => false


/--
Main entry point for level checking an expression. For most expressions, this is
a simple recursive traversal of the AST. For entity dereferencing expressions,
it calls to `checkEntityAccessLevel` which ensures that expression is valid
specifically in an entity access position
-/
def checkLevel (tx : TypedExpr) (env : Environment) (n : Nat) : Bool :=
  match tx with
  | .lit _ _ => true
  | .var _ _ => true
  | .ite x₁ x₂ x₃ _ =>
    checkLevel x₁ env n &&
    checkLevel x₂ env n &&
    checkLevel x₃ env n
  | .unaryApp _ x₁ _ =>
    checkLevel x₁ env n
  | .binaryApp .mem x₁ x₂ _
  | .binaryApp .getTag x₁ x₂ _
  | .binaryApp .hasTag x₁ x₂ _ =>
    n > 0 &&
    checkEntityAccessLevel x₁ env (n - 1) n [] &&
    checkLevel x₂ env n
  | .and x₁ x₂ _
  | .or x₁ x₂ _
  | .binaryApp _ x₁ x₂ _ =>
    checkLevel x₁ env n &&
    checkLevel x₂ env n
  | .hasAttr x₁ _ _
  | .getAttr x₁ _ _ =>
    match x₁.typeOf with
    | .entity _ =>
      n > 0 &&
      checkEntityAccessLevel x₁ env (n - 1) n []
    | _ => checkLevel x₁ env n
  | .call _ xs _
  | .set xs _ =>
    xs.attach.all λ e =>
      have := List.sizeOf_lt_of_mem e.property
      checkLevel e env n
  | .record axs _ =>
    axs.attach₂.all λ e =>
      checkLevel e.val.snd env n

 end

def typecheckAtLevel (policy : Policy) (env : Environment) (n : Nat) : Bool :=
  match typeOf policy.toExpr ∅ env with
  | .ok (tx, _) => checkLevel tx env n
  | _           => false

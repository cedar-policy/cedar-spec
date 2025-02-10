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

structure LevelCheckResult where
  -- The primary output of the level checking procedure. `false` if any access
  -- exceeds the specified level.
  checked: Bool
  -- Was the checked expression an entity root? Returns `false` for entity
  -- literals, which are not roots used by the slicing algorithm. Used
  -- internally by the level checking procedure to forbid access on entity
  -- literals.
  root: Bool

def LevelCheckResult.and (r₀ r₁ : LevelCheckResult) : LevelCheckResult := LevelCheckResult.mk (r₀.checked && r₁.checked) (r₀.root && r₁.root)

def checkLevel (tx : TypedExpr) (n : Nat) : LevelCheckResult :=
  match tx with
  | .lit _ _ => LevelCheckResult.mk true false
  | .var _ _ => LevelCheckResult.mk true true
  | .ite x₁ x₂ x₃ _ =>
    let c₁ := checkLevel x₁ n
    let c₂ := checkLevel x₂ n
    let c₃ := checkLevel x₃ n
    LevelCheckResult.mk
      (c₁.checked && c₂.checked && c₃.checked)
      (c₂.root && c₃.root)
  | .unaryApp _ x₁ _ =>
    checkLevel x₁ n
  | .binaryApp .mem x₁ x₂ _
  | .binaryApp .getTag x₁ x₂ _
  | .binaryApp .hasTag x₁ x₂ _ =>
    let c₁ := checkLevel x₁ (n - 1)
    let c₂ := checkLevel x₂ n
    LevelCheckResult.mk
      (c₁.root && n > 0 && c₁.checked && c₂.checked)
      c₁.root
  | .and x₁ x₂ _
  | .or x₁ x₂ _
  | .binaryApp _ x₁ x₂ _ =>
    let c₁ := checkLevel x₁ n
    let c₂ := checkLevel x₂ n
    LevelCheckResult.mk
      (c₁.checked && c₂.checked)
      true
  | .hasAttr x₁ _ _
  | .getAttr x₁ _ _ =>
    match x₁.typeOf with
    | .entity _ =>
      let c₁ := checkLevel x₁ (n - 1)
      LevelCheckResult.mk
        (c₁.root && n > 0 && c₁.checked)
        c₁.root
    | _ => (checkLevel x₁ n)
  | .call _ xs _
  | .set xs _ =>
    xs.attach.foldl
      (λ c ex =>
        have := List.sizeOf_lt_of_mem ex.property
        let c₁ := checkLevel ex.val n
        LevelCheckResult.mk
          (c.checked && c₁.checked)
          (c.root && c₁.root))
      (LevelCheckResult.mk true true)
  | .record axs _ =>
    axs.attach.foldl
      (λ c a =>
        let t := a.val.snd
        --have : sizeOf t < 1 + sizeOf axs := by
        --  have : t = a.val.snd := by simp [t]
        --  rw [this]
        --  have h₁ := List.sizeOf_lt_of_mem a.property
        --  rw [Prod.mk.sizeOf_spec a.val.fst a.val.snd] at h₁
        --  omega
        let c₁ := checkLevel a.val.snd n
        LevelCheckResult.mk
          (c.checked && c₁.checked)
          (c.root && c₁.root))
      (LevelCheckResult.mk true true)
  termination_by tx
  decreasing_by
    all_goals {
      try { simp ; omega }
      -- TODO: Record case doesn't go through after changing from `all` to `foldl`
      try sorry
    }

def typedAtLevel (e : Expr) (c : Capabilities) (env : Environment) (n : Nat) : Bool :=
  match typeOf e c env with
  | .ok (te, _) => (checkLevel te n).checked
  | _           => false

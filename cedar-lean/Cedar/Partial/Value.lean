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

import Cedar.Partial.Expr
import Cedar.Spec.Value

/-!
This file defines Cedar partial values.
-/

namespace Cedar.Partial

open Cedar.Data

inductive Value where
  | value (v : Spec.Value)
  | residual (r : Partial.Expr)

deriving instance Repr, DecidableEq, Inhabited for Value

def Value.asPartialExpr : Partial.Value → Partial.Expr
  | .value v    => v.asPartialExpr
  | .residual r => r

instance : Coe Spec.Value Partial.Value where
  coe := Partial.Value.value

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new `Partial.Expr`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Expr` will still contain some unknowns.
-/
-- NB: this function can't live in Partial/Expr.lean because it needs Partial.Value, and
-- Partial/Expr.lean can't import Partial/Value.lean, cyclic dependency
def Expr.subst (subsmap : Map Unknown Partial.Value) : Partial.Expr → Partial.Expr
  | .lit p => .lit p -- no unknowns, nothing to substitute
  | .var v => .var v -- no unknowns, nothing to substitute
  | .ite x₁ x₂ x₃ => .ite (x₁.subst subsmap) (x₂.subst subsmap) (x₃.subst subsmap)
  | .and x₁ x₂ => .and (x₁.subst subsmap) (x₂.subst subsmap)
  | .or x₁ x₂ => .or (x₁.subst subsmap) (x₂.subst subsmap)
  | .unaryApp op x₁ => .unaryApp op (x₁.subst subsmap)
  | .binaryApp op x₁ x₂ => .binaryApp op (x₁.subst subsmap) (x₂.subst subsmap)
  | .getAttr x₁ attr => .getAttr (x₁.subst subsmap) attr
  | .hasAttr x₁ attr => .hasAttr (x₁.subst subsmap) attr
  | .set xs => .set (xs.map₁ λ ⟨x, _⟩ => x.subst subsmap)
  | .record pairs => .record (pairs.attach₂.map λ ⟨(k, v), _⟩ => (k, v.subst subsmap))
  | .call xfn xs => .call xfn (xs.map₁ λ ⟨x, _⟩ => x.subst subsmap)
  | .unknown u => match subsmap.find? u with
    | some val => val.asPartialExpr
    | none => .unknown u -- no substitution available

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new `Partial.Value`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Value` will still contain some unknowns.
-/
def Value.subst (subsmap : Map Unknown Partial.Value) : Partial.Value → Partial.Value
  | .residual r => .residual (r.subst subsmap)
  | .value v    => .value v -- doesn't contain unknowns, nothing to substitute

end Cedar.Partial

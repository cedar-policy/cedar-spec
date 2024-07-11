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

import Cedar.Spec.Expr
import Cedar.Spec.Value

/-!
  This file defines Cedar partial values and substitutions.
-/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr BinaryOp ExtFun UnaryOp)

-- Unknowns are currently represented by a string name
abbrev Unknown := String

mutual

/--
  `Partial.Value` represents the result of partial-evaluating an expression.
  If you flatten `Partial.ResidualExpr` into this definition, it's very close to
  `Expr`, but can contain `Unknown`s, and also cannot contain `.var` (those
  will be substituted either by values or unknowns).
-/
inductive Value where
  | value (v : Spec.Value)
  | residual (r : ResidualExpr)
deriving Repr, Inhabited

/--
  Represents a residual expression (other than a concrete value).
  Very similar to `Expr` but with an `.unknown` case, without the `.lit`
  case, and without the `.var` case (during evaluation, all vars will be
  substituted either by values or unknowns).
-/
inductive ResidualExpr where
  | unknown (u : Unknown)
  | ite (cond : Partial.Value) (thenValue : Partial.Value) (elseValue : Partial.Value)
  | and (lhs : Partial.Value) (rhs : Partial.Value)
  | or (lhs : Partial.Value) (rhs : Partial.Value)
  | unaryApp (op : UnaryOp) (pv : Partial.Value)
  | binaryApp (op : BinaryOp) (pv₁ : Partial.Value) (pv₂ : Partial.Value)
  | getAttr (pv : Partial.Value) (attr : Attr)
  | hasAttr (pv : Partial.Value) (attr : Attr)
  | set (pvs : List Partial.Value)
  | record (map : List (Attr × Partial.Value))
  | call (xfn : ExtFun) (pvs : List Partial.Value)
deriving Repr, Inhabited

end

instance : Coe Spec.Value Partial.Value where
  coe := Partial.Value.value

instance : Coe Unknown ResidualExpr where
  coe := ResidualExpr.unknown

instance : Coe Unknown Partial.Value where
  coe u := .residual (.unknown u)

end Cedar.Partial

namespace Cedar.Spec

/--
  Convert an `Expr` to `Partial.Value`, if possible (i.e., if the
  `Expr` does not contain any `.var`)

  Consider using `Expr.substToPartialValue` instead
-/
def Expr.asPartialValue : Expr → Option Partial.Value
  | .lit p => some (.value p)
  | .var _ => none
  | .ite x₁ x₂ x₃ => do
      some (.residual (.ite (← x₁.asPartialValue) (← x₂.asPartialValue) (← x₃.asPartialValue)))
  | .and x₁ x₂ => do
      some (.residual (.and (← x₁.asPartialValue) (← x₂.asPartialValue)))
  | .or x₁ x₂ => do
      some (.residual (.or (← x₁.asPartialValue) (← x₂.asPartialValue)))
  | .unaryApp op x₁ => do
      some (.residual (.unaryApp op (← x₁.asPartialValue)))
  | .binaryApp op x₁ x₂ => do
      some (.residual (.binaryApp op (← x₁.asPartialValue) (← x₂.asPartialValue)))
  | .getAttr x₁ attr => do
      some (.residual (.getAttr (← x₁.asPartialValue) attr))
  | .hasAttr x₁ attr => do
      some (.residual (.hasAttr (← x₁.asPartialValue) attr))
  | .set xs => do
      some (.residual (.set (← xs.mapM₁ λ ⟨x, _⟩ => x.asPartialValue)))
  | .record attrs => do
      some (.residual (.record (← attrs.attach₂.mapM λ ⟨(k, v), _⟩ => do some (k, (← v.asPartialValue)))))
  | .call xfn args => do
      some (.residual (.call xfn (← args.mapM₁ λ ⟨x, _⟩ => x.asPartialValue)))

end Cedar.Spec

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr BinaryOp ExtFun Prim UnaryOp Var)

mutual

def decPartialValue (x y : Partial.Value) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case value.value x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case residual.residual x₁ y₁ =>
    exact match decResidualExpr x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decResidualExpr (x y : Partial.ResidualExpr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case unknown.unknown x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ y₁ y₂ y₃ =>
    exact match decPartialValue x₁ y₁, decPartialValue x₂ y₂, decPartialValue x₃ y₃ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ y₁ y₂ | or.or x₁ x₂ y₁ y₂ =>
    exact match decPartialValue x₁ y₁, decPartialValue x₂ y₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ o' y₁ =>
    exact match decEq o o', decPartialValue x₁ y₁ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ o' y₁ y₂ =>
    exact match decEq o o', decPartialValue x₁ y₁, decPartialValue x₂ y₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a y₁ a' | hasAttr.hasAttr x₁ a y₁ a' =>
    exact match decPartialValue x₁ y₁, decEq a a' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs ys =>
    exact match decPartialValueList xs ys with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs ays =>
    exact match decProdAttrPartialValueList axs ays with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs f' ys =>
    exact match decEq f f', decPartialValueList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrPartialValueList (axs ays : List (Attr × Partial.Value)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decPartialValue x y, decProdAttrPartialValueList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decPartialValueList (xs ys : List Partial.Value) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decPartialValue x y, decPartialValueList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq Partial.Value := decPartialValue
instance : DecidableEq Partial.ResidualExpr := decResidualExpr

/--
  Defines a mapping from unknowns to the `Partial.Value`s to replace them with
  during a substitution.
-/
structure Subsmap where
  m : Map Unknown Partial.Value

mutual

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new `Partial.Value`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Value` will still contain some unknowns.
-/
def Value.subst (subsmap : Subsmap) : Partial.Value → Partial.Value
  | .value v => .value v -- doesn't contain unknowns, nothing to substitute
  | .residual r => r.subst subsmap

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a `Partial.Value`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Value` will still contain some unknowns.

  This function does not attempt to constant-fold or reduce after the substitution
  (so, e.g., substituting u=5 in `3 + u` will give `3 + 5`).
  To reduce, use `Partial.evaluateValue`.
-/
def ResidualExpr.subst (subsmap : Subsmap) : ResidualExpr → Partial.Value
  | .unknown u => match subsmap.m.find? u with
    | some pv => pv
    | none => .residual (.unknown u) -- no substitution available
  | .ite pv₁ pv₂ pv₃ => .residual (.ite (pv₁.subst subsmap) (pv₂.subst subsmap) (pv₃.subst subsmap))
  | .and pv₁ pv₂ => .residual (.and (pv₁.subst subsmap) (pv₂.subst subsmap))
  | .or pv₁ pv₂ => .residual (.or (pv₁.subst subsmap) (pv₂.subst subsmap))
  | .unaryApp op pv₁ => .residual (.unaryApp op (pv₁.subst subsmap))
  | .binaryApp op pv₁ pv₂ => .residual (.binaryApp op (pv₁.subst subsmap) (pv₂.subst subsmap))
  | .getAttr pv₁ attr => .residual (.getAttr (pv₁.subst subsmap) attr)
  | .hasAttr pv₁ attr => .residual (.hasAttr (pv₁.subst subsmap) attr)
  | .set pvs => .residual (.set (pvs.map₁ λ ⟨x, _⟩ => x.subst subsmap))
  | .record pairs => .residual (.record (pairs.attach₂.map λ ⟨(k, v), _⟩ => (k, v.subst subsmap)))
  | .call xfn pvs => .residual (.call xfn (pvs.map₁ λ ⟨x, _⟩ => x.subst subsmap))

end

end Cedar.Partial

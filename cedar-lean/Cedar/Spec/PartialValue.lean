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

import Cedar.Data.Map
import Cedar.Spec.Ext.IPAddr
import Cedar.Spec.PartialExpr
import Cedar.Spec.Value

/-!
This file defines Cedar partial values.
-/

namespace Cedar.Spec

open Cedar.Data

inductive PartialValue where
  | value (v : Value)
  | residual (r : PartialExpr)

deriving instance Repr, DecidableEq, Inhabited for PartialValue

def Value.asPartialExpr (v : Value) : PartialExpr :=
  match v with
  | .prim p => PartialExpr.lit p
  | .set s => PartialExpr.set (s.elts.map Value.asPartialExpr)
  | .record m => PartialExpr.record (m.kvs.map fun (k, v)=> (k, v.asPartialExpr))
  | .ext (.decimal d) => PartialExpr.call ExtFun.decimal [PartialExpr.lit (.string d.unParse)]
  | .ext (.ipaddr ip) => PartialExpr.call ExtFun.ip [PartialExpr.lit (.string (Cedar.Spec.Ext.IPAddr.unParse ip))]
decreasing_by sorry

def PartialValue.asPartialExpr (v : PartialValue) : PartialExpr :=
  match v with
  | .value v    => Value.asPartialExpr v
  | .residual r => r

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialExpr.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialExpr` will still contain some unknowns.
-/
-- NB: this function can't live in PartialExpr.lean because it needs PartialValue, and
-- PartialExpr.lean can't import PartialValue, cyclic dependency
def PartialExpr.subst (x : PartialExpr) (subsmap : Map String PartialValue) : PartialExpr :=
  match x with
  | .lit _ => x -- no unknowns, nothing to substitute
  | .var _ => x -- no unknowns, nothing to substitute
  | .ite x₁ x₂ x₃ =>
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    let x₃' := x₃.subst subsmap
    .ite x₁' x₂' x₃'
  | .and x₁ x₂ =>
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .and x₁' x₂'
  | .or x₁ x₂ =>
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .or x₁' x₂'
  | .unaryApp op x₁ =>
    let x₁' := x₁.subst subsmap
    .unaryApp op x₁
  | .binaryApp op x₁ x₂ =>
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .binaryApp op x₁' x₂'
  | .getAttr x₁ attr =>
    let x₁' := x₁.subst subsmap
    .getAttr x₁' attr
  | .hasAttr x₁ attr =>
    let x₁' := x₁.subst subsmap
    .hasAttr x₁' attr
  | .set xs =>
    let xs' := xs.map (PartialExpr.subst · subsmap)
    .set xs'
  | .record pairs =>
    let pairs' := pairs.map fun (k, v) => (k, v.subst subsmap)
    .record pairs'
  | .call xfn xs =>
    let xs' := xs.map (PartialExpr.subst · subsmap)
    .call xfn xs'
  | unknown name => match subsmap.find? name with
    | some val => val.asPartialExpr
    | none => x -- no substitution available, return `x` unchanged
decreasing_by sorry

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialValue.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialValue` will still contain some unknowns.
-/
def PartialValue.subst (v : PartialValue) (subsmap : Map String PartialValue) : PartialValue :=
  match v with
  | .residual r => .residual (r.subst subsmap)
  | .value v    => .value v -- doesn't contain unknowns, nothing to substitute

/--
  If converting a Value to PartialExpr gives a primitive, the Value was that
  primitive
-/
theorem Value.prim_prim {v : Value} {p : Prim} :
  v.asPartialExpr = .lit p ↔ v = .prim p
:= by
  unfold Value.asPartialExpr
  constructor
  case mp =>
    intro h₁
    cases v <;> simp at *
    case prim => trivial
    case ext x => cases x <;> simp at h₁
  case mpr => intro h₁ ; simp [h₁]

/--
  subst on an Expr is id
-/
theorem subs_expr_id {expr : Expr} {subsmap : Map String PartialValue} :
  expr.asPartialExpr.subst subsmap = expr.asPartialExpr
:= by
  sorry

end Cedar.Spec

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

import Cedar.Spec.Value
import Cedar.Spec.Expr
import Cedar.Validation.TypedExpr

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

-- The result produced by TPE
-- We do not need `unknown`s because they can be represented by entity dereferences
inductive Residual where
  | val (v : Value) (ty : CedarType)
  | prim (p : Prim) (ty : CedarType)
  | var (v : Var)  (ty : CedarType)
  | ite (cond : Residual) (thenExpr : Residual) (elseExpr : Residual)  (ty : CedarType)
  | and (a : Residual) (b : Residual)  (ty : CedarType)
  | or (a : Residual) (b : Residual)  (ty : CedarType)
  | unaryApp (op : UnaryOp) (expr : Residual)  (ty : CedarType)
  | binaryApp (op : BinaryOp) (a : Residual) (b : Residual)  (ty : CedarType)
  | getAttr (expr : Residual) (attr : Attr)  (ty : CedarType)
  | hasAttr (expr : Residual) (attr : Attr)  (ty : CedarType)
  | set (ls : List Residual)  (ty : CedarType)
  | record (map : List (Attr × Residual))  (ty : CedarType)
  | call (xfn : ExtFun) (args : List Residual) (ty : CedarType)

def TypedExpr.toResidual : TypedExpr → Residual
  | .lit p ty => .prim p ty
  | .var v ty => .var v ty
  | .ite c x y ty => .ite (toResidual c) (toResidual x) (toResidual y) ty
  | .and a b ty => .and (toResidual a) (toResidual b) ty
  | .or a b ty => .or (toResidual a) (toResidual b) ty
  | .unaryApp op e ty => .unaryApp op (toResidual e) ty
  | .binaryApp op a b ty => .binaryApp op (toResidual a) (toResidual b) ty
  | .getAttr e a ty => .getAttr (toResidual e) a ty
  | .hasAttr e a ty => .hasAttr (toResidual e) a ty
  | .set s ty => .set (s.map₁ λ ⟨x, _⟩ ↦ toResidual x) ty
  | .record m ty => .record (m.map₁ λ ⟨(a, x), _⟩ ↦ (a, toResidual x)) ty
  | .call f args ty => .call f (args.map₁ λ ⟨x, _⟩ ↦ toResidual x) ty
decreasing_by
  all_goals
    simp_wf
    try omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    replace h := List.sizeOf_lt_of_mem h
    have h₁ : sizeOf (a, x) >= sizeOf x := by
      simp_arith
    omega
  case _ h =>
    replace h := List.sizeOf_lt_of_mem h
    omega

instance : Coe TypedExpr Residual where
  coe := TypedExpr.toResidual

def Residual.asValue : Residual → Option Value
  | .val v _ => .some v
  | _ => .none

def Value.toResidual (v : Value) (ty : CedarType) : Residual :=
  .val v ty

-- The interpreter of `Residual` that defines its semantics
def Residual.evaluate (x : Residual) (req : Request) (es: Entities) : Result Value :=
  match x with
  | .val v _ => .ok v
  | .prim p _ => .ok $ .prim p
  | .var (.principal) _ => .ok req.principal
  | .var (.resource) _ => .ok req.resource
  | .var (.action) _ => .ok req.action
  | .var (.context) _ => .ok req.context
  | .ite c x y _ => do
    let c ← c.evaluate req es
    let b ← c.asBool
    if b then x.evaluate req es else y.evaluate req es
  | .and x y _ => do
    let b ← (x.evaluate req es).as Bool
    if !b then .ok b else (y.evaluate req es).as Bool
  | .or x y _ => do
    let b ← (x.evaluate req es).as Bool
    if b then .ok b else (y.evaluate req es).as Bool
  | .unaryApp op e _ => do
    let v ← e.evaluate req es
    apply₁ op v
  | .binaryApp op x y _ => do
    let v₁ ← evaluate x req es
    let v₂ ← evaluate y req es
    apply₂ op v₁ v₂ es
  | .hasAttr e a _ => do
    let v ← e.evaluate req es
    Cedar.Spec.hasAttr v a es
  | .getAttr e a _ => do
    let v ← e.evaluate req es
    Cedar.Spec.hasAttr v a es
  | .set xs _ => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    .ok (Set.make vs)
  | .record axs _ => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => bindAttr a₁ (evaluate x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs _ => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    Cedar.Spec.call xfn vs
termination_by x
decreasing_by
  all_goals
    simp_wf
    try omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    simp at h
    omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega

end Cedar.TPE

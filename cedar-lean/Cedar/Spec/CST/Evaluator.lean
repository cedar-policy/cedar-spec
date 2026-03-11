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

import Cedar.Spec.CST.Expr
import Cedar.Spec.Evaluator

/-! This file defines the CST evaluator that directly interprets CST expressions. -/

namespace Cedar.Spec.CST

open Cedar.Spec
open Cedar.Data

/-- Evaluate a CST relational operator -/
def evaluateRel (op : RelOp) (v₁ v₂ : Value) (es : Entities) : Result Value :=
  match op with
  | .eq        => apply₂ .eq v₁ v₂ es
  | .notEq     => do let r ← apply₂ .eq v₁ v₂ es; apply₁ .not r
  | .less      => apply₂ .less v₁ v₂ es
  | .lessEq    => apply₂ .lessEq v₁ v₂ es
  | .greater   => do let r ← apply₂ .lessEq v₁ v₂ es; apply₁ .not r
  | .greaterEq => do let r ← apply₂ .less v₁ v₂ es; apply₁ .not r
  | .mem       => apply₂ .mem v₁ v₂ es

/-- Apply a chain of unary ops (evaluator-side, operating on Values) -/
def evalUnaryOps : List UnaryOp → Value → Result Value
  | [],          v => .ok v
  | .not :: ops, v => do let inner ← evalUnaryOps ops v; apply₁ .not inner
  | .neg :: ops, v => do let inner ← evalUnaryOps ops v; apply₁ .neg inner

/-- Evaluate extended has: e has a.b.c with short-circuit semantics -/
def evaluateExtendedHas (base : Value) (es : Entities) : List Attr → Result Value
  | []      => .ok true
  | [a]     => Spec.hasAttr base a es
  | a :: as => do
    let b ← (Spec.hasAttr base a es).as Bool
    if !b then .ok false
    else do
      let v ← Spec.getAttr base a es
      evaluateExtendedHas v es as

mutual

/-- Evaluate n-ary Or with short-circuit semantics -/
def evaluateOrChain (req : Request) (es : Entities)
    (acc : Value) : List CST.Expr → Result Value
  | []        => .ok acc
  | e :: rest => do
    let b ← (Result.as Bool (.ok acc))
    if b then .ok acc
    else do
      let v ← Expr.evaluate e req es
      let _ ← (Result.as Bool (.ok v))
      evaluateOrChain req es v rest

/-- Evaluate n-ary And with short-circuit semantics -/
def evaluateAndChain (req : Request) (es : Entities)
    (acc : Value) : List CST.Expr → Result Value
  | []        => .ok acc
  | e :: rest => do
    let b ← (Result.as Bool (.ok acc))
    if !b then .ok acc
    else do
      let v ← Expr.evaluate e req es
      let _ ← (Result.as Bool (.ok v))
      evaluateAndChain req es v rest

/-- Evaluate n-ary Add/Sub left-to-right -/
def evaluateAddChain (req : Request) (es : Entities)
    (acc : Value) : List (AddOp × CST.Expr) → Result Value
  | [] => .ok acc
  | (.plus, e) :: rest => do
    let v ← Expr.evaluate e req es
    let r ← apply₂ .add acc v es
    evaluateAddChain req es r rest
  | (.minus, e) :: rest => do
    let v ← Expr.evaluate e req es
    let r ← apply₂ .sub acc v es
    evaluateAddChain req es r rest

/-- Evaluate n-ary Mult left-to-right -/
def evaluateMultChain (req : Request) (es : Entities)
    (acc : Value) : List CST.Expr → Result Value
  | [] => .ok acc
  | e :: rest => do
    let v ← Expr.evaluate e req es
    let r ← apply₂ .mul acc v es
    evaluateMultChain req es r rest

/-- Main CST evaluator -/
def Expr.evaluate (cst : CST.Expr) (req : Request) (es : Entities) : Result Value :=
  match cst with
  | .lit p           => .ok p
  | .var v           => Spec.evaluate (.var v) req es
  | .ite c t e       => do
    let b ← (c.evaluate req es).as Bool
    if b then t.evaluate req es else e.evaluate req es
  | .or init ext     => do
    let v ← init.evaluate req es
    evaluateOrChain req es v ext
  | .and init ext    => do
    let v ← init.evaluate req es
    evaluateAndChain req es v ext
  | .rel op l r      => do
    let v₁ ← l.evaluate req es
    let v₂ ← r.evaluate req es
    evaluateRel op v₁ v₂ es
  | .has e a         => do
    let v ← e.evaluate req es
    Spec.hasAttr v a es
  | .extendedHas e [] => .ok true
  | .extendedHas e as => do
    let v ← e.evaluate req es
    evaluateExtendedHas v es as
  | .like e p        => do
    let v ← e.evaluate req es
    apply₁ (.like p) v
  | .is e ety        => do
    let v ← e.evaluate req es
    apply₁ (.is ety) v
  | .isIn e ety inE  => do
    let v ← e.evaluate req es
    let b ← (apply₁ (.is ety) v).as Bool
    if !b then .ok false
    else do
      let v₂ ← inE.evaluate req es
      apply₂ .mem v v₂ es
  | .add init ext    => do
    let v ← init.evaluate req es
    evaluateAddChain req es v ext
  | .mult init ext   => do
    let v ← init.evaluate req es
    evaluateMultChain req es v ext
  | .unary ops e     => do
    let v ← e.evaluate req es
    CST.evalUnaryOps ops v
  | .getAttr e a     => do
    let v ← e.evaluate req es
    Spec.getAttr v a es
  | .hasAttr e a     => do
    let v ← e.evaluate req es
    Spec.hasAttr v a es
  | .set elems       => do
    let vs ← elems.mapM₁ (fun ⟨e, _⟩ => e.evaluate req es)
    .ok (Set.make vs)
  | .record pairs    => do
    let avs ← pairs.mapM₂ (fun ⟨(a, e), _⟩ => do let v ← e.evaluate req es; pure (a, v))
    .ok (Map.make avs)
  | .call fn args    => do
    let vs ← args.mapM₁ (fun ⟨e, _⟩ => e.evaluate req es)
    Spec.call fn vs
  | .methodCall recv fn args => do
    let vr ← recv.evaluate req es
    let vs ← args.mapM₁ (fun ⟨e, _⟩ => e.evaluate req es)
    Spec.call fn (vr :: vs)

end

/-- Evaluate a CST condition directly: when → body, unless → not body -/
def Condition.evaluate (c : CST.Condition) (req : Request) (es : Entities) : Result Value :=
  match c.kind with
  | .when   => c.body.evaluate req es
  | .unless => do let v ← c.body.evaluate req es; apply₁ .not v

/-- Evaluate CST conditions with short-circuit and semantics (top to bottom) -/
def Conditions.evaluate : List CST.Condition → Request → Entities → Result Value
  | [],      _,   _  => .ok true
  | [c],     req, es => c.evaluate req es
  | c :: cs, req, es => do
    let b ← (c.evaluate req es).as Bool
    if !b then .ok false
    else Conditions.evaluate cs req es

/-- Evaluate a CST policy directly: check scopes then conditions -/
def Policy.evaluate (p : CST.Policy) (req : Request) (es : Entities) : Result Value := do
  let b₁ ← (Spec.evaluate p.principalScope.toExpr req es).as Bool
  if !b₁ then return false
  let b₂ ← (Spec.evaluate p.actionScope.toExpr req es).as Bool
  if !b₂ then return false
  let b₃ ← (Spec.evaluate p.resourceScope.toExpr req es).as Bool
  if !b₃ then return false
  Conditions.evaluate p.conditions req es

/-- A CST policy is satisfied when its direct evaluation returns true -/
def satisfiedCST (p : CST.Policy) (req : Request) (es : Entities) : Bool :=
  (p.evaluate req es) = .ok true

end Cedar.Spec.CST

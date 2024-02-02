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

import Cedar.Spec.Entities
import Cedar.Spec.Evaluator
import Cedar.Spec.Expr
import Cedar.Spec.Request

/-! This file defines the semantics of Cedar partial evaluation. -/

namespace Cedar.Spec

open Cedar.Data

/--
  Identical to `Expr` except that it has an `unknown` case, and the recursive
  elements are also all `PartialExpr` instead of `Expr`
-/
inductive PartialExpr where
  | expr (expr : Expr PartialExpr)
  | unknown

inductive PartialValue where
  | value (v : Value)
  | residual (r : PartialExpr)

inductive PartialRequest where
  | known (req : Request)

inductive PartialEntities where
  | known (entities : Entities)

class PartialEvaluatable (α : Type) where
  partialEval : (a : α) -> (req : PartialRequest) -> (es : PartialEntities) -> Result PartialValue

def liftConcrete (res : Result Value) : Result PartialValue :=
  match res with
  | .ok val => .ok (.value val)
  | .error e => .error e

instance [ConcreteEvaluatable α] : PartialEvaluatable α where
  partialEval (x : α) req es :=
  match (req, es) with
  | (.known req, .known es) => liftConcrete (ConcreteEvaluatable.eval x req es)

mutual

instance [PartialEvaluatable α] : PartialEvaluatable (Expr α) where
  partialEval (x : Expr α) req es :=
  match (req, es) with
  | (.known known_req, .known known_es) =>
    match x with
    | .lit l => liftConcrete (ConcreteEvaluatable.eval (Expr.lit l) known_req known_es)
    | .var v => liftConcrete (ConcreteEvaluatable.eval (Expr.var v) known_req known_es)
    /-
    | .ite x₁ x₂ x₃ => do
      let b ← (PartialEvaluatable.partialEval x₁ req es)
      match b with
      | .value v => do
        let b ← b.as Bool
        if b then PartialEvaluatable.partialEval x₂ req es else PartialEvaluatable.partialEval x₃ req es
    -/
    | .unaryApp op₁ x₁ => do
      let pval ← PartialEvaluatable.partialEval x₁ req es
      match pval with
        | .value val => do
          let val ← apply₁ op₁ val -- TODO: reuse the concrete evaluator code somehow
          .ok (.value val)
        | .residual r => .ok (.residual (PartialExpr.expr (Expr.unaryApp op₁ r)))

instance : PartialEvaluatable PartialExpr where
  partialEval (x : PartialExpr) req es :=
  match x with
  | .expr expr => PartialEvaluatable.partialEval expr req es
  | .unknown => .ok (.residual x)

end

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
  | known (expr : Expr PartialExpr)
  | unknown

inductive PartialValue where
  | value (v : Value)
  | residual (r : PartialExpr)

inductive PartialRequest where
  | known (r : Request)

inductive PartialEntities where
  | known (entities : Entities)

class PartialEvaluatable (α : Type) where
  partialEval : (a : α) -> (req : PartialRequest) -> (es : PartialEntities) -> Result PartialValue

instance [PartialEvaluatable α] : PartialEvaluatable (Expr α) where
  partialEval (x : Expr α) req es :=

instance PartialEvaluatable PartialExpr where
  partialEval (x : PartialExpr) req es :=
  match x with
  | .known expr => PartialEvaluatable.partialEval expr req es
  | .unknown => .error

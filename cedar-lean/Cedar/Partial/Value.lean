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
import Cedar.Partial.Expr
import Cedar.Spec.Ext.IPAddr
import Cedar.Spec.ExtFun
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

def Value.asPartialExpr (v : Partial.Value) : Partial.Expr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r

/--
  Like `Partial.Value`, but cannot contain residual expressions which depend on
  vars or entity data
-/
inductive RestrictedValue where
  | value (v : Spec.Value)
  | residual (r : Partial.RestrictedExpr)

deriving instance Inhabited for RestrictedValue

def RestrictedValue.asPartialExpr (v : Partial.RestrictedValue) : Partial.Expr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r.asPartialExpr

def RestrictedValue.asPartialRestrictedExpr (v : Partial.RestrictedValue) : Partial.RestrictedExpr :=
  match v with
  | .value v    => v.asPartialRestrictedExpr
  | .residual r => r

def RestrictedValue.asPartialValue (v : RestrictedValue) : Partial.Value :=
  match v with
  | .value v    => .value v
  | .residual r => .residual (r.asPartialExpr)

end Cedar.Partial

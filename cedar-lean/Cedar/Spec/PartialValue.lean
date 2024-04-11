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
import Cedar.Spec.ExtFun
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

def PartialValue.asPartialExpr (v : PartialValue) : PartialExpr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r

/--
  Like `PartialValue`, but cannot contain residual expressions which depend on
  vars or entity data
-/
inductive RestrictedPartialValue where
  | value (v : Value)
  | residual (r : RestrictedPartialExpr)

deriving instance Inhabited for RestrictedPartialValue

def RestrictedPartialValue.asPartialExpr (v : RestrictedPartialValue) : PartialExpr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r.asPartialExpr

def RestrictedPartialValue.asRestrictedPartialExpr (v : RestrictedPartialValue) : RestrictedPartialExpr :=
  match v with
  | .value v    => v.asRestrictedPartialExpr
  | .residual r => r

def RestrictedPartialValue.asPartialValue (v : RestrictedPartialValue) : PartialValue :=
  match v with
  | .value v    => .value v
  | .residual r => .residual (r.asPartialExpr)

end Cedar.Spec

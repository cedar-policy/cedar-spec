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

import Cedar.Partial.Expr
import Cedar.Partial.Value
import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Spec.Value

/-!
This file defines Cedar partial requests.
-/

namespace Cedar.Partial

open Cedar.Data

inductive UidOrUnknown where
  | known (uid : Spec.EntityUID)
  | unknown (u : Unknown)

deriving instance Repr, DecidableEq, Inhabited for UidOrUnknown

instance : Coe UidOrUnknown Partial.Value where
  coe x := match x with
  | .known uid => .value uid
  | .unknown u => .residual (Partial.Expr.unknown u)

structure Request where
  principal : UidOrUnknown
  action : UidOrUnknown
  resource : UidOrUnknown
  context : Map Spec.Attr Partial.RestrictedValue -- allows individual context attributes to have unknown values, but does not allow it to be unknown whether a context attribute exists at all

deriving instance Inhabited for Request

end Cedar.Partial

namespace Cedar.Spec

def Request.asPartialRequest (req : Spec.Request) : Partial.Request :=
  {
    principal := .known req.principal,
    action := .known req.action,
    resource := .known req.resource,
    context := req.context.mapOnValues Partial.RestrictedValue.value,
  }

instance : Coe Spec.Request Partial.Request where
  coe := Spec.Request.asPartialRequest

end Cedar.Spec

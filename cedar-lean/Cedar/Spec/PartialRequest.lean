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

import Cedar.Spec.Expr
import Cedar.Spec.PartialExpr
import Cedar.Spec.PartialValue
import Cedar.Spec.Request
import Cedar.Spec.Value

/-!
This file defines Cedar partial requests.
-/

namespace Cedar.Spec

open Cedar.Data

inductive UidOrUnknown where
  | known (uid : EntityUID)
  | unknown (name : String)

deriving instance Repr, DecidableEq, Inhabited for UidOrUnknown

instance : Coe UidOrUnknown PartialValue where
  coe x := match x with
  | .known uid    => .value uid
  | .unknown name => .residual (PartialExpr.unknown name)

structure PartialRequest where
  principal : UidOrUnknown
  action : UidOrUnknown
  resource : UidOrUnknown
  context : Map Attr RestrictedPartialValue -- allows individual context attributes to have unknown values, but does not allow it to be unknown whether a context attribute exists at all

deriving instance Inhabited for PartialRequest

def Request.asPartialRequest (req : Request) : PartialRequest :=
  {
    principal := .known req.principal,
    action := .known req.action,
    resource := .known req.resource,
    context := req.context.mapOnValues RestrictedPartialValue.value,
  }

instance : Coe Request PartialRequest where
  coe := Request.asPartialRequest


end Cedar.Spec

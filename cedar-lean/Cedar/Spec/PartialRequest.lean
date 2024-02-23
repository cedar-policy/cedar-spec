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
  context : Map Attr PartialValue -- allows individual context attributes to have unknown values, but does not allow it to be unknown whether a context attribute exists at all

deriving instance Repr, DecidableEq, Inhabited for PartialRequest

def Request.asPartialRequest (req : Request) : PartialRequest :=
  {
    principal := .known req.principal,
    action := .known req.action,
    resource := .known req.resource,
    context := req.context.mapOnValues PartialValue.value,
  }

instance : Coe Request PartialRequest where
  coe := Request.asPartialRequest

/--
  Given a map of unknown-name to value, substitute the unknown in `UidOrUnknown`
  if possible. If the `UidOrUnknown` is already known, or it's an unknown that doesn't
  have a mapping in `subsmap`, return it unchanged.

  Returns `none` if the substitution is invalid -- e.g., if trying to substitute
  a non-EntityUID into `UidOrUnknown`.
-/
def UidOrUnknown.subst (u : UidOrUnknown) (subsmap : Map String PartialValue) : Option UidOrUnknown :=
  match u with
  | .known uid => some (.known uid)
  | .unknown name => match subsmap.find? name with
    | some (.value (.prim (.entityUID uid))) => some (.known uid)
    | some (.residual (.unknown name')) => some (.unknown name') -- substituting an unknown with another unknown, we'll allow it
    | none => some u -- no substitution available, return `u` unchanged
    | _ => none -- substitution is not for a literal UID or literal unknown. Not valid, return none

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialRequest.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialRequest` will still contain some unknowns.

  Returns `none` if the substitution is invalid -- e.g., if trying to substitute
  a non-EntityUID into `UidOrUnknown`.
-/
def PartialRequest.subst (req : PartialRequest) (subsmap : Map String PartialValue) : Option PartialRequest :=
  do
    let principal ← req.principal.subst subsmap
    let action ← req.action.subst subsmap
    let resource ← req.resource.subst subsmap
    let context := req.context.mapOnValues (PartialValue.subst · subsmap)
    some { principal, action, resource, context }

end Cedar.Spec

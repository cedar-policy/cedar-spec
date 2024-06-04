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
open Cedar.Spec (Attr EntityUID)

inductive UidOrUnknown where
  | known (uid : EntityUID)
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
  context : Map Attr Partial.Value -- allows individual context attributes to have unknown values, but does not allow it to be unknown whether a context attribute exists at all

deriving instance Inhabited for Request

end Cedar.Partial

namespace Cedar.Spec

def Request.asPartialRequest (req : Spec.Request) : Partial.Request :=
  {
    principal := .known req.principal,
    action := .known req.action,
    resource := .known req.resource,
    context := req.context.mapOnValues Partial.Value.value,
  }

instance : Coe Spec.Request Partial.Request where
  coe := Spec.Request.asPartialRequest

end Cedar.Spec

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (EntityUID)

/--
  Given a map of unknown-name to value, substitute the unknown in `UidOrUnknown`
  if possible. If the `UidOrUnknown` is already known, or it's an unknown that doesn't
  have a mapping in `subsmap`, return it unchanged.

  Returns `none` if the substitution is invalid -- e.g., if trying to substitute
  a non-`EntityUID` into `UidOrUnknown`.
-/
def UidOrUnknown.subst (subsmap : Subsmap) : UidOrUnknown → Option UidOrUnknown
  | .known uid => some (.known uid)
  | .unknown unk => match subsmap.m.find? unk with
    | some (.value (.prim (.entityUID uid))) => some (.known uid)
    | some (.residual (.unknown unk')) => some (.unknown unk') -- substituting an unknown with another unknown, we'll allow it
    | none => some (.unknown unk) -- no substitution available, return `unk` unchanged
    | _ => none -- substitution is not for a literal UID or literal unknown. Not valid, return none

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new `Partial.Request`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Request` will still contain some unknowns.

  Returns `none` if the substitution is invalid -- e.g., if trying to substitute
  a non-`EntityUID` into `UidOrUnknown`.
-/
def Request.subst (subsmap : Subsmap) : Partial.Request → Option Partial.Request
  | { principal, action, resource, context } => do
    let principal ← principal.subst subsmap
    let action ← action.subst subsmap
    let resource ← resource.subst subsmap
    let context := context.mapOnValues (Partial.Value.subst subsmap)
    some { principal, action, resource, context }


end Cedar.Partial

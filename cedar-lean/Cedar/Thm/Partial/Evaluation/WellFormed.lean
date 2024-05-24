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

import Cedar.Partial.Entities
import Cedar.Partial.Request
import Cedar.Partial.Value
import Cedar.Spec.Request
import Cedar.Spec.Value
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set

/-!
  This file defines `WellFormed` for various Spec and Partial types
-/

namespace Cedar.Spec

/--
  We define `WellFormed` for `Value` in the obvious way
-/
def Value.WellFormed (v : Value) : Prop :=
  match v with
  | .set s => s.WellFormed
  | .record r => r.WellFormed
  | _ => true

/--
  `Request`s are `WellFormed` if the context is `WellFormed`
-/
def Request.WellFormed (req : Request) : Prop :=
  req.context.WellFormed

end Cedar.Spec

namespace Cedar.Partial

/--
  We define `WellFormed` for `Partial.Value` using `Spec.Value.WellFormed`
-/
def Value.WellFormed (pval : Partial.Value) : Prop :=
  match pval with
  | .value v => v.WellFormed
  | .residual _ => true

/--
  `Partial.Request`s are `AllWellFormed` if the context is `WellFormed` and
  all the context's constituent `Partial.RestrictedValue`s are also `WellFormed`.
  (principal, action, and resource are always well-formed)
-/
def Request.AllWellFormed (preq : Partial.Request) : Prop :=
  preq.context.WellFormed ∧ ∀ rpval ∈ preq.context.values, rpval.WellFormed

/--
  We define `WellFormed` for `Partial.EntityData` in the obvious way
-/
def EntityData.WellFormed (edata : Partial.EntityData) : Prop :=
  edata.attrs.WellFormed ∧ edata.ancestors.WellFormed

/--
  `Partial.Entities` are `AllWellFormed` if they are `WellFormed` and all the
  constituent `Partial.EntityData` are also `WellFormed`
-/
def Entities.AllWellFormed (entities : Partial.Entities) : Prop :=
  entities.WellFormed ∧ ∀ edata ∈ entities.values, edata.WellFormed

end Cedar.Partial

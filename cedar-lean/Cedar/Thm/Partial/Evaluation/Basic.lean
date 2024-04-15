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

import Cedar.Partial.Entities
import Cedar.Partial.Evaluator
import Cedar.Partial.Request
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set

/-!
  This file contains definitions and lemmas used by multiple files in the
  Thm/Partial folder
-/

namespace Cedar.Thm

/--
  If `x` evaluates to a residual, that residual contains an unknown
-/
def Partial.Expr.ResidualsContainUnknowns (x : Partial.Expr) {request : Partial.Request} {entities : Partial.Entities} : Prop :=
  ∀ r,
  Partial.evaluate x request entities = .ok (.residual r) →
  r.containsUnknown

/--
  If `rpval` is a residual, that residual contains an unknown
-/
def Partial.RestrictedValue.ResidualsContainUnknowns (rpval : Partial.RestrictedValue) : Prop :=
  match rpval with
  | .residual r => r.containsUnknown
  | .value _ => true

/--
  All residuals in attribute values in `edata` contain unknowns
-/
def Partial.EntityData.ResidualsContainUnknowns (edata : Partial.EntityData) : Prop :=
  ∀ rpval ∈ edata.attrs.values, Partial.RestrictedValue.ResidualsContainUnknowns rpval

/--
  All residuals in attribute values in `entities` contain unknowns
-/
def Partial.Entities.ResidualsContainUnknowns (entities : Partial.Entities) : Prop :=
  ∀ edata ∈ entities.values, Partial.EntityData.ResidualsContainUnknowns edata

/--
  All residuals in a `request` (ie, in the `context`) contain unknowns
-/
def Partial.Request.ResidualsContainUnknowns (request : Partial.Request) : Prop :=
  ∀ val ∈ request.context.values, Partial.RestrictedValue.ResidualsContainUnknowns val

end Cedar.Thm

namespace Cedar.Spec

/--
  We define WellFormed for Value in the obvious way
-/
def Value.WellFormed (v : Value) : Prop :=
  match v with
  | .set s => s.WellFormed
  | .record r => r.WellFormed
  | _ => true

end Cedar.Spec

namespace Cedar.Partial

/--
  We define WellFormed for Partial.Value using Spec.Value.WellFormed
-/
def Value.WellFormed (pval : Partial.Value) : Prop :=
  match pval with
  | .value v => v.WellFormed
  | .residual _ => true

/--
  We define WellFormed for Partial.RestrictedValue using Spec.Value.WellFormed
-/
def RestrictedValue.WellFormed (rpval : Partial.RestrictedValue) : Prop :=
  match rpval with
  | .value v => v.WellFormed
  | .residual _ => true

/--
  Partial.Requests are AllWellFormed if the context is WellFormed and
  all the context's constituent Partial.RestrictedValues are also WellFormed.
  (principal, action, and resource are always well-formed)
-/
def Request.AllWellFormed (preq : Partial.Request) : Prop :=
  preq.context.WellFormed ∧ ∀ rpval ∈ preq.context.values, rpval.WellFormed

/--
  We define WellFormed for Partial.EntityData in the obvious way
-/
def EntityData.WellFormed (edata : Partial.EntityData) : Prop :=
  edata.attrs.WellFormed ∧ edata.ancestors.WellFormed

/--
  Partial.Entities are AllWellFormed if they are WellFormed and all the
  constituent Partial.EntityData are also WellFormed
-/
def Entities.AllWellFormed (entities : Partial.Entities) : Prop :=
  entities.WellFormed ∧ ∀ edata ∈ entities.values, edata.WellFormed

end Cedar.Partial

namespace Cedar.Thm.Partial.Evaluation

/--
  Partial evaluation always returns well-formed results
-/
theorem partial_eval_wf {expr : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} {pval : Partial.Value} :
  entities.AllWellFormed →
  (Partial.evaluate expr request entities = .ok pval) →
  pval.WellFormed
:= by
  sorry

end Cedar.Thm.Partial.Evaluation

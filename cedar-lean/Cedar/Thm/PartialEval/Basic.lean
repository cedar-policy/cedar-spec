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

import Cedar.Spec.PartialEntities
import Cedar.Spec.PartialEvaluator
import Cedar.Spec.PartialRequest
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set

/-!
  This file contains definitions and lemmas used by multiple files in the
  Thm/PartialEval folder
-/

namespace Cedar.Thm

open Cedar.Spec

/--
  If `x` evaluates to a residual, that residual contains an unknown
-/
def PartialExpr.ResidualsContainUnknowns (x : PartialExpr) {request : PartialRequest} {entities : PartialEntities} : Prop :=
  ∀ r,
  partialEvaluate x request entities = .ok (.residual r) →
  r.containsUnknown

/--
  If `rpval` is a residual, that residual contains an unknown
-/
def RestrictedPartialValue.ResidualsContainUnknowns (rpval : RestrictedPartialValue) : Prop :=
  match rpval with
  | .residual r => r.containsUnknown
  | .value _ => true

/--
  All residuals in attribute values in `edata` contain unknowns
-/
def PartialEntityData.ResidualsContainUnknowns (edata : PartialEntityData) : Prop :=
  ∀ rpval ∈ edata.attrs.values, RestrictedPartialValue.ResidualsContainUnknowns rpval

/--
  All residuals in attribute values in `entities` contain unknowns
-/
def PartialEntities.ResidualsContainUnknowns (entities : PartialEntities) : Prop :=
  ∀ edata ∈ entities.values, PartialEntityData.ResidualsContainUnknowns edata

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

/--
  We define WellFormed for PartialValue using Value.WellFormed
-/
def PartialValue.WellFormed (pval : PartialValue) : Prop :=
  match pval with
  | .value v => v.WellFormed
  | .residual _ => true

/--
  We define WellFormed for PartialEntityData in the obvious way
-/
def PartialEntityData.WellFormed (edata : PartialEntityData) : Prop :=
  edata.attrs.WellFormed ∧ edata.ancestors.WellFormed

/--
  PartialEntities are AllWellFormed if they are WellFormed and all the
  constituent PartialEntityData are also WellFormed
  well-formed
-/
def PartialEntities.AllWellFormed (entities : PartialEntities) : Prop :=
  entities.WellFormed ∧ ∀ edata ∈ entities.values, edata.WellFormed

end Cedar.Spec

namespace Cedar.Thm

open Cedar.Spec

/--
  Partial evaluation always returns well-formed results
-/
theorem partial_eval_wf {expr : PartialExpr} {request : PartialRequest} {entities : PartialEntities} {pval : PartialValue} :
  entities.AllWellFormed →
  (partialEvaluate expr request entities = .ok pval) →
  pval.WellFormed
:= by
  sorry

end Cedar.Thm

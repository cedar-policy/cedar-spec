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

import Cedar.TPE
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.Residual
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

abbrev PEWellTyped (env : TypeEnv)
  (r₁ r₂ : Residual)
  (req : Request)
  (preq : PartialRequest)
  (es : Entities)
  (pes : PartialEntities) : Prop :=
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine env req es preq pes →
  Residual.WellTyped env r₁ →
  Residual.WellTyped env r₂

theorem entity_data_from_partial
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {pe : PartialEntityData} :
  InstanceOfWellFormedEnvironment req es env →
  EntitiesRefine env es pes →
  pes.find? uid = some pe →
  ∃ (edata : EntityData),
    es.find? uid = some edata ∧
    PartialIsValid (fun attrs => ValueRefines env (.record edata.attrs) (.record attrs)) pe.attrs ∧
    PartialIsValid (· = edata.ancestors) pe.ancestors ∧
    PartialIsValid (fun tags => ValueRefines env (.record edata.tags) (.record tags)) pe.tags ∧
    InstanceOfSchemaEntry uid edata env
:= by
  sorry -- EntitiesRefine now uses ValueRefines instead of equality

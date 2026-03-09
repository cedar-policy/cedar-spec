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
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env r₁ →
  Residual.WellTyped env r₂

theorem entity_data_from_partial
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {pe : PartialEntityData} :
  InstanceOfWellFormedEnvironment req es env →
  EntitiesRefine es pes →
  pes.find? uid = some pe →
  ∃ (edata : EntityData),
    es.find? uid = some edata ∧
    PartialIsValid (· = edata.attrs) pe.attrs ∧
    PartialIsValid (· = edata.ancestors) pe.ancestors ∧
    PartialIsValid (· = edata.tags) pe.tags ∧
    InstanceOfSchemaEntry uid edata env
:= by
  intros h_wf h_eref h_find
  specialize h_eref uid pe h_find
  rcases h_eref with ⟨edata, h_es, h_attrs, h_anc, h_tags⟩
  exists edata
  refine ⟨h_es, h_attrs, h_anc, h_tags, ?_⟩
  unfold InstanceOfWellFormedEnvironment at h_wf
  rcases h_wf with ⟨_, _, h_schema⟩
  unfold InstanceOfSchema at h_schema
  exact h_schema.1 uid edata h_es

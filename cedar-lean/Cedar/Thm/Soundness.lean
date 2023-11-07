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

import Cedar.Spec
import Cedar.Thm.Lemmas.Validator
import Mathlib.Data.List.Basic

/-!
This file defines the top-level soundness property for the valdator.
--/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

/--
Top-level soundness theorem: If validation succeeds, then for any request
consistent with the schema, every policy in the store will satisfy `EvaluatesToBool`.
-/
theorem validate_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchSchema schema request entities →
  validate policies schema = .ok () →
  ∀ policy, policy ∈ policies → EvaluatesToBool policy request entities
:= by
  intro h₀ h₁ policy hₚ
  unfold validate at h₁
  simp at h₁
  apply typecheck_policy_with_environments_is_sound (envs:=schema.toEnvironments)
  intro env hₑ
  apply match_schema_implies_match_environments (schema:=schema)
  apply h₀
  apply hₑ
  apply (forM_all_ok _ _ h₁)
  assumption

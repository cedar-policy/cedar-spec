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

import Cedar.Spec.PartialExpr
import Cedar.Spec.Policy
import Cedar.Spec.Response

/-!
This file defines Cedar partial responses.
-/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

structure Residual where
  id : PolicyID
  effect : Effect
  condition : PartialExpr

structure ResidualResponse where
  residuals : List Residual
  determiningPolicies : Set PolicyID -- all policies that could possibly be determining, for any assignment of the unknowns
  erroringPolicies : Set PolicyID -- all policies that could possibly be erroring, for any assignment of the unknowns

inductive PartialResponse where
  | known (resp : Response)
  | residual (resp : ResidualResponse)

----- Derivations -----

deriving instance Repr, DecidableEq for Residual
deriving instance Repr, DecidableEq for ResidualResponse
deriving instance Repr, DecidableEq for PartialResponse

end Cedar.Spec

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

module

public import CedarRustModel.Convert
public import Cedar.Spec
import CedarRustModel.Lemmas.Authorizer

/-!
The model's authorizer (`cedar-rust-model/src/authorizer.rs`, extracted to
Lean by Aeneas) agrees with `Cedar.Spec.isAuthorized`.
-/

namespace CedarRustModel

open Aeneas.Std Cedar.Data Cedar.Spec
open cedar_rust_model

/-- The model's authorizer does not panic and agrees with `Cedar.Spec.isAuthorized`. -/
public theorem is_authorized_correct
    (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData))
    (ps : value.List authorizer.Policy) (lps : List Cedar.Spec.Policy)
    (hps : List.Forall₂ Policy.Corresponds (List.toList ps) lps) :
    ∃ r, authorizer.is_authorized req es ps = .ok r ∧
      Response.toSpec r =
        Cedar.Spec.isAuthorized (Request.toSpec req) (Entities.toSpec es) lps :=
  is_authorized_ok req es ps lps hps

end CedarRustModel

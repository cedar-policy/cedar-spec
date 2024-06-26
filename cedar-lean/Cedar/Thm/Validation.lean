import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
If validation succeeds, then for any request consistent with the schema, either
(1) evaluation of every policy produces a boolean or (2) returns an error TODO
-/

theorem validation_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
validate policies schema = .ok () →
RequestAndEntitiesConsistentWithSchema schema request entities →
AllEvaluateCorrectly policies request entities := by
intro h₀ h₁
unfold validate at h₀


-- end Cedar.Thm

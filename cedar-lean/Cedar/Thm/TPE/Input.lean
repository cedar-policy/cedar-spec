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

import Cedar.TPE.Input
import Cedar.Spec
import Cedar.Validation

namespace Cedar.Thm.TPE

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation

def PartialRequestAndEntitiesMatchEnvironment (env : Environment) (request : PartialRequest) (entities : PartialEntities) : Prop := sorry

def IsConsistent (env : Environment) (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Prop := sorry

end Cedar.Thm.TPE

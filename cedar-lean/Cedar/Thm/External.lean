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

-- These files contain theorems about partial schemas, which may declare external entity types and
-- actions, about linking them, and about validating requests and entities against them.
import Cedar.Thm.External.PartialSchema
import Cedar.Thm.External.Linker
import Cedar.Thm.External.PartialValidation

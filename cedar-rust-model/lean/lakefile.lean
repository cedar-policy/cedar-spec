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

import Lake
open Lake DSL

-- Must match the version of `aeneas` used to generate `CedarRustModel/Extracted.lean`
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "74aabd52f77001cf9eaad51b4f4b867a7dc6b111" / "backends" / "lean"

require Cedar from "../../cedar-lean"

package CedarRustModel

@[default_target]
lean_lib CedarRustModel

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

import CedarGenProof.ExprGen.Parts
import CedarGenProof.ExprGen.Sound

/-! # `CedarGen.Relational.ExprGen`'s derivation, proved sound and complete

`Sound` proves every definition sound. `Setup` proves the enumerators' searches and every component
complete but the large ones, whose parts `Parts` proves in files Lake checks in parallel. Each command
fails if a law it proves depends on an axiom but `propext`, `Classical.choice` and `Quot.sound`; this
module imports them all and reports the laws by kind. -/

#specimen_audit "RequestVars"

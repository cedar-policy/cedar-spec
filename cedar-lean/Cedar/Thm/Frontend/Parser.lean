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

import Cedar.Thm.Frontend.StringParsing
import Cedar.Thm.Frontend.Parser.Ident

/-! This file states and proves the main theorems about the Cedar parser's pure functions. -/

namespace Cedar.Frontend.Cst.Parser

/-- `classifyIdent` is a left inverse of `Ident.toString`. -/
theorem classifyIdent_roundtrip (i : Ident) :
    classifyIdent i.toString = i := by
  cases i with
  | idIdent s h => apply classifyIdent_toString_ident
  | _ => rfl

end Cedar.Frontend.Cst.Parser

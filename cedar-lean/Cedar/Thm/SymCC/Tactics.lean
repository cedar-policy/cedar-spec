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

import Cedar.Thm.SymCC.Data

/-!
This file contains basic utility tactics.
--/

namespace Cedar.Thm


/--
This tactic simplifes assumptions of the form `do (let x ← expr ...)` by
performing a `cases` and `simp` on `expr`.
-/

syntax "simp_do_let" term (" at " ident)? : tactic

macro_rules
| `(tactic| simp_do_let $e $[at $h:ident]?) =>
  `(tactic|
    cases h' : $e <;>
    simp only [h', Except.bind_err, Except.bind_ok, reduceCtorEq] $[at $h:ident]?)

open Lean Elab Meta Tactic in
elab "clean_i" : tactic => liftMetaTactic fun mvarId => mvarId.withContext do
  let mut toClear := #[]
  for localDecl in (← getLCtx) do
    if localDecl.userName.hasMacroScopes then
      toClear := toClear.push localDecl.fvarId
  return [← mvarId.tryClearMany toClear]

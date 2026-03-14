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

import Cedar.TPE
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

theorem partial_eval_well_typed_hasAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.hasAttr expr attr ty) (TPE.evaluate (Residual.hasAttr expr attr ty) preq pes) req preq es pes
:= by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.hasAttr]
  split
  case h_1 =>
    apply Residual.WellTyped.error
  case h_2 r₁ h₁ =>
    split
    case h_1 x m h₂ =>
      exact well_typed_bool
    case h_2 x h₂ =>
      -- unknown(tgt, _) → .hasAttr tgt attr ty
      -- Need WellTyped env (.hasAttr tgt attr ty)
      -- This requires target well-typedness (Lemma 7.3)
      sorry
    case h_3 =>
      -- none → false
      exact well_typed_bool
  case h_3 =>
    -- entity case: match on pes.attrs uid
    split
    · -- some attrs: match on attrs.find? attr
      split
      · exact well_typed_bool  -- present → true
      · -- unknown → .hasAttr r attr ty (entity case)
        cases h_wt with
        | hasAttr_entity h₅ h₆ =>
          exact .hasAttr_entity h_expr_wt (by rw [partial_eval_preserves_typeof _ h₅ preq pes]; exact h₆)
        | hasAttr_record h₅ h₆ =>
          exact .hasAttr_record h_expr_wt (by rw [partial_eval_preserves_typeof _ h₅ preq pes]; exact h₆)
      · exact well_typed_bool  -- none → false
    · -- none → .hasAttr r attr ty
      cases h_wt with
      | hasAttr_entity h₅ h₆ =>
        exact .hasAttr_entity h_expr_wt (by rw [partial_eval_preserves_typeof _ h₅ preq pes]; exact h₆)
      | hasAttr_record h₅ h₆ =>
        exact .hasAttr_record h_expr_wt (by rw [partial_eval_preserves_typeof _ h₅ preq pes]; exact h₆)
  case h_4 =>
    -- non-value: .hasAttr r attr ty
    cases h_wt with
    | hasAttr_entity h₅ h₆ =>
      exact .hasAttr_entity h_expr_wt (by rw [partial_eval_preserves_typeof _ h₅ preq pes]; exact h₆)
    | hasAttr_record h₅ h₆ =>
      exact .hasAttr_record h_expr_wt (by rw [partial_eval_preserves_typeof _ h₅ preq pes]; exact h₆)

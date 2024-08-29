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

import Cedar.Partial.Evaluator
import Cedar.Spec.Expr
import Cedar.Thm.Partial.WellFormed

/-!
  This file contains definitions of `Prop`s used by multiple files in the
  Thm/Partial/Evaluation folder
-/

namespace Cedar.Thm.Partial

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Expr)

/--
  Prop that partial evaluation and concrete evaluation of the same concrete
  expression/request/entities produce the same result
-/
def PartialEvalEquivConcreteEval (expr : Expr) (request : Spec.Request) (entities : Spec.Entities) : Prop :=
  Partial.evaluate expr request entities = (Spec.evaluate expr request entities).map Partial.Value.value

/--
  Prop that partial evaluation returns a concrete value
-/
def EvaluatesToConcrete (expr : Expr) (request : Partial.Request) (entities : Partial.Entities) : Prop :=
  ∃ v, Partial.evaluate expr request entities = .ok (.value v)

/--
  Prop that .subst preserves evaluation to a concrete value
-/
def SubstPreservesEvaluationToConcrete (expr : Expr) (req req' : Partial.Request) (entities : Partial.Entities) (subsmap : Subsmap) : Prop :=
  req.subst subsmap = some req' →
  ∀ v,
    Partial.evaluate expr req entities = .ok (.value v) →
    Partial.evaluate expr req' (entities.subst subsmap) = .ok (.value v)

/--
  Prop that .subst preserves evaluation to an error

  (not necessarily the same error, but some error)
-/
def SubstPreservesEvaluationToError (expr : Expr) (req req' : Partial.Request) (entities : Partial.Entities) (subsmap : Subsmap) : Prop :=
  req.subst subsmap = some req' →
  ∀ e,
    Partial.evaluate expr req entities = .error e →
    ∃ e', Partial.evaluate expr req' (entities.subst subsmap) = .error e'

/--
  Prop that a list of partial values is actually a list of concrete values
-/
def IsAllConcrete (pvals : List Partial.Value) : Prop :=
  ∃ vs, pvals.mapM (λ x => match x with | .value v => some v | .residual _ => none) = some vs

/--
  Prop that partial evaluation returns a well-formed value
-/
def EvaluatesToWellFormed (expr : Expr) (request : Partial.Request) (entities : Partial.Entities) : Prop :=
  ∀ pval, Partial.evaluate expr request entities = .ok pval → pval.WellFormed

end Cedar.Thm.Partial

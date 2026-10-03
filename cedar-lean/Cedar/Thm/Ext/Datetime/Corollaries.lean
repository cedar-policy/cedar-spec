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

public import Cedar.Thm.Ext.Datetime

namespace Cedar.Thm.Datetime
open Cedar.Spec.Ext
open Datetime

/-! # Derived datetime parser corollaries -/

/-- Exact parser characterization derived from soundness and completeness: parsing succeeds with
    `d` precisely when the declarative grammar relation assigns the input the value
    `d.val.toInt`. -/
public theorem parse_eq_some_iff_isDatetimeValue (str : String) (d : Datetime) :
    Datetime.parse str = some d ↔ IsDatetimeValue str d.val.toInt :=
  ⟨parse_sound str d, parse_complete str d⟩

/-- Total `Option` formulation of the partial serialization roundtrip. -/
public theorem bind_parse_toString? (d : Datetime) :
    (toString? d).bind Datetime.parse = (toString? d).map (fun _ => d) := by
  cases h : toString? d with
  | none => rfl
  | some str =>
    simp only [Option.bind_some, Option.map_some]
    exact parse_toString_roundtrip h

end Cedar.Thm.Datetime

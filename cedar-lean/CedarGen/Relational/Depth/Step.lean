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

import CedarGen.Relational.Depth.Bound

/-! One fuel step of the depth bound, per worker of the expression-producing block. -/

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness
open Cedar.Validation.Relational.ExprGen.RequestVars

set_option maxHeartbeats 4000000

theorem stepHasType (f : Nat) (ih : Bound f) : HasTypeBound (f + 1) := by depth_step f ih
theorem stepExtCall (f : Nat) (ih : Bound f) : ExtCallBound (f + 1) := by depth_step f ih
theorem stepList (f : Nat) (ih : Bound f) : ListBound (f + 1) := by depth_step f ih
theorem stepRecordOf (f : Nat) (ih : Bound f) : RecordOfBound (f + 1) := by depth_step f ih
theorem stepFields (f : Nat) (ih : Bound f) : FieldsBound (f + 1) := by depth_step f ih
theorem stepHasTypeTy (f : Nat) (ih : Bound f) : HasTypeTyBound (f + 1) := by depth_step f ih
theorem stepExtCallTy (f : Nat) (ih : Bound f) : ExtCallTyBound (f + 1) := by depth_step f ih
theorem stepRecordOfTy (f : Nat) (ih : Bound f) : RecordOfTyBound (f + 1) := by depth_step f ih
theorem stepRecordTy (f : Nat) (ih : Bound f) : RecordTyBound (f + 1) := by depth_step f ih
theorem stepRecord (f : Nat) (ih : Bound f) : RecordBound (f + 1) := by depth_step f ih

end Cedar.Validation.Relational.Depth

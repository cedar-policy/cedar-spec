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

import Cedar.SymCC.Env

/-! Some facts about `UUF.*_id`s. -/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC

theorem uuf_attrs_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.attrs_id ety₁ ≠ UUF.ancs_id ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp [UUF.attrs_id, UUF.ancs_id, toString, String.data]

theorem uuf_attrs_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.attrs_id ety₁ ≠ UUF.tag_keys_id ety₂
:= by
  apply String.ne_of_data_ne
  simp [UUF.attrs_id, UUF.tag_keys_id, toString, String.data]

theorem uuf_attrs_tag_vals_no_confusion
  {ety₁ ety₂} :
  UUF.attrs_id ety₁ ≠ UUF.tag_vals_id ety₂
:= by
  apply String.ne_of_data_ne
  simp [UUF.attrs_id, UUF.tag_vals_id, toString, String.data]

theorem uuf_tag_vals_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.tag_vals_id ety₁ ≠ UUF.tag_keys_id ety₂
:= by
  apply String.ne_of_data_ne
  simp [UUF.tag_keys_id, UUF.tag_vals_id, toString, String.data]

theorem uuf_tag_keys_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tag_keys_id ety₁ ≠ UUF.ancs_id ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp [UUF.tag_keys_id, UUF.ancs_id, toString, String.data]

theorem uuf_tag_vals_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tag_vals_id ety₁ ≠ UUF.ancs_id ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp [UUF.tag_vals_id, UUF.ancs_id, toString, String.data]

end Cedar.Thm

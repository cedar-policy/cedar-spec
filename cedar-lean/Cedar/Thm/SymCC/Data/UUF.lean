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

theorem prefix_ne_at_index {p₁ p₂ x y : String} {i : Nat}
  (h₁ : i < p₁.data.length)
  (h₂ : i < p₂.data.length)
  (hₙ : p₁.data[i]? ≠ p₂.data[i]?) :
  (p₁ ++ x).data ≠ (p₂ ++ y).data := by
  intro h
  have hᵢ := congrArg (fun l => l[i]?) h
  simp only at hᵢ
  rw [String.data_append, String.data_append] at hᵢ
  rw [List.getElem?_append_left h₁] at hᵢ
  rw [List.getElem?_append_left h₂] at hᵢ
  contradiction

macro "gen_prefix_no_confusion" name:ident p₁:str p₂:str i:num : command => do
  let newName := Lean.mkIdent (name.getId.appendAfter "_no_confusion_prefix")
  `(theorem $newName {x y : String} : ($p₁ ++ x).data ≠ ($p₂ ++ y).data := by
      apply prefix_ne_at_index (i := $i)
      · decide
      · decide
      · decide
   )

gen_prefix_no_confusion attrs_ancs      "attrs["   "ancs["    1
gen_prefix_no_confusion attrs_tagKeys   "attrs["   "tagKeys[" 0
gen_prefix_no_confusion attrs_tagVals   "attrs["   "tagVals[" 0
gen_prefix_no_confusion tagVals_tagKeys "tagVals[" "tagKeys[" 3
gen_prefix_no_confusion tagKeys_ancs    "tagKeys[" "ancs["    0
gen_prefix_no_confusion tagVals_ancs    "tagVals[" "ancs["    0

theorem uuf_attrs_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.attrsId ety₁ ≠ UUF.ancsId ety₂ ancTy := by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, toString, UUF.ancsId, String.append_assoc]
  exact attrs_ancs_no_confusion_prefix

theorem uuf_attrs_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.attrsId ety₁ ≠ UUF.tagKeysId ety₂
:= by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, UUF.tagKeysId, toString, String.append_assoc]
  exact attrs_tagKeys_no_confusion_prefix

theorem uuf_attrs_tag_vals_no_confusion
  {ety₁ ety₂} :
  UUF.attrsId ety₁ ≠ UUF.tagValsId ety₂
:= by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, UUF.tagValsId, toString, String.append_assoc]
  exact attrs_tagVals_no_confusion_prefix

theorem uuf_tag_vals_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.tagValsId ety₁ ≠ UUF.tagKeysId ety₂
:= by
  apply String.ne_of_data_ne
  simp only [UUF.tagValsId, UUF.tagKeysId, toString, String.append_assoc]
  exact tagVals_tagKeys_no_confusion_prefix

theorem uuf_tag_keys_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tagKeysId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp only [UUF.tagKeysId, UUF.ancsId, toString, String.append_assoc]
  exact tagKeys_ancs_no_confusion_prefix

theorem uuf_tag_vals_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tagValsId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp only [UUF.tagValsId, UUF.ancsId, toString, String.append_assoc]
  exact tagVals_ancs_no_confusion_prefix

end Cedar.Thm

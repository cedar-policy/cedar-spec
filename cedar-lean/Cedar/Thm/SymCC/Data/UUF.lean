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

theorem attrs_ancs_no_confusion_prefix {x y: String} :
  ("attrs[" ++ x).data = ("ancs[" ++ y).data → False := by
  intro h
  have h₁ : "attrs[".data[1]? = some 't' := rfl
  have h₂ : "ancs[".data[1]? = some 'n' := rfl
  have h₃ : "attrs[".data[1]? = "ancs[".data[1]? := by
    have h_eq : ("attrs[" ++ x).data[1]? = ("ancs[" ++ y).data[1]? := by
      rw[h]
    have h_len1 : "attrs[".data.length > 1 := by decide
    have h_len2 : "ancs[".data.length > 1 := by decide
    rw [String.data_append, List.getElem?_append_left h_len1] at h_eq
    rw [String.data_append, List.getElem?_append_left h_len2] at h_eq
    exact h_eq
  rw [h₁, h₂] at h₃
  simp at h₃

theorem attrs_tag_keys_confusion_prefix {x y: String} :
  ("attrs[" ++ x).data = ("tagKeys[" ++ y).data → False := by
  intro h
  have h₁ : "attrs[".data[0]? = some 'a' := rfl
  have h₂ : "tagKeys[".data[0]? = some 't' := rfl
  have h₃ : "attrs[".data[0]? = "tagKeys[".data[0]? := by
    have h_eq : ("attrs[" ++ x).data[0]? = ("tagKeys[" ++ y).data[0]? := by
      rw[h]
    have h_len1 : "attrs[".data.length > 0 := by decide
    have h_len2 : "tagKeys[".data.length > 0 := by decide
    rw [String.data_append, List.getElem?_append_left h_len1] at h_eq
    rw [String.data_append, List.getElem?_append_left h_len2] at h_eq
    exact h_eq
  rw [h₁, h₂] at h₃
  simp at h₃

theorem uuf_attrs_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.attrsId ety₁ ≠ UUF.ancsId ety₂ ancTy := by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, toString, UUF.ancsId, ne_eq]
  intro h
  rw [String.append_assoc] at h
  have this : ("ancs[" ++ (String.join (List.map (fun s => s ++ "::") ety₂.path) ++ ety₂.id) ++ ", " ++
        (String.join (List.map (fun s => s ++ "::") ancTy.path) ++ ancTy.id) ++
      "]") = "ancs[" ++ ((String.join (List.map (fun s => s ++ "::") ety₂.path) ++ ety₂.id) ++ ", " ++
        (String.join (List.map (fun s => s ++ "::") ancTy.path) ++ ancTy.id) ++
      "]") := by
      rfl
  rw [this] at h
  exact attrs_ancs_no_confusion_prefix h

theorem uuf_attrs_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.attrsId ety₁ ≠ UUF.tagKeysId ety₂
:= by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, UUF.tagKeysId, toString, ne_eq]
  intro h
  rw [String.append_assoc] at h
  have this : "tagKeys[" ++ (String.join (List.map (fun s => s ++ "::") ety₂.path) ++ ety₂.id) ++ "]" =
    "tagKeys[" ++ ((String.join (List.map (fun s => s ++ "::") ety₂.path) ++ ety₂.id) ++ "]") := by
    rfl
  rw [this] at h
  exact attrs_tag_keys_confusion_prefix h

theorem uuf_attrs_tag_vals_no_confusion
  {ety₁ ety₂} :
  UUF.attrsId ety₁ ≠ UUF.tagValsId ety₂
:= by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, UUF.tagValsId, toString]
  sorry

theorem uuf_tag_vals_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.tagValsId ety₁ ≠ UUF.tagKeysId ety₂
:= by
  apply String.ne_of_data_ne
  simp only [UUF.attrsId, UUF.tagValsId, toString]
  sorry

theorem uuf_tag_keys_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tagKeysId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp only [UUF.tagKeysId, UUF.ancsId, toString]
  sorry

theorem uuf_tag_vals_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tagValsId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  apply String.ne_of_data_ne
  simp only [UUF.tagValsId, UUF.ancsId, toString]
  sorry

end Cedar.Thm

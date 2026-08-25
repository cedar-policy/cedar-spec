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

import Cedar.Frontend.Parser
import Cedar.Frontend.Cst

/-! This file contains lemmas for proving roundtrip properties of ident conversion. -/

namespace Cedar.Frontend.Cst.Parser

open Cedar.Frontend.Cst

----- classifyIdent / Ident.toString roundtrip -----

/-- `classifyIdent` is a left inverse of `Ident.toString` for keyword identifiers. -/
theorem classifyIdent_toString_keyword (i : Cst.Ident) (h : ¬∃ s hs, i = .idIdent s hs) :
    classifyIdent (Ident.toString i) = i := by
  cases i with
  | idIdent s hs => exact absurd ⟨s, hs, rfl⟩ h
  | _ => rfl

/-- `classifyIdent` roundtrips with `Ident.toString` when the string is not a keyword. -/
theorem classifyIdent_toString_ident (s : String)
    (h : s ∉ keywords) :
    classifyIdent (Ident.toString (.idIdent s h)) = .idIdent s h := by
  simp only [Ident.toString, classifyIdent, h, ↓reduceDIte]

/-- `Ident.toString` is a left inverse of `classifyIdent` for all Cedar keywords. -/
theorem toString_classifyIdent_keyword (s : String) (h : s ∈ keywords) :
    Ident.toString (classifyIdent s) = s := by
  simp only [keywords, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> rfl

/-- `Ident.toString` is a left inverse of `classifyIdent` for non-keyword identifiers. -/
theorem toString_classifyIdent_ident (s : String)
    (h : s ∉ keywords) :
    Ident.toString (classifyIdent s) = s := by
  simp only [classifyIdent, dif_neg h, Ident.toString]

public theorem unreserved_iff_not_in_keywords {s : String} :
    s.toUnreservedCedarId?.isSome = true ↔ s ∉ keywords := by
  simp only [String.toUnreservedCedarId?]
  split <;> simp_all

@[simp]
public theorem Ident.toUnreservedString?_idIdent (s : String) (h : s ∉ keywords) :
    Ident.toUnreservedString? (.idIdent s h) = some s := by
  simp [Ident.toUnreservedString?, String.toUnreservedCedarId?, h]

@[simp]
public theorem Ident.toString_idIdent (s : String) (h : s ∉ keywords) :
    Ident.toString (.idIdent s h) = s := rfl

public theorem toUnreservedCedarId_some_eq {s s0: String} (h: s.toUnreservedCedarId? = some s0) :
     s = s0 := by
  simp only [String.toUnreservedCedarId?] at h
  split at h <;> simp_all

end Cedar.Frontend.Cst.Parser

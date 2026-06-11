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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Data

/-!
# lub preserves CedarType.WellFormed

Proves that `lub?` preserves the `CedarType.WellFormed` property: if the left
input is well-formed and `lub?` succeeds, the result is well-formed.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

private theorem lubRecordType_preserves_keys
    {r₁ r₂ r : List (Attr × Qualified CedarType)}
    (hlub : lubRecordType r₁ r₂ = some r) :
    r.map Prod.fst = r₁.map Prod.fst := by
  induction r₁ generalizing r₂ r with
  | nil =>
    cases r₂ <;> simp [lubRecordType] at hlub
    subst hlub; simp
  | cons hd₁ tl₁ ih =>
    cases r₂ with
    | nil => simp [lubRecordType] at hlub
    | cons hd₂ tl₂ =>
      unfold lubRecordType at hlub
      cases hk : (hd₁.fst != hd₂.fst) with
      | true => simp [hk] at hlub
      | false =>
        simp [hk] at hlub
        have hk' : hd₁.fst = hd₂.fst := by
          have := Bool.eq_false_iff.mp hk; simp [bne] at this; exact this
        cases hq : lubQualifiedType hd₁.snd hd₂.snd <;> simp [hq] at hlub
        cases hr : lubRecordType tl₁ tl₂ <;> simp [hr] at hlub
        subst hlub; simp [hk', ih hr]

private theorem sortedBy_of_same_keys {α β₁ β₂ : Type} [LT α]
    {r₁ : List (α × β₁)} {r : List (α × β₂)}
    (hsorted : r₁.SortedBy Prod.fst)
    (hkeys : r.map Prod.fst = r₁.map Prod.fst) :
    r.SortedBy Prod.fst := by
  induction r generalizing r₁ with
  | nil => exact .nil
  | cons hd tl ih =>
    cases r₁ with
    | nil => simp at hkeys
    | cons hd₁ tl₁ =>
      simp at hkeys
      obtain ⟨hfst, htl_keys⟩ := hkeys
      cases tl with
      | nil => exact .cons_nil
      | cons hd' tl' =>
        cases tl₁ with
        | nil => simp at htl_keys
        | cons hd₁' tl₁' =>
          simp at htl_keys
          obtain ⟨hfst', htl'_keys⟩ := htl_keys
          have hsorted_tl₁ : (hd₁' :: tl₁').SortedBy Prod.fst := by
            cases hsorted with
            | cons_cons _ h => exact h
          apply List.SortedBy.cons_cons
          · rw [hfst, hfst']
            cases hsorted with
            | cons_cons hlt _ => exact hlt
          · exact ih hsorted_tl₁ (by simp [hfst', htl'_keys])

private theorem lubRecordType_preserves_map_wf
    {r₁ r₂ r : List (Attr × Qualified CedarType)}
    (hwf : Map.WellFormed (Map.mk r₁))
    (hlub : lubRecordType r₁ r₂ = some r) :
    Map.WellFormed (Map.mk r) := by
  rw [Map.wf_iff_sorted]; simp only [Map.toList_mk_id]
  have hsorted := (Map.wf_iff_sorted.mp hwf)
  simp only [Map.toList_mk_id] at hsorted
  exact sortedBy_of_same_keys hsorted (lubRecordType_preserves_keys hlub)

/--
`lub?` preserves `CedarType.WellFormed`: if `ty₁` is well-formed and
`lub? ty₁ ty₂ = some ty`, then `ty` is well-formed.
-/
theorem lub_preserves_wf_left {env : TypeEnv} {ty₁ ty₂ ty : CedarType}
    (hwf : CedarType.WellFormed env ty₁)
    (hlub : lub? ty₁ ty₂ = some ty) :
    CedarType.WellFormed env ty := by
  unfold lub? at hlub
  split at hlub
  · simp [lubBool] at hlub; subst hlub; exact .bool_wf
  · rename_i s₁ s₂
    cases hlu : @lub? s₁ s₂ <;> simp [hlu] at hlub
    subst hlub; cases hwf with | set_wf h => exact .set_wf (lub_preserves_wf_left h hlu)
  · rename_i r₁ r₂
    cases hlubr : lubRecordType r₁ r₂ <;> simp [hlubr] at hlub
    subst hlub; cases hwf with
    | record_wf hwf_map hattr_wf =>
      apply CedarType.WellFormed.record_wf
      · exact lubRecordType_preserves_map_wf hwf_map hlubr
      · intro attr qty hfind
        have hlub_rel := lubRecordType_is_lub_of_record_types hlubr
        have ⟨qty₁', qty₂', hfind₁, _, hlubq⟩ := lubRecord_find_implies_find hlub_rel hfind
        have hqty₁_wf := hattr_wf attr qty₁' hfind₁
        cases qty₁' with
        | required ty_inner =>
          cases hqty₁_wf with
          | required_wf hwf_inner =>
            cases qty₂' with
            | required ty_inner₂ =>
              simp [lubQualifiedType] at hlubq
              cases hlu : lub? ty_inner ty_inner₂ <;> simp [hlu] at hlubq
              subst hlubq
              have _hsz : sizeOf ty_inner < sizeOf (CedarType.record (Map.mk r₁)) :=
                sizeOf_attr_type_lt_sizeOf_record_type rfl hfind₁
              exact .required_wf (lub_preserves_wf_left hwf_inner hlu)
            | optional _ => simp [lubQualifiedType] at hlubq
        | optional ty_inner =>
          cases hqty₁_wf with
          | optional_wf hwf_inner =>
            cases qty₂' with
            | optional ty_inner₂ =>
              simp [lubQualifiedType] at hlubq
              cases hlu : lub? ty_inner ty_inner₂ <;> simp [hlu] at hlubq
              subst hlubq
              have _hsz : sizeOf ty_inner < sizeOf (CedarType.record (Map.mk r₁)) :=
                sizeOf_attr_type_lt_sizeOf_record_type rfl hfind₁
              exact .optional_wf (lub_preserves_wf_left hwf_inner hlu)
            | required _ => simp [lubQualifiedType] at hlubq
  · split at hlub
    · simp at hlub; subst hlub; exact hwf
    · simp at hlub
  termination_by sizeOf ty₁

end Cedar.Thm

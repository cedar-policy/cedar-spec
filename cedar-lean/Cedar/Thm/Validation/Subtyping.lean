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
import Cedar.Validation.Types
import Cedar.Validation.Subtyping
import Cedar.Data.Map
import Cedar.Thm

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.Data
open Cedar.Thm

mutual

inductive IsSubtype : CedarType → CedarType → Prop
| bool (bty₁ : BoolType) (bty₂ : BoolType)
  (h : bty₁ = bty₂ ∨ bty₂ = .anyBool) :
  IsSubtype (.bool bty₁) (.bool bty₂)
| int : IsSubtype .int .int
| string : IsSubtype .string .string
| entity (ety₁ : EntityType) (ety₂ : EntityType)
  (h : ety₁ = ety₂) :
  IsSubtype (.entity ety₁) (.entity ety₂)
| set (ety₁ : CedarType) (ety₂ : CedarType)
  (h : IsSubtype ety₁ ety₂) :
  IsSubtype (.set ety₁) (.set ety₂)
| record_empty : IsSubtype (.record (Map.mk [])) (.record (Map.mk []))
| record_optional
  (a₁ : Attr)
  (t₁ : CedarType)
  (a₂ : Attr)
  (t₂ : CedarType)
  (m₁ : List (Attr × QualifiedType))
  (m₂ : List (Attr × QualifiedType))
  (h₁ : a₁ = a₂)
  (h₂ : IsSubtype t₁ t₂)
  (h₃ : IsSubtype (.record (Map.mk m₁)) (.record (Map.mk m₂))) :
  IsSubtype (.record (Map.mk ((a₁, (.optional t₁))::m₁))) (.record (Map.mk ((a₂, (.optional t₂))::m₂)))
| record_required
  (a₁ : Attr)
  (t₁ : CedarType)
  (a₂ : Attr)
  (t₂ : CedarType)
  (m₁ : List (Attr × QualifiedType))
  (m₂ : List (Attr × QualifiedType))
  (h₁ : a₁ = a₂)
  (h₂ : IsSubtype t₁ t₂)
  (h₃ : IsSubtype (.record (Map.mk m₁)) (.record (Map.mk m₂))) :
  IsSubtype (.record (Map.mk ((a₁, (.required t₁))::m₁))) (.record (Map.mk ((a₂, (.required t₂))::m₂)))
| ext (ety₁ : ExtType) (ety₂ : ExtType)
  (h : ety₁ = ety₂) :
  IsSubtype (.ext ety₁) (.ext ety₂)
end

theorem subty_means_is_subtype (ty₁ ty₂ : CedarType) :
  subty ty₁ ty₂ = true → IsSubtype ty₁ ty₂ := by
  intro h
  simp only [subty] at h
  split at h
  case _ ty heq =>
    unfold lub? at heq
    split at heq <;> simp only [decide_eq_true_eq] at h <;> rw [h] at heq
    case _ b₁ b₂ =>
      simp only [lubBool, Option.some.injEq, CedarType.bool.injEq] at heq
      have h₁ : b₁ = b₂ ∨ b₂ = BoolType.anyBool := by
        split at heq
        case _ heq₁ =>
          apply Or.inl
          exact heq₁
        case _ =>
          apply Or.inr
          symm at heq
          exact heq
      exact IsSubtype.bool b₁ b₂ h₁
    case _ s₁ s₂ =>
      rw [do_some] at heq
      cases heq
      case _ ty heq₁ =>
        have ⟨heq₁, heq₂⟩ := heq₁
        have heq₁ : subty s₁ s₂ = true := by
          unfold subty
          rw [heq₁]
          simp only [decide_eq_true_eq]
          simp only [CedarType.set.injEq] at heq₂
          exact heq₂
        exact IsSubtype.set s₁ s₂ (subty_means_is_subtype s₁ s₂ heq₁)
    case _ r₁ r₂ =>
      rw [do_some] at heq
      cases heq
      case _ r heq₁ =>
        have ⟨heq₁, heq₂⟩ := heq₁
        simp only [CedarType.record.injEq, Map.mk.injEq] at heq₂
        rw [heq₂] at heq₁
        unfold lubRecordType at heq₁
        split at heq₁
        case _ =>
          exact IsSubtype.record_empty
        case _ k₁ q₁ r₁ k₂ q₂ r₂ heq₃ =>
          sorry
        case _ =>
          cases heq₁
    case _ => sorry
  case _ =>
    cases h

theorem record_subtype_means_equiv_attrs { l₁ l₂ : List (Attr × QualifiedType) } :
  IsSubtype (.record (Map.mk l₁)) (.record (Map.mk l₂)) →
    ∀ a, a ∈ (Map.mk l₁) → a ∈ (Map.mk l₂) := by
  intro h a h₁
  cases h
  case _ =>
    exact h₁
  case _ a₁ ty₁ a₂ ty₂ m₁ m₂ h₂ h₃ h₄ =>
    have h₅ := record_subtype_means_equiv_attrs h₄
    sorry
  case _ => sorry

theorem instance_of_subtype_is_instance_of_type {ty₁ ty₂ : CedarType} {v : Value} :
  IsSubtype ty₁ ty₂ → InstanceOfType v ty₁ → InstanceOfType v ty₂ := by
  intro h₁ h₂
  cases h₂ <;> cases h₁
  case instance_of_bool b bty₁ h₃ bty₂ h₄ =>
    cases h₄
    case _ h =>
      rw [h] at h₃
      exact InstanceOfType.instance_of_bool b bty₂ h₃
    case _ h =>
      rw [h]
      exact bool_is_instance_of_anyBool b
  case instance_of_int x =>
    exact InstanceOfType.instance_of_int
  case instance_of_string s =>
    exact InstanceOfType.instance_of_string
  case instance_of_entity uid ety₁ h₃ ety₂ h₄ =>
    rw [← h₄]
    exact InstanceOfType.instance_of_entity uid ety₁ h₃
  case instance_of_set s ty₁ h₃ ty₂ h₄ =>
    have h₅ : ∀ v, v ∈ s → InstanceOfType v ty₂ := by
      intro v hᵢ
      have h₃ := h₃ v hᵢ
      exact instance_of_subtype_is_instance_of_type h₄ h₃
    exact InstanceOfType.instance_of_set s ty₂ h₅
  case _ m h₃ h₄ h₅ =>
    exact InstanceOfType.instance_of_record m (Map.mk []) h₃ h₄ h₅
  case _ m a₁ ty₁ a₂ ty₂ l₁ l₂ h₃ h₄ h₅ h₆ h₇ h₈ =>
    have h₉ : ∀ (k : Attr), m.contains k → ((Map.mk ((a₂, Qualified.optional ty₂) :: l₂)).contains k) := by
      sorry
    sorry
  case _ => sorry
  case instance_of_ext x xty₁ h₃ xty₂ h₅ =>
    rw [← h₅]
    exact InstanceOfType.instance_of_ext x xty₁ h₃
end Cedar.Thm

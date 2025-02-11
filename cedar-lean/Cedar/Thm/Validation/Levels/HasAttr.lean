import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Slice
import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel

/-!
This file proves that level checking for `.hasAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_has_attr_entity {e : Expr} {tx₁: TypedExpr} {ty : CedarType} {a : Attr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (hl : checkLevel (tx₁.hasAttr a ty) n = true)
  (ht : typeOf e c₀ env = Except.ok (tx₁, c₁))
  (hety : tx₁.typeOf = CedarType.entity ety)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.hasAttr e a) request entities = evaluate (.hasAttr e a) request slice
:= by
  have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc hr ht
  rw [hety] at h₁₄
  replace ⟨ euid, h₁₄, h₁₅⟩ := instance_of_entity_type_is_entity h₁₄
  subst h₁₄ h₁₅
  simp [checkLevel, hety] at hl
  have ⟨ ⟨ hl₁, _⟩, hl₂ ⟩ := hl ; clear hl
  have h₈ := check_level_checked_succ hl₂
  have h₉ : (1 + (n - 1)) = n := by omega
  rw [h₉] at h₈ ; clear h₉
  simp [evaluate]
  rw [←ihe hs hc hr ht h₈]
  clear h₈
  simp [hasAttr, attrsOf, Entities.attrsOrEmpty]
  unfold EvaluatesTo at h₁₃
  rcases h₁₃ with h₁₃ | h₁₃ | h₁₃ | h₁₃ <;> simp [h₁₃]
  cases hee : entities.find? euid <;> simp [hee]
  case none =>
    simp [not_entities_then_not_slice hs hee]
  case some =>
    have h₈ : n = (n - 1).succ := by omega
    rw [h₈] at hs
    have h₇ := checked_eval_entity_in_slice hc hr ht hl₂ hl₁ h₁₃ hee hs
    simp [h₇]

theorem level_based_slicing_is_sound_has_attr_record {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (hl : checkLevel (ty₁.hasAttr a tx.typeOf) n = true)
  (ht : typeOf e c₀ env = Except.ok (ty₁, c₁'))
  (hrty : ty₁.typeOf = CedarType.record rty)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.hasAttr e a) request entities = evaluate (.hasAttr e a) request slice
:= by
  have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc hr ht
  rw [hrty] at h₁₄
  replace ⟨ euid, h₁₄⟩ := instance_of_record_type_is_record h₁₄
  subst h₁₄
  simp [checkLevel, hrty] at hl
  have ih := ihe hs hc hr ht hl
  simp [evaluate, ←ih]
  cases he : evaluate e request entities <;> simp [he]
  simp [hasAttr]
  rename_i v
  unfold EvaluatesTo at h₁₃
  simp [he] at h₁₃
  subst h₁₃
  simp [attrsOf]

theorem level_based_slicing_is_sound_has_attr {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (e.hasAttr a) c₀ env = Except.ok (tx, c₁))
  (hl : checkLevel tx n = true)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.hasAttr e a) request entities = evaluate (.hasAttr e a) request slice
:= by
  have ⟨ h₇, ty₁, _, ht, h₅, h₆ ⟩ := type_of_hasAttr_inversion ht
  rw [h₅] at hl
  cases h₆
  case _ hety =>
    replace ⟨ ety, hety ⟩ := hety
    exact level_based_slicing_is_sound_has_attr_entity hs hc hr hl ht hety ihe
  case _ hrty =>
    replace ⟨ rty, hrty ⟩ := hrty
    exact level_based_slicing_is_sound_has_attr_record hs hc hr hl ht hrty ihe

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Slice
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
  (hl : (tx₁.hasAttr a ty).AtLevel env n)
  (ht : typeOf e c₀ env = Except.ok (tx₁, c₁))
  (hety : tx₁.typeOf = CedarType.entity ety)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.hasAttr e a) request entities = evaluate (.hasAttr e a) request slice
:= by
  have ⟨ hgc, v, he, hv ⟩ := type_of_is_sound hc hr ht
  rw [hety] at hv
  replace ⟨ euid, hety', hv⟩ := instance_of_entity_type_is_entity hv
  subst hety' hv
  cases hl
  case hasAttrRecord hnety _ =>
    specialize hnety euid.ty
    contradiction
  rename_i n hel₁ hl₁ _
  simp [evaluate]
  have hl₁' := entity_access_at_level_then_at_level hl₁
  specialize ihe hs hc hr ht hl₁'
  rw [←ihe]
  unfold EvaluatesTo at he
  rcases he with he | he | he | he <;> simp [he]
  have hfeq := checked_eval_entity_find_entities_eq_find_slice hc hr ht hl₁ he hs
  simp [hfeq, hasAttr, attrsOf, Entities.attrsOrEmpty]

theorem level_based_slicing_is_sound_has_attr_record {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (hl : (ty₁.hasAttr a tx.typeOf).AtLevel env n)
  (ht : typeOf e c₀ env = Except.ok (ty₁, c₁'))
  (hrty : ty₁.typeOf = CedarType.record rty)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.hasAttr e a) request entities = evaluate (.hasAttr e a) request slice
:= by
  have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc hr ht
  rw [hrty] at h₁₄
  replace ⟨ euid, h₁₄⟩ := instance_of_record_type_is_record h₁₄
  subst h₁₄
  cases hl
  case hasAttr hety =>
    simp [hety] at hrty
  rename_i hl
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
  (hl : tx.AtLevel env n)
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

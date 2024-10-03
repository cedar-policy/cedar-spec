import Cedar.Data.Map
import Cedar.Spec.EntitySlice
import Cedar.Spec.Value
import Cedar.Thm.Entities
import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Validation.Types
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Levels
import Cedar.Thm.SubExpression

namespace Cedar.Thm
open Cedar.Data
open Cedar.Validation
open Cedar.Spec

def simpleSlice_soundness (e : Expr) : Prop  :=
  ∀ entities slice request env (c₁ c₂ : Capabilities) (ty : CedarType),
    typeOf e c₁ env (.finite 1 == Level.infinite) = .ok (ty, c₂) →
    CapabilitiesInvariant c₁ request entities →
    simpleSlice request entities = .some slice →
    RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1)  →
    evaluate e request slice = evaluate e request entities

theorem simpleSlice_sound_lit (l : Prim) (entities slice : Entities) (request : Request)  :
  evaluate (.lit l) request slice = evaluate (.lit l) request entities
  := by
  cases l <;> simp [evaluate]

theorem simpleSlice_is_sound_var (v : Var) (entities slice : Entities) (request : Request)  :
  evaluate (.var v) request slice = evaluate (.var v) request entities
  := by
  cases v <;> simp [evaluate]

theorem one_is_less_than_infinity : Level.finite 1 < .infinite := by
  apply LevelLT.finite₂

theorem simpleSlice_is_sound_ite (cond cons alt : Expr) (entities slice : Entities) (request : Request) (env : Environment) (c₁ c₂ : Capabilities) (ty : CedarType)
  (well_typed : typeOf (.ite cond cons alt) c₁ env (Level.finite 1 == .infinite) = .ok (ty, c₂))
  (slice_eq : simpleSlice request entities = .some slice)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (full_store_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (ih₁ : simpleSlice_soundness cond)
  (ih₂ : simpleSlice_soundness cons)
  (ih₃ : simpleSlice_soundness alt) :
  evaluate (.ite cond cons alt) request slice = evaluate (.ite cond cons alt) request entities
  := by
  simp [evaluate]
  have ⟨bty, c₁', ty₁, c₂', ty₂, c₃, hinv₁, hinv₂⟩ := type_of_ite_inversion well_typed
  cases bty
  case tt =>
    simp at hinv₂

    have ⟨caps_inv_cond, v_cond, cond_sound, v_cond_typed⟩ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ (v : Value), EvaluatesToLeveled cond request entities v ∧ InstanceOfType v (.bool .tt) := by
      apply type_of_is_sound_noninfinite
      apply one_is_less_than_infinity
      repeat assumption
    cases v_cond_typed
    rename_i bool v_cond_typed
    cases bool
    <;> simp [InstanceOfBoolType] at v_cond_typed
    have eval_cond_matches : evaluate cond request slice = evaluate cond request entities := by
      apply ih₁
      repeat assumption
    rcases cond_sound with cond_sound | cond_sound | cond_sound
      <;> simp [cond_sound, eval_cond_matches, Result.as, Coe.coe, Value.asBool]

    replace ⟨hinv₂, hinv₃, hinv₄⟩ := hinv₂
    subst hinv₃
    subst hinv₄
    apply ih₂
    apply hinv₂
    apply capability_union_invariant
    assumption
    apply caps_inv_cond
    repeat assumption
  case ff =>
    simp at hinv₂
    replace ⟨hinv₂, hinv₃, hinv₄⟩ := hinv₂
    subst hinv₃
    subst hinv₄

    have ⟨caps_inv_cond, v_cond, cond_sound, v_cond_typed⟩ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ (v : Value), EvaluatesToLeveled cond request entities v ∧ InstanceOfType v (.bool .ff) := by
      apply type_of_is_sound_noninfinite
      apply one_is_less_than_infinity
      repeat assumption
    cases v_cond_typed
    rename_i bool v_cond_typed
    cases bool
    <;> simp [InstanceOfBoolType] at v_cond_typed
    have eval_cond_matches : evaluate cond request slice = evaluate cond request entities := by
      apply ih₁
      repeat assumption
    rcases cond_sound with cond_sound | cond_sound | cond_sound
      <;> simp [cond_sound, eval_cond_matches, Result.as, Coe.coe, Value.asBool]
    apply ih₃
    repeat assumption
  case anyBool =>
    simp at hinv₂
    have ⟨caps_inv_cond, v_cond, cond_sound, v_cond_typed⟩ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ (v : Value), EvaluatesToLeveled cond request entities v ∧ InstanceOfType v (.bool .anyBool) := by
      apply type_of_is_sound_noninfinite
      apply one_is_less_than_infinity
      repeat assumption

    have eval_cond_matches : evaluate cond request slice = evaluate cond request entities := by
      apply ih₁
      repeat assumption


    rcases cond_sound with cond_sound | cond_sound | cond_sound
    <;> simp [cond_sound, eval_cond_matches, Result.as, Coe.coe, Value.asBool]
    cases v_cond_typed
    rename_i bool v_cond_typed
    clear v_cond_typed
    replace ⟨hinv₂, hinv₃, _⟩ := hinv₂
    cases bool
    case true =>
      simp
      apply ih₂
      apply hinv₂
      apply capability_union_invariant
      assumption
      apply caps_inv_cond
      assumption
      repeat assumption
    case false =>
      simp
      apply ih₃
      repeat assumption


theorem simpleSlice_is_sound_getAttr (e : Expr) (attr : Attr) (entities slice : Entities) (request : Request) (env : Environment) (c₁ c₂ : Capabilities) (ty : CedarType)
  (well_typed : typeOf (.getAttr e attr) c₁ env (.finite 1 == Level.infinite) = .ok (ty, c₂))
  (slice_eq : simpleSlice request entities = .some slice)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (full_store_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (ih : simpleSlice_soundness e)
  :
  evaluate (.getAttr e attr) request slice = evaluate (.getAttr e attr) request entities
  := by
  simp [evaluate]

  have ⟨hinv₁, c₁', hinv₂⟩ := type_of_getAttr_inversion_levels well_typed
  cases hinv₂
  case _ hinv₂ => -- entity case
    replace ⟨etype, l₂, hinv₂, hinv₃⟩ := hinv₂
    have ⟨caps_inv_subexpr, v, sound_subexpr, v_well_typed⟩ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity etype l₂) := by
      apply type_of_is_sound_noninfinite
      apply one_is_less_than_infinity
      repeat assumption
    have eval_matches : evaluate e request slice = evaluate e request entities := by
      apply ih
      repeat assumption
    rcases sound_subexpr with sound_subexpr | sound_subexpr | sound_subexpr
    <;> simp [sound_subexpr, eval_matches]








    sorry
  case _ =>
    sorry









theorem simpleSlice_is_sound (e : Expr) (entities slice : Entities) (request : Request) (env : Environment) (c₁ c₂ : Capabilities) (ty : CedarType)
  (well_typed : typeOf e c₁ env false = .ok (ty, c₂))
  (slice_eq : simpleSlice request entities = .some slice)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (h : NoEuidsInEnv env)
  (full_store_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1)) :
  evaluate e request slice = evaluate e request entities
  := by
  cases e
  case lit l =>
    apply simpleSlice_sound_lit
  case var v =>
    apply simpleSlice_is_sound_var
  case ite cond cons alt =>
    apply simpleSlice_is_sound_ite
    repeat assumption
    all_goals {
      simp [simpleSlice_soundness]
      intros
      apply simpleSlice_is_sound
      repeat assumption
    }
  case and lhs rhs =>
    sorry
  case or lhs rhs =>
    sorry
  case getAttr expr attr =>
    sorry


  sorry

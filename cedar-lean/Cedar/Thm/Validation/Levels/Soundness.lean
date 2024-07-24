import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Validation.Typechecker.Set
import Cedar.Thm.Validation.Typechecker.Call
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Levels.Util
import Cedar.Thm.Validation.Levels.WellFormed

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_is_sound_noninfinite_lit (p : Prim) {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.lit p) c₁ env (l == .infinite) = .ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (.lit p) c₂ request entities ∧
  ∃ v,  EvaluatesToLeveled (.lit p) request entities v ∧ InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.lit p) c₂ request entities ∧ ∃ v, EvaluatesTo (.lit p) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  constructor <;> try assumption
  exists v'
  constructor <;> try assumption
  cases p <;> (
    simp [EvaluatesToLeveled]
    inrr
    cases hsound₂ <;> rename_i hsound₂ <;> simp [evaluate] at hsound₂
    rw [← hsound₂]
    simp [hsound₂, evaluate])

theorem type_of_is_sound_noninfinite_var (x : Var) {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.var x) c₁ env (l == .infinite) = .ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (.var x) c₂ request entities ∧
  ∃ v,  EvaluatesToLeveled (.var x) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.var x) c₂ request entities ∧ ∃ v, EvaluatesTo (.var x) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  constructor <;> try assumption
  exists v'
  constructor <;> try assumption
  simp [EvaluatesToLeveled]
  inrr
  cases hsound₂
    <;> rename_i hsound₂
    <;> simp [evaluate] at hsound₂
    <;> cases x <;> simp at hsound₂
    <;> simp [evaluate, hsound₂]

theorem type_of_is_sound_noninfinite_ite {cond cons alt : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.ite cond cons alt) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled cond)
  (ih₂ : TypeOfIsSoundLeveled cons)
  (ih₃ : TypeOfIsSoundLeveled alt) :
  GuardedCapabilitiesInvariant (.ite cond cons alt) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.ite cond cons alt) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.ite cond cons alt) c₂ request entities ∧ ∃ v, EvaluatesTo (.ite cond cons alt) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  constructor <;> try assumption
  exists v'
  constructor <;> try assumption
  have hinv := type_of_ite_inversion h₄
  replace ⟨bty, c₁', ty₂, c₂', ty₃, c₃, hinv⟩ := hinv
  cases bty
  case tt =>
    simp at hinv
    have ⟨hinv₁, hinv₂, hinv₃, hinv₄⟩ := hinv
    clear hinv
    subst hinv₄
    subst hinv₃
    simp [EvaluatesToLeveled]
    have hsound₁ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ v_cond, EvaluatesToLeveled cond request entities v_cond ∧ InstanceOfType v_cond (.bool .tt) := by
      apply ih₁
      apply h₁
      apply h₂
      apply h₃
      apply hinv₁
    have ⟨hsound₁₁, v_cond, hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₂
    case _ hsound₁₂ =>
      inl
      simp [evaluate, hsound₁₂, Result.as]
    case _ hsound₁₂ =>
      cases hsound₁₂
      case _ hsound₁₂ =>
        inrl
        simp [evaluate, hsound₁₂, Result.as]
      case _ hsound₁₂ =>
        cases hsound₁₃
        rename_i bool hsound₁₃
        cases bool <;> simp [InstanceOfBoolType] at hsound₁₃
        have hsound₂ : GuardedCapabilitiesInvariant cons c₂' request entities ∧ ∃ v_cons, EvaluatesToLeveled cons request entities v_cons ∧ InstanceOfType v_cons ty := by
          apply ih₂
          apply h₁
          apply capability_union_invariant
          apply h₂
          apply hsound₁₁
          apply hsound₁₂
          apply h₃
          apply hinv₂
        have ⟨_, v_cons, hsound₂₂, hsound₂₃⟩ := hsound₂
        clear hsound₂
        cases hsound₂₂
        case _ hsound₂₂ =>
          inl
          simp [evaluate, hsound₁₂, Result.as, Coe.coe, Value.asBool, hsound₂₂]
        case _ hsound₂₂ =>
          cases hsound₂₂
          case _ hsound₂₂ =>
            inrl
            simp [evaluate, hsound₁₂, Result.as, Coe.coe, Value.asBool, hsound₂₂]
          case _ hsound₂₂ =>
            inrr
            simp [evaluate, hsound₁₂, Result.as, Coe.coe, Value.asBool, hsound₂₂]
            have heval : evaluate (.ite cond cons alt) request entities = .ok v_cons := by
              simp [evaluate, hsound₁₂, Result.as, Coe.coe, Value.asBool, hsound₂₂]
            dril_to_value hsound₂ heval
            rfl
  case ff =>
    simp at hinv
    have ⟨hinv₁, hinv₂, hinv₃, hinv₄⟩ := hinv
    clear hinv
    subst hinv₄
    subst hinv₃
    have hsound₁ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ v_cond, EvaluatesToLeveled cond request entities v_cond ∧ InstanceOfType v_cond (.bool .ff) := by
      apply ih₁
      apply h₁
      apply h₂
      apply h₃
      apply hinv₁
    have ⟨_, v_cond, hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    simp [EvaluatesToLeveled]
    cases hsound₁₂
    case _ hsound₁₂ =>
      inl
      simp [evaluate, hsound₁₂, Result.as]
    case _ hsound₁₂ =>
      cases hsound₁₂
      case _ hsound₁₂ =>
        inrl
        simp [evaluate, hsound₁₂, Result.as]
      case _ hsound₁₂ =>
        cases hsound₁₃
        rename_i bool hsound₁₃
        cases bool <;> simp [InstanceOfBoolType] at hsound₁₃
        have hsound₂ : GuardedCapabilitiesInvariant alt c₂ request entities ∧ ∃ v, EvaluatesToLeveled alt request entities v ∧ InstanceOfType v ty := by
          apply ih₃
          apply h₁
          apply h₂
          apply h₃
          apply hinv₂
        have ⟨_, v_alt, hsound₂₂, hsound₂₃⟩ := hsound₂
        clear hsound₂
        cases hsound₂₂
        case _ hsound₂₂ =>
          inl
          simp [evaluate, hsound₁₂, hsound₂₂, Result.as, Coe.coe, Value.asBool]
        case _ hsound₂₂ =>
          cases hsound₂₂
          case _ hsound₂₂ =>
            inrl
            simp [evaluate, hsound₁₂, hsound₂₂, Result.as, Coe.coe, Value.asBool]
          case _ hsound₂₂ =>
            inrr
            simp [evaluate, hsound₁₂, hsound₂₂, Result.as, Coe.coe, Value.asBool]
            have heval : evaluate (.ite cond cons alt) request entities = .ok v_alt := by
              simp [evaluate, hsound₁₂, hsound₂₂, Result.as, Coe.coe, Value.asBool]
            dril_to_value hsound₂ heval
            rfl
  case anyBool =>
    simp at hinv
    have ⟨hinv₁, hinv₂, hinv₃, _, _⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ v, EvaluatesToLeveled cond request entities v ∧ InstanceOfType v (.bool .anyBool) := by
      apply ih₁
      repeat assumption
    have ⟨hsound₁₁, v_cond, hsound₁₂, hsound₁₃⟩ :=  hsound₁
    clear hsound₁
    simp [EvaluatesToLeveled]
    cases hsound₁₂
    case _ hsound₁₂ =>
      inl
      simp [evaluate, hsound₁₂, Result.as]
    case _ hsound₁₂ =>
      cases hsound₁₂
      case _ hsound₁₂ =>
        inrl
        simp [evaluate, hsound₁₂, Result.as]
      case _ hsound₁₂ =>
        cases hsound₁₃
        rename_i bool hbol
        cases bool
        case true =>
          have hsound₂ : GuardedCapabilitiesInvariant cons c₂' request entities ∧ ∃ v, EvaluatesToLeveled cons request entities v ∧ InstanceOfType v ty₂ := by
            apply ih₂
            apply h₁
            apply capability_union_invariant
            apply h₂
            apply hsound₁₁
            apply hsound₁₂
            apply h₃
            apply hinv₂
          have ⟨_, v_cons, hsound₂₂, hsound₂₃⟩ := hsound₂
          clear hsound₂
          cases hsound₂₂
          case _ hsound₂₂ =>
            inl
            simp [evaluate, hsound₂₂, hsound₁₂, Result.as, Coe.coe, Value.asBool]
          case _ hsound₂₂ =>
            cases hsound₂₂
            case _ hsound₂₂ =>
              inrl
              simp [evaluate, hsound₂₂, hsound₁₂, Result.as, Coe.coe, Value.asBool]
            case _ hsound₂₂ =>
              inrr
              have heval : evaluate (.ite cond cons alt) request entities = .ok v_cons := by
                simp [evaluate, hsound₂₂, hsound₁₂, Result.as, Coe.coe, Value.asBool]
              simp [heval]
              dril_to_value hsound₂ heval
              rfl
        case false =>
          have hsound₂ : GuardedCapabilitiesInvariant alt c₃ request entities ∧ ∃ v, EvaluatesToLeveled alt request entities v ∧ InstanceOfType v ty₃ := by
            apply ih₃
            apply h₁
            apply h₂
            apply h₃
            apply hinv₃
          have ⟨_, v_cons, hsound₂₂, hsound₂₃⟩ := hsound₂
          clear hsound₂
          cases hsound₂₂
          case _ hsound₂₂ =>
            inl
            simp [evaluate, hsound₂₂, hsound₁₂, Result.as, Coe.coe, Value.asBool]
          case _ hsound₂₂ =>
            cases hsound₂₂
            case _ hsound₂₂ =>
              inrl
              simp [evaluate, hsound₂₂, hsound₁₂, Result.as, Coe.coe, Value.asBool]
            case _ hsound₂₂ =>
              inrr
              have heval : evaluate (.ite cond cons alt) request entities = .ok v_cons := by
                simp [evaluate, hsound₂₂, hsound₁₂, Result.as, Coe.coe, Value.asBool]
              simp [heval]
              dril_to_value hsound₂ heval
              rfl

theorem type_of_is_sound_noninfinite_and {lhs rhs : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.and lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.and lhs rhs) c₂ request entities  ∧
  ∃ v, EvaluatesToLeveled (.and lhs rhs) request entities v ∧ InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.and lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.and lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_and_inversion h₄
  replace ⟨bty₁, c₁', hinv₁, hinv⟩ := hinv
  cases bty₁
  case tt =>
    simp at hinv
    have ⟨bty₂, c₂', hinv₂, _⟩ := hinv
    clear hinv
    have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.bool .tt) := by
      apply ih₁
      repeat assumption
    have ⟨hsound₁₁, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i bool hbool
    cases bool <;> simp [InstanceOfBoolType] at hbool
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
    have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.bool bty₂) := by
      apply ih₂
      apply h₁
      apply capability_union_invariant
      apply h₂
      apply hsound₁₁
      apply h₁₂
      apply h₃
      apply hinv₂
    have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
    cases hsound₂₃
    clear hsound₂
    rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂ <;> simp [evaluate, h₂₂, Result.as, Coe.coe, Value.asBool, pure, Except.pure]
    rename_i bool hb
    rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, h₂₂, Result.as, Coe.coe, Value.asBool, pure, Except.pure] at hs
    assumption
  case ff =>
    simp at hinv
    have ⟨hinv₁, hinv₂⟩ := hinv
    clear hinv
    subst hinv₁
    subst hinv₂
    have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.bool .ff) := by
      apply ih₁
      repeat assumption
    have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i bool hbool
    simp [EvaluatesToLeveled]
    cases bool <;> simp [InstanceOfBoolType] at hbool
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as, Coe.coe, Value.asBool]
    rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, Result.as, Coe.coe, Value.asBool] at hs
    assumption
  case anyBool =>
    simp at hinv
    have ⟨bty₂, c₂', hinv₂, _⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.bool .anyBool) := by
      apply ih₁
      repeat assumption
    have ⟨hsound₁₁, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i bool hbool
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [h₁₂, evaluate, Result.as, Coe.coe, Value.asBool]
    cases bool
    case true =>
      simp
      have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.bool bty₂) := by
        apply ih₂
        apply h₁
        apply capability_union_invariant
        apply h₂
        apply hsound₁₁
        repeat assumption
      have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
      cases hsound₂₃
      rename_i bool hbool
      clear hsound₂
      rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂ <;> simp [h₂₂, pure, Except.pure]
      rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, h₂₂, Result.as, Coe.coe, Value.asBool, pure, Except.pure] at hs
      assumption
    case false =>
      simp
      rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, Result.as, Coe.coe, Value.asBool, pure, Except.pure] at hs
      assumption

theorem type_of_is_sound_noninfinite_or {lhs rhs : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.or lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.or lhs rhs) c₂ request entities  ∧
  ∃ v, EvaluatesToLeveled (.or lhs rhs) request entities v ∧ InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.or lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.or lhs rhs) request entities v ∧  InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_or_inversion h₄
  replace ⟨bty₁, c₁', hinv₁, hinv⟩ := hinv
  have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.bool bty₁) := by
    apply ih₁
    repeat assumption
  have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
  cases hsound₁₃
  rename_i lhs_bool hsound₁₃
  cases bty₁
  case tt =>
    simp at hinv
    have ⟨hinv₂, hinv₃⟩ := hinv
    subst hinv₂
    subst hinv₃
    clear hinv
    simp [EvaluatesToLeveled]
    cases lhs_bool <;> simp [InstanceOfBoolType] at hsound₁₃
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as, Coe.coe, Value.asBool]
    rename InstanceOfType v (.bool .tt) => hinst
    cases hinst
    rename_i bool hinst
    cases bool <;> simp [InstanceOfBoolType] at hinst
    rfl
  case ff =>
    simp at hinv
    replace ⟨bty₂, c₂', hinv⟩ := hinv
    subst hinv
    have hsound₂ : GuardedCapabilitiesInvariant rhs c₂ request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.bool bty₂) := by
      apply ih₂
      repeat assumption
    have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
    cases hsound₂₃
    rename_i rhs_bool hsound₂₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as, Coe.coe, Value.asBool]
    cases lhs_bool <;> simp [InstanceOfBoolType] at hsound₁₃
    rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂ <;> simp [h₂₂, Result.as, Coe.coe, Value.asBool, pure, Except.pure]
    rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, h₂₂, Result.as, Coe.coe, Value.asBool, pure, Except.pure] at hs
    assumption
  case anyBool =>
    simp at hinv
    replace ⟨bty₂, c₂', hinv₂, hinv⟩ := hinv
    clear hinv
    have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.bool bty₂) := by
      apply ih₂
      repeat assumption
    have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
    clear hsound₂
    simp [EvaluatesToLeveled]
    cases hsound₂₃
    rename_i rhs_bool hsound₂₃
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
      <;> cases lhs_bool
      <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂ <;> simp [evaluate, h₂₂, h₁₂, Result.as, Value.asBool, Coe.coe, pure, Except.pure]
      <;> rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₂₂, h₁₂, Result.as, Value.asBool, Coe.coe, pure, Except.pure] at hs
      <;> assumption

theorem type_of_is_sound_noninfinite_getAttr {e : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (e.getAttr a) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (e.getAttr a) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (e.getAttr a) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (e.getAttr a) c₂ request entities ∧ ∃ v, EvaluatesTo (e.getAttr a) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_getAttr_inversion_levels h₄
  replace ⟨_, c₁', hinv⟩ := hinv
  cases hinv
  case _ hinv =>
    -- Entity Case
    replace ⟨ety, l', hinv₁, hinv₂⟩ := hinv
    clear hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety l') := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i euid hsound₁₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
    inrr
    simp [getAttr]
    have wf : entities ⊢ (.prim (.entityUID euid)) : (.entity ety l') := by
      apply evaluates_to_well_formed
      repeat assumption
    cases wf
    case _ wf =>
      cases hinv₂
      omega
    case _ =>
      rename_i attrs h₄ h₃ h₂ h₁
      simp [attrsOf, h₃]
      rcases hsound with hs | hs | hs | hs
        <;> simp [evaluate, attrsOf, h₃, h₁₂, getAttr, Map.findOrErr] at hs
        <;> cases hfind : attrs.find? a
        <;> simp [hfind] at hs
      subst hs
      simp [Map.findOrErr, hfind]
  case _ hinv =>
    -- Record Case
    replace ⟨rty, hinv⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.record rty) := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i rv h₁ h₂ h₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂  <;> simp [evaluate, h₁₂, Result.as, getAttr, attrsOf]
    inrr
    rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, Result.as, getAttr, attrsOf] at hs
      <;> cases hfind : rv.find? a
      <;> simp [hfind, Map.findOrErr] at hs
    subst hs
    simp [Map.findOrErr, hfind]

theorem type_of_is_sound_noninfinite_unary {e : Expr} {o : UnaryOp} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.unaryApp o e) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.unaryApp o e) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.unaryApp o e) request entities v ∧ InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.unaryApp o e) c₂ request entities ∧ ∃ v, EvaluatesTo (.unaryApp o e) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  cases o
  case _ =>
    have hinv := type_of_not_inversion h₄
    replace ⟨_, bty, c₁', _, hinv⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.bool bty) := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₂₃⟩ := hsound₁
    clear hsound₁
    cases hsound₂₃
    rename_i bool hbool
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
    inrr
    simp [apply₁]
    rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, Result.as, apply₁] at hs
    assumption
  case _ =>
    have hinv := type_of_neg_inversion h₄

    replace ⟨_, _, c₁', hinv⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.int) := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₂₃⟩ := hsound₁
    clear hsound₁
    cases hsound₂₃
    rename_i i
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
    simp [apply₁]
    simp [intOrErr]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, Result.as, apply₁] at hs
      <;> cases hneg : i.neg?
      <;> simp [hneg, intOrErr]
      <;> simp [hneg, intOrErr] at hs
      <;> assumption
  case _ =>
    have hinv := type_of_like_inversion h₄
    replace ⟨_, _, c₁', hinv⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v .string := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i s
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
    inrr
    simp [apply₁]
    rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, Result.as, apply₁] at hs
    assumption
  case _ =>
    rename_i ety_rhs _
    have hinv := type_of_is_inversion h₄
    replace ⟨_, _, l, c₁', hinv⟩ := hinv
    rename EntityType => ety_lhs
    rename InstanceOfType v ty => hinst
    cases heq : decide (ety_rhs = ety_lhs) <;> simp at heq
    case _ =>
      rw [if_neg] at hinv
      have ⟨hinv₁, hinv₂⟩ := hinv
      clear hinv
      subst hinv₁
      have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety_lhs l) := by
        apply ih
        repeat assumption
      have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
      clear hsound₁
      cases hsound₁₃
      rename_i euid hsound₁₃
      simp [EvaluatesToLeveled]
      rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
      inrr
      simp [InstanceOfEntityType] at hsound₁₃
      simp [apply₁, heq]
      rw [← hsound₁₃]
      have hneq : (ety_rhs == ety_lhs) = false := by
        exact beq_false_of_ne heq
      simp [hneq]
      cases hinst
      rename_i bool hbool
      cases bool <;> simp [InstanceOfBoolType] at hbool
      rfl
      assumption
    case _ =>
      subst heq
      simp at hinv
      have ⟨hinv₁, hivnv₂⟩ := hinv
      clear hinv
      subst hinv₁
      have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety_rhs l) := by
        apply ih
        repeat assumption
      have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
      clear hsound₁
      cases hsound₁₃
      rename_i euid hsound₁₃
      simp [EvaluatesToLeveled]
      rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂ <;> simp [evaluate, h₁₂, Result.as]
      inrr
      simp [InstanceOfEntityType] at hsound₁₃
      simp [apply₁, hsound₁₃]
      cases hinst
      rename_i bool hinst
      cases bool <;> simp [InstanceOfBoolType] at hinst
      rfl

macro "singleton_boolean" hinst:(ident) : tactic =>
  `(tactic | (
    have hinst := $hinst
    cases hinst
    rename_i bool hinst
    cases bool <;> simp [InstanceOfBoolType] at hinst
  ))

theorem type_of_is_sound_noninfinite_binary_eq {lhs rhs : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp .eq lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp .eq lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp .eq lhs rhs) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.binaryApp .eq lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.binaryApp .eq lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_eq_inversion h₄
  replace ⟨_, hinv⟩ := hinv
  split at hinv
  case _ hinv =>
    rename_i p₁ p₂ _ _
    simp [EvaluatesToLeveled]
    inrr
    rename InstanceOfType v ty => hinst
    cases heq : decide (p₁ = p₂)
    case _ =>
      simp [evaluate, apply₂, heq, BEq.beq]
      simp at heq
      rw [if_neg] at hinv
      subst hinv
      cases hinst
      rename_i bool hinst
      cases bool <;> simp [InstanceOfBoolType] at hinst
      rfl
      assumption
    case _ =>
      simp at heq
      subst heq
      simp [evaluate, apply₂]
      simp at hinv
      subst hinv
      cases hinst
      rename_i bool hinst
      cases bool <;> simp [InstanceOfBoolType] at hinst
      rfl
  case _ hinv =>
    replace ⟨ty₁, c₁', ty₂, c₂', hinv₁, hinv₂, hinv⟩ := hinv
    split at hinv
    case _ _ =>
      have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v ty₁ := by
        apply ih₁
        repeat assumption
      have ⟨_, v_lhs, hsound₁₂, _⟩ := hsound₁
      clear hsound₁
      have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v ty₂ := by
        apply ih₂
        repeat assumption
      have ⟨_, v_rhs, hsound₂₂, _⟩ := hsound₂
      clear hsound₂
      simp [EvaluatesToLeveled]
      rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
        <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
        <;> simp [evaluate, h₁₂, h₂₂, Result.as, apply₂]
      rcases hsound with hs | hs | hs | hs <;> simp [evaluate, h₁₂, h₂₂, Result.as, apply₂] at hs
      assumption
    case _ hinv =>
      replace ⟨hinv₃, ety₁, l₁, ety₂, l₂, hinv₄, hinv₅⟩ := hinv
      subst hinv₄
      subst hinv₅
      have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.entity ety₁ l₁) := by
        apply ih₁
        repeat assumption
      have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
      clear hsound₁
      have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.entity ety₂ l₂) := by
        apply ih₂
        repeat assumption
      have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
      clear hsound₂
      simp [EvaluatesToLeveled]
      rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
        <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
        <;> simp [evaluate, h₁₂, h₂₂, Result.as, apply₂]
      have hneq : ¬ v_lhs = v_rhs := by
        apply no_entity_type_lub_implies_not_eq
        repeat assumption
      have hnbeq : (v_lhs == v_rhs) = false := by
        exact beq_false_of_ne hneq
      simp [hnbeq]
      rename InstanceOfType v ty => hinst
      subst hinv₃
      cases hinst
      rename_i bool hinst
      cases bool <;> simp [InstanceOfBoolType] at hinst
      rfl

theorem empty_set_decide [DecidableEq α] (a : α) :
  ((Set.empty.contains a)) = false
  := by
  simp [Set.empty, Set.contains]
  unfold Not
  intros h
  simp [Set.elts] at h

theorem map_or_err_err (set : Set Value)  (e₁ e₂ : Error)
  (h : Set.mapOrErr Value.asEntityUID set e₁ = .error e₂) :
  e₁ = e₂ := by
  simp [Set.mapOrErr] at h
  cases h₁ : List.mapM Value.asEntityUID set.elts
    <;> simp [h₁] at h
  assumption

theorem type_of_is_sound_noninfinite_binary_mem {lhs rhs : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp .mem lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp .mem lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp .mem lhs rhs) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.binaryApp .mem lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.binaryApp .mem lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_mem_inversion_finite h₄
  replace ⟨_, ety₁, ety₂, l₁, l₂, _, hinv₂, c₂', hinv⟩ := hinv
  cases hinv
  case _ hinv => -- single entity case
    replace ⟨c₁', hinv₂⟩ := hinv₂
    have ⟨hinv₃, _⟩ := hinv
    clear hinv
    have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.entity ety₁ l₁) := by
      apply ih₁
      repeat assumption
    have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i euid_lhs hsound₁₃
    simp [InstanceOfEntityType] at hsound₁₃
    have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.entity ety₂ l₂) := by
      apply ih₂
      repeat assumption
    have ⟨_, v_lhs, hsound₂₂, hsound₂₃⟩ := hsound₂
    clear hsound₂
    cases hsound₂₃
    rename_i euid_rhs hsound₂₃
    simp [InstanceOfEntityType] at hsound₂₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
      <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
      <;> simp [evaluate, h₁₂, h₂₂, Result.as]
    inrr
    simp [apply₂, inₑ, Entities.ancestorsOrEmpty]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, h₂₂, apply₂, inₑ, Entities.ancestorsOrEmpty, empty_set_decide] at hs
    assumption
  case _ hinv => -- set of entities case
    replace ⟨c₁', hinv₂⟩ := hinv₂
    have ⟨hinv₃, hinv₄⟩ := hinv
    clear hinv
    have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.entity ety₁ l₁) := by
      apply ih₁
      repeat assumption
    have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
    cases hsound₁₃
    rename_i euid_lhs hsound₁₃
    simp [InstanceOfEntityType] at hsound₁₃
    subst hsound₁₃
    clear hsound₁
    have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.set (.entity ety₂ l₂)) := by
      apply ih₂
      repeat assumption
    have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
    clear hsound₂
    cases hsound₂₃
    rename_i set_rhs hsound₁₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
      <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
      <;> simp [evaluate, h₁₂, h₂₂]
    inrr
    rcases hsound with hs | hs | hs | hs
    case _ =>
      simp [evaluate, h₁₂, h₂₂, apply₂, inₛ] at hs
      cases hset : Set.mapOrErr Value.asEntityUID set_rhs Error.typeError
      case _ err =>
        have heq : .typeError = err := by
          apply map_or_err_err
          apply hset
        subst heq
        simp [hset] at hs
      case _ =>
        simp [hset] at hs
    case _ =>
      simp [evaluate, h₁₂, h₂₂, apply₂, inₛ] at hs
      cases hset : Set.mapOrErr Value.asEntityUID set_rhs Error.typeError
      case _ err =>
        have heq : .typeError = err := by
          apply map_or_err_err
          apply hset
        subst heq
        simp [hset] at hs
      case _ =>
        simp [hset] at hs
    case _ =>
      simp [evaluate, h₁₂, h₂₂, apply₂, inₛ] at hs
      cases hset : Set.mapOrErr Value.asEntityUID set_rhs Error.typeError
      case _ err =>
        have heq : .typeError = err := by
          apply map_or_err_err
          apply hset
        subst heq
        simp [hset] at hs
      case _ =>
        simp [hset] at hs
    case _ =>
      simp [evaluate, h₁₂, h₂₂] at hs
      assumption

theorem type_of_is_sound_noninfinite_binary_int_cmp {lhs rhs : Expr} {o : BinaryOp} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (hₒ : o = .less ∨ o = .lessEq)
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp o lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, hinst⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_int_cmp_inversion hₒ h₄
  have ⟨_, hinv₂, hinv₃, hinv₄⟩ := hinv
  clear hinv
  subst hinv₂
  replace ⟨c₁', hinv₃⟩ := hinv₃
  replace ⟨c₂', hinv₄⟩ := hinv₄
  have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v .int := by
    apply ih₁
    repeat assumption
  have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
  clear hsound₁
  cases hsound₁₃
  rename_i int_lhs
  have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v .int := by
    apply ih₂
    repeat assumption
  have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
  clear hsound₂
  cases hsound₂₃
  rename_i int_rhs
  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
    <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
    <;> simp [evaluate, h₁₂, h₂₂]
  inrr
  rcases hsound with hs | hs | hs | hs
    <;> cases hₒ
    <;> rename_i hₒ
    <;> simp [evaluate, h₁₂, h₂₂, apply₂, hₒ] at hs
    <;> simp [apply₂, hₒ]
    <;> assumption

theorem type_of_is_sound_noninfinite_binary_int_arith {lhs rhs : Expr} {o : BinaryOp} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (hₒ : o = .add ∨ o = .sub ∨ o = .mul)
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp o lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_int_arith_inversion hₒ h₄
  have ⟨_, hinv₂, hinv₃, hinv₄⟩ := hinv
  clear hinv
  subst hinv₂
  replace ⟨c₁', hinv₃⟩ := hinv₃
  replace ⟨c₂', hinv₄⟩ := hinv₄
  have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v .int := by
    apply ih₁
    repeat assumption
  have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
  clear hsound₁
  cases hsound₁₃
  rename_i i_lhs
  have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v .int := by
    apply ih₂
    repeat assumption
  have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
  clear hsound₂
  cases hsound₂₃
  rename_i i_rhs
  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
    <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
    <;> rcases hₒ with hₒ | hₒ | hₒ
    <;> subst hₒ
    <;> simp [evaluate, h₁₂, h₂₂]
    <;> simp [apply₂]
  case _ =>
    cases h : (i_lhs.add? i_rhs) <;> simp [intOrErr]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, h₂₂, apply₂, h, intOrErr] at hs
    assumption
  case _ =>
    cases h : (i_lhs.sub? i_rhs) <;> simp [intOrErr]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, h₂₂, apply₂, h, intOrErr] at hs
    assumption
  case _ =>
    cases h : (i_lhs.mul? i_rhs) <;> simp [intOrErr]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, h₂₂, apply₂, h, intOrErr] at hs
    assumption

theorem type_of_is_sound_noninfinite_binary_contains {lhs rhs : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp .contains lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp .contains lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp .contains lhs rhs) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.binaryApp .contains lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.binaryApp .contains lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, hinst⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption
  have hinv := type_of_contains_inversion h₄
  have ⟨_, _, ty₁, ty₂, _, hinv₄, hinv₅⟩ := hinv
  clear hinv
  replace ⟨c₁', hinv₄⟩ := hinv₄
  replace ⟨c₂', hinv₅⟩ := hinv₅

  have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.set ty₁) := by
    apply ih₁
    repeat assumption
  have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
  clear hsound₁
  cases hsound₁₃
  rename_i set_lhs hsound₁₃

  have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v ty₂ := by
    apply ih₂
    repeat assumption
  have ⟨_, v_rhs, hsound₂₂, _⟩ := hsound₂
  clear hsound₂

  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
    <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
    <;> simp [evaluate, h₁₂, h₂₂, apply₂]
    <;> cases hcontains : (set_lhs.contains v_rhs)
    <;> rcases hsound with hs | hs | hs | hs
    <;> simp [evaluate, h₁₂, h₂₂, apply₂, hcontains] at hs
    <;> assumption

theorem type_of_is_sound_noninfinite_binary_containsA {lhs rhs : Expr} {o : BinaryOp} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (hₒ : o = .containsAll ∨ o = .containsAny)
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp o lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_containsA_inversion hₒ h₄
  have ⟨_, _, ty₁, ty₂, _, hinv₄, hinv₅⟩ := hinv
  replace ⟨c₁', hinv₄⟩ := hinv₄
  replace ⟨c₂', hinv₅⟩ := hinv₅

  have hsound₁ : GuardedCapabilitiesInvariant lhs c₁' request entities ∧ ∃ v, EvaluatesToLeveled lhs request entities v ∧ InstanceOfType v (.set ty₁) := by
    apply ih₁
    repeat assumption
  have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
  clear hsound₁
  cases hsound₁₃
  rename_i set_lhs hsound₁₃

  have hsound₂ : GuardedCapabilitiesInvariant rhs c₂' request entities ∧ ∃ v, EvaluatesToLeveled rhs request entities v ∧ InstanceOfType v (.set ty₂) := by
    apply ih₂
    repeat assumption
  have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
  clear hsound₂
  cases hsound₂₃
  rename_i set_rhs hsound₂₃

  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
    <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
    <;> cases hₒ
    <;> rename_i hₒ
    <;> subst hₒ
    <;> simp [evaluate, h₁₂, h₂₂, apply₂, ]
  case _ =>
    cases h : set_rhs.subset set_lhs
      <;>rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, h₂₂, apply₂, h] at hs
      <;> assumption
  case _ =>
    cases h : set_rhs.intersects set_lhs
      <;>rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, h₂₂, apply₂, h] at hs
      <;> assumption

theorem type_of_is_sound_noninfinite_binary {lhs rhs : Expr} {o : BinaryOp} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.binaryApp o lhs rhs) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih₁ : TypeOfIsSoundLeveled lhs)
  (ih₂ : TypeOfIsSoundLeveled rhs) :
  GuardedCapabilitiesInvariant (.binaryApp o lhs rhs) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.binaryApp o lhs rhs) request entities v ∧ InstanceOfType v ty := by
  cases o
  case eq =>
    apply type_of_is_sound_noninfinite_binary_eq
    repeat assumption
  case mem =>
    apply type_of_is_sound_noninfinite_binary_mem
    repeat assumption
  case less =>
    apply type_of_is_sound_noninfinite_binary_int_cmp
    simp
    repeat assumption
  case lessEq =>
    apply type_of_is_sound_noninfinite_binary_int_cmp
    simp
    repeat assumption
  case add =>
    apply type_of_is_sound_noninfinite_binary_int_arith
    simp
    repeat assumption
  case sub =>
    apply type_of_is_sound_noninfinite_binary_int_arith
    simp
    repeat assumption
  case mul =>
    apply type_of_is_sound_noninfinite_binary_int_arith
    simp
    repeat assumption
  case contains =>
    apply type_of_is_sound_noninfinite_binary_contains
    repeat assumption
  case containsAll =>
    apply type_of_is_sound_noninfinite_binary_containsA
    simp
    repeat assumption
  case containsAny =>
    apply type_of_is_sound_noninfinite_binary_containsA
    simp
    repeat assumption

theorem type_of_is_sound_noninfinite_hasAttr {e : Expr} {a : Attr} {c₁ c₂ : Capabilities} {request : Request} {entities : Entities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.hasAttr e a) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.hasAttr e a) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.hasAttr e a) request entities v ∧ InstanceOfType v ty := by
  have hsound : GuardedCapabilitiesInvariant (.hasAttr e a) c₂ request entities ∧ ∃ v, EvaluatesTo (.hasAttr e a) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_hasAttr_inversion h₄
  replace ⟨_, c₁', hinv⟩ := hinv
  cases hinv
  case _ hinv =>
    have ⟨ety, l', hinv₁⟩ := hinv
    clear hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety l') := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    rename_i euid hsound₁₃
    simp [InstanceOfEntityType] at hsound₁₃
    subst hsound₁₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
      <;> simp [evaluate, h₁₂]
    inrr
    simp [hasAttr, attrsOf]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, hasAttr, attrsOf] at hs
    assumption
  case _ hinv =>
    replace ⟨rty, hinv⟩ := hinv
    have hsound₁ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.record rty) := by
      apply ih
      repeat assumption
    have ⟨_, v', hsound₁₂, hsound₁₃⟩ := hsound₁
    clear hsound₁
    cases hsound₁₃
    simp [EvaluatesToLeveled]
    rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
      <;> simp [evaluate, h₁₂, hasAttr, attrsOf]
    rcases hsound with hs | hs | hs | hs
      <;> simp [evaluate, h₁₂, hasAttr, attrsOf] at hs
    assumption

theorem type_of_is_sound_noninfinite_set_helper {es : List Expr} {c₁ : Capabilities} {env : Environment}  {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : ∀ (e), e ∈ es → ∃ ty' c', typeOf e c₁ env (l == .infinite) = .ok (ty', c'))
  (ih : ∀ (e), e ∈ es → TypeOfIsSoundLeveled e) :
  ∃ vs,
    (
      es.mapM (λ pair => evaluate pair request entities) = .ok vs ∨
      es.mapM (λ pair => evaluate pair request entities) = .error Error.arithBoundsError ∨
      es.mapM (λ pair => evaluate pair request entities) = .error Error.extensionError
    ) := by


  cases es
  case nil =>
    exists []
    simp [List.mapM, List.mapM.loop, pure, Except.pure]
  case cons head tail =>
    rw [List.mapM_cons]
    have typed : ∃ ty' c', typeOf head c₁ env (l == .infinite) = .ok (ty', c') := by
      apply h₄
      simp
    replace ⟨ty', c', typed⟩ := typed

    have hsound : GuardedCapabilitiesInvariant head c' request entities ∧ ∃ v, EvaluatesToLeveled head request entities v ∧ InstanceOfType v ty' := by
      apply ih
      simp
      repeat assumption
    replace ⟨_, v_head, hsound⟩ := hsound
    have ih' := (@type_of_is_sound_noninfinite_set_helper tail) h₁ h₂ h₃
      (by
        intros e hin
        apply h₄
        simp [hin]
      )
      (by
        intros e hin
        apply ih
        simp [hin]
      )
    replace ⟨vs_tail, ih'⟩ := ih'
    rcases hsound with hs | hs | hs
      <;> rcases ih' with ih' | ih' | ih'
      <;> simp [evaluate, hs, ih', pure, Except.pure]

theorem type_of_is_sound_noninfinite_set {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.set es) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : ∀ e, e ∈ es → TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.set es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.set es) request entities v ∧ InstanceOfType v ty := by

  have hsound : GuardedCapabilitiesInvariant (.set es) c₂ request entities ∧ ∃ v, EvaluatesTo (.set es) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_set_inversion h₄
  have ⟨_, ty₁, _, hinv₃⟩ := hinv
  clear hinv

  have helper : ∃ vs, (
    es.mapM (λ e => evaluate e request entities) = .ok vs ∨
    es.mapM (λ e => evaluate e request entities) = .error Error.arithBoundsError ∨
    es.mapM (λ e => evaluate e request entities) = .error Error.extensionError
  ) := by
    apply type_of_is_sound_noninfinite_set_helper
    apply h₁
    apply h₂
    apply h₃
    intros e hin
    have ⟨ty', c', h', _⟩  := hinv₃ e hin
    exists ty'
    exists c'
    apply ih
  replace ⟨vs, helper⟩ := helper
  rcases helper with helper | helper | helper
    <;> simp [EvaluatesToLeveled, evaluate, List.mapM₁, List.attach, List.attachWith,
      List.mapM_pmap_subtype (λ e => evaluate e request entities),
      helper
    ]
    <;> rcases hsound with hs | hs | hs | hs
    <;> simp [EvaluatesToLeveled, evaluate, List.mapM₁, List.attach, List.attachWith,
      List.mapM_pmap_subtype (λ e => evaluate e request entities),
      helper
    ] at hs
    <;> assumption

theorem type_of_is_sound_noninfinite_record_helper {members : List (Attr × Expr)} {c₁ : Capabilities} {env : Environment}  {request : Request} {entities : Entities} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : ∀ a e, (a, e) ∈ members → ∃ ty' c', typeOf e c₁ env (l == .infinite) = .ok (ty', c'))
  (ih : ∀ a e, (a, e) ∈ members → TypeOfIsSoundLeveled e) :
  ∃ vs,
    (
      members.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) = .ok vs ∨
      members.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) = .error Error.arithBoundsError ∨
      members.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) = .error Error.extensionError
    )
  := by
  cases members
  case nil =>
    exists []
    simp [List.mapM, List.mapM.loop, pure, Except.pure]
  case cons head tail =>
    rw [List.mapM_cons]
    have ⟨attr, expr⟩ := head
    have typed : ∃ ty' c', typeOf expr c₁ env (l == .infinite) = .ok (ty', c') := by
      apply h₄ attr expr
      simp
    replace ⟨ty', c', typed⟩ := typed
    have hsound : GuardedCapabilitiesInvariant expr c' request entities ∧ ∃ v, EvaluatesToLeveled expr request entities v ∧ InstanceOfType v ty' := by
      apply ih
      simp
      inl
      rfl
      repeat assumption
    replace ⟨_, v, hsound, _⟩ := hsound
    have ih' := (@type_of_is_sound_noninfinite_record_helper tail) h₁ h₂ h₃
      (by
        intros a e hin
        apply h₄
        simp
        apply Or.inr
        assumption
      )
      (by
        intros a e hin
        apply ih
        simp
        apply Or.inr
        apply hin
      )

    replace ⟨vs, ih'⟩ := ih'
    simp [bindAttr] at ih'

    rcases hsound with hs | hs | hs
    <;> rcases ih' with ih' | ih' | ih'
    <;> simp [bindAttr, evaluate, hs, ih', pure, Except.pure]

theorem get_type (a : Attr) (e : Expr) {members : List (Attr × Expr)} {rty : List (Attr × QualifiedType)} {c₁ : Capabilities} {env : Environment} {l : Level}
  (h₁ : List.Forall₂ (AttrExprHasAttrType c₁ env l) members rty)
  (h₂ : (a,e) ∈ members) :
  ∃ ty c, typeOf e c₁ env (l == .infinite) = .ok (ty, c) := by
  cases members
  case nil =>
    cases h₂
  case cons head tail =>
    cases h₁
    rename_i attrtype type_tail h_head h_tail
    simp [AttrExprHasAttrType] at h_head
    cases h₂
    case _ =>
      have ⟨ty', _, c', heq₂⟩ := h_head
      exists ty'
      exists c'
    case _ hin =>
      apply get_type a e
      apply h_tail
      apply hin

theorem type_of_is_sound_noninfinite_record {members: List (Attr × Expr)} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.record members) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : ∀ e a, (a,e) ∈ members → TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.record members) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.record members) request entities v ∧ InstanceOfType v ty := by

  have hsound : GuardedCapabilitiesInvariant (.record members) c₂ request entities ∧ ∃ v, EvaluatesTo (.record members) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_record_inversion h₄
  have ⟨_, rty, _, hinv₂⟩ := hinv
  clear hinv
  simp [EvaluatesToLeveled, evaluate, List.mapM₂, List.attach₂, List.mapM_pmap_subtype (λ (pair : (Attr × Expr)) => bindAttr pair.fst (evaluate pair.snd request entities))]
  have helper : ∃ vs, (
    members.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) = .ok vs ∨
    members.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) = .error Error.arithBoundsError ∨
    members.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) = .error Error.extensionError
  ) := by
    apply type_of_is_sound_noninfinite_record_helper
    apply h₁
    apply h₂
    apply h₃
    intros a e hin
    apply get_type a e
    apply hinv₂
    apply hin
    intros a e hin
    apply ih
    apply hin
  replace ⟨vs, helper⟩ := helper
  rcases helper with helper | helper | helper
    <;> simp [helper]
    <;> rcases hsound with hs | hs | hs | hs
    <;> simp [EvaluatesToLeveled, helper, evaluate, List.mapM₂, List.attach₂, List.mapM_pmap_subtype (λ (pair : (Attr × Expr)) => bindAttr pair.fst (evaluate pair.snd request entities))] at hs
  assumption

theorem type_of_is_sound_noninfinite_call_decimal  {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.call .decimal es) c₁ env (l == .infinite) = .ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (.call .decimal es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.call .decimal es) request entities v ∧
      InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.call .decimal es) c₂ request entities ∧  ∃ v, EvaluatesTo (.call .decimal es) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound

  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_call_decimal_inversion h₄
  have ⟨_, _, decimal_src, hinv₃⟩ := hinv
  simp [hinv₃, EvaluatesToLeveled, evaluate, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype, call, res]
  cases hdec : Ext.Decimal.decimal decimal_src <;> simp [hdec]
  rcases hsound with hs | hs | hs | hs
    <;> simp [hinv₃, EvaluatesToLeveled, evaluate, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype, call, res, hdec] at hs
  assumption

theorem type_of_is_sound_noninfinite_call_ip {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.call .ip es) c₁ env (l == .infinite) = .ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (.call .ip es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.call .ip es) request entities v ∧
      InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.call .ip es) c₂ request entities ∧  ∃ v, EvaluatesTo (.call .ip es) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound

  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_call_ip_inversion h₄
  have ⟨_, _, ip_src, hinv₃⟩ := hinv
  simp [hinv₃, EvaluatesToLeveled, evaluate, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype, call, res]
  cases hdec : Ext.IPAddr.ip ip_src <;> simp [hdec]
  rcases hsound with hs | hs | hs | hs
    <;> simp [hinv₃, EvaluatesToLeveled, evaluate, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype, call, res, hdec] at hs
  assumption

theorem type_of_is_sound_noninfinite_call_dec_compare {xfn : ExtFun} {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (hc : IsDecimalComparator xfn)
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.call xfn es) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : ∀ e, e ∈ es → TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.call xfn es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.call xfn es) request entities v ∧
      InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.call xfn es) c₂ request entities ∧
                ∃ v, EvaluatesTo (.call xfn es) request entities v ∧
                  InstanceOfType v ty
    := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_call_decimal_comparator_inversion hc h₄
  have ⟨_, _, e₁, e₂, c₁', c₂', hinv₃, hinv₄, hinv₅⟩ := hinv
  simp [hinv₃]
  clear hinv

  have hsound₁ : GuardedCapabilitiesInvariant e₁ c₁' request entities ∧ ∃ v, EvaluatesToLeveled e₁ request entities v ∧ InstanceOfType v (.ext ExtType.decimal) := by
    apply ih
    simp [hinv₃]
    repeat assumption
  have ⟨_, v_lhs, hsound₁₂, hsound₁₃⟩ := hsound₁
  clear hsound₁
  cases hsound₁₃
  rename_i extval hsound₁₃
  simp [InstanceOfExtType] at hsound₁₃
  cases extval <;> simp at hsound₁₃

  have hsound₂ : GuardedCapabilitiesInvariant e₂ c₂' request entities ∧ ∃ v, EvaluatesToLeveled e₂ request entities v ∧ InstanceOfType v (.ext ExtType.decimal) := by
    apply ih
    simp [hinv₃]
    repeat assumption
  have ⟨_, v_rhs, hsound₂₂, hsound₂₃⟩ := hsound₂
  clear hsound₂
  cases hsound₂₃
  rename_i extval hsound₂₃
  simp [InstanceOfExtType] at hsound₂₃
  cases extval <;> simp at hsound₂₃

  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
  <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
  <;> cases xfn
  <;> simp [IsDecimalComparator] at hc
  <;> simp [evaluate, h₁₂, h₂₂, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype (λ e => evaluate e request entities), call]
  <;> rcases hsound with hs | hs | hs | hs
  <;> simp [evaluate, hinv₃, h₁₂, h₂₂, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype (λ e => evaluate e request entities), call] at hs
  <;> assumption

theorem type_of_is_sound_noninfinite_call_ip_recognizer {xfn : ExtFun} {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (hc : IsIpAddrRecognizer xfn)
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.call xfn es) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : ∀ e, e ∈ es → TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.call xfn es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.call xfn es) request entities v ∧
      InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.call xfn es) c₂ request entities ∧
                ∃ v, EvaluatesTo (.call xfn es) request entities v ∧
                  InstanceOfType v ty
    := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_call_ipAddr_recognizer_inversion hc h₄
  have ⟨_, _, e₁, c₁', hinv₃, hinv₄⟩ := hinv
  subst hinv₃
  clear hinv


  have hsound₁ : GuardedCapabilitiesInvariant e₁ c₁' request entities ∧ ∃ v, EvaluatesToLeveled e₁ request entities v ∧ InstanceOfType v (CedarType.ext (ExtType.ipAddr)) := by
    apply ih
    simp
    repeat assumption
  have ⟨_, _, hsound₁₂, hsound₁₃⟩ := hsound₁
  clear hsound₁
  cases hsound₁₃
  rename_i extval hsound₁₃
  cases extval <;> simp [InstanceOfExtType] at hsound₁₃
  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
  <;> rcases hsound with hs | hs | hs | hs
  <;> cases xfn
  <;> simp [IsIpAddrRecognizer] at hc
  <;> simp [evaluate, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype, h₁₂, call]
  <;> simp [evaluate, List.mapM₁, List.attach, List.attachWith, List.mapM_pmap_subtype, h₁₂, call] at hs
  <;> assumption

theorem type_of_is_sound_noninfinite_call_isInRange {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.call .isInRange es) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : ∀ e, e ∈ es → TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.call .isInRange es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.call .isInRange es) request entities v ∧
      InstanceOfType v ty
  := by
  have hsound : GuardedCapabilitiesInvariant (.call .isInRange es) c₂ request entities ∧
                ∃ v, EvaluatesTo (.call .isInRange es) request entities v ∧
                InstanceOfType v ty
    := by
    type_soundness
  replace ⟨_, v, hsound, _⟩ := hsound
  constructor <;> try assumption
  exists v
  constructor <;> try assumption

  have hinv := type_of_call_isInRange_inversion h₄
  have ⟨_, _, e₁, e₂, c₁', c₂', hinv₃, hinv₄, hinv₅⟩ := hinv
  clear hinv
  subst hinv₃

  have hsound₁ : GuardedCapabilitiesInvariant e₁ c₁' request entities ∧ ∃ v, EvaluatesToLeveled e₁ request entities v ∧ InstanceOfType v (.ext ExtType.ipAddr) := by
    apply ih
    simp
    repeat assumption
  have ⟨_, _, hsound₁₂, hsound₁₃⟩ := hsound₁
  cases hsound₁₃
  rename_i ext hsound₁₃
  cases ext <;> simp [InstanceOfExtType] at hsound₁₃
  clear hsound₁

  have hsound₂ : GuardedCapabilitiesInvariant e₂ c₂' request entities ∧ ∃ v, EvaluatesToLeveled e₂ request entities v ∧ InstanceOfType v (.ext ExtType.ipAddr) := by
    apply ih
    simp
    repeat assumption
  have ⟨_, _, hsound₂₂, hsound₂₃⟩ := hsound₂
  cases hsound₂₃
  rename_i ext hsound₂₃
  cases ext <;> simp [InstanceOfExtType] at hsound₂₃

  simp [EvaluatesToLeveled]
  rcases hsound₁₂ with h₁₂ | h₁₂ | h₁₂
  <;> rcases hsound₂₂ with h₂₂ | h₂₂ | h₂₂
  <;> simp [evaluate, h₁₂, h₂₂, List.mapM₁, List.attach, List.attachWith, call]
  <;> rcases hsound with hs | hs | hs | hs
  <;> simp [evaluate, h₁₂, h₂₂, List.mapM₁, List.attach, List.attachWith, call] at hs
  assumption

theorem type_of_is_sound_noninfinite_call {xfn : ExtFun} {es : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ty : CedarType} {l : Level}
  (h₁ : l < .infinite)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l)
  (h₄ : typeOf (.call xfn es) c₁ env (l == .infinite) = .ok (ty, c₂))
  (ih : ∀ e, e ∈ es → TypeOfIsSoundLeveled e) :
  GuardedCapabilitiesInvariant (.call xfn es) c₂ request entities ∧
  ∃ v, EvaluatesToLeveled (.call xfn es) request entities v ∧
      InstanceOfType v ty
  := by
  cases xfn
  case decimal =>
    apply type_of_is_sound_noninfinite_call_decimal
    repeat assumption
  case ip =>
    apply type_of_is_sound_noninfinite_call_ip
    repeat assumption
  case lessThanOrEqual =>
    apply type_of_is_sound_noninfinite_call_dec_compare
    simp [IsDecimalComparator]
    repeat assumption
  case lessThan =>
    apply type_of_is_sound_noninfinite_call_dec_compare
    simp [IsDecimalComparator]
    repeat assumption
  case greaterThan =>
    apply type_of_is_sound_noninfinite_call_dec_compare
    simp [IsDecimalComparator]
    repeat assumption
  case greaterThanOrEqual =>
    apply type_of_is_sound_noninfinite_call_dec_compare
    simp [IsDecimalComparator]
    repeat assumption
  case isIpv4 =>
    apply type_of_is_sound_noninfinite_call_ip_recognizer
    simp [IsIpAddrRecognizer]
    repeat assumption
  case isIpv6 =>
    apply type_of_is_sound_noninfinite_call_ip_recognizer
    simp [IsIpAddrRecognizer]
    repeat assumption
  case isLoopback =>
    apply type_of_is_sound_noninfinite_call_ip_recognizer
    simp [IsIpAddrRecognizer]
    repeat assumption
  case isMulticast =>
    apply type_of_is_sound_noninfinite_call_ip_recognizer
    simp [IsIpAddrRecognizer]
    repeat assumption
  case isInRange =>
    apply type_of_is_sound_noninfinite_call_isInRange
    repeat assumption

macro "prove_ih" ih:(ident) : tactic =>
  `(tactic | (
    simp [TypeOfIsSoundLeveled]
    intros
    apply $ih
    repeat assumption))

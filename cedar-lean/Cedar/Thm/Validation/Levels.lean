import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Validation.Typechecker.Set
import Cedar.Thm.Validation.Typechecker.Call
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Levels.Soundness
import Cedar.Thm.Validation.Levels.Util


namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

-- Main soundness theorem of the leveled type system
-- If you type check with an non-finite level
-- And you provide a well formed store
-- Then the only erors you can get are arithmatic/extension errors
theorem type_of_is_sound_noninfinite {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level} :
  l < .infinite →
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironmentLeveled env request entities l →
  typeOf e c₁ env (l == .infinite) = .ok (ty, c₂) →
  GuardedCapabilitiesInvariant e c₂ request entities ∧
  ∃ (v : Value), EvaluatesToLeveled e request entities v ∧ InstanceOfType v ty
  := by
  intros h_level_finite h_caps h_reqs_levels h_typeof
  have h_reqs := request_and_entity_match_level_implies_regular h_reqs_levels

  have h_sound := (@ type_of_is_sound e) h_caps h_reqs h_typeof
  have ⟨h_sound₁, v, _, _⟩ := h_sound
  clear h_sound
  cases e
  case lit =>
    apply type_of_is_sound_noninfinite_lit
    repeat assumption
  case var x _ =>
    apply type_of_is_sound_noninfinite_var x h_caps h_reqs_levels h_typeof
  case ite =>
    apply type_of_is_sound_noninfinite_ite
    repeat assumption
    case _ =>
      prove_ih type_of_is_sound_noninfinite
    case _ =>
      prove_ih type_of_is_sound_noninfinite
    case _ =>
      prove_ih type_of_is_sound_noninfinite
  case and =>
    apply type_of_is_sound_noninfinite_and
    repeat assumption
    case _ =>
      prove_ih type_of_is_sound_noninfinite
    case _ =>
      prove_ih type_of_is_sound_noninfinite
  case or =>
    apply type_of_is_sound_noninfinite_or
    repeat assumption
    case _ =>
      prove_ih type_of_is_sound_noninfinite
    case _ =>
      prove_ih type_of_is_sound_noninfinite
  case getAttr =>
    apply type_of_is_sound_noninfinite_getAttr
    repeat assumption
    prove_ih type_of_is_sound_noninfinite
  case unaryApp =>
    apply type_of_is_sound_noninfinite_unary
    repeat assumption
    prove_ih type_of_is_sound_noninfinite
  case binaryApp =>
    apply type_of_is_sound_noninfinite_binary
    repeat assumption
    prove_ih type_of_is_sound_noninfinite
    prove_ih type_of_is_sound_noninfinite
  case hasAttr =>
    apply type_of_is_sound_noninfinite_hasAttr
    repeat assumption
    prove_ih type_of_is_sound_noninfinite
  case set =>
    apply type_of_is_sound_noninfinite_set
    repeat assumption
    intros
    prove_ih type_of_is_sound_noninfinite
  case record =>
    apply type_of_is_sound_noninfinite_record
    repeat assumption
    intros
    prove_ih type_of_is_sound_noninfinite
  case call =>
    apply type_of_is_sound_noninfinite_call
    repeat assumption
    intros
    prove_ih type_of_is_sound_noninfinite
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  case _ =>
    rename e = (.ite _ _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = (.ite _ _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = (.ite _ _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = (.and _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = (.and _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = (.or _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = (.or _ _) => heq
    simp [heq]
    omega
  case _ =>
    rename e = .unaryApp _ _ => heq
    simp [heq]
    omega
  case _ =>
    rename e = .binaryApp _ _ _ => heq
    simp [heq]
    omega
  case _ =>
    rename e = .binaryApp _ _ _ => heq
    simp [heq]
    omega
  case _ =>
    rename e = .getAttr _ _ => heq
    simp [heq]
    omega
  case _ =>
    rename e = .hasAttr _ _ => heq
    simp [heq]
    omega
  case _ =>
    rename List Expr => members
    rename _ = Expr.set _ => heq
    rename _ ∈ members => hin
    rename Expr => e'
    have size₁ : sizeOf e' < sizeOf members := by
      apply List.in_lists_means_smaller
      assumption
    have size₂ : sizeOf members < sizeOf (Expr.set members) := by
      simp
      omega
    rw [← heq] at size₂
    omega
  case _ =>
    rename List (Attr × Expr) => members
    rename _ = Expr.record members => heq
    rename Expr => e'
    rename Attr => a
    have step₁ : sizeOf e' < sizeOf (a,e') := by
      simp
      omega
    have step₂ : sizeOf (a,e') < sizeOf members := by
      apply List.in_lists_means_smaller
      assumption
    have step₃ : sizeOf members < sizeOf (Expr.record members) := by
      simp
      omega
    rw [← heq] at step₃
    omega
  case _ =>
    rename List Expr => args
    rename _ = Expr.call _ args => heq
    rename ExtFun => xfn
    rename Expr => e'
    have step₁ : sizeOf e' < sizeOf args := by
      apply List.in_lists_means_smaller
      assumption
    have step₂ : sizeOf args < sizeOf (Expr.call xfn args) := by
      simp
      omega
    rw [← heq] at step₂
    omega

end Cedar.Thm

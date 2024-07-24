
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Validation.Typechecker.Set
import Cedar.Thm.Validation.Typechecker.Call
import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Levels.Util

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

-- This is the central property we will be proving here
-- If you start from a well formed entity store and evaluate an expression
-- Then you should end up with a value/type that is well formed
def EvaluatesToWellFormed (x : Expr) : Prop :=
  ∀ (v : Value) (ty : CedarType) (request : Request)
  (env : Environment)
  (entities : Entities) (c₁ c₂ : Capabilities)  (l₁ : Level),
  l₁ < .infinite →
  RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁ →
  typeOf x c₁ env (l₁ == .infinite) = Except.ok (ty, c₂) →
  evaluate x request entities = Except.ok v →
  CapabilitiesInvariant c₁ request entities →
   (entities ⊢ v : ty)

-- A well formed value/type is still well formed at its lub
theorem levels_lub {entities : Entities} {v : Value} {ty₁ ty₂ ty : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = some ty)
  (h₂ : entities ⊢ v : ty₁)  :
  (entities ⊢ v : ty) := by
  cases ty₁ <;> cases ty₂ <;> cases ty
    <;> try simp [lub?, lubBool, Option.bind] at h₁
    <;> try simp [lub?, lubBool, Option.bind] at h₂
  case _ =>
    rename_i bty₁ bty₂ bty
    cases bty₁ <;> cases bty₂ <;> cases bty
      <;> try simp [lub?, lubBool] at h₁ <;> try assumption
    case _ =>
      cases h₂
      rename_i b h₁
      cases b <;> simp [InstanceOfBoolType] at h₁
      apply WellFormed.bool
      simp [InstanceOfBoolType]
    case _ =>
      cases h₂
      rename_i b h₁
      cases b <;> simp [InstanceOfBoolType] at h₁
      apply WellFormed.bool
      simp [InstanceOfBoolType]
    case _ =>
      cases h₂
      rename_i b h₁
      cases b <;> simp [InstanceOfBoolType] at h₁
      apply WellFormed.bool
      simp [InstanceOfBoolType]
    case _ =>
      cases h₂
      rename_i b h₁
      cases b <;> simp [InstanceOfBoolType] at h₁
      apply WellFormed.bool
      simp [InstanceOfBoolType]
  case _ =>
    assumption
  case _ =>
    assumption
  case _ =>
    rename_i ty₁ l₁ ty₂ l₂ ty l
    replace ⟨h₁, h₃, h₄⟩ := h₁
    subst h₁
    subst h₃
    subst h₄
    cases h₂
    case entity₀ euid h₁ =>
      cases l₂ <;> simp [min, Option.min, Level.finite, none]
        <;> apply WellFormed.entity₀
        <;> assumption
    case entityₙ euid attrs heq h₂ h₃ h₁ =>
      apply WellFormed.entityₙ
      assumption
      assumption
      intros k v t' hin
      apply h₂
      assumption
      intros k v t' hin
      have hstep : level t' ≥ l₁.sub1 := by apply h₁ ; repeat assumption
      cases l₁ <;> cases l₂
      case _ =>
        simp [Level.sub1] at hstep
        have hinf := le_infinite hstep
        rw [hinf]
        simp [LE.le, min, Option.min, Level.sub1, Level.infinite]
      case _ =>
        rename_i n
        simp [min, Option.min]
        have hinf := le_infinite hstep
        rw [hinf]
        apply all_le_infinit
      case _ =>
        rename_i n
        simp [min, Option.min]
        simp at hstep
        assumption
      case _ n₁ n₂ =>
        cases n₁ <;> cases n₂ <;> try (simp [min, Option.min, Level.sub1] ; apply zero_le_all)
        case _ n₁ n₂ =>
          simp [Level.sub1] at hstep
          simp
          have h : (min (n₁ + 1) (n₂ + 1) = n₁ + 1) ∨ (min (n₁ + 1) (n₂ + 1) = n₂ + 1) := by omega
          cases h
          case _ h =>
            simp [Level.sub1, h]
            assumption
          case _ h =>
            simp [Level.sub1, h]
            have h : some n₂ ≤ some n₁ := by apply le_lift ; omega
            apply le_trans
            repeat assumption
  case _ =>
    rename_i ty₁ ty₂ ty
    cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h₁
  case _ =>
    rename_i ty₁ ty₂
    cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h₁
  case _ =>
    rename_i ty₁ ty₂
    cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h₁
  case _ =>
    rename_i ty₁ ty₂ ety₂ l₂
    cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h₁
  case _ =>
    rename_i ty₁ ty₂ ty
    cases hlub : (ty₁ ⊔ ty₂) <;> try simp [hlub] at h₁
    subst h₁
    cases h₂
    rename_i set h₂
    apply WellFormed.set
    intros v hin
    apply levels_lub
    apply hlub
    apply h₂
    apply hin
  case _ =>
    rename_i ty₁ ty₂ rty
    cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h₁
  case _ =>
    rename_i ty₁ ty₂ rty
    cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h₁
  case _ =>
    not_record
  case _ =>
    not_record
  case _ =>
    not_record
  case _ =>
    not_record
  case _ =>
    not_record
  case _ =>
    rename_i rty₁ rty₂ rty

    cases h₂
    rename_i value_record h₃ h₄ h₅
    cases rty₁
    rename_i rty₁
    cases rty₂
    rename_i rty₂
    cases rty
    rename_i rty
    have hlub : IsLubOfRecordTypes rty rty₁ rty₂ := by
      apply lubRecordType_is_lub_of_record_types
      simp [lub?, Option.bind] at h₁
      cases hlubRecord : lubRecordType rty₁ rty₂ <;> simp [hlubRecord] at h₁
      subst h₁
      rfl
    apply WellFormed.record
    case _ =>
      intros k h_contains
      apply lubRecord_contains_left
      apply hlub
      apply h₃
      apply h_contains
    case _ =>
      intros k v qty h_value_find h_ty_find
      have h := lubRecord_find_implies_find hlub h_ty_find
      have ⟨qty₁, qty₂, h_find₁, _, h_lub₁⟩ := h
      clear h
      have hwf : entities ⊢ v : (Qualified.getType qty₁) := by
        apply h₅
        repeat assumption
      apply levels_lub
      apply qualitype_lub_lifts
      apply h_lub₁
      apply hwf
    case _ =>
      intros k qty h_find h_isreq
      have h := lubRecord_find_implies_find_left hlub h_find
      have ⟨qty₁, h_find₁, h_req₁⟩ := h
      apply h₄ k qty₁
      apply h_find₁
      simp [h_req₁, h_isreq]
  case _ =>
    not_record
  case _ =>
    rename_i xty₁ xty₂ xty
    have ⟨h₂, h₃⟩ := h₁
    subst h₂
    subst h₃
    assumption
termination_by (sizeOf v)
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  case _ =>
    rename Set Value => members
    rename _ = (Value.set members) => heq
    rw [heq]
    have step₁ : sizeOf v < sizeOf (members) := by
      apply Set.in_set_means_smaller
      assumption
    have step₂ : sizeOf members < sizeOf (Value.set members) := by
      simp
      omega
    omega
  case _ =>
    rename _ = Value.record _ => heq
    rename Map Attr Value => members
    rw [heq]
    have step₁ : sizeOf v < sizeOf members := by
      apply Map.find_means_smaller
      assumption
    simp
    omega

theorem evaluates_to_value {v v' : Value} {e : Expr} {entities : Entities} {req : Request}
  (h₁ : EvaluatesTo e req entities v)
  (h₂ : evaluate e req entities = Except.ok v') :
  v = v' := by
  cases h₁ <;> rename_i h₁ <;> try simp [h₁] at h₂
  cases h₁ <;> rename_i h₁ <;> try simp [h₁] at h₂
  cases h₁ <;> rename_i h₁ <;> try simp [h₁] at h₂
  assumption

theorem eq_is_bool {lhs rhs : Expr} {c₁ c₂ : Capabilities} {ty : CedarType}  {env : Environment} {l₁ : Level}
  (h₁ : typeOf (.binaryApp .eq lhs rhs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂)) :
  ∃ bty, ty = .bool bty
  := by
  have hinv := type_of_eq_inversion h₁
  have ⟨hinv₁, hinv₂⟩ := hinv
  clear hinv
  subst hinv₁
  split at hinv₂
  case _ =>
    split at hinv₂
    <;> subst hinv₂
    <;> try (solve | exists .tt)
    exists .ff
  case _ =>
    replace ⟨ty₁, _, ty₂, _, _, _, hinv₄ ⟩ := hinv₂
    split at hinv₄
    case _ =>
      exists BoolType.anyBool
    case _ =>
      exists BoolType.ff
      simp [hinv₄]

theorem int_cmp_is_bool {o : BinaryOp} {lhs rhs : Expr} {c₁ c₂ : Capabilities} {ty : CedarType} {env : Environment} {l₁ : Level}
  (h₁ : o = .less ∨ o = .lessEq)
  (h₂ : typeOf (.binaryApp o rhs lhs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂)) :
  ∃ bty, ty = .bool bty := by
  have hinv := type_of_int_cmp_inversion h₁ h₂
  replace ⟨_, hinv, _⟩ := hinv
  subst hinv
  exists .anyBool

theorem int_arith_is_int {o : BinaryOp} {lhs rhs : Expr} {c₁ c₂ : Capabilities} {ty : CedarType} {env : Environment} {l₁ : Level}
  (h₁ : o = .add ∨ o = .sub ∨ o = .mul)
  (h₂ : typeOf (.binaryApp o rhs lhs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂)) :
  ty = .int  := by
  have hinv := type_of_int_arith_inversion h₁ h₂
  simp [hinv]

theorem evaluates_to_well_formed_binary {o : BinaryOp} {lhs rhs : Expr} {v : Value} {ty: CedarType} {request : Request} {entities: Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.binaryApp o lhs rhs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.binaryApp o lhs rhs) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities)
  :
  entities ⊢ v : ty := by
  have hsound := (@type_of_is_sound (.binaryApp o lhs rhs))
    (by assumption)
    (by
      apply request_and_entity_match_level_implies_regular
      assumption
    )
    (by assumption)
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  have heq : v' = v := by
    apply evaluates_to_value
    repeat assumption
  subst heq
  cases o
  case eq =>
    have heq := eq_is_bool h₃
    replace ⟨bty, heq⟩ := heq
    subst heq
    cases hsound₃
    apply WellFormed.bool
    assumption
  case mem =>
    have hinv := type_of_mem_inversion h₃
    have ⟨_, ety₂, l', l'', hinv₁, _, c₂', hinv₃⟩ := hinv
    cases hinv₃
      <;> rename_i hinv₃
      <;> have ⟨_, hinv₄⟩ := hinv₃
      <;> simp [typeOfInₑ, typeOfInₛ] at hinv₄
      <;> split at hinv₄
      <;> simp [ok, err] at hinv₄
      <;> subst hinv₄
      <;> cases hsound₃
      <;> apply WellFormed.bool
      <;> assumption
  case less =>
    have hbty := int_cmp_is_bool (by simp) h₃
    replace ⟨bty, hbty⟩ := hbty
    subst hbty
    cases hsound₃
    apply WellFormed.bool
    assumption
  case lessEq =>
    have hbty := int_cmp_is_bool (by simp) h₃
    replace ⟨bty, hbty⟩ := hbty
    subst hbty
    cases hsound₃
    apply WellFormed.bool
    assumption
  case add =>
    have hint := int_arith_is_int (by simp) h₃
    subst hint
    cases hsound₃
    apply WellFormed.int
  case sub =>
    have hint := int_arith_is_int (by simp) h₃
    subst hint
    cases hsound₃
    apply WellFormed.int
  case mul =>
    have hint := int_arith_is_int (by simp) h₃
    subst hint
    cases hsound₃
    apply WellFormed.int
  case contains =>
    have hinv := type_of_contains_inversion h₃
    have heq : ty = CedarType.bool BoolType.anyBool := by simp [hinv]
    subst heq
    cases hsound₃
    apply WellFormed.bool
    assumption
  case containsAll =>
    have hinv := type_of_containsA_inversion (by simp) h₃
    have heq : ty = CedarType.bool BoolType.anyBool := by simp [hinv]
    subst heq
    cases hsound₃
    apply WellFormed.bool
    assumption
  case containsAny =>
    have hinv := type_of_containsA_inversion (by simp) h₃
    have heq : ty = CedarType.bool BoolType.anyBool := by simp [hinv]
    subst heq
    cases hsound₃
    apply WellFormed.bool
    assumption

theorem evaluates_to_well_formed_unary {o : UnaryOp} {x : Expr} {v : Value} {ty: CedarType} {request : Request} {entities: Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.unaryApp o x) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.unaryApp o x) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities)
  :
  entities ⊢ v : ty := by
  have hreq : RequestAndEntitiesMatchEnvironment env request entities := by
    apply request_and_entity_match_level_implies_regular
    assumption
  have hsound := (@type_of_is_sound (.unaryApp o x)) (by assumption) (by assumption) (by assumption)
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  have heq : v' = v := by
    apply evaluates_to_value
    repeat assumption
  subst heq
  clear hsound
  cases o
  case not =>
    have hinv := type_of_not_inversion h₃
    have ⟨_, bty, _, hinv₂, _⟩ := hinv
    clear hinv
    subst hinv₂
    cases hsound₃
    apply WellFormed.bool
    assumption
  case neg =>
    have hinv := type_of_neg_inversion h₃
    have ⟨_, hinv₂, _, _⟩ := hinv
    clear hinv
    subst hinv₂
    cases hsound₃
    apply WellFormed.int
  case like =>
    have hinv := type_of_like_inversion h₃
    have ⟨_, hinv₂, _⟩ := hinv
    subst hinv₂
    cases hsound₃
    apply WellFormed.bool
    assumption
  case is =>
    have hinv := type_of_is_inversion h₃
    have ⟨_, ety', _, _, hinv₂, _⟩ := hinv
    clear hinv
    rename_i _
    split at hinv₂ <;> (
      subst hinv₂
      cases hsound₃
      apply WellFormed.bool
      assumption
    )

theorem evaluates_to_well_formed_var {v : Var} {val : Value}  {request : Request} {entities: Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.var v) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.var v) request entities = Except.ok val)
  :
  entities ⊢ val : ty
  := by
  unfold RequestAndEntitiesMatchEnvironmentLeveled at h₂
  have ⟨_, _, _, _, _, _, _⟩ := h₂
  clear h₂
  cases v
    <;> simp [evaluate] at h₅
    <;> subst h₅
    <;> simp [typeOf, typeOfVar, ok] at h₃
    <;> replace ⟨h₃, _⟩ := h₃
    <;> subst h₃
    <;> assumption

theorem evaluates_to_well_formed_lit {l : Prim}  {ty: CedarType} {request : Request} {entities: Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.lit l) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.lit l) request entities = Except.ok v)
  :
  entities ⊢ v : ty := by
  cases l <;> try (
    rename_i value
    cases value <;> (
      simp [evaluate] at h₅
      subst h₅
      simp [typeOf, typeOfLit, ok] at h₃
      replace ⟨h₃, _⟩ := h₃
      subst h₃
    )
  )
  case int =>
    apply WellFormed.int
  case bool.true =>
    apply WellFormed.bool
    simp [InstanceOfBoolType]
  case bool.false =>
    apply WellFormed.bool
    simp [InstanceOfBoolType]
  case string =>
    apply WellFormed.string
  case entityUID =>
    rename_i euid
    cases heq : decide (l₁ == .infinite)
    case _ =>
      simp at heq
      simp [typeOf, typeOfLit] at h₃
      split at h₃
      case _ =>
        simp [ok] at h₃
        replace ⟨h₃, _⟩ := h₃
        subst h₃
        simp [evaluate] at h₅
        subst h₅
        apply WellFormed.entity₀
        simp [InstanceOfEntityType]
      case _ =>
        exfalso
        simp [err] at h₃
    case _ =>
      simp at heq
      subst heq
      cases h₁

theorem set_eval_step {members : List Expr} {values : List Value}  {v : Value} {request : Request} {entities : Entities}
 (h₁ : (members.mapM (λ x => evaluate x request entities)) = .ok values)
 (h₂ : v ∈ values) :
  ∃ e, e ∈ members ∧ evaluate e request entities = .ok v
  := by
  cases values
  case nil =>
    cases h₂
  case cons head tail =>
    cases members
    case nil =>
      simp [pure, Except.pure] at h₁
    case cons members_head members_tail =>
      cases h₂ -- Case analysis on `v ∈ (head :: tail)`
      case _ => -- Case 1: `v = head`
        rw [List.mapM_cons] at h₁
        cases h_eval_head : evaluate members_head request entities <;> simp [h_eval_head] at h₁
        rename_i head_value
        cases h_eval_tail : List.mapM (λ x => evaluate x request entities) members_tail <;> simp [h_eval_tail] at h₁
        rename_i values_tail
        simp [pure, Except.pure] at h₁
        exists members_head
        simp [h₁, h_eval_head]
      case _ => -- Case 2: `v ∈ tail ∧ v ≠ head`. This is the inductive case
        rename_i hin
        rw [List.mapM_cons] at h₁
        cases h_eval_head : evaluate members_head request entities <;> simp [h_eval_head] at h₁
        rename_i head_value
        cases h_eval_tail : List.mapM (λ x => evaluate x request entities) members_tail <;> simp [h_eval_tail] at h₁
        rename_i values_tail
        simp [pure, Except.pure] at h₁
        have ⟨_,  h₄⟩ := h₁
        subst h₄
        have ih := @set_eval_step members_tail values_tail v request entities h_eval_tail hin
        replace⟨e, ih⟩ := ih
        exists e
        constructor <;> simp [ih]

macro "extn_comparator_correct" f:(ident) inv:(ident) hsound₃:(ident) hsound₂:(ident) h₃:(ident) h₅:(ident) : tactic =>
  `(tactic | (
    have h₃ := $h₃
    have hsound₃ := $hsound₃
    have hsound₂ := $hsound₂
    have h₅ := $h₅
    have hinv := $inv (by simp [IsDecimalComparator, IsIpAddrRecognizer]) h₃
    replace ⟨hinv, _⟩ := hinv
    subst hinv
    cases hsound₃
    cases hsound₂ <;> rename_i hsound₂ <;> simp [h₅] at hsound₂
    subst hsound₂
    apply $f
    assumption
  ))

macro "decimal_comparator_correct" hsound₃:(ident) hsound₂:(ident) h₃:(ident) h₅:(ident) : tactic =>
  `(tactic | (
    extn_comparator_correct WellFormed.bool type_of_call_decimal_comparator_inversion $hsound₃ $hsound₂ $h₃ $h₅
  ))

macro "ip_recognizer_correct" hsound₃:(ident) hsound₂:(ident) h₃:(ident) h₅:(ident) : tactic =>
  `(tactic | (
    extn_comparator_correct WellFormed.bool type_of_call_ipAddr_recognizer_inversion $hsound₃ $hsound₂ $h₃ $h₅
  ))

theorem evaluates_to_well_formed_call {xfn : ExtFun} {xs : List Expr} {v : Value} {ty : CedarType} {request : Request} {entities : Entities} {env : Environment} {c₁ c₂ : Capabilities} {l : Level}
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (.call xfn xs) c₁ env (l == Level.infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.call xfn xs) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities) :
  entities ⊢ v : ty
  := by
  have hsound := (@type_of_is_sound (.call xfn xs))
    (by assumption)
    (by assumption)
    (by assumption)
  have ⟨hsound₁, v, hsound₂, hsound₃⟩ := hsound
  clear hsound
  cases xfn
  case decimal =>
    have hinv := type_of_call_decimal_inversion h₃
    replace ⟨hinv, _⟩ := hinv
    subst hinv
    cases hsound₃
    cases hsound₂ <;> rename_i hsound₂ <;> simp [h₅] at hsound₂
    subst hsound₂
    apply WellFormed.ext
    assumption
  case lessThan =>
    decimal_comparator_correct hsound₃ hsound₂ h₃ h₅
  case lessThanOrEqual =>
    decimal_comparator_correct hsound₃ hsound₂ h₃ h₅
  case greaterThan =>
    decimal_comparator_correct hsound₃ hsound₂ h₃ h₅
  case greaterThanOrEqual =>
    decimal_comparator_correct hsound₃ hsound₂ h₃ h₅
  case ip =>
    have hinv := type_of_call_ip_inversion h₃
    replace ⟨hinv, _⟩ := hinv
    subst hinv
    cases hsound₃
    cases hsound₂ <;> rename_i hsound₂ <;> simp [h₅] at hsound₂
    subst hsound₂
    apply WellFormed.ext
    assumption
  case isIpv4 =>
    ip_recognizer_correct hsound₃ hsound₂ h₃ h₅
  case isIpv6 =>
    ip_recognizer_correct hsound₃ hsound₂ h₃ h₅
  case isLoopback =>
    ip_recognizer_correct hsound₃ hsound₂ h₃ h₅
  case isMulticast =>
    ip_recognizer_correct hsound₃ hsound₂ h₃ h₅
  case isInRange =>
    have hinv := type_of_call_isInRange_inversion h₃
    replace ⟨hinv, _⟩ := hinv
    subst hinv
    cases hsound₃
    cases hsound₂ <;> rename_i hsound₂ <;> simp [h₅] at hsound₂
    subst hsound₂
    apply WellFormed.bool
    assumption

theorem evaluates_to_well_formed_ite {cond cons alt : Expr} {v : Value} {request : Request} {entities : Entities} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.ite cond cons alt) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.ite cond cons alt) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities)
  (ih₁ : EvaluatesToWellFormed cons)
  (ih₂ : EvaluatesToWellFormed alt) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.ite cond cons alt) c₂ request entities ∧ ∃ v, EvaluatesTo (.ite cond cons alt) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  dril_to_value hsound₂ h₅
  have hinv := type_of_ite_inversion h₃
  replace ⟨bty, c₁', ty₂, c₂', ty₃, c₃, hinv₁, hinv⟩ := hinv
  have hsound_cond : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ v, EvaluatesTo cond request entities v ∧ InstanceOfType v (.bool bty)  := by
    type_soundness
  have ⟨hsound_cond₁, v_cond, hsound_cond₂, hsound_cond₃⟩ := hsound_cond
  clear hsound_cond
  have heval_cond : ∃ v, evaluate cond request entities = Except.ok v := by
    cases hcond : evaluate cond request entities
    case error =>
      simp [evaluate, hcond, Result.as] at h₅
    case ok v =>
      exists v
  replace ⟨v_cond, heval_cond⟩ := heval_cond
  dril_to_value hsound_cond₂ heval_cond
  cases hsound_cond₃
  rename_i bool_val hsound_cond₃
  cases bty
  case tt =>
    simp at hinv
    have ⟨hinv₂, hinv₃, _⟩ := hinv
    clear hinv
    subst hinv₃
    cases bool_val <;> simp [InstanceOfBoolType] at hsound_cond₃
    apply ih₁
    repeat assumption
    simp [evaluate, heval_cond, Result.as, Coe.coe, Value.asBool] at h₅
    assumption
    apply capability_union_invariant
    assumption
    apply hsound_cond₁
    assumption
  case ff =>
    simp at hinv
    have ⟨hinv₂, hinv₃, hinv₄⟩ := hinv
    clear hinv
    subst hinv₃
    subst hinv₄
    cases bool_val <;> simp [InstanceOfBoolType] at hsound_cond₃
    apply ih₂
    repeat assumption
    simp [evaluate, heval_cond, Result.as, Coe.coe, Value.asBool] at h₅
    repeat assumption
  case anyBool =>
    simp at hinv
    have ⟨hinv₁, hinv₂, hinv₃, hinv₄⟩ := hinv
    clear hinv
    subst hinv₄
    cases bool_val
    case true =>
      have hsound_cons : GuardedCapabilitiesInvariant cons c₂' request entities ∧ ∃ v, EvaluatesTo cons request entities v ∧ InstanceOfType v ty₂ := by
        apply type_of_is_sound
        apply capability_union_invariant
        assumption
        apply hsound_cond₁
        assumption
        apply request_and_entity_match_level_implies_regular
        assumption
        assumption
      have ⟨_, v_cons, hsound_cons₂, _⟩ := hsound_cons
      clear hsound_cons
      have heval_cons : ∃ v, evaluate cons request entities = .ok v := by
        cases h : evaluate cons request entities
        case ok v =>
          exists v
        case error =>
          simp [evaluate, heval_cond, h, Result.as, Coe.coe, Value.asBool] at h₅
      replace ⟨v_cons', heval_cons⟩ := heval_cons
      dril_to_value hsound_cons₂ heval_cons
      simp [heval_cons, heval_cond, evaluate, Result.as, Coe.coe, Value.asBool] at h₅
      subst h₅
      have step : (entities ⊢ v_cons : ty₂) := by
        apply ih₁
        assumption
        assumption
        assumption
        assumption
        apply capability_union_invariant
        assumption
        apply hsound_cond₁
        assumption
      apply levels_lub
      repeat assumption
    case false =>

      have hsound_alt : GuardedCapabilitiesInvariant alt c₃ request entities ∧ ∃ v, EvaluatesTo alt request entities v ∧ InstanceOfType v ty₃ := by
        type_soundness
      have ⟨hsound_alt₁, v_alt, hsound_alt₂, hsound_alt₃⟩ := hsound_alt
      clear hsound_alt
      have heval_alt : ∃ v, evaluate alt request entities = .ok v := by
        cases h : evaluate alt request entities
        case ok v =>
          exists v
        case error =>
          simp [evaluate, h, heval_cond, Result.as, Coe.coe, Value.asBool] at h₅
      replace ⟨v_alt', heval_alt⟩ := heval_alt
      dril_to_value hsound_alt₂ heval_alt
      simp [evaluate, heval_alt, heval_cond, Result.as, Coe.coe, Value.asBool] at h₅
      subst h₅
      have step : entities ⊢ v_alt : ty₃ := by
        apply ih₂
        repeat assumption
      apply levels_lub
      rw [lub_comm] at hinv₃
      repeat assumption

macro "bool_constant" hinv:(ident) hsound₃:(ident) : tactic =>
  `(tactic | (
    solve | (
      have hinv := $hinv
      have hsound₃ := $hsound₃
      simp [lubBool] at hinv
      have ⟨hinv₁, hinv₂, hinv₃⟩ := hinv
      subst hinv₂
      cases hsound₃
      rename_i bool_val hsound₃
      cases bool_val <;> simp [InstanceOfBoolType] at hsound₃
      apply WellFormed.bool
      assumption
    )
  ))

theorem evaluates_to_well_formed_and {lhs rhs : Expr} {v : Value} {request : Request} {entities : Entities} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.and lhs rhs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.and lhs rhs) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.and lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.and lhs rhs) request entities v ∧ InstanceOfType v ty
  := by type_soundness
  have ⟨_, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  dril_to_value hsound₂ h₅
  have hinv := type_of_and_inversion h₃
  replace ⟨bty, c₁', hinv⟩ := hinv
  cases bty
  case tt =>
    simp at hinv
    replace ⟨_, bty₂, c₂', hinv⟩ := hinv
    cases bty₂ <;> bool_constant hinv hsound₃
  case ff =>
    simp at hinv
    bool_constant hinv hsound₃
  case anyBool =>
    simp at hinv
    replace ⟨_, bty₂, c₂', hinv⟩ := hinv
    cases bty₂ <;> simp at hinv <;> bool_constant hinv hsound₃

theorem evaluates_to_well_formed_or {lhs rhs : Expr} {v : Value} {request : Request} {entities : Entities} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.or lhs rhs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.or lhs rhs) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.or lhs rhs) c₂ request entities ∧ ∃ v, EvaluatesTo (.or lhs rhs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨_, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  dril_to_value hsound₂ h₅
  have hinv := type_of_or_inversion h₃
  replace ⟨bty₁, c₁', hinv⟩ := hinv
  cases bty₁
  case tt =>
    bool_constant hinv hsound₃
  case ff =>
    simp at hinv
    replace ⟨_, bty₂, hinv⟩ := hinv
    cases bty₂
    case ff =>
      have ⟨_, hinv₂⟩ := hinv
      clear hinv
      subst hinv₂
      cases hsound₃
      rename_i bool hsound₃
      cases bool <;> simp [InstanceOfBoolType] at hsound₃
      apply WellFormed.bool
      assumption
    case tt =>
      have ⟨_, hinv₂⟩ := hinv
      clear hinv
      subst hinv₂
      cases hsound₃
      rename_i bool hsound₃
      cases bool <;> simp [InstanceOfBoolType] at hsound₃
      apply WellFormed.bool
      assumption
    case anyBool =>
      have ⟨_, hinv₂⟩ := hinv
      clear hinv
      subst hinv₂
      cases hsound₃
      rename_i bool hsound₃
      cases bool <;> simp [InstanceOfBoolType] at hsound₃
      <;> apply WellFormed.bool
      <;> assumption
  case anyBool =>
    simp at hinv
    replace ⟨_, bty₂, c₂', hinv⟩ := hinv
    cases bty₂ <;> bool_constant hinv hsound₃

theorem evaluates_to_well_formed_getAttr_entity {e : Expr} {attr : Attr} {v : Value} {request : Request} {entities : Entities} {env : Environment} {c₁ c₁' : Capabilities} {l₁ l₂ : Level} {ety : EntityType}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₄ : evaluate (.getAttr e attr) request entities = .ok v)
  (h₅ : CapabilitiesInvariant c₁ request entities)
  (h₆ : typeOf e c₁ env (l₁ == Level.infinite) = Except.ok (CedarType.entity ety l₂, c₁'))
  (h₇ : l₂ > Level.finite 0)
  (ih : EvaluatesToWellFormed e) :
  (entities ⊢ v : ty) := by
  have hsound : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesTo e request entities v ∧ InstanceOfType v (.entity ety l₂) := by
    type_soundness
  have ⟨_, v_entity, hsound₂, hsound₃⟩ := hsound
  have heval : ∃ v_entity', evaluate e request entities = .ok v_entity' := by
    cases h : evaluate e request entities
    case ok v =>
      exists v
    case error =>
      simp [evaluate, Result.as, h] at h₄
  replace ⟨v_entity', heval⟩ := heval
  dril_to_value hsound₂ heval
  cases hsound₃
  rename_i euid hsound₃
  have step : entities ⊢ (.prim (.entityUID euid)) : .entity ety l₂ := by
    apply ih
    repeat assumption
  cases step -- Two ways to have a well formed entity value
  case _ => -- The level can be zero, which is impossible as we're derefing ijt
    cases h₇
    omega
  case _ => -- The level can be nonzero
    rename_i attrs ih₁ ih₂ ih₃ ih₄
    apply ih₁
    simp [getAttr, attrsOf, ih₁, evaluate, heval, ih₂] at h₄
    apply Map.findOrErr_ok_implies_in_kvs
    apply h₄

theorem evaluates_to_well_formed_getAttr_record {e : Expr} {attr : Attr} {v : Value} {request : Request} {entities : Entities} {env : Environment} {c₁ c₂ c₁' : Capabilities} {l₁ : Level} {rty : RecordType}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.getAttr e attr) c₁ env (l₁ == .infinite) = .ok (ty, c₂))
  (h₄ : evaluate (.getAttr e attr) request entities = .ok v)
  (h₅ : CapabilitiesInvariant c₁ request entities)
  (h₆ : typeOf e c₁ env (l₁ == Level.infinite) = Except.ok (CedarType.record rty, c₁'))
  (ih : EvaluatesToWellFormed e) :
  (entities ⊢ v : ty) := by
  have hsound : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesTo e request entities v ∧ InstanceOfType v (.record rty) := by
    type_soundness
  have ⟨_, v_record, hsound₂, hsound₃⟩ := hsound
  clear hsound
  have heval : ∃ v_record', evaluate e request entities = .ok v_record' := by
    cases h: evaluate e request entities
    case ok v =>
      exists v
    case error _ =>
      simp [h, evaluate, Result.as] at h₄
  replace ⟨v_record', heval⟩ := heval
  dril_to_value hsound₂ heval
  cases hsound₃
  rename_i record hsound₃₁ hsound₃₂ hsound₃₃
  have step : entities ⊢ (Value.record record) : .record rty := by
    apply ih
    repeat assumption
  cases step
  rename_i ih₁ ih₂ ih₃
  simp [evaluate, getAttr, attrsOf, heval] at h₄
  have hcontains : rty.contains attr = true := by
    apply hsound₃₁
    simp [Map.contains]
    cases h : record.find? attr
    case a.some =>
      simp
    case a.none =>
      simp [Map.findOrErr, h] at h₄
  have hqty : ∃ (qty : QualifiedType), rty.find? attr = .some qty := by
    simp [Map.contains] at hcontains
    cases h : Map.find? rty attr
    case none =>
      simp [h] at hcontains
    case some qty =>
      exists qty
  replace ⟨qty, hqty⟩ := hqty
  have heq : qty.getType = ty := by
    simp [typeOf, h₆, typeOfGetAttr, getAttrInRecord, hqty] at h₃
    cases qty
    case _ =>
      simp at h₃
      cases hin : decide ((e,attr) ∈ c₁) <;> simp at hin
      case _ =>
        rw [if_neg] at h₃
        simp [err] at h₃
        assumption
      case _ =>
        rw [if_pos] at h₃
        rename_i ty'
        simp [ok] at h₃
        replace ⟨h₃, _⟩ := h₃
        subst h₃
        simp [Qualified.getType]
        assumption
    case _ =>
      rename_i ty'
      simp [ok] at h₃
      replace ⟨h₃, _⟩ := h₃
      subst h₃
      simp [Qualified.getType]
  have step := ih₃ attr v qty
    (by
      cases h : record.find? attr <;> simp [h, Map.findOrErr] at h₄
      subst h₄
      rfl
    )
    hqty
  rw [heq] at step
  assumption

theorem evaluates_to_well_formed_getAttr {e : Expr} {attr : Attr} {v : Value} {request : Request} {entities : Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.getAttr e attr) c₁ env (l₁ == .infinite) = .ok (ty, c₂))
  (h₄ : evaluate (.getAttr e attr) request entities = .ok v)
  (h₅ : CapabilitiesInvariant c₁ request entities)
  (ih : EvaluatesToWellFormed e) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.getAttr e attr) c₂ request entities ∧ ∃ v, EvaluatesTo (.getAttr e attr) request entities v ∧  InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, _⟩ := hsound
  clear hsound
  dril_to_value hsound₂ h₄
  have hinv := type_of_getAttr_inversion_levels h₃
  replace ⟨hinv₁, c₁', hinv⟩ := hinv
  subst hinv₁
  cases hinv <;> rename_i hinv
  case _ =>
    replace ⟨ety, l₂, hinv₁, hinv₂⟩ := hinv
    clear hinv
    apply evaluates_to_well_formed_getAttr_entity
    repeat assumption
  case _ =>
    replace ⟨rty, hinv⟩ := hinv
    apply evaluates_to_well_formed_getAttr_record
    repeat assumption

theorem levels_correct_hasAttr {e : Expr} {attr : Attr} {v : Value} {request : Request} {entities : Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.hasAttr e attr) c₁ env (l₁ == .infinite) = .ok (ty, c₂))
  (h₄ : evaluate (.hasAttr e attr) request entities = .ok v)
  (h₅ : CapabilitiesInvariant c₁ request entities) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.hasAttr e attr) c₂ request entities ∧ ∃ v, EvaluatesTo (.hasAttr e attr) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨_, v', hsound₂, hsound₃⟩ := hsound
  dril_to_value hsound₂ h₄
  have hinv := type_of_hasAttr_inversion' h₃
  replace ⟨bty, hinv⟩ := hinv
  subst hinv
  cases bty <;> try (
    solve | (
    cases hsound₃
    rename_i bool hsound₃
    cases bool <;> simp [InstanceOfBoolType] at hsound₃
    apply WellFormed.bool
    assumption
    )
  )
  case anyBool =>
    cases hsound₃
    apply WellFormed.bool
    assumption

theorem levels_correct_set {members : List Expr} {v : Value} {request : Request} {entities : Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.set members) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₄ : evaluate (.set members) request entities = .ok v)
  (h₅ : CapabilitiesInvariant c₁ request entities)
  (ih : ∀ e, e ∈ members → EvaluatesToWellFormed e) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.set members) c₂ request entities ∧ ∃ v, EvaluatesTo (.set members) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  dril_to_value hsound₂ h₄
  have hinv := type_of_set_inversion h₃
  have ⟨hinv₁, ty', hinv₂, hinv₃⟩ := hinv
  clear hinv
  subst hinv₂
  subst hinv₁
  cases hsound₃
  rename_i set_value hinst
  apply WellFormed.set
  intros v hin
  simp [evaluate, List.mapM₁, List.attach, List.attachWith] at h₄
  rw [List.mapM_pmap_subtype (λ (e : Expr) => evaluate e request entities) members] at h₄
  cases hmembers : List.mapM (λ e => evaluate e request entities) members <;> simp [hmembers] at h₄
  rename_i member_list
  have in_list : v ∈ member_list := by
    apply Set.in_constructor_in_set
    rw [h₄]
    assumption
  have hexpr := (@set_eval_step members member_list) hmembers in_list
  have ⟨e, hexpr₁, hexpr₂⟩ := hexpr
  clear hexpr
  have hinv₄ := hinv₃ e hexpr₁
  replace ⟨tyᵢ, cᵢ, hinv₄, hinv₅⟩ := hinv₄
  have step : entities ⊢ v : tyᵢ := by
    apply ih
    repeat assumption
  apply levels_lub
  repeat assumption

theorem record_eval_step (attrs : List (Attr × Expr)) (record : List (Attr × Value)) (request : Request) (entities : Entities) (attr : Attr) (v : Value)
  (h₁ : List.mapM (λ (pair : (Attr × Expr)) => bindAttr pair.fst (evaluate pair.snd request entities)) attrs = .ok record)
  (h₂ : (attr, v) ∈ record) :
  ∃ e, (attr, e) ∈ attrs ∧ evaluate e request entities = .ok v := by
  cases attrs <;> cases record
  case _ =>
    cases h₂
  case _ =>
    simp [List.mapM, List.mapM.loop, pure, Except.pure] at h₁
  case _ =>
    cases h₂
  case _ attr_head attr_tail record_head record_tail =>
    rw [List.mapM_cons] at h₁
    cases hhead : bindAttr attr_head.fst (evaluate attr_head.snd request entities) <;> simp [hhead] at h₁
    cases htail : List.mapM (λ pair => bindAttr pair.fst (evaluate pair.snd request entities)) attr_tail <;> simp [htail] at h₁
    rename_i head tail
    cases h₂
    case _ =>
      cases head
      simp [pure, Except.pure] at h₁
      have ⟨⟨heq₁, heq₂⟩, heq₃⟩ := h₁
      subst heq₁
      subst heq₂
      subst heq₃
      rename_i attr v
      clear h₁
      have ⟨attr', e⟩ := attr_head
      exists e
      simp [bindAttr] at hhead
      cases heval : evaluate e request entities <;> simp [heval] at hhead
      simp [hhead]
    case _ hin =>
      simp [pure, Except.pure] at h₁
      simp [h₁] at htail
      have ih := record_eval_step attr_tail record_tail request entities attr v htail hin
      replace ⟨e, ih⟩ := ih
      exists e
      simp [ih]

theorem forall₂_find_match {α β : Type} (l₁ : List α) (l₂ : List β) (p : α → β → Prop) (a : α)
  (h₁ : List.Forall₂ p l₁ l₂)
  (h₂ : a ∈ l₁) :
  ∃ b, b ∈ l₂ ∧ p a b
  := by
  cases h₁
  case nil =>
    cases h₂
  case cons =>
    rename_i a_head b_head a_tail b_tail holds_on_head holds_on_tail
    cases h₂
    case _ =>
      exists b_head
      simp [holds_on_head]
    case _ hin =>
      have ih := forall₂_find_match a_tail b_tail p a holds_on_tail hin
      replace ⟨b, ih₁, ih₂⟩ := ih
      exists b
      simp [ih₁, ih₂]

theorem AttrExprHasAttrType_constraints_keys (k₁ k₂ : Attr) (e : Expr) (qty : QualifiedType) (c : Capabilities) (env : Environment) (l : Level)
  (h₁ : AttrExprHasAttrType c env l (k₁, e) (k₂, qty)) :
  k₁ = k₂ := by
  simp [AttrExprHasAttrType] at h₁
  have ⟨_, h₁⟩ := h₁
  simp [h₁]

theorem evaluate_empty_record (request : Request) (entities : Entities) :
  evaluate (.record []) request entities = .ok (Value.record (Map.make [])) := by
  simp [evaluate, List.mapM₂, List.attach₂]

theorem evaluates_to_well_formed_record {attrs : List (Attr × Expr)} {v : Value} {request : Request} {entities : Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf (.record attrs) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate (.record attrs) request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities)
  (ih : ∀ (a : Attr) (e : Expr), (a,e) ∈ attrs → EvaluatesToWellFormed e ) :
  entities ⊢ v : ty := by
  have hsound : GuardedCapabilitiesInvariant (.record attrs) c₂ request entities ∧ ∃ v, EvaluatesTo (.record attrs) request entities v ∧ InstanceOfType v ty := by
    type_soundness
  have ⟨hsound₁, v', hsound₂, hsound₃⟩ := hsound
  clear hsound
  dril_to_value hsound₂ h₅
  clear hsound₂
  have hinv := type_of_record_inversion h₃
  replace ⟨_, rty, hinv₁, hinv⟩ := hinv
  subst hinv₁
  cases hsound₃
  rename_i attr_map hsound₃ hsound₄ hsound₅
  cases attrs
  case nil =>
    cases hinv
    simp [evaluate_empty_record, Map.make, List.canonicalize] at h₅
    rw [← h₅]
    apply WellFormed.record
    case _ =>
      intros k  hcontains
      simp [Map.contains, Map.find?, List.find?] at hcontains
    case _ =>
      intros k v qty hfind_value hfind_type
      simp [Map.find?, List.find?] at hfind_value
    case _ =>
      intros k qty hfind
      simp [Map.find?, List.find?] at hfind
  case cons attr attrs =>
    sorry

theorem evaluates_to_well_formed {x : Expr} {v : Value} {ty: CedarType} {request : Request} {entities: Entities} {env : Environment} {c₁ c₂ : Capabilities} {l₁ : Level}
  (h₁ : l₁ < .infinite)
  (h₂ : RequestAndEntitiesMatchEnvironmentLeveled env request entities l₁)
  (h₃ : typeOf x c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (h₅ : evaluate x request entities = Except.ok v)
  (h_caps : CapabilitiesInvariant c₁ request entities)
  :
  entities ⊢ v : ty
  := by
  have hreq : RequestAndEntitiesMatchEnvironment env request entities :=  by
    apply request_and_entity_match_level_implies_regular
    assumption
  cases x
  case lit p =>
    apply evaluates_to_well_formed_lit
    repeat assumption
  case var x =>
    apply evaluates_to_well_formed_var
    repeat assumption
  case ite cond cons alt =>
    apply evaluates_to_well_formed_ite
    repeat assumption
    case ih₁ =>
      simp [EvaluatesToWellFormed]
      intros
      apply evaluates_to_well_formed
      repeat assumption
    case ih₂ =>
      simp [EvaluatesToWellFormed]
      intros
      apply evaluates_to_well_formed
      repeat assumption
  case _ lhs rhs => -- and
    apply evaluates_to_well_formed_and
    repeat assumption
  case _ lhs rhs => -- or
    apply evaluates_to_well_formed_or
    repeat assumption
  case _ op expr => -- unary ops
    apply evaluates_to_well_formed_unary
    repeat assumption
  case _ o lhs rhs => -- binary ops
    apply evaluates_to_well_formed_binary
    repeat assumption
  case _ => --get attr
    apply evaluates_to_well_formed_getAttr
    repeat assumption
    simp [EvaluatesToWellFormed]
    intros
    apply evaluates_to_well_formed
    repeat assumption
  case hasAttr expr attr =>
    apply levels_correct_hasAttr
    repeat assumption
  case set members =>
    apply levels_correct_set
    repeat assumption
    intros
    simp [EvaluatesToWellFormed]
    intros
    apply evaluates_to_well_formed
    repeat assumption
  case record attrs =>
    apply evaluates_to_well_formed_record
    repeat assumption
    intros _ e _
    simp [EvaluatesToWellFormed]
    intros
    apply evaluates_to_well_formed
    repeat assumption
  case call xfn args =>
    apply evaluates_to_well_formed_call
    repeat assumption
termination_by (sizeOf x)
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  case _ =>
    rename_i heq _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq]
    simp
    omega
  case _ =>
    rename_i heq _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq]
    simp
    omega
  case _ =>
    rename_i heq _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq]
    simp
    omega
  case _ =>
    rename_i members heq e hin _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq]
    have hstep : sizeOf e < sizeOf members := by
      apply List.in_lists_means_smaller e members
      assumption
    simp
    omega
  case _ =>
    rename_i members heq a hin _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq]
    have step1 : sizeOf e < sizeOf (a,e) := by
      simp
      omega
    have step2 : sizeOf (a,e) < sizeOf members := by
      apply List.in_lists_means_smaller
      assumption
    simp
    omega

end Cedar.Thm

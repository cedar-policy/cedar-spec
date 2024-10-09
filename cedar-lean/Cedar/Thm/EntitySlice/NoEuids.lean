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
import Cedar.Thm.EntitySlice.Completeness

namespace Cedar.Thm
open Cedar.Data
open Cedar.Validation
open Cedar.Spec


mutual
inductive NoEuidTypesIn : CedarType → Prop where
  | int : NoEuidTypesIn .int
  | bool : ∀ bty, NoEuidTypesIn (.bool bty)
  | string : NoEuidTypesIn .string
  | ext : ∀ ext, NoEuidTypesIn (.ext ext)
  | set : ∀ ty,
    NoEuidTypesIn ty →
    NoEuidTypesIn (.set ty)
  | record :  ∀ m,
    (∀ k qty, m.find? k = some qty →
    NoEuidTypesIn qty.getType) →
    NoEuidTypesIn (.record m)

inductive NoEuidTypesInList : List (Attr × QualifiedType) → Prop where
  | empty : NoEuidTypesInList []
  | cons : ∀ k qty rest,
    NoEuidTypesIn qty.getType →
    NoEuidTypesInList rest →
    NoEuidTypesInList ((k,qty)::rest)

inductive NoEuidValues : Value → Prop where
  | int : ∀ i, NoEuidValues (.prim (.int i))
  | bool : ∀ b, NoEuidValues (.prim (.bool b))
  | string : ∀ s, NoEuidValues (.prim (.string s))
  | ext : ∀ extv, NoEuidValues (.ext extv)
  | set : ∀ members,
    NoEuidValuesInSet members →
    NoEuidValues (.set (Set.mk members))
  | record : ∀ m ,
    (∀ k v, m.find? k = some v →
    NoEuidValues v) →
    NoEuidValues (.record m)


inductive NoEuidValuesInSet : List Value → Prop where
  | empty : NoEuidValuesInSet []
  | cons : ∀ v vs,
    NoEuidValues v →
    NoEuidValuesInSet vs →
    NoEuidValuesInSet (v::vs)

end

def NoEuidsInEnv (env : Environment) : Prop :=
  NoEuidTypesIn (.record env.reqty.context)

def NoEuidsInContext (req : Request) : Prop :=
  NoEuidValues (.record req.context)

theorem well_typed_without_euids_list (ty : CedarType) (list : List Value)
  (well_typed : ∀ v, v ∈ list → InstanceOfType v ty)
  (no_euids : NoEuidTypesIn ty)
  (ih : ∀ ty v, v ∈ list → InstanceOfType v ty → NoEuidTypesIn ty → NoEuidValues v)
  :
  NoEuidValuesInSet list
  := by
  cases list <;> constructor
  case _ head tail =>
    apply ih
    simp
    apply well_typed
    simp
    apply no_euids
  case _ head tail =>
    apply well_typed_without_euids_list
    intros v in_tail
    apply well_typed
    simp [in_tail]
    apply no_euids
    intros ty v in_tail wt' noeuids'
    apply ih
    simp [in_tail]
    repeat assumption




theorem well_typed_without_euids_record (values : Map Attr Value) (types : Map Attr QualifiedType)
  (well_typed : InstanceOfType (.record values) (.record types))
  (no_euids : NoEuidTypesIn (.record types))
  (ih : ∀ ty k v, values.find? k = some v → InstanceOfType v ty → NoEuidTypesIn ty → NoEuidValues v) :
  NoEuidValues (.record values)
  := by
  cases no_euids
  rename_i no_euids
  cases well_typed
  rename_i h₁ h₂ h₃


  constructor
  intros k v in_values
  have values_contains : values.contains k = true := by
    refine Map.contains_iff_some_find?.mpr ?_
    exists v


  have ⟨qty, in_types⟩ : ∃ qty, types.find? k = some qty := by
    exact Option.isSome_iff_exists.mp (h₁ k values_contains)

  apply ih qty.getType
  apply in_values
  apply h₂
  apply in_values
  apply in_types
  apply no_euids
  apply in_types





theorem well_typed_without_euids (ty : CedarType) (v : Value)
  (well_typed : InstanceOfType v ty)
  (no_euids : NoEuidTypesIn ty) :
  NoEuidValues v
  := by
  cases v
  case prim p =>
    cases p
    case int _ =>
      apply NoEuidValues.int
    case bool _ =>
      apply NoEuidValues.bool
    case string _ =>
      apply NoEuidValues.string
    case entityUID  =>
      cases well_typed
      cases no_euids
  case set members =>
    cases well_typed
    rename_i ty' well_typed_set
    cases no_euids
    rename_i no_euids
    cases members
    rename_i members
    constructor
    apply well_typed_without_euids_list
    apply well_typed_set
    apply no_euids
    intros
    apply well_typed_without_euids
    repeat assumption
  case record map_values =>
    cases well_typed
    rename_i types h₁ h₂ h₃
    apply well_typed_without_euids_record
    apply InstanceOfType.instance_of_record
    apply h₁
    apply h₂
    apply h₃
    apply no_euids
    intros ty k v in_values is_ty no_euids'
    apply well_typed_without_euids
    repeat assumption
  case _ =>
    constructor
termination_by sizeOf v
decreasing_by
  case _ =>
    simp_wf
    rename Value => v'
    rename List Value => members
    rename_i set eq_value _ set' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rename set = set' => eq
    subst eq
    subst eq_value
    rename set = Set.mk members => set_eq
    subst set_eq
    simp
    have step : sizeOf v' < sizeOf members := by
      apply List.sizeOf_lt_of_mem
      assumption
    omega
  case _ =>
    simp_wf
    rename Map Attr Value => m
    rename Value => v'
    rename _ = m => eq
    subst eq
    rename Map Attr Value => m
    rename v = .record m => eq
    subst eq
    simp
    have step : sizeOf v' < sizeOf m := by
      apply Map.find_means_smaller
      assumption
    omega

theorem no_euids_in_reqty_means_no_euids_in_context : ∀ env request entities l,
  NoEuidsInEnv env →
  RequestAndEntitiesMatchEnvironmentLeveled env request entities l →
  NoEuidsInContext request
  := by
  intros env request entities l no_euids well_typed
  simp [NoEuidsInEnv] at no_euids
  simp [NoEuidsInContext]
  apply well_typed_without_euids
  case _ =>
    simp [RequestAndEntitiesMatchEnvironmentLeveled, InstanceOfRequestTypeLevel] at well_typed
    have h₁ := well_typed.left.right.right.right.right.right.right
    apply h₁
  case _ =>
    apply no_euids

def evalsToEuid (e : Expr) : Prop :=
  ∀ entities request env (c₁ c₂ : Capabilities) ety l euid,
    typeOf e c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂) →
    l ≠ Level.zero →
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1) →
    NoEuidsInEnv env →
    evaluate e request entities = .ok (Value.prim (.entityUID euid)) →
    (euid ∈ [request.principal, request.action, request.resource]) ∧ l = Level.finite 1

def evalsToRecord (e : Expr) : Prop :=
  ∀ entities request env c₁ c₂ rty rv,
    typeOf e c₁ env (.finite 1 == Level.infinite) = .ok (.record rty, c₂) →
    CapabilitiesInvariant c₁ request entities →
    RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1) →
    NoEuidsInEnv env →
    evaluate e request entities = .ok (.record rv) →
    (∀ k ety euid v l,
      rty.find? k = some v →
      v.getType = .entity ety l →
      l ≠ Level.zero →
      rv.find? k = some (.prim (.entityUID euid)) →
      euid ∈ [request.principal, request.action, request.resource] ∧ l = .finite 1
    )

def evalsSpec (e : Expr) : Prop := evalsToEuid (e) ∧ evalsToRecord e


theorem evals_to_euid_lit (p : Prim) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (.lit p) c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (non_zero : l ≠ Level.zero)
  (is_euid : evaluate (.lit p) request entities = .ok (Value.prim (.entityUID euid))) :
  (euid ∈ [request.principal, request.action, request.resource]) ∧ l = Level.finite 1
  := by
  cases p <;> simp [evaluate] at is_euid
  case _ =>
    exfalso
    simp [typeOf, typeOfLit] at well_typed
    split at well_typed
    case _ =>
      simp [ok] at well_typed
      replace ⟨well_typed, _⟩ := well_typed
      replace ⟨_, well_typed⟩ := well_typed
      rw [if_neg] at well_typed
      subst well_typed
      simp [Level.zero] at non_zero
      unfold Not
      intros contra
      cases contra
    case _ =>
      simp [err] at well_typed

theorem evals_to_record_lit (p : Prim) entities request env c₁ c₂ rty rv
    (well_typed : typeOf (.lit p) c₁ env (.finite 1 == Level.infinite) = .ok (.record rty, c₂))
    (caps_inv : CapabilitiesInvariant c₁ request entities)
    (well_typed_req : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
    (no_euids : NoEuidsInEnv env)
    (eval : evaluate (.lit p) request entities = .ok (.record rv)) :
    (∀ k ety euid v l,
      rty.find? k = some v →
      v.getType = .entity ety l →
      l ≠ Level.zero →
      rv.find? k = some (.prim (.entityUID euid)) →
      euid ∈ [request.principal, request.action, request.resource] ∧ l = .finite 1
    )
    := by
    exfalso
    simp [typeOf, typeOfLit] at well_typed
    cases p <;> try simp [ok] at well_typed
    case _ b =>
      cases b <;> simp [ok] at well_typed
    case _ euid =>
      split at well_typed <;> simp [err] at well_typed

theorem eval_spec_lit (p : Prim) :
  evalsSpec (.lit p)
  := by
  simp only [evalsSpec, evalsToEuid]
  constructor
  case _ =>
    intros
    apply evals_to_euid_lit
    repeat assumption
  case _ =>
    intros
    apply evals_to_record_lit
    repeat assumption

theorem evals_to_euid_var (v : Var) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (.var v) c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (req_well_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (is_euid : evaluate (.var v) request entities = .ok (Value.prim (.entityUID euid))) :
  (euid ∈ [request.principal, request.action, request.resource]) ∧ l = .finite 1
  := by
  cases v <;>
  simp [evaluate] at is_euid <;> constructor
  <;> try simp [is_euid]
  all_goals {
    simp [RequestAndEntitiesMatchEnvironmentLeveled] at req_well_typed
    have h := req_well_typed.left
    simp [InstanceOfRequestTypeLevel] at h
    simp [typeOf,typeOfVar, ok] at well_typed
    have h₂ := well_typed.left.right
    simp [h] at h₂
    simp [h₂]
  }

theorem evals_to_record_var (v : Var) entities request env c₁ c₂ rty rv
    (well_typed : typeOf (.var v) c₁ env (.finite 1 == Level.infinite) = .ok (.record rty, c₂))
    (caps_inv : CapabilitiesInvariant c₁ request entities)
    (well_typed_req : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
    (no_euids : NoEuidsInEnv env)
    (eval : evaluate (.var v) request entities = .ok (.record rv)) :
    (∀ k ety euid v l,
      rty.find? k = some v →
      v.getType = .entity ety l →
      l ≠ Level.zero →
      rv.find? k = some (.prim (.entityUID euid)) →
      euid ∈ [request.principal, request.action, request.resource] ∧ l = .finite 1
    )
    := by
    cases v <;> simp [evaluate] at eval
    subst eval
    intros k ety euid v l in_rty type_is_entity level_zero in_rv
    exfalso
    have no_euids_in_context : NoEuidsInContext request := by
      exact
        no_euids_in_reqty_means_no_euids_in_context env request entities (Level.finite 1) no_euids
          well_typed_req
    simp [NoEuidsInContext] at no_euids_in_context
    cases no_euids_in_context
    rename_i no_euids_in_context
    have contra : NoEuidValues (.prim (.entityUID euid)) := by
      apply no_euids_in_context
      apply in_rv
    cases contra

theorem eval_spec_var (v : Var) :
  evalsSpec (.var v) := by
  simp [evalsSpec]
  constructor
  case _ =>
    simp only [evalsToEuid]
    intros
    apply evals_to_euid_var
    repeat assumption
  case _ =>
    simp only [evalsToRecord]
    intros
    apply evals_to_record_var
    repeat assumption


theorem levels_nonzero {l l' : Level}
  (l_not_zero : l ≠ .finite 0)
  (l'_ge : l ≤ l') :
  l' ≠ .finite 0
  := by
  cases l <;> cases l' <;> try simp [Level.finite]
  case _ =>
    cases l'_ge
  case _ n₁ n₂ =>
    have n₁_not_zero : n₁ ≠ 0 := by
      simp [Level.finite] at l_not_zero
      omega
    have step : n₁ ≤ n₂ := by
      exact Level.le_inversion l'_ge
    simp [Level.finite]
    omega


theorem le_one_and_zero (l₁ l₂ : Level)
  (h₁ : l₁ ≠ .finite 0)
  (h₂ : l₂ = .finite 1)
  (h₃ : l₁ ≤ l₂) :
  l₁ = .finite 1 := by
  cases l₁ <;> cases l₂
  case _ =>
    cases h₂
  case _ =>
    cases h₃
  case _ =>
    cases h₂
  case _ n₁ n₂ =>
    simp [Level.finite] at h₂
    subst h₂
    simp [LE.le] at h₃
    cases h₃
    case _ h =>
      subst h
      simp [Level.finite]
    case _ h =>
      cases h
      simp [Level.finite] at h₁
      omega

theorem evals_to_euid_ite (cond cons alt : Expr) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (.ite cond cons alt)  c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (non_zero : l ≠ Level.zero)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (req_well_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (no_euids : NoEuidsInEnv env)
  (is_euid : evaluate (.ite cond cons alt) request entities = .ok (Value.prim (.entityUID euid)))
  (ih₁ : evalsToEuid cons)
  (ih₂ : evalsToEuid alt) :
  (euid ∈ [request.principal, request.action, request.resource]) ∧ l = .finite 1
  := by
  have ⟨bty, c₁', ty₂, c₂', ty₃, c₃, hinv₁, hinv⟩ := type_of_ite_inversion well_typed
  have ⟨gcaps_inv, v_cond, sound₁, sound₂⟩ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ v, EvaluatesToLeveled cond request entities v  ∧ InstanceOfType v (.bool bty) := by
    apply type_of_is_sound_noninfinite
    apply LevelLT.finite₂
    apply 1
    repeat assumption
  cases bty
  case tt =>
    simp at hinv
    cases sound₂
    rename_i bool sound₂
    simp [InstanceOfBoolType] at sound₂
    cases bool
      <;> simp at sound₂
    rcases sound₁ with evals | evals | evals
      <;> simp [evals, evaluate, Result.as]  at is_euid
    case _ =>
      simp [Coe.coe, Value.asBool] at is_euid
      have ⟨hinv₂, hinv₃, _⟩ := hinv
      subst hinv₃
      apply ih₁
      repeat assumption
      apply capability_union_invariant
      assumption
      apply gcaps_inv
      repeat assumption
  case ff =>
    simp at hinv
    cases sound₂
    rename_i bool sound₂
    simp [InstanceOfBoolType] at sound₂
    cases bool
      <;> simp at sound₂
    rcases sound₁ with evals | evals | evals
      <;> simp [evals, evaluate, Result.as, Coe.coe, Value.asBool] at is_euid
    have ⟨hinv₂, hinv₃, _⟩  := hinv
    subst hinv₃
    apply ih₂
    apply hinv₂
    apply non_zero
    repeat assumption
  case anyBool =>
    simp at hinv
    cases sound₂
    rename_i bool sound₂
    cases bool
    case true =>
      rcases sound₁ with evals | evals | evals
      <;> simp [evals, evaluate, Result.as, Coe.coe, Value.asBool] at is_euid
      have ⟨l', step₁⟩ : ∃ l', ty₂ = .entity ety l' := by
        apply lubs_to_entity ty₃ ty₂ ety l
        rw [lub_comm]
        simp [hinv]
      have typed_as_entity := hinv.left
      rw [step₁] at typed_as_entity
      simp only [evalsToEuid] at ih₁
      have step₂ : l ≤ l' := by
        apply lub_to_entity_level_bound ty₃ ety l' l
        rw [lub_comm]
        rw [← step₁]
        simp [hinv]
      have ⟨euid_is_good, lub_level_one⟩ : euid ∈ [request.principal, request.action, request.resource] ∧ (l' = .finite 1) := by
        apply ih₁
        apply typed_as_entity
        apply levels_nonzero
        apply non_zero
        apply step₂
        apply capability_union_invariant
        assumption
        apply gcaps_inv
        repeat assumption
      simp [euid_is_good]
      apply le_one_and_zero
      repeat assumption
    case false =>
      rcases sound₁ with evals | evals | evals
      <;> simp [evals, evaluate, Result.as, Coe.coe, Value.asBool] at is_euid
      have ⟨l', step₁⟩ : ∃ l', ty₃ = .entity ety l' := by
        apply lubs_to_entity ty₂ ty₃ ety l
        simp [hinv]
      have typed_as_entity := hinv.right.left
      rw [step₁] at typed_as_entity
      have step₂ : l ≤ l' := by
        apply lub_to_entity_level_bound ty₂ ety l' l
        rw [← step₁]
        simp [hinv]
      have ⟨euid_is_good, lub_is_one⟩ : euid ∈ [request.principal, request.action, request.resource] ∧ l' = .finite 1 := by
        apply ih₂
        apply typed_as_entity
        apply levels_nonzero
        apply non_zero
        repeat assumption
      simp [euid_is_good]
      apply le_one_and_zero
      repeat assumption



theorem evals_to_record_ite (cond cons alt : Expr) entities request env c₁ c₂ rty rv
    (well_typed : typeOf (.ite cond cons alt) c₁ env (.finite 1 == Level.infinite) = .ok (.record rty, c₂))
    (caps_inv : CapabilitiesInvariant c₁ request entities)
    (well_typed_req : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
    (no_euids : NoEuidsInEnv env)
    (eval : evaluate (.ite cond cons alt) request entities = .ok (.record rv))
    (ih₁ : evalsToRecord cons)
    (ih₂ : evalsToRecord alt) :
    (∀ k ety euid v l,
      rty.find? k = some v →
      v.getType = .entity ety l →
      l ≠ Level.zero →
      rv.find? k = some (.prim (.entityUID euid)) →
      euid ∈ [request.principal, request.action, request.resource] ∧ l = .finite 1
    )
    := by
    have ⟨bty, c₁', ty₂, c₂', ty₃, c₃, type_of_cond, hinv⟩ := type_of_ite_inversion well_typed
    have ⟨gcaps_inv, v_cond, sound₁, sound₂⟩ : GuardedCapabilitiesInvariant cond c₁' request entities ∧ ∃ v, EvaluatesToLeveled cond request entities v  ∧ InstanceOfType v (.bool bty) := by
      apply type_of_is_sound_noninfinite
      apply LevelLT.finite₂
      apply 1
      repeat assumption
    cases bty <;> simp at hinv
    case tt =>
      have ⟨type_of_cons, ty_eq, caps⟩ := hinv
      clear hinv
      subst ty_eq
      subst caps

      rcases sound₁ with eval_cond | eval_cond | eval_cond
      <;> simp [eval_cond, evaluate, Result.as, Coe.coe, Value.asBool] at eval
      cases sound₂
      rename_i bool sound₂
      cases bool <;> simp [InstanceOfBoolType] at sound₂

      intros k ety euid v l in_rty is_entity non_zero' in_rv
      apply ih₁
      apply type_of_cons
      apply capability_union_invariant
      assumption
      apply gcaps_inv
      apply eval_cond
      assumption
      assumption
      simp at eval
      apply eval
      repeat assumption
    case ff =>
      have ⟨type_of_alt, ty_eq, c_eq⟩ := hinv
      subst ty_eq
      subst c_eq
      rcases sound₁ with eval_cond | eval_cond | eval_cond
      <;> simp [evaluate, eval_cond, Result.as, Coe.coe, Value.asBool] at eval
      cases sound₂
      rename_i bool sound₂
      cases bool <;> simp [InstanceOfBoolType] at sound₂
      simp at eval
      intros k ety euid v l in_rty is_entity non_zero' in_rv
      apply ih₂
      repeat assumption
    case anyBool =>
      have ⟨type_of_cons, type_of_alt, ty_eq, c_eq⟩ := hinv
      clear hinv
      subst c_eq
      rcases sound₁ with eval_cond | eval_cond | eval_cond
      <;> simp [eval_cond, evaluate, Result.as, Coe.coe, Value.asBool] at eval
      cases sound₂
      rename Bool => b
      cases b
      case true =>
        simp at eval
        intros k ety euid v l in_rty is_entity non_zero' in_rv
        have ⟨rty₂, is_rty⟩ :  ∃ rty, ty₂ = .record rty := by
          apply lub_record_inversion₁
          rw [lub_comm]
          assumption
        subst is_rty
        have ⟨l', qty', in_rty₂, qty'_is_entity, l_le_l'⟩: ∃ l' qty', rty₂.find? k = some qty' ∧ qty'.getType = .entity ety l' ∧ l ≤ l' := by
          apply lub_record_inversion₂
          rw [lub_comm]
          apply ty_eq
          apply in_rty
          apply is_entity

        simp only [evalsToRecord] at ih₁

        have step : ∀ k ety euid v l,
          rty₂.find? k = some v →
          v.getType = .entity ety l →
          l ≠ Level.zero →
          rv.find? k = some (Value.prim (Prim.entityUID euid)) →
          euid ∈ [request.principal,request.action,request.resource] ∧ l = .finite 1
          := by
          apply ih₁ entities request env (c₁ ∪ c₁') c₂'
          apply type_of_cons
          apply capability_union_invariant
          apply caps_inv
          apply gcaps_inv
          apply eval_cond
          apply well_typed_req
          apply no_euids
          apply eval

        have l'_non_zero : l' ≠ Level.zero := by
          cases l' <;> simp [Level.zero, Level.finite]
          rename_i n'
          cases l
          case _ =>
            cases l_le_l'
          case _ n =>
            simp [Level.zero, Level.finite] at non_zero'
            simp [LE.le] at l_le_l'
            cases l_le_l'
            case _ =>
              omega
            case _ h =>
              cases h
              omega

        have ⟨euid_good, level_one⟩ : euid ∈ [request.principal, request.action, request.resource ] ∧ l' = Level.finite 1 := by
          apply step
          apply in_rty₂
          apply qty'_is_entity
          apply l'_non_zero
          apply in_rv

        simp [euid_good]

        subst level_one
        simp [LE.le] at l_le_l'
        cases l
        case _ =>
          cases l_le_l' <;> rename_i h <;> cases h
        case _ n =>
          cases l_le_l' <;> try assumption
          rename_i h
          cases h
          simp [Level.finite, Level.zero] at non_zero'
          omega
      case false =>
        simp at eval
        intros k ety euid v l in_rty is_entity non_zero' in_rv
        have ⟨rty₃, is_rty⟩ :  ∃ rty, ty₃ = .record rty := by
          apply lub_record_inversion₁
          assumption
        subst is_rty
        have ⟨l', qty', in_rty₂, qty'_is_entity, l_le_l'⟩: ∃ l' qty', rty₃.find? k = some qty' ∧ qty'.getType = .entity ety l' ∧ l ≤ l' := by
          apply lub_record_inversion₂
          apply ty_eq
          apply in_rty
          apply is_entity

        simp only [evalsToRecord] at ih₁

        have step : ∀ k ety euid v l,
          rty₃.find? k = some v →
          v.getType = .entity ety l →
          l ≠ Level.zero →
          rv.find? k = some (Value.prim (Prim.entityUID euid)) →
          euid ∈ [request.principal,request.action,request.resource] ∧ l = .finite 1
          := by
          apply ih₂ entities request env c₁ c₃
          apply type_of_alt
          apply caps_inv
          apply well_typed_req
          apply no_euids
          apply eval

        have l'_non_zero : l' ≠ Level.zero := by
          cases l' <;> simp [Level.zero, Level.finite]
          rename_i n'
          cases l
          case _ =>
            cases l_le_l'
          case _ n =>
            simp [Level.zero, Level.finite] at non_zero'
            simp [LE.le] at l_le_l'
            cases l_le_l'
            case _ =>
              omega
            case _ h =>
              cases h
              omega

        have ⟨euid_good, level_one⟩ : euid ∈ [request.principal, request.action, request.resource ] ∧ l' = Level.finite 1 := by
          apply step
          apply in_rty₂
          apply qty'_is_entity
          apply l'_non_zero
          apply in_rv

        simp [euid_good]

        subst level_one
        simp [LE.le] at l_le_l'
        cases l
        case _ =>
          cases l_le_l' <;> rename_i h <;> cases h
        case _ n =>
          cases l_le_l' <;> try assumption
          rename_i h
          cases h
          simp [Level.finite, Level.zero] at non_zero'
          omega

def eval_spec_ite (cond cons alt : Expr)
  (ih₁ : evalsSpec cons)
  (ih₂ : evalsSpec alt)
  :
  evalsSpec (.ite cond cons alt)
  := by
  simp [evalsSpec] at *
  constructor
  case _ =>
    simp only [evalsToEuid]
    intros
    apply evals_to_euid_ite
    repeat assumption
    all_goals simp [ih₁,ih₂]
  case _ =>
    simp only [evalsToRecord]
    intros
    apply evals_to_record_ite
    repeat assumption
    repeat simp [ih₁, ih₂]
    repeat assumption

theorem and_is_always_bool (lhs rhs : Expr) env (c₁ c₂ : Capabilities) ty :
  typeOf (.and lhs rhs) c₁ env (l == Level.infinite) = .ok (ty, c₂) →
  ∃ bty, ty = .bool bty
  := by
  intros well_typed
  have ⟨bty, _, _, hinv⟩ := type_of_and_inversion well_typed
  cases bty
  case tt =>
    simp at hinv
    replace ⟨bty₂, _, _, hinv⟩ := hinv
    cases bty₂
    case _ =>
      simp [lubBool] at hinv
      exists .anyBool
      simp [hinv]
    case _ =>
      simp [lubBool] at hinv
      exists .tt
      simp [hinv]
    case _ =>
      simp at hinv
      exists .ff
      simp [hinv]
  case ff =>
    simp at hinv
    exists .ff
    simp [hinv]
  case anyBool =>
    simp at hinv
    replace ⟨bty₂, _, _, hinv⟩ := hinv
    cases bty₂
    case _ =>
      simp [lubBool] at hinv
      exists .anyBool
      simp [hinv]
    case _ =>
      simp [lubBool] at hinv
      exists .anyBool
      simp [hinv]
    case _ =>
      simp [lubBool] at hinv
      exists .ff
      simp [hinv]


theorem eval_spec_and (lhs rhs : Expr) :
  evalsSpec (.and lhs rhs)
  := by
  constructor
  case _ =>
    simp [evalsToEuid, evalsToRecord]
    intros entities requuest env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨bty, is_bool⟩ := and_is_always_bool lhs rhs env c₁ c₂ (.entity ety l) well_typed
    simp at is_bool
  case _ =>
    simp [evalsToRecord]
    intros entities requuest env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨bty, is_bool⟩ := and_is_always_bool lhs rhs env c₁ c₂ (.record rty) well_typed
    simp at is_bool

theorem or_is_always_bool (lhs rhs : Expr) env (c₁ c₂ : Capabilities) ty :
  typeOf (.or lhs rhs) c₁ env (l == Level.infinite) = .ok (ty, c₂) →
  ∃ bty, ty = .bool bty
  := by
  intros h
  have ⟨bty, _, _, hinv⟩ := type_of_or_inversion h
  cases bty
  case tt =>
    simp at hinv
    exists .tt
    simp [hinv]
  case ff =>
    simp at hinv
    replace ⟨bty₂, _, hinv⟩ := hinv
    exists bty₂
  case _ =>
    simp at hinv
    replace ⟨bty₂, _, _, hinv⟩ := hinv
    cases bty₂
    case _ =>
      simp at hinv
      exists .anyBool
      simp [hinv]
    case _ =>
      simp at hinv
      exists .tt
      simp [hinv]
    case _ =>
      simp at hinv
      exists .anyBool
      simp [hinv]


theorem eval_spec_or (lhs rhs : Expr) :
  evalsSpec (.or lhs rhs)
  := by
  constructor
  case _ =>
    simp [evalsToEuid, evalsToRecord]
    intros entities requuest env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨bty, is_bool⟩ := or_is_always_bool lhs rhs env c₁ c₂ (.entity ety l) well_typed
    simp at is_bool
  case _ =>
    simp [evalsToRecord]
    intros entities requuest env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨bty, is_bool⟩ := or_is_always_bool lhs rhs env c₁ c₂ (.record rty) well_typed
    simp at is_bool



theorem eval_spec_unop (e : Expr) (o : UnaryOp)  :
  evalsSpec (.unaryApp o e)
  := by
  cases o <;> constructor <;> simp [evalsToEuid, evalsToRecord]
  case _ =>
    intros entities request env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨_, bty, _, hinv, _⟩  := type_of_not_inversion well_typed
    simp at hinv
  case _  =>
    intros entities request env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨_, bty, _, hinv, _⟩ := type_of_not_inversion well_typed
    simp at hinv
  case _ =>
    intros entities request env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨_, hinv, _⟩ := type_of_neg_inversion well_typed
    simp at hinv
  case _ =>
    intros entities request env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨_, hinv, _⟩ := type_of_neg_inversion well_typed
    simp at hinv
  case _ =>
    intros entities request env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨_, hinv, _⟩ := type_of_like_inversion well_typed
    simp at hinv
  case _ =>
    intros entities request env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨_, hinv, _⟩ := type_of_like_inversion well_typed
    simp at hinv
  case _ =>
    intros entities request env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨_, _, _, _, hinv, _⟩ := type_of_is_inversion well_typed
    simp at hinv
  case _ =>
    intros entities request env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨_, _, _, _, hinv, _⟩ := type_of_is_inversion well_typed
    simp at hinv

theorem eval_spec_eq  (lhs rhs : Expr) :
  evalsSpec (.binaryApp .eq lhs rhs)
  := by
  constructor
  case _ =>
    simp [evalsToEuid]
    intros entities request env c₁ c₂ ety l euid well_typed
    exfalso
    have ⟨_, hinv⟩ := type_of_eq_inversion well_typed
    split at hinv
    case _ =>
      split at hinv <;> assumption
    case _ =>
      replace ⟨ty₁, _, ty₂, _, _, _, hinv⟩ := hinv
      cases lub : (ty₁ ⊔ ty₂)
      <;> simp [lub] at hinv
  case _ =>
    simp [evalsToRecord]
    intros entities request env c₁ c₂ rty rv well_typed
    exfalso
    have ⟨_, hinv⟩ := type_of_eq_inversion well_typed
    split at hinv
    case _ =>
      split at hinv <;> assumption
    case _ =>
      replace ⟨ty₁, _, ty₂, _, _, _, hinv⟩ := hinv
      cases lub : (ty₁ ⊔ ty₂)
      <;> simp [lub] at hinv

theorem type_of_mem_is_bool (lhs rhs : Expr) env c₁ c₂ l ty :
  typeOf (.binaryApp .mem lhs rhs) c₁ env (l == Level.infinite) = .ok (ty, c₂) →
  ∃ bty, ty = .bool bty
  := by
  intros h
  simp [typeOf] at h
  cases lhs_ty : typeOf lhs c₁ env (l == .infinite) <;>
  cases rhs_ty : typeOf rhs c₁ env (l == .infinite) <;>
  simp [lhs_ty, rhs_ty, typeOfBinaryApp] at h
  split at h <;> try contradiction
  case _ =>
    simp [typeOfInₑ] at h
    split at h
    <;> simp [ok, err] at h
    rename_i o ty₁ ty₂ ety₁ l₁ ety₂ _ _ _ _ _
    exists (typeOfInₑ.type ety₁  ety₂ lhs rhs env)
    simp [h]
  case _ =>
    simp [typeOfInₛ] at h
    split at h
    <;> simp [ok, err] at h
    rename_i ety₁ _ ety₂ _ _ _ _ _
    exists (typeOfInₛ.type ety₁ ety₂ lhs rhs env)
    simp [h]


theorem eval_spec_mem (lhs rhs : Expr) :
  evalsSpec (.binaryApp .mem lhs rhs)
  := by
  constructor
  case _ =>
    simp only [evalsToEuid]
    intros entities request env c₁ c₂ ety l euid well_typed
    have ⟨bty, is_bty⟩ := type_of_mem_is_bool lhs rhs env c₁ c₂ (.finite 1) (.entity ety l) well_typed
    contradiction
  case _ =>
    simp only [evalsToRecord]
    intros entities request env c₁ c₂ rty rv well_typed
    have ⟨bty, is_bty⟩ := type_of_mem_is_bool lhs rhs env c₁ c₂ (.finite 1) (.record rty) well_typed
    contradiction

theorem eval_spec_int_cmp (o : BinaryOp) (lhs rhs : Expr)
  (is_arith_cmp : o = .less ∨ o = .lessEq) :
  evalsSpec (.binaryApp o lhs rhs)
  := by
  constructor
  case _ =>
    simp [evalsToEuid]
    intros entities request env c₁ c₂ ety l euid well_typed
    have ⟨_, h⟩ := int_cmp_is_bool is_arith_cmp well_typed
    contradiction
  case _ =>
    simp [evalsToRecord]
    intros entities request env c₁ c₂ rty rv well_typed
    have ⟨_, h⟩ := int_cmp_is_bool is_arith_cmp well_typed
    contradiction


theorem eval_spec_int_arith (o : BinaryOp) (lhs rhs : Expr)
  (is_arith : o = .add ∨ o = .sub ∨ o = .mul ) :
  evalsSpec (.binaryApp o lhs rhs)
  := by
  constructor
  case _ =>
    simp [evalsToEuid]
    intros entities request env c₁ c₂ ety l euid well_typed
    have h := int_arith_is_int is_arith well_typed
    contradiction
  case _ =>
    simp [evalsToRecord]
    intros entities request env c₁ c₂ rty rv well_typed
    have h := int_arith_is_int is_arith well_typed
    contradiction

theorem contains_is_bool (lhs rhs : Expr) {env c₁ c₂ l ty}
  (well_typed : typeOf (.binaryApp .contains lhs rhs) c₁ env (l == Level.infinite) = .ok (ty, c₂)) :
  ∃ bty, ty = .bool bty
  := by
  simp [typeOf] at well_typed
  cases lhs_typed : typeOf lhs c₁ env (l == .infinite) <;>
  cases rhs_typed : typeOf rhs c₁ env (l == .infinite) <;>
  simp [lhs_typed, rhs_typed] at well_typed
  rename_i lhs_ty rhs_ty
  simp [typeOfBinaryApp] at well_typed
  split at well_typed <;> try contradiction
  simp [ifLubThenBool] at well_typed
  split at well_typed
  <;> simp [ok, err] at well_typed
  exists .anyBool
  simp [well_typed]



theorem eval_spec_contains (lhs rhs : Expr) :
  evalsSpec (.binaryApp .contains lhs rhs)
  := by
  constructor
  case _ =>
    simp [evalsToEuid]
    intros entities request env c₁ c₂ ety l euid well_typed
    have ⟨bty, is_bty⟩ := contains_is_bool lhs rhs well_typed
    contradiction
  case _ =>
    simp [evalsToRecord]
    intros entities request env c₁ c₂ rty rv well_typed
    have ⟨bty, is_bty⟩ := contains_is_bool lhs rhs well_typed
    contradiction

theorem containsA_is_bool (o : BinaryOp) (lhs rhs : Expr) {env c₁ c₂ l ty}
  (is_containsA : o = .containsAll ∨ o = .containsAny)
  (well_typed : typeOf (.binaryApp o lhs rhs) c₁ env (l == Level.infinite) = .ok (ty, c₂)) :
  ∃ bty, ty = .bool bty
  := by
  simp [typeOf] at well_typed
  cases lhs_typed : typeOf lhs c₁ env (l == .infinite) <;>
  cases rhs_typed : typeOf rhs c₁ env (l == .infinite) <;>
  simp [lhs_typed, rhs_typed] at well_typed
  rename_i lhs_ty rhs_ty
  simp [typeOfBinaryApp] at well_typed
  split at well_typed <;> try contradiction
  all_goals {
    simp [ifLubThenBool] at well_typed
    split at well_typed <;> simp [ok,err] at well_typed
    exists .anyBool
    simp [well_typed]
  }


theorem eval_spec_containsA (o : BinaryOp) (lhs rhs : Expr)
  (is_containsA : o = .containsAll ∨ o = .containsAny) :
  evalsSpec (.binaryApp o lhs rhs)
  := by
  sorry

theorem eval_spec_binop (o : BinaryOp) (lhs rhs : Expr) :
  evalsSpec (.binaryApp o lhs rhs)
  := by
  cases o
  case _ =>
    apply eval_spec_eq
  case _ =>
    apply eval_spec_mem
  case _ =>
    apply eval_spec_int_cmp
    simp
  case _ =>
    apply eval_spec_int_cmp
    simp
  case _ =>
    apply eval_spec_int_arith
    simp
  case _ =>
    apply eval_spec_int_arith
    simp
  case _ =>
    apply eval_spec_int_arith
    simp
  case _ =>
    apply eval_spec_contains
  case _ =>
    apply eval_spec_containsA
    simp
  case _ =>
    apply eval_spec_containsA
    simp


theorem sub1_lemma ty ety l
  (h : setLevel (Level.finite 1).sub1 ty = CedarType.entity ety l)
  :
  l = .finite 0
  := by
  simp [Level.sub1, Level.finite] at h
  cases ty <;> simp [setLevel] at h
  simp [Level.finite, h]

theorem gt_implies_ne : ∀  (l₁ l₂  : Level),
  l₁ > l₂  → l₁ ≠ l₂
  := by
  intros l₁ l₂ h
  cases l₁ <;> cases l₂ <;> cases h <;> simp
  omega

theorem evals_to_euid_getAttr (attr : Attr) (e : Expr) (ih : evalsSpec e) :
  evalsToEuid (.getAttr e attr)
  := by
  have lt : .finite 1 < Level.infinite := by
    apply LevelLT.finite₂
  simp only [evalsToEuid]
  intros entities request env c₁ c₂ ety l euid well_typed non_zero caps_inv req_ty no_euids evals_to_euid
  have ⟨c₂_eq, c₁', hinv⟩ := type_of_getAttr_inversion_levels well_typed
  subst c₂_eq
  cases hinv
  case _ hinv =>
    replace ⟨ety', l₂, hinv, l₂_gt_zero⟩ := hinv
    have ⟨gcaps_inv, euid_val, e_evals, e_well_typed⟩ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety' l₂) := by
      apply type_of_is_sound_noninfinite
      apply lt
      apply caps_inv
      apply req_ty
      apply hinv
    cases e_well_typed
    rename_i euid' e_well_typed
    rcases e_evals with e_evals | e_evals | e_evals
    <;> simp [e_evals, evaluate, Result.as, getAttr] at evals_to_euid
    cases find_attrs : attrsOf (.prim (.entityUID euid')) entities.attrs
    <;> simp [find_attrs] at evals_to_euid
    rename_i entity_attrs
    have ⟨is_scope_var, level_one⟩ : euid' ∈ [request.principal, request.action, request.resource] ∧ l₂ = Level.finite 1 := by
      have euid := ih.left
      apply euid
      apply hinv
      apply gt_implies_ne
      simp only [Level.zero]
      apply l₂_gt_zero
      apply caps_inv
      apply req_ty
      apply no_euids
      apply e_evals
    simp [typeOf, hinv, typeOfGetAttr, find_attrs, level_one] at well_typed
    rw [if_pos] at well_typed
    cases find_attr_type : env.ets.attrs? ety'
    <;> simp [find_attr_type, err, ok] at well_typed
    rename_i rty
    cases getAttr : getAttrInRecord (.entity ety' (.finite 1)) rty e attr c₁
    <;> simp [getAttr] at well_typed
    rename_i pair
    have is_zero : l = Level.finite 0 := by
      apply sub1_lemma
      apply well_typed.left
    exfalso
    simp [Level.zero] at non_zero
    apply non_zero
    apply is_zero
    apply LevelLT.finite₁
    omega
  case _ hinv =>
    replace ⟨rty, hinv⟩ := hinv
    have ⟨gcaps_sound, v, e_evals_to, e_has_type⟩ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.record rty) := by
      apply type_of_is_sound_noninfinite
      repeat assumption
    cases e_has_type
    rename_i rv h₁ h₂ h₃
    have to_record := ih.right
    simp only [evalsToRecord] at to_record
    simp [evaluate] at evals_to_euid
    rcases e_evals_to with e_evals_to | e_evals_to | e_evals_to
    <;> simp [e_evals_to, getAttr, attrsOf] at evals_to_euid
    cases attrExists : rv.findOrErr attr Error.attrDoesNotExist
    <;> simp [attrExists] at evals_to_euid
    rename_i v

    simp [typeOf, hinv, typeOfGetAttr, getAttrInRecord] at well_typed
    cases type_find : rty.find? attr
    <;> simp [type_find, err, ok] at well_typed
    rename_i qty
    have qty_is_ety : qty.getType = .entity ety l := by
      split at well_typed <;> try contradiction
      case _ =>
        rename_i eq
        simp at eq
        simp [Qualified.getType, eq]
        simp [Except.ok] at well_typed
        assumption
      case _ =>
        rename_i eq
        simp at eq
        simp [eq, Qualified.getType, eq]
        split at well_typed <;> try contradiction
        simp [Except.ok] at well_typed
        assumption
    apply to_record entities request env c₁ c₁' rty rv
    apply hinv
    apply caps_inv
    apply req_ty
    apply no_euids
    apply e_evals_to
    apply type_find
    apply qty_is_ety
    apply non_zero
    subst evals_to_euid
    exact Map.findOrErr_ok_iff_find?_some.mp attrExists


theorem getAttr_some_implies_in_kvs (attr : Attr) (euid : EntityUID) (attrs : Map Attr Value) (entities : Entities) (v : Value)
  (is_attrs : entities.attrs euid = .ok attrs)
  (got_attr : getAttr (.prim (.entityUID euid)) attr entities = .ok v) :
  (attr, v) ∈ attrs.kvs
  := by
  simp [getAttr, attrsOf, Entities.attrs] at got_attr
  cases find_attrs : entities.findOrErr euid Error.entityDoesNotExist
  <;> simp [find_attrs] at got_attr
  rename_i edata
  cases find_attr : edata.attrs.findOrErr attr Error.attrDoesNotExist
  <;> simp [find_attr] at got_attr
  subst got_attr
  rename_i v
  simp [Entities.attrs, find_attrs] at is_attrs
  subst is_attrs
  exact Map.findOrErr_ok_implies_in_kvs find_attr


theorem evals_to_record_getAttr (attr : Attr) (e : Expr) (ih : evalsSpec e) :
  evalsToRecord (.getAttr e attr)
  := by
  simp [evalsToRecord]
  intros entities request env c₁ c₂ rty rv well_typed caps_inv req_ty no_euids evals_to_record
  have lt : Level.finite 1 < Level.infinite := by
    apply LevelLT.finite₂
  have ⟨c₂_eq, c₁', hinv⟩ := type_of_getAttr_inversion_levels well_typed
  subst c₂_eq
  cases hinv
  case _ hinv =>
    replace ⟨ety, l₂, hinv, level⟩ := hinv
    have h := ih.left
    have ⟨gcaps, v_euid, evals, instance_of⟩ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety l₂) := by
      apply type_of_is_sound_noninfinite
      repeat assumption
    rcases evals with evals | evals | evals
    <;> simp [evals, evaluate] at evals_to_record
    cases instance_of
    rename_i euid instance_of
    have ⟨is_scope_var, is_level_one⟩ : euid ∈ [request.principal, request.action, request.resource] ∧ l₂ = Level.finite 1 := by
      apply h
      repeat assumption
      exact gt_implies_ne l₂ Level.zero level
      repeat assumption
    subst is_level_one
    simp at is_scope_var
    rcases is_scope_var with is_principal | is_action | is_resource
    case _ =>
      subst is_principal
      have wf := req_ty.right.right.right.left
      have req_wt := req_ty.left.right.left
      rw [req_wt] at wf
      cases wf
      rename_i attrs h₁ h₂ h₃ h₄
      have step : entities ⊢ (.record rv) : (.int) := by
        apply h₁
        exact
          getAttr_some_implies_in_kvs attr request.principal attrs entities (Value.record rv) h₂
            evals_to_record











      sorry
    case _ =>
      sorry
    case _ =>
      sorry
  case _ =>
    sorry





theorem eval_spec_getAttr (attr : Attr) (e : Expr) (ih : evalsSpec e) :
  evalsSpec (.getAttr e attr)
  := by
  constructor
  case _ =>
    apply evals_to_euid_getAttr
    apply ih
  case _ =>
    sorry

theorem evals_to_euid_getAttr (attr : Attr) (e : Expr) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (e.getAttr attr) c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (non_zero : l ≠ Level.zero)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (req_well_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (no_euids : NoEuidsInEnv env)
  (is_euid : evaluate (e.getAttr attr) request entities = .ok (Value.prim (.entityUID euid)))
  (ih : evalsToEuid e)
  :
  (euid ∈ [request.principal, request.action, request.resource]) ∧ l = Level.finite 1
  := by
  have hinv := type_of_getAttr_inversion_levels well_typed
  replace ⟨hinv₁, c₁', hinv⟩ := hinv
  have lt : (.finite 1 < Level.infinite) := by
    apply LevelLT.finite₂
  cases hinv
  case _ hinv =>
    replace ⟨ety', l₂, hinv₂, hinv⟩ := hinv
    have ⟨gcaps, v, evals, instance_of⟩ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.entity ety' l₂) := by
      apply type_of_is_sound_noninfinite
      repeat assumption
    cases instance_of
    rename_i euid' inst
    rcases evals with evals | evals | evals
    <;> simp [evals, evaluate] at is_euid
    have ⟨euid_good, level_one⟩ : euid' ∈ [request.principal, request.action, request.resource] ∧ l₂ = .finite 1 := by
      apply ih
      apply hinv₂
      simp
      unfold Not
      intros contra
      subst contra
      cases hinv
      omega
      repeat assumption
    subst level_one
    simp [typeOf, hinv₂, typeOfGetAttr] at well_typed
    rw [if_pos] at well_typed
    cases find : env.ets.attrs? ety'
    <;> simp [find, err] at well_typed
    rename_i rty
    cases getAttr : (getAttrInRecord (.entity ety' (.finite 1)) rty e attr c₁)
    <;> simp [getAttr] at well_typed
    rename_i pair
    have ⟨ty',c'⟩ := pair
    simp at well_typed
    exfalso
    have contra : l = Level.finite 0 := by
      apply sub1_lemma
      apply well_typed.left
    subst contra
    simp [Level.finite, Level.zero] at non_zero
    apply LevelLT.finite₁
    omega
  case _ hinv =>
    replace ⟨rty, hinv⟩ := hinv
    have ⟨gcaps, v, evals, instance_of⟩ : GuardedCapabilitiesInvariant e c₁' request entities ∧ ∃ v, EvaluatesToLeveled e request entities v ∧ InstanceOfType v (.record rty) := by
      apply type_of_is_sound_noninfinite
      repeat assumption
    cases instance_of
    rename_i rv h₁ h₂ h₃
    rcases evals with evals | evals | evals
    <;> simp [evals,evaluate] at is_euid
    have no_euids_in_record : NoEuidValues (.record rv) := by
      apply evals_to_record
      apply hinv
      repeat assumption

    sorry


theorem eval_spec (e : Expr) :
  evalsSpec e
  := by
  cases e
  case lit p =>
    exact eval_spec_lit p
  case var v =>
    exact eval_spec_var v
  case ite cond cons alt =>
    refine eval_spec_ite cond cons alt ?ih₁ ?ih₂
    repeat apply eval_spec
  case and lhs rhs =>
    exact eval_spec_and lhs rhs
  case or lhs rhs =>
    exact eval_spec_or lhs rhs
  case unaryApp o e =>
    exact eval_spec_unop e o
  case binaryApp o lhs rhs =>
    exact eval_spec_binop o lhs rhs
  case getAttr e attr =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry

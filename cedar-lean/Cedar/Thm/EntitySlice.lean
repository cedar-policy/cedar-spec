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

theorem append_membership {α : Type} (l₁ : List α) (l₂ : List α) (a : α) :
  a ∈ (l₁ ++ l₂) →
  a ∈ l₁ ∨ a ∈ l₂
  := by
  intros in_append
  cases l₁
  case nil =>
    simp [List.append] at in_append
    simp [in_append]
  case cons head tail =>
    cases in_append
    case head =>
      simp
    case tail in_tail =>
      have step : a ∈ tail ∨ a ∈ l₂ := by
        apply append_membership
        apply in_tail
      rcases step with step | step
        <;> simp [step]

theorem in_joins_in_member {α : Type} (l : List (List α)) (a : α)
  (in_lists : a ∈ l.join) :
  ∃ l',
    l' ∈ l ∧ a ∈ l'
  := by
  cases l
  case nil =>
    simp [List.join] at in_lists
  case cons head tail =>
    rw [List.join_cons] at in_lists
    have step : a ∈ head ∨ a ∈ tail.join := by
      apply append_membership
      assumption
    rcases step with step | step
    case _ =>
      exists head
      constructor
      · simp
      · apply step
    case _ =>
      have step₂ : ∃ l', l' ∈ tail ∧ a ∈ l' := by
        apply in_joins_in_member
        assumption
      replace ⟨l', step₂⟩ := step₂
      exists l'
      constructor <;> try simp
      repeat simp [step₂]

theorem in_joins_in_member' {α : Type} (head_list : List α) (tail_list : List (List α)) (a : α)
  (in_lists : a ∈ (head_list :: tail_list).join) :
  ∃ target_list,
    a ∈ target_list ∧
    (
      target_list = head_list ∨ target_list ∈ tail_list
    )
  := by
  have h := in_joins_in_member (head_list :: tail_list) a in_lists
  replace ⟨target, h₁, h₂⟩ := h
  clear h
  exists target
  simp [h₂]
  cases h₁
  case head =>
    simp
  case tail in_tail =>
    apply Or.inr
    apply in_tail

def in_list_in_join {α : Type} (list : List α) (lists : List (List α)) (a : α)
  (in_list : a ∈ list)
  (in_lists : list ∈ lists) :
  a ∈ lists.join
  := by
  exact List.mem_join_of_mem in_lists in_list

def join_cons {α : Type} (list : List α) (lists : List (List α)) (a : α) :
  a ∈ lists.join →
  a ∈ (list :: lists).join
  := by
  intros h
  simp [List.join]
  apply Or.inr
  simp at h
  apply h


def SimpleSliceContxtSoundness (v : Value) : Prop :=
  ∀ euid edata (entities slice : Entities) (list : List (EntityUID × EntityData)),
    v.findEuids entities = some list →
    slice.find? euid = some edata →
    (euid, edata) ∈ list →
    slice.find? euid = entities.find? euid

theorem simpleSlice_set (members : List Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (list : List (List (EntityUID × EntityData)))
  (h : members.mapM (λ value => value.findEuids entities) = some list)
  (in_slice : slice.find? euid = some edata)
  (in_list : (euid, edata) ∈ list.join)
  (ih : ∀ v, v ∈ members → SimpleSliceContxtSoundness v) :
  slice.find? euid = entities.find? euid
  := by
  cases members
  case nil =>
    simp [List.mapM, List.mapM.loop] at h
    subst h
    simp [List.join] at in_list
  case cons head tail =>
    rw [List.mapM_cons] at h
    cases find_in_head : head.findEuids entities
    <;> simp [find_in_head] at h
    cases find_in_tail : tail.mapM (λ value => value.findEuids entities)
    <;> simp [find_in_tail] at h
    rename_i head_list tail_list
    have step : ∃ target_list,
      (euid, edata) ∈ target_list ∧
      (
        target_list = head_list ∨ target_list ∈ tail_list
      ) := by
      apply in_joins_in_member'
      rw [← h] at in_list
      apply in_list
    replace ⟨target_list, step₁, step₂⟩ := step
    clear step
    subst h
    cases step₂
    case _ step₂ =>
      subst step₂
      apply ih
      simp
      apply Or.inl
      rfl
      apply find_in_head
      apply in_slice
      apply step₁
    case _ step₂ =>
      apply simpleSlice_set
      apply find_in_tail
      apply in_slice
      apply in_list_in_join
      apply step₁
      apply step₂
      intros v in_tail
      apply ih
      simp [in_tail]


theorem simpleSlice_context_record (kvs : Map Attr  Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities)
  (h : (Value.record kvs).findEuids entities = some list)
  (in_slice : slice.find? euid = some edata)
  (in_list : (euid, edata) ∈ list)
  (ih : ∀ v, v ∈ kvs.values → SimpleSliceContxtSoundness v) :
  slice.find? euid = entities.find? euid
  := by
  simp [Value.findEuids, List.mapM₁, List.attach, List.attachWith] at h
  simp [List.mapM_pmap_subtype (λ (value : Value) => value.findEuids entities)] at h
  cases mapping : kvs.values.mapM (λ value => value.findEuids entities)
  <;> simp [mapping] at h
  rename_i llist
  apply simpleSlice_set kvs.values
  apply mapping
  apply in_slice
  rw [h]
  apply in_list
  apply ih

theorem simpleSlice_context_value (v : Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (context_entities : List (EntityUID × EntityData))
  (context_entities_def : v.findEuids entities = some context_entities)
  (in_slice : slice.find? euid = some edata)
  (in_context_entities : (euid, edata) ∈ context_entities) :
  slice.find? euid = entities.find? euid
  := by
  cases v
  case prim p =>
    cases p
    case bool b =>
      exfalso
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      subst context_entities_def
      simp at in_context_entities
    case int i =>
      exfalso
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      subst context_entities_def
      simp at in_context_entities
    case string s =>
      exfalso
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      subst context_entities_def
      simp at in_context_entities
    case entityUID euid' =>
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      cases find : entities.find? euid'
        <;> simp [find] at context_entities_def
      subst context_entities_def
      cases in_context_entities
      case tail h =>
        cases h
      case head =>
        simp [find, in_slice]
  case set members =>
    simp [Value.findEuids] at context_entities_def
    simp [List.mapM₁, List.attach, List.attachWith] at context_entities_def
    simp [List.mapM_pmap_subtype (λ (value : Value) => value.findEuids entities )] at context_entities_def
    cases mapping : members.toList.mapM (λ value => value.findEuids entities)
    <;> simp [mapping] at context_entities_def
    rename_i list_of_lists
    apply simpleSlice_set
    apply mapping
    apply in_slice
    rw [← context_entities_def] at in_context_entities
    apply in_context_entities
    intros v in_values
    apply simpleSlice_context_value
  case record =>
    apply simpleSlice_context_record
    repeat assumption
    rename_i kvs
    intros v in_map
    apply simpleSlice_context_value
  case ext =>
    simp [Value.findEuids] at context_entities_def
    subst context_entities_def
    simp at in_context_entities
termination_by (sizeOf v)
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ =>
    rename Value => v'
    rename Set Value => set
    rename v = Value.set set => eq
    rw [eq]
    have step₁ : sizeOf v' < sizeOf set := by
      apply Set.sizeOf_lt_of_mem
      exact in_values
    simp
    omega
  case _ =>
    rename Value => v'
    rename Map Attr Value => map
    rename v = Value.record map => eq
    rw [eq]
    have step : sizeOf v' < sizeOf map := by
      exact Map.sizeOf_lt_of_in_values in_map
    simp
    omega



theorem simpleSlice_context (req : Request) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (context_entities : List (EntityUID × EntityData))
  (context_entities_def : loadEuids req.context entities = some context_entities)
  (in_slice : slice.find? euid = some edata)
  (in_context_entiites : (euid, edata) ∈ context_entities) :
  slice.find? euid = entities.find? euid
  := by
  simp [loadEuids] at context_entities_def
  apply simpleSlice_context_value
  apply context_entities_def
  apply in_slice
  apply in_context_entiites



theorem simpleSlice_is_subslice (req : Request) (entities slice : Entities)
  (slice_def : simpleSlice req entities = some slice) :
  subslice slice entities
  := by
  simp [subslice]
  intros euid edata in_slice
  simp [simpleSlice] at slice_def
  cases find_principal : entities.find? req.principal
    <;> simp [find_principal] at slice_def
  cases find_action : entities.find? req.action
    <;> simp [find_action] at slice_def
  cases find_resource : entities.find? req.resource
    <;> simp [find_resource] at slice_def
  rename_i principal action resource
  cases find_entities_in_context : (loadEuids req.context entities)
    <;> simp [find_entities_in_context] at slice_def
  rename_i context_entities
  have location : (euid, edata) ∈ (req.principal, principal) :: (req.action, action) :: (req.resource, resource) :: context_entities := by
    have in_kvs : (euid, edata) ∈ slice.kvs := by
      exact Map.find_means_mem in_slice
    apply Map.make_mem_list_mem
    rw [slice_def]
    assumption
  cases location
  -- It's the principal
  simp [in_slice, find_principal]
  rename_i location
  cases location
  -- It's the action
  simp [in_slice, find_action]
  rename_i location
  cases location
  -- It's the resource
  simp [in_slice, find_resource]
  rename_i location

  apply simpleSlice_context
  repeat assumption


theorem simpleSlice_respects_entity_schema (req : Request) (entities slice : Entities) (env : Environment)
  (h₁ : simpleSlice req entities = some slice)
  (h₂ : InstanceOfEntitySchema entities env.ets) :
  InstanceOfEntitySchema slice env.ets
  := by
  simp [InstanceOfEntitySchema]
  have is_subslice : subslice slice entities  := by
    apply simpleSlice_is_subslice
    assumption
  intros uid edata in_slice
  have in_full_store : edata = Map.find? entities uid := by
    rw [← in_slice]
    apply is_subslice
    apply in_slice
  apply h₂
  simp [in_full_store]





theorem simpleSlice_complete (euid : EntityUID) (request : Request) (entities slice : Entities)
  (slice_def : simpleSlice request entities = some slice )
  (euid_correct : euid = request.principal ∨ euid = request.action ∨ euid = request.resource ) :
  euid ∈ slice.keys
  := by
  simp [simpleSlice] at slice_def
  cases find_principal : Map.find? entities request.principal
    <;> simp [find_principal] at slice_def
  cases find_action : Map.find? entities request.action
    <;> simp [find_action] at slice_def
  cases find_resource : Map.find? entities request.resource
    <;> simp [find_resource] at slice_def
  cases find_context : loadEuids request.context entities
    <;> simp [find_context] at slice_def
  rename_i principal action resource context

  rw [← slice_def]
  rcases euid_correct with is_principal | is_action | is_resource
  case _ =>
    subst is_principal
    apply Map.in_constructor_in_keys
    simp
    apply Or.inl
    rfl
  case _ =>
    subst is_action
    apply Map.in_constructor_in_keys
    simp
    inrl
    rfl
  case _ =>
    subst is_resource
    apply Map.in_constructor_in_keys
    simp
    inrrl
    rfl

mutual
inductive NoEuidTypesIn : CedarType → Prop where
  | int : NoEuidTypesIn .int
  | bool : ∀ bty, NoEuidTypesIn (.bool bty)
  | string : NoEuidTypesIn .string
  | ext : ∀ ext, NoEuidTypesIn (.ext ext)
  | set : ∀ ty,
    NoEuidTypesIn ty →
    NoEuidTypesIn (.set ty)
  | record :  ∀ kvs,
    NoEuidTypesInList kvs →
    NoEuidTypesIn (.record (Map.mk kvs))

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
  | record : ∀ kvs,
    NoEuidValuesInRecord kvs →
    NoEuidValues (.record (Map.mk kvs))


inductive NoEuidValuesInSet : List Value → Prop where
  | empty : NoEuidValuesInSet []
  | cons : ∀ v vs,
    NoEuidValues v →
    NoEuidValuesInSet vs →
    NoEuidValuesInSet (v::vs)

inductive NoEuidValuesInRecord : List (Attr × Value) → Prop where
  | empty : NoEuidValuesInRecord []
  | cons : ∀ k v kvs,
    NoEuidValues v →
    NoEuidValuesInRecord kvs →
    NoEuidValuesInRecord ((k,v)::kvs)

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





theorem well_typed_without_euids_record' (map_values : List (Attr × Value)) (map_types : List (Attr × QualifiedType))
  (well_typed : ∀ k v, (k,v) ∈  map_values → ∃ ty, (k, ty) ∈ map_types ∧ InstanceOfType v ty.getType ∧ NoEuidTypesIn ty.getType )
  (ih : ∀ ty k v, (k,v) ∈ map_values → InstanceOfType v ty → NoEuidTypesIn ty → NoEuidValues v)
  :
  NoEuidValuesInRecord map_values
  := by
  induction map_values
  case nil =>
    constructor
  case cons head tail local_ih =>
    have ⟨key, value⟩ := head
    have ⟨ty, in_record_type, instance_of, no_euids⟩  := well_typed key value (by simp)
    constructor
    case _ =>
      apply ih
      simp
      apply Or.inl
      rfl
      apply instance_of
      apply no_euids
    case _ =>
      apply local_ih
      intros k v in_tail
      have ⟨ty, step⟩ : ∃ ty, (k, ty) ∈ map_types ∧ InstanceOfType v ty.getType ∧ NoEuidTypesIn ty.getType := by
        apply well_typed
        simp [in_tail]
      exists ty
      intros ty k v in_tail instance_of no_euids
      apply ih
      simp
      apply Or.inr
      apply in_tail
      apply instance_of
      apply no_euids




theorem well_typed_without_euids_record (map_values : List (Attr × Value)) (map_types : List (Attr × QualifiedType))
  (well_typed : InstanceOfType  (.record (.mk map_values)) (.record (.mk map_types)))
  (no_euids_in_type : NoEuidTypesInList map_types)
  (ih : ∀ ty k v, (k,v) ∈ map_values → InstanceOfType v ty → NoEuidTypesIn ty → NoEuidValues v)
  :
  NoEuidValuesInRecord map_values
  := by
  cases well_typed
  rename_i h₁ h₂ h₃
  apply well_typed_without_euids_record'
  intros k v in_values
  have ⟨ty, in_type⟩ : ∃ ty, (k,ty) ∈ map_types := by
    have step : (Map.mk map_types).contains k = true := by
      apply h₁
      rw [Map.contains_iff_some_find?]
      apply Map.in_mk_in_map
      apply in_values
    apply Map.in_list_if_contains
    apply step
  exists ty
  constructor
  case _ =>
    apply in_type
  case _ =>
    constructor
    case _ =>
      apply h₂
      apply (Map.in_list_iff_find?_some ?_).mp
      simp [Map.kvs]

      sorry
    case _ =>
      sorry






  sorry



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

    cases map_values
    rename_i map_values
    constructor
    cases well_typed
    rename_i rty h₁ h₂ h₃
    cases no_euids
    rename_i map_types h₄
    apply well_typed_without_euids_record
    repeat assumption
    apply InstanceOfType.instance_of_record
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
    (euid ∈ [request.principal, request.action, request.resource])

theorem evals_to_euid_lit (p : Prim) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (.lit p) c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (non_zero : l ≠ Level.zero)
  (is_euid : evaluate (.lit p) request entities = .ok (Value.prim (.entityUID euid))) :
  (euid ∈ [request.principal, request.action, request.resource])
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

theorem evals_to_euid_var (v : Var) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (.var v) c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (is_euid : evaluate (.var v) request entities = .ok (Value.prim (.entityUID euid))) :
  (euid ∈ [request.principal, request.action, request.resource])
  := by
  cases v
    <;>
    simp [evaluate] at is_euid
    <;> (
    subst is_euid
    simp
    )

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



theorem evals_to_euid_ite (cond cons alt : Expr) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf (.ite cond cons alt)  c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (non_zero : l ≠ Level.zero)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (req_well_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (no_euids : NoEuidsInEnv env)
  (is_euid : evaluate (.ite cond cons alt) request entities = .ok (Value.prim (.entityUID euid)))
  (ih₁ : evalsToEuid cons)
  (ih₂ : evalsToEuid alt) :
  (euid ∈ [request.principal, request.action, request.resource])
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
      apply ih₁
      apply typed_as_entity
      have step₂ : l ≤ l' := by
        apply lub_to_entity_level_bound ty₃ ety l' l
        rw [lub_comm]
        rw [← step₁]
        simp [hinv]
      apply levels_nonzero
      apply non_zero
      apply step₂
      apply capability_union_invariant
      assumption
      apply gcaps_inv
      repeat assumption
    case false =>
      rcases sound₁ with evals | evals | evals
      <;> simp [evals, evaluate, Result.as, Coe.coe, Value.asBool] at is_euid
      have ⟨l', step₁⟩ : ∃ l', ty₃ = .entity ety l' := by
        apply lubs_to_entity ty₂ ty₃ ety l
        simp [hinv]
      have typed_as_entity := hinv.right.left
      rw [step₁] at typed_as_entity
      apply ih₂
      apply typed_as_entity
      have step₂ : l ≤ l' := by
        apply lub_to_entity_level_bound ty₂ ety l' l
        rw [← step₁]
        simp [hinv]
      apply levels_nonzero
      apply non_zero
      repeat assumption




theorem evals_to_euid (e : Expr) entities request env c₁ c₂ ety l euid
  (well_typed : typeOf e c₁ env (.finite 1 == Level.infinite) = .ok (.entity ety l, c₂))
  (non_zero : l ≠ Level.zero)
  (caps_inv : CapabilitiesInvariant c₁ request entities)
  (req_well_typed : RequestAndEntitiesMatchEnvironmentLeveled env request entities (.finite 1))
  (no_euids : NoEuidsInEnv env)
  (is_euid : evaluate e request entities = .ok (Value.prim (.entityUID euid))) :
  (euid ∈ [request.principal, request.action, request.resource])
  := by
  cases e
  case lit p =>
    apply evals_to_euid_lit
    repeat assumption
  case var v =>
    apply evals_to_euid_var
    repeat assumption
  case ite cond cons alt =>
    apply evals_to_euid_ite
    repeat assumption
    all_goals {
      unfold evalsToEuid
      intros
      apply evals_to_euid
      repeat assumption
    }
  case and lhs rhs =>

    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry




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
  (h : noEuidsInEnv env)
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

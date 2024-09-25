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



theorem simpleSlice_context_value (v : Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (context_entities : List (EntityUID × EntityData))
  (context_entities_def : v.findEuids entities = some context_entities)
  (in_slice : slice.find? euid = some edata)
  (in_context_entiites : (euid, edata) ∈ context_entities) :
  slice.find? euid = entities.find? euid
  := by
  cases v
  case prim p =>
    cases p <;> try
      (
      simp [Value.findEuids, Prim.findEuids] at context_entities_def ;
      subst context_entities_def
      cases in_context_entiites
      )
    case entityUID euid' =>
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      cases find : entities.find? euid'
        <;> simp [find] at context_entities_def
      subst context_entities_def
      cases in_context_entiites
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
    rw [← context_entities_def] at in_context_entiites
    apply in_context_entiites
    intros v in_values
    apply simpleSlice_context_value
  case record =>
    sorry
  case ext =>
    sorry

theorem simpleSlice_context (req : Request) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (context_entities : List (EntityUID × EntityData))
  (context_entities_def : loadEuids req.context entities = some context_entities)
  (in_slice : slice.find? euid = some edata)
  (in_context_entiites : (euid, edata) ∈ context_entities) :
  slice.find? euid = entities.find? euid
  := by
  simp [loadEuids] at context_entities_def



  sorry


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









theorem simpleSlice_is_subslice (req : Request) (entities slice : Entities)
  (h : simpleSlice req entities = some slice) :
  subslice slice entities
  := by
  simp [subslice]
  intros euid edata h'
  simp [simpleSlice] at h
  cases find_principal : entities.find? req.principal
    <;> simp [find_principal] at h
  cases find_action : entities.find? req.action
    <;> simp [find_action] at h
  cases find_resource : entities.find? req.resource
    <;> simp [find_resource] at h
  rename_i principal action resource
  have location : (euid, edata) ∈ [(req.principal, principal),  (req.action, action),  (req.resource, resource)] := by
    have in_map : (euid, edata) ∈ slice.kvs := by
      exact Map.find_means_mem h'
    apply Map.make_mem_list_mem
    rw [h]
    assumption
  rcases location with location | location
  case _ =>
    rw [h']
    rw [find_principal]
  rename_i location
  rcases location with location | location
  case _ =>
    rw [h']
    rw [find_action]
  rename_i location
  rcases location with location | location
  case _ =>
    rw [h']
    rw [find_resource]
  rename_i location
  cases location


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
    case _ =>
      simp [simpleSlice_soundness]
      intros
      apply simpleSlice_is_sound
      repeat assumption
    case _ =>
      simp [simpleSlice_soundness]
      intros
      apply simpleSlice_is_sound
      repeat assumption
    case _ =>
      simp [simpleSlice_soundness]
      intros
      apply simpleSlice_is_sound
      repeat assumption
  case and lhs rhs =>
    sorry
  case or lhs rhs =>
    sorry
  case getAttr expr attr =>
    sorry


  sorry

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

module

public import Cedar.Thm.Validation.Relational.EnvironmentValidation
public import Cedar.Thm.Validation.Relational.Policy
public import Cedar.Validation.Relational.Request
import Batteries.Data.List.Lemmas
import all Cedar.Data.List -- unfolds `attach₂`
import all Cedar.Data.Map -- unfolds `contains`, `find`, `keys`, …
import all Cedar.Data.Set -- unfolds `all`, `any`, `contains`, …
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.EnvironmentValidator -- unfolds `validateWellFormed`
import all Cedar.Validation.RequestEntityValidator -- unfolds `instanceOfBoolType`, `instanceOfEntityType`, `instanceOfExtType`, …
import all Cedar.Validation.Typechecker -- unfolds `entityUID`, `typeOfLit`
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `QualifiedType`, …
import all Cedar.Validation.Validator -- unfolds `environment`, `environments`

/-! # `ValidRequest` characterizes `validateRequest` -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Lookups -/

private theorem mem_attach₂_of_mem {α β : Type} [SizeOf α] [SizeOf β] {l : List (α × β)}
    {p : α × β} (hp : p ∈ l) :
    (⟨p, List.sizeOf_snd_lt_sizeOf_list hp⟩ : { x : α × β // sizeOf x.snd < 1 + sizeOf l }) ∈
      l.attach₂ := by
  simp only [List.attach₂, List.mem_pmap]; exact ⟨p, hp, rfl⟩

/-- `ValidEntityUID` is the validity test `instanceOfEntityType` and `typeOfLit` use. -/
theorem validEntityUID_iff {ets : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    {eid : String} (hndE : (ets.toList.map Prod.fst).Nodup)
    (hndA : (acts.toList.map Prod.fst).Nodup) :
    ValidEntityUID ety eid ets acts ↔
      (ets.isValidEntityUID ⟨ety, eid⟩ || acts.contains ⟨ety, eid⟩) = true :=
  ⟨fun h => validEntityUID_lit h hndE hndA, fun h => validEntityUID_of_checkEntities h⟩

/-! ## Values as instances of types -/

theorem instanceOfBoolType_iff {b : Bool} {bty : BoolType} :
    InstanceOfBoolType b bty ↔ instanceOfBoolType b bty = true := by
  constructor
  · intro h; cases h <;> simp [instanceOfBoolType]
  · intro h
    cases b <;> cases bty <;> simp only [instanceOfBoolType, Bool.false_eq_true] at h <;>
      first | exact .tt | exact .ff | exact .anyBool _

theorem instanceOfExtType_iff {x : Ext} {xty : ExtType} :
    InstanceOfExtType x xty ↔ instanceOfExtType x xty = true := by
  constructor
  · intro h; cases h <;> simp [instanceOfExtType]
  · intro h
    cases x <;> cases xty <;> simp only [instanceOfExtType, Bool.false_eq_true] at h <;>
      first | exact .decimal _ | exact .ipaddr _ | exact .datetime _ | exact .duration _

theorem instanceOfEntityType_iff {ets : EntitySchema} {acts : ActionSchema} {uid : EntityUID}
    {ety : EntityType} (hndE : (ets.toList.map Prod.fst).Nodup)
    (hndA : (acts.toList.map Prod.fst).Nodup) :
    instanceOfEntityType uid ety ⟨ets, acts⟩ = true ↔
      uid.ty = ety ∧ ValidEntityUID ety uid.eid ets acts := by
  obtain ⟨ety', eid⟩ := uid
  simp only [instanceOfEntityType, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, (validEntityUID_iff hndE hndA).mpr h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, (validEntityUID_iff hndE hndA).mp h⟩

theorem instanceOfTypeList_iff {ets : EntitySchema} {acts : ActionSchema} {ty : CedarType} :
    ∀ {vs : List Value}, InstanceOfTypeList ets acts vs ty ↔ ∀ v ∈ vs, InstanceOfType ets acts v ty
  | [] => ⟨fun _ => by simp, fun _ => .nil _ _ _⟩
  | v :: vs => by
    rw [List.forall_mem_cons, ← instanceOfTypeList_iff]
    constructor
    · intro h; cases h with | cons _ _ _ hv hvs => exact ⟨hv, hvs⟩
    · rintro ⟨hv, hvs⟩; exact .cons _ _ _ _ _ hv hvs

theorem instanceOfRecordEntries_iff {ets : EntitySchema} {acts : ActionSchema}
    {rty : List (Attr × QualifiedType)} :
    ∀ {avs : List (Attr × Value)}, InstanceOfRecordEntries ets acts avs rty ↔
      ∀ p ∈ avs, ∃ qty, MapContains p.1 qty (.mk rty) ∧ InstanceOfType ets acts p.2 qty.getType
  | [] => ⟨fun _ => by simp, fun _ => .nil _ _ _⟩
  | (a, v) :: avs => by
    rw [List.forall_mem_cons, ← instanceOfRecordEntries_iff]
    constructor
    · intro h; cases h with | cons _ _ _ qty _ hmc hv hvs => exact ⟨⟨qty, hmc, hv⟩, hvs⟩
    · rintro ⟨⟨qty, hmc, hv⟩, hvs⟩; exact .cons _ _ _ _ _ _ _ hmc hv hvs

theorem requiredAttrsPresent_iff {avs : List (Attr × Value)} :
    ∀ {rty : List (Attr × QualifiedType)}, RequiredAttrsPresent avs rty ↔
      ∀ p ∈ rty, p.2.isRequired = true → (Map.mk avs).contains p.1 = true
  | [] => ⟨fun _ => by simp, fun _ => .nil _⟩
  | (a, qty) :: rty => by
    rw [List.forall_mem_cons, ← requiredAttrsPresent_iff]
    constructor
    · intro h
      cases h with
      | optional _ _ _ h => exact ⟨by simp [Qualified.isRequired], h⟩
      | required _ v _ _ hmc h =>
        exact ⟨fun _ => map_contains_iff_mapContains.mpr ⟨v, hmc⟩, h⟩
    · rintro ⟨hq, h⟩
      cases qty with
      | optional ty => exact .optional _ _ _ _ h
      | required ty =>
        obtain ⟨v, hmc⟩ := map_contains_iff_mapContains.mp (hq rfl)
        exact .required _ _ _ _ _ hmc h

/-- The record case of `instanceOfType`, on a record type with distinct keys. -/
theorem instanceOfType_record_iff {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
    {schema : Schema} (hnd : (rty.map Prod.fst).Nodup) :
    instanceOfType (.record (Map.mk avs)) (.record (Map.mk rty)) schema = true ↔
      (∀ p ∈ avs, ∃ qty, MapContains p.1 qty (.mk rty) ∧ instanceOfType p.2 qty.getType schema) ∧
        ∀ p ∈ rty, p.2.isRequired = true → (Map.mk avs).contains p.1 = true := by
  have hnd' : ((Map.mk rty).toList.map Prod.fst).Nodup := hnd
  simp only [instanceOfType, Map.toList, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨hc, hi⟩, hr⟩
    refine ⟨fun p hp => ?_, fun p hp hreq => ?_⟩
    · obtain ⟨qty, hf⟩ := Map.contains_iff_some_find?.mp (hc p hp)
      have := hi _ (mem_attach₂_of_mem hp)
      simp only [hf] at this
      exact ⟨qty, find?_mapContains hf, this⟩
    · have hf := mapContains_find?_nodup (mem_mapContains (k := p.1) (v := p.2) hp) hnd'
      have := hr p hp
      simp only [requiredAttributePresent, hf, hreq, ite_true] at this
      exact this
  · rintro ⟨hi, hr⟩
    refine ⟨⟨fun p hp => ?_, fun x hx => ?_⟩, fun p hp => ?_⟩
    · obtain ⟨qty, hmc, _⟩ := hi p hp
      exact Map.find?_some_implies_contains (mapContains_find?_nodup hmc hnd')
    · obtain ⟨qty, hmc, h⟩ := hi x.val (List.mem_attach₂ hx)
      simp only [mapContains_find?_nodup hmc hnd']
      exact h
    · have hf := mapContains_find?_nodup (mem_mapContains (k := p.1) (v := p.2) hp) hnd'
      simp only [requiredAttributePresent, hf]
      cases hq : p.2.isRequired
      · simp
      · simpa using hr p hp hq

/-- `InstanceOfType` agrees with `instanceOfType` on types whose records have distinct keys. -/
theorem instanceOfType_iff {ets : EntitySchema} {acts : ActionSchema}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    ∀ (v : Value) {ty : CedarType}, TyWf ty →
      (InstanceOfType ets acts v ty ↔ instanceOfType v ty ⟨ets, acts⟩ = true)
  | .prim (.bool b), .bool bty, _ => by
    rw [instanceOfType, ← instanceOfBoolType_iff]
    exact ⟨fun h => by cases h; assumption, fun h => .bool _ _ _ _ h⟩
  | .prim (.int i), .int, _ => by simp only [instanceOfType]; exact ⟨fun _ => trivial, fun _ => .int _ _ _⟩
  | .prim (.string s), .string, _ => by
    simp only [instanceOfType]; exact ⟨fun _ => trivial, fun _ => .string _ _ _⟩
  | .prim (.entityUID ⟨ety', eid⟩), .entity ety, _ => by
    rw [instanceOfType, instanceOfEntityType_iff hndE hndA]
    constructor
    · intro h; cases h; exact ⟨rfl, by assumption⟩
    · rintro ⟨rfl, h⟩; exact .entity _ _ _ _ h
  | .set ⟨vs⟩, .set ty, hwf => by
    have hty : TyWf ty := by cases hwf; assumption
    simp only [instanceOfType, Set.all₁_eq_all (f := fun v => instanceOfType v ty ⟨ets, acts⟩),
      Set.all, Set.elts, List.all_eq_true]
    have ih : ∀ v ∈ vs, (InstanceOfType ets acts v ty ↔ instanceOfType v ty ⟨ets, acts⟩ = true) :=
      fun v hv =>
        have : sizeOf v < sizeOf (Value.set ⟨vs⟩) := by
          have := List.sizeOf_lt_of_mem hv
          simp only [Value.set.sizeOf_spec, Set.mk.sizeOf_spec]; omega
        instanceOfType_iff hndE hndA v hty
    constructor
    · intro h
      cases h with
      | set _ _ hl => exact fun v hv => (ih v hv).mp (instanceOfTypeList_iff.mp hl v hv)
    · intro h
      exact .set _ _ _ _ (instanceOfTypeList_iff.mpr fun v hv => (ih v hv).mpr (h v hv))
  | .record ⟨avs⟩, .record ⟨rty⟩, hwf => by
    have ⟨hnd, hq⟩ : (rty.map Prod.fst).Nodup ∧ ∀ q ∈ rty.map Prod.snd, TyWfQ q := by
      cases hwf; constructor <;> assumption
    rw [instanceOfType_record_iff hnd]
    have ih : ∀ p ∈ avs, ∀ qty : QualifiedType, MapContains p.1 qty (.mk rty) →
        (InstanceOfType ets acts p.2 qty.getType ↔
          instanceOfType p.2 qty.getType ⟨ets, acts⟩ = true) :=
      fun p hp qty hmc =>
        have : sizeOf p.2 < 1 + (1 + sizeOf avs) := by
          have := List.sizeOf_lt_of_mem hp
          have : sizeOf p.2 < sizeOf p := by
            obtain ⟨a, v⟩ := p; simp only [Prod.mk.sizeOf_spec]; omega
          omega
        have hwfq : TyWf qty.getType := by
          have := hq qty (List.mem_map.mpr ⟨(p.1, qty), mapContains_mem hmc, rfl⟩)
          cases this <;> assumption
        instanceOfType_iff hndE hndA p.2 hwfq
    constructor
    · intro h
      cases h with
      | record _ _ he hr =>
        refine ⟨fun p hp => ?_, requiredAttrsPresent_iff.mp hr⟩
        obtain ⟨qty, hmc, hi⟩ := instanceOfRecordEntries_iff.mp he p hp
        exact ⟨qty, hmc, (ih p hp qty hmc).mp hi⟩
    · rintro ⟨he, hr⟩
      refine .record _ _ _ _ (instanceOfRecordEntries_iff.mpr fun p hp => ?_)
        (requiredAttrsPresent_iff.mpr hr)
      obtain ⟨qty, hmc, hi⟩ := he p hp
      exact ⟨qty, hmc, (ih p hp qty hmc).mpr hi⟩
  | .ext x, .ext xty, _ => by
    rw [instanceOfType, ← instanceOfExtType_iff]
    exact ⟨fun h => by cases h; assumption, fun h => .ext _ _ _ _ h⟩
  | .prim (.bool _), .int, _ | .prim (.bool _), .string, _ | .prim (.bool _), .entity _, _
  | .prim (.bool _), .set _, _ | .prim (.bool _), .record _, _ | .prim (.bool _), .ext _, _
  | .prim (.int _), .bool _, _ | .prim (.int _), .string, _ | .prim (.int _), .entity _, _
  | .prim (.int _), .set _, _ | .prim (.int _), .record _, _ | .prim (.int _), .ext _, _
  | .prim (.string _), .bool _, _ | .prim (.string _), .int, _ | .prim (.string _), .entity _, _
  | .prim (.string _), .set _, _ | .prim (.string _), .record _, _ | .prim (.string _), .ext _, _
  | .prim (.entityUID _), .bool _, _ | .prim (.entityUID _), .int, _
  | .prim (.entityUID _), .string, _ | .prim (.entityUID _), .set _, _
  | .prim (.entityUID _), .record _, _ | .prim (.entityUID _), .ext _, _
  | .set _, .bool _, _ | .set _, .int, _ | .set _, .string, _ | .set _, .entity _, _
  | .set _, .record _, _ | .set _, .ext _, _
  | .record _, .bool _, _ | .record _, .int, _ | .record _, .string, _ | .record _, .entity _, _
  | .record _, .set _, _ | .record _, .ext _, _
  | .ext _, .bool _, _ | .ext _, .int, _ | .ext _, .string, _ | .ext _, .entity _, _
  | .ext _, .set _, _ | .ext _, .record _, _ => by
    simp only [instanceOfType, Bool.false_eq_true, iff_false]; intro h; cases h
termination_by v => sizeOf v

/-! ## Schema environments -/

/-- Membership in `Schema.environments`, unfolded. -/
theorem mem_environments_iff {schema : Schema} {env : TypeEnv} : env ∈ schema.environments ↔
    ∃ act entry p r, (act, entry) ∈ schema.acts.toList ∧ p ∈ entry.appliesToPrincipal.toList ∧
      r ∈ entry.appliesToResource.toList ∧
        env = ⟨schema.ets, schema.acts, ⟨p, act, r, entry.context⟩⟩ := by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap, Prod.exists]
  constructor
  · rintro ⟨rt, ⟨act, entry, hmem, hrt⟩, rfl⟩
    change rt ∈ (entry.appliesToPrincipal.toList.product entry.appliesToResource.toList).map
      (fun (pr : EntityType × EntityType) => (⟨pr.1, act, pr.2, entry.context⟩ : RequestType)) at hrt
    simp only [List.mem_map, List.product, List.mem_flatMap, Prod.exists] at hrt
    obtain ⟨p, r, ⟨p', hp, r', hr, heq⟩, rfl⟩ := hrt
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨act, entry, _, _, hmem, hp, hr, rfl⟩
  · rintro ⟨act, entry, p, r, hmem, hp, hr, rfl⟩
    refine ⟨_, ⟨act, entry, hmem, ?_⟩, rfl⟩
    change _ ∈ (entry.appliesToPrincipal.toList.product entry.appliesToResource.toList).map
      (fun (pr : EntityType × EntityType) => (⟨pr.1, act, pr.2, entry.context⟩ : RequestType))
    simp only [List.mem_map, List.product, List.mem_flatMap, Prod.exists]
    exact ⟨p, r, ⟨p, hp, r, hr, rfl⟩, rfl⟩

/-! ## Requests -/

/-- `InstanceOfRequestType` agrees with `instanceOfRequestType` on an environment satisfying
    `EnvAssumptions`. -/
theorem instanceOfRequestType_iff {env : TypeEnv} {req : Request} (hwf : EnvAssumptions env) :
    InstanceOfRequestType env req ↔ instanceOfRequestType req env = true := by
  have hndE := hwf.ets_keys_nodup
  have hndA := hwf.acts_keys_nodup
  have hctx := hwf.context_tyWf
  obtain ⟨ets, acts, ⟨pty, act, rty, ctxty⟩⟩ := env
  obtain ⟨⟨pty', peid⟩, act', ⟨rty', reid⟩, ctx⟩ := req
  simp only [instanceOfRequestType, TypeEnv.schema, Bool.and_eq_true, beq_iff_eq,
    instanceOfEntityType_iff hndE hndA]
  rw [← instanceOfType_iff hndE hndA _ hctx]
  constructor
  · intro h
    cases h with
    | mk _ _ _ _ _ _ _ _ _ hp hr hc => exact ⟨⟨⟨⟨rfl, hp⟩, rfl⟩, rfl, hr⟩, hc⟩
  · rintro ⟨⟨⟨⟨rfl, hp⟩, rfl⟩, rfl, hr⟩, hc⟩
    exact .mk _ _ _ _ _ _ _ _ _ hp hr hc

/-- **Request validation.** On a schema whose environments satisfy `EnvAssumptions`,
    `validateRequest` accepts a request exactly when `ValidRequest` holds for it. -/
theorem validateRequest_iff {schema : Schema} {req : Request}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    validateRequest schema req = .ok () ↔ ValidRequest schema req := by
  have hfun : validateRequest schema req = .ok () ↔
      ∃ env ∈ schema.environments, instanceOfRequestType req env = true := by
    simp only [validateRequest, requestMatchesEnvironment]
    by_cases h : (schema.environments.any fun env => instanceOfRequestType req env) = true
    · simp only [h, ite_true, true_iff]; simpa only [List.any_eq_true] using h
    · simp only [h, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
      simpa only [List.any_eq_true] using h
  rw [hfun]
  constructor
  · rintro ⟨env, henv, h⟩
    exact .mk _ env _ (schemaEnvironment_iff_mem.mpr henv) ((instanceOfRequestType_iff (hwf env henv)).mpr h)
  · intro h
    cases h with
    | mk env _ hse hi =>
      have henv := schemaEnvironment_iff_mem.mp hse
      exact ⟨env, henv, (instanceOfRequestType_iff (hwf env henv)).mp hi⟩

/-- `validateRequest_iff` on a schema that passes Cedar's schema well-formedness check. -/
theorem validateRequest_iff_of_validateWellFormed {schema : Schema} {req : Request}
    (hwf : schema.validateWellFormed = .ok ()) :
    validateRequest schema req = .ok () ↔ ValidRequest schema req :=
  validateRequest_iff (envAssumptions_of_validateWellFormed hwf)

end Cedar.Validation.Relational

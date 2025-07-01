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

import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.Validation.WellTyped.TypeLifting
import Cedar.Thm.Validation.Typechecker.Record

/-!
This file contains expression-kind-specific lemmas of the theorem `well_typed_is_sound`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec

theorem well_typed_is_sound_lit
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{p : Prim}
{ty : CedarType}
(h₁ : Prim.WellTyped env p ty)
(h₂ : evaluate (Expr.lit p) request entities = Except.ok v) :
InstanceOfType env v (TypedExpr.lit p ty).typeOf
:= by
  simp only [evaluate] at h₂
  cases h₁ <;>
  simp only [TypedExpr.typeOf] <;>
  simp only [Except.ok.injEq] at h₂ <;>
  rw [←h₂]
  case bool => simp only [bool_is_instance_of_anyBool]
  case int => exact InstanceOfType.instance_of_int
  case string => exact InstanceOfType.instance_of_string
  case entityUID uid h =>
    have : InstanceOfEntityType env uid uid.ty := by
      simp [InstanceOfEntityType, EntityUID.WellFormed, h]
    exact InstanceOfType.instance_of_entity uid uid.ty this

theorem well_typed_is_sound_var
{v : Value}
{var : Var}
{env : Environment}
{request : Request}
{entities : Entities}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : Var.WellTyped env var ty)
(h₃ : evaluate (Expr.var var) request entities = Except.ok v) :
InstanceOfType env v (TypedExpr.var var ty).typeOf
:= by
  cases h₂ <;>
  simp only [TypedExpr.typeOf] <;>
  simp only [TypedExpr.toExpr, evaluate, Except.ok.injEq] at h₃ <;>
  rw [←h₃] <;>
  simp only [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₁
  case principal =>
    rcases h₁ with ⟨⟨h₁, _, _, _⟩, _, _⟩
    exact InstanceOfType.instance_of_entity request.principal env.reqty.principal h₁
  case resource =>
    rcases h₁ with ⟨⟨_, _, h₁, _⟩, _, _⟩
    exact InstanceOfType.instance_of_entity request.resource env.reqty.resource h₁
  case action =>
    rcases h₁ with ⟨⟨_, h₁, _, _⟩, _, _⟩
    simp only [h₁]
    have : InstanceOfEntityType env env.reqty.action env.reqty.action.ty := by
      simp [InstanceOfEntityType, EntityUID.WellFormed]
      sorry
    exact InstanceOfType.instance_of_entity env.reqty.action env.reqty.action.ty this
  case context =>
    rcases h₁ with ⟨⟨_, _, _, h₁⟩, _, _⟩
    exact type_lifting_preserves_instance_of_type h₁

theorem well_typed_is_sound_ite
{request : Request}
{entities : Entities}
{x₁ x₂ x₃ : TypedExpr}
{v : Value}
(h₄ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(h₅ : x₂.typeOf = x₃.typeOf)
(hᵢ₁ : ∀ {v : Value}, evaluate x₁.toExpr request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, evaluate x₂.toExpr request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(hᵢ₃ : ∀ {v : Value}, evaluate x₃.toExpr request entities = Except.ok v → InstanceOfType env v x₃.typeOf)
(h₃ : evaluate (x₁.toExpr.ite x₂.toExpr x₃.toExpr) request entities = Except.ok v) :
  InstanceOfType env v (x₁.ite x₂ x₃ x₂.typeOf).typeOf
:= by
  simp only [evaluate] at h₃
  generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
  cases res₁
  case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
  case ok =>
    rename_i v₁
    specialize hᵢ₁ hᵢ₁'
    simp only [h₄] at hᵢ₁
    clear h₄
    replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
    simp only [hᵢ₁] at hᵢ₁'
    simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₃
    have h : (TypedExpr.ite x₁ x₂ x₃ x₂.typeOf).typeOf = x₂.typeOf := by
      simp only [TypedExpr.typeOf]
    rw [h]
    clear h
    cases b <;> simp [hᵢ₁'] at h₃
    case false =>
      rw [h₅]
      exact hᵢ₃ h₃
    case true =>
      exact hᵢ₂ h₃

theorem well_typed_is_sound_and
{request : Request}
{entities : Entities}
{x₁ x₂ : TypedExpr}
{v : Value}
(h₄ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(h₅ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : ∀ {v : Value}, evaluate x₁.toExpr request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, evaluate x₂.toExpr request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(h₃ : evaluate (x₁.toExpr.and x₂.toExpr) request entities = Except.ok v) :
  InstanceOfType env v (x₁.and x₂ (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [evaluate] at h₃
  generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
  cases res₁
  case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
  case ok =>
    specialize hᵢ₁ hᵢ₁'
    simp only [h₄] at hᵢ₁
    clear h₄
    replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
    simp only [hᵢ₁] at hᵢ₁'
    simp only [Result.as, hᵢ₁', Coe.coe, Value.asBool, Except.bind_ok] at h₃
    simp only [TypedExpr.typeOf]
    cases b <;> simp at h₃
    case false =>
      rw [←h₃]
      simp only [bool_is_instance_of_anyBool]
    case true =>
      generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
      cases res₂
      case error =>
        simp only [hᵢ₂', Except.map_error, reduceCtorEq] at h₃
      case ok =>
        simp only [hᵢ₂'] at h₃
        specialize hᵢ₂ hᵢ₂'
        simp only [h₅] at hᵢ₂
        clear h₅
        replace ⟨_, hᵢ₂⟩ := instance_of_anyBool_is_bool hᵢ₂
        simp only [hᵢ₂, Except.map_ok, Except.ok.injEq] at h₃
        simp only [←h₃, bool_is_instance_of_anyBool]

theorem well_typed_is_sound_or
{request : Request}
{entities : Entities}
{x₁ x₂ : TypedExpr}
{v : Value}
(h₄ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(h₅ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : ∀ {v : Value}, evaluate x₁.toExpr request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, evaluate x₂.toExpr request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(h₃ : evaluate (x₁.toExpr.or x₂.toExpr) request entities = Except.ok v) :
  InstanceOfType env v (x₁.or x₂ (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [evaluate] at h₃
  generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
  cases res₁
  case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
  case ok =>
    specialize hᵢ₁ hᵢ₁'
    simp only [h₄] at hᵢ₁
    clear h₄
    replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
    simp only [hᵢ₁] at hᵢ₁'
    simp only [Result.as, hᵢ₁', Coe.coe, Value.asBool, Except.bind_ok] at h₃
    simp only [TypedExpr.typeOf]
    cases b <;> simp at h₃
    case false =>
      generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
      cases res₂
      case error =>
        simp only [hᵢ₂', Except.map_error, reduceCtorEq] at h₃
      case ok =>
        simp only [hᵢ₂'] at h₃
        specialize hᵢ₂ hᵢ₂'
        simp only [h₅] at hᵢ₂
        clear h₅
        replace ⟨_, hᵢ₂⟩ := instance_of_anyBool_is_bool hᵢ₂
        simp only [hᵢ₂, Except.map_ok, Except.ok.injEq] at h₃
        simp only [←h₃, bool_is_instance_of_anyBool]
    case true =>
      rw [←h₃]
      simp only [bool_is_instance_of_anyBool]

theorem well_typed_is_sound_unary_app
{request : Request}
{entities : Entities}
{x₁ : TypedExpr}
{v : Value}
{op₁ : UnaryOp}
{ty : CedarType}
(h₄ : op₁.WellTyped x₁ ty)
(h₃ : evaluate (Expr.unaryApp op₁ x₁.toExpr) request entities = Except.ok v) :
  InstanceOfType env v (TypedExpr.unaryApp op₁ x₁ ty).typeOf
:= by
  simp only [evaluate] at h₃
  generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
  cases res₁
  case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₃
  case ok v =>
    simp only [hᵢ₁, apply₁, Except.bind_ok] at h₃
    split at h₃ <;> cases h₄ <;> simp only [TypedExpr.typeOf]
    · simp only [Except.ok.injEq] at h₃
      simp only [←h₃, bool_is_instance_of_anyBool]
    · simp only [intOrErr] at h₃
      split at h₃
      · simp only [Except.ok.injEq] at h₃
        rw [←h₃]
        exact InstanceOfType.instance_of_int
      · cases h₃
    · simp only [Except.ok.injEq] at h₃
      simp only [←h₃, bool_is_instance_of_anyBool]
    · simp only [Except.ok.injEq] at h₃
      simp only [←h₃, bool_is_instance_of_anyBool]
    · simp at h₃
      subst h₃
      simp only [bool_is_instance_of_anyBool]
    · cases h₃
    · cases h₃
    · cases h₃
    · cases h₃
    · cases h₃

theorem well_typed_is_sound_binary_app
{request : Request}
{entities : Entities}
{x₁ x₂ : TypedExpr}
{v : Value}
{op₂ : BinaryOp}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₄ : BinaryOp.WellTyped env op₂ x₁ x₂ ty)
(hᵢ₁ : ∀ {v : Value}, evaluate x₁.toExpr request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, evaluate x₂.toExpr request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(h₃ : evaluate (Expr.binaryApp op₂ x₁.toExpr x₂.toExpr) request entities = Except.ok v) :
  InstanceOfType env v (TypedExpr.binaryApp op₂ x₁ x₂ ty).typeOf
:= by
  simp only [evaluate] at h₃
  generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
  generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
  cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₃
  -- case ok.ok
  rename_i v₁ v₂
  simp only [apply₂] at h₃
  simp only [TypedExpr.typeOf]
  split at h₃ <;>
  cases h₄ <;>
  try cases h₃ <;>
  try simp only [bool_is_instance_of_anyBool]
  · simp only [intOrErr] at h₃
    split at h₃
    · simp only [Except.ok.injEq] at h₃
      simp [←h₃]
      exact InstanceOfType.instance_of_int
    · cases h₃
  · simp only [intOrErr] at h₃
    split at h₃
    · simp only [Except.ok.injEq] at h₃
      simp [←h₃]
      exact InstanceOfType.instance_of_int
    · cases h₃
  · simp only [intOrErr] at h₃
    split at h₃
    · simp only [Except.ok.injEq] at h₃
      simp [←h₃]
      exact InstanceOfType.instance_of_int
    · cases h₃
  · specialize hᵢ₂ hᵢ₂'
    rename_i h₂
    simp only [h₂] at hᵢ₂
    cases hᵢ₂
  · simp only [inₛ, do_ok_eq_ok] at h₃
    rcases h₃ with ⟨_, _, h₃⟩
    simp only [← h₃, bool_is_instance_of_anyBool]
  · rename_i uid₁ tag _ _ h₄ _ _
    simp only [getTag, Data.Map.findOrErr] at h₃
    generalize hᵢ : entities.tags uid₁ = res₁
    cases res₁ <;> rw [hᵢ] at h₃
    case error => simp only [Except.bind_err, reduceCtorEq] at h₃
    case ok =>
      simp only [Except.bind_ok] at h₃
      split at h₃
      · rename_i ht₁ _ _ _ v₁ heq
        simp only [Except.ok.injEq] at h₃
        subst h₃
        specialize hᵢ₁ hᵢ₁'
        simp only [ht₁] at hᵢ₁
        cases hᵢ₁
        rename_i ht₁
        simp only [InstanceOfEntityType] at ht₁
        simp only [ht₁] at h₄
        simp only [RequestAndEntitiesMatchEnvironment] at h₁
        rcases h₁ with ⟨_, h₁, _⟩
        simp only [InstanceOfEntitySchema] at h₁
        simp only [Entities.tags, do_ok_eq_ok, Data.Map.findOrErr] at hᵢ
        split at hᵢ
        · simp only [Except.ok.injEq, exists_eq_left'] at hᵢ
          rename_i entry heq₁
          specialize h₁ uid₁ entry heq₁
          replace ⟨entry₁, ⟨h₅, _, _, _, h₆⟩⟩ := h₁
          simp [InstanceOfEntityTags] at h₆
          simp [EntitySchema.tags?] at h₄
          rcases h₄ with ⟨_, h₃₁, h₃₂⟩
          simp only [h₅, Option.some.injEq] at h₃₁
          simp only [← h₃₁] at h₃₂
          simp only [h₃₂] at h₆
          simp only [←hᵢ] at heq
          specialize h₆ v₁ (Data.Map.in_list_in_values (Data.Map.find?_mem_toList heq))
          exact type_lifting_preserves_instance_of_type h₆
        · simp only [reduceCtorEq, false_and, exists_const] at hᵢ
      · cases h₃

theorem well_typed_is_sound_has_attr
{v : Value}
{request : Request}
{entities : Entities}
{x₁ : TypedExpr}
{attr : Attr}
(h₃ : evaluate (x₁.toExpr.hasAttr attr) request entities = Except.ok v) :
  InstanceOfType env v (x₁.hasAttr attr (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [evaluate] at h₃
  generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
  cases res₁ <;> simp [hᵢ'] at h₃
  simp only [hasAttr, do_ok_eq_ok] at h₃
  rcases h₃ with ⟨_, _, h₃⟩
  simp only [← h₃, TypedExpr.typeOf, bool_is_instance_of_anyBool]

theorem well_typed_is_sound_get_attr_entity
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{ety : EntityType}
{rty : RecordType}
{x₁ : TypedExpr}
{attr : Attr}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : ∀ {v : Value}, evaluate x₁.toExpr request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(h₄ : x₁.typeOf = CedarType.entity ety)
(h₅ : (env.ets.attrs? ety).map RecordType.liftBoolTypes = some rty)
(h₆ : Option.map Qualified.getType (Data.Map.find? rty attr) = some ty)
(h₇ : evaluate (x₁.toExpr.getAttr attr) request entities = Except.ok v) :
InstanceOfType env v (x₁.getAttr attr ty).typeOf
:= by
  generalize hᵢ : evaluate x₁.toExpr request entities = res₁
  cases res₁ <;> simp [evaluate, hᵢ] at h₇
  rename_i v₁
  replace h₂ := h₂ hᵢ
  simp only [h₄] at h₂
  cases h₂
  rename_i uid het
  simp only [InstanceOfEntityType] at het
  simp only [RequestAndEntitiesMatchEnvironment, InstanceOfEntitySchema] at h₁
  obtain ⟨_, h₁, _⟩ := h₁
  simp only [getAttr, attrsOf, Entities.attrs, Data.Map.findOrErr, bind_assoc, Except.bind_ok] at h₇
  split at h₇
  · simp only [Except.bind_ok] at h₇
    rename_i data heq
    rcases h₁ uid data heq with ⟨entry, h₁₁, _, h₁₂, _⟩
    split at h₇
    · rename_i v₁ heq₁
      simp only [Except.ok.injEq] at h₇
      cases h₁₂
      rename_i h₈
      simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h₅
      rcases h₅ with ⟨a, ⟨a₁, h₅₁, h₅₃⟩, h₅₂⟩
      simp [←het.1] at h₁₁
      simp only [h₁₁, Option.some.injEq] at h₅₁
      simp only [← h₅₁] at h₅₃
      have h₈ := λ qty => h₈ attr v₁ qty heq₁
      simp only [h₅₂] at h₈
      simp only [Option.map_eq_some_iff] at h₆
      rcases h₆ with ⟨qty, h₆₁, h₆₂⟩
      simp [←h₅₂, RecordType.liftBoolTypes, lift_bool_types_record_eq_map_on_values] at h₆₁
      replace ⟨qty', h₆₁, h₆₃⟩ := Data.Map.find?_mapOnValues_some' QualifiedType.liftBoolTypes h₆₁
      simp [←h₅₃] at h₆₁
      specialize h₈ qty' h₆₁
      simp [TypedExpr.typeOf]
      subst h₆₂
      subst h₆₃
      cases qty'
      all_goals {
        simp [QualifiedType.liftBoolTypes, Qualified.getType]
        simp [Qualified.getType] at h₈
        subst h₇
        exact type_lifting_preserves_instance_of_type h₈
      }
    · cases h₇
  · simp only [Except.bind_err, reduceCtorEq] at h₇

theorem well_typed_is_sound_get_attr_record
{v : Value}
{request : Request}
{entities : Entities}
{rty : RecordType}
{x₁ : TypedExpr}
{attr : Attr}
{ty : CedarType}
(h₂ : ∀ {v : Value}, evaluate x₁.toExpr request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(h₄ : x₁.typeOf = CedarType.record rty)
(h₅ : Option.map Qualified.getType (Data.Map.find? rty attr) = some ty)
(h₆ : evaluate (x₁.toExpr.getAttr attr) request entities = Except.ok v) :
InstanceOfType env v (x₁.getAttr attr ty).typeOf
:= by
  generalize hᵢ : evaluate x₁.toExpr request entities = res₁
  cases res₁ <;> simp [evaluate, hᵢ] at h₆
  rename_i v₁
  replace h₂ := h₂ hᵢ
  simp only [h₄] at h₂
  cases h₂
  rename_i h₇
  simp only [getAttr, attrsOf, Data.Map.findOrErr, Except.bind_ok] at h₆
  split at h₆
  · rename_i v₁ heq
    have h₇ := λ qty => h₇ attr v₁ qty heq
    simp only [Option.map_eq_some_iff] at h₅
    rcases h₅ with ⟨qty, h₅₁, h₅₂⟩
    have h₇ := h₇ qty h₅₁
    simp only [Except.ok.injEq] at h₆
    simp [TypedExpr.typeOf, ←h₆, ←h₅₂]
    exact h₇
  · cases h₆

theorem well_typed_is_sound_set
{v : Value}
{request : Request}
{entities : Entities}
{ls : List TypedExpr}
{ty : CedarType}
(h₁ : ∀ (x : TypedExpr), x ∈ ls → ∀ (v : Value), evaluate x.toExpr request entities = Except.ok v → InstanceOfType env v x.typeOf)
(h₂ : ∀ (x : TypedExpr), x ∈ ls → x.typeOf = ty)
(h₃ : evaluate (Expr.set (ls.map₁ λ x => x.val.toExpr)) request entities = Except.ok v)
: InstanceOfType env v (TypedExpr.set ls ty.set).typeOf
:= by
  simp only [evaluate, do_ok_eq_ok] at h₃
  obtain ⟨v₁, h₃₁, h₃₂⟩ := h₃
  subst h₃₂
  rw [List.map₁_eq_map, List.mapM₁_eq_mapM (λ x => evaluate x request entities)] at h₃₁
  simp only [List.mapM_map, List.mapM_ok_iff_forall₂] at h₃₁
  have h₄ := List.forall₂_implies_all_right h₃₁
  simp only [TypedExpr.typeOf]
  have hₛ : ∀ v, v ∈ (Data.Set.make v₁) → InstanceOfType env v ty := by
    intro v h
    rw [←Data.Set.make_mem] at h
    obtain ⟨x, hₓ₁, hₓ₂⟩ := h₄ v h
    have h' := h₁ x hₓ₁ v hₓ₂
    rw [h₂ x hₓ₁] at h'
    exact h'
  exact InstanceOfType.instance_of_set (Data.Set.make v₁) ty hₛ

theorem attr_value_has_attrType
{request : Request}
{entities : Entities}
{m : List (Attr × TypedExpr)}
{r : List (Attr × Value)}
(h₁ : ∀ (k : Attr) (v : TypedExpr),
  (k, v) ∈ m → ∀ (v_1 : Value), evaluate v.toExpr request entities = Except.ok v_1 → InstanceOfType env v_1 v.typeOf)
(h₃ : List.Forall₂ (λ x y => Prod.mk x.fst <$> evaluate x.snd.toExpr request entities = Except.ok y) m r) :
List.Forall₂ (λ x y => x.fst = y.fst ∧ InstanceOfType env x.snd (Qualified.getType y.snd)) r (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m)
:= by
  cases h₃
  case nil => simp only [List.map_nil, List.Forall₂.nil]
  case cons at₁ av at₂ lv hᵢ₃ hᵢ₄ =>
    have h : (at₁.fst, at₁.snd) ∈ at₁ :: at₂ := by
        simp only [List.mem_cons, true_or]
    generalize hᵢ₅ : evaluate at₁.snd.toExpr request entities = res
    cases res
    case error => simp only [hᵢ₅, Except.map_error, reduceCtorEq] at hᵢ₃
    case ok v =>
      simp only [hᵢ₅, Except.map_ok, Except.ok.injEq] at hᵢ₃
      have hᵢ := attr_value_has_attrType (λ k v h => h₁ k v (List.mem_cons_of_mem at₁ h)) hᵢ₄
      have : av = (av.fst, av.snd) := by rfl
      rw [this] at hᵢ₃
      clear this
      simp only [Prod.mk.injEq] at hᵢ₃
      obtain ⟨hᵢ₃₁, hᵢ₃₂⟩ := hᵢ₃
      apply List.Forall₂.cons
      apply And.intro
      · simp only
        symm
        exact hᵢ₃₁
      · simp [Qualified.getType]
        have h₆ := h₁ at₁.fst at₁.snd
        simp at h₆
        specialize h₆ v hᵢ₅
        rw [hᵢ₃₂] at h₆
        exact h₆
      · exact hᵢ

theorem well_typed_is_sound_record
{v : Value}
{request : Request}
{entities : Entities}
{m : List (Attr × TypedExpr)}
{rty : RecordType}
(h₁ : ∀ (k : Attr) (v : TypedExpr),
  (k, v) ∈ m → ∀ (v_1 : Value), evaluate v.toExpr request entities = Except.ok v_1 → InstanceOfType env v_1 v.typeOf)
(h₂ : rty =
  Data.Map.make
    (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m))
(h₃ : evaluate (Expr.record (List.map (fun x => (x.1.fst, x.1.snd.toExpr)) m.attach₂)) request entities = Except.ok v) :
  InstanceOfType env v (TypedExpr.record m (CedarType.record rty)).typeOf
:= by
  simp only [evaluate, do_ok_eq_ok] at h₃
  obtain ⟨r, h₄, h₅⟩ := h₃
  subst h₅
  rw [List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))] at h₄
  simp only [List.mapM₂, List.attach₂] at h₄
  simp only [List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities))] at h₄
  simp only [bindAttr, bind_pure_comp, List.mapM_map, List.mapM_ok_iff_forall₂] at h₄
  let rty' := (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m)
  have h₆ : rty = Data.Map.make rty' := by
    simp only [h₂]
    rfl
  subst h₆
  have h₅ : List.Forall₂ (AttrValueHasAttrType (env := env)) r rty' := by
    exact attr_value_has_attrType h₁ h₄
  simp [TypedExpr.typeOf]
  apply mk_vals_instance_of_mk_types
  let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType env v qty.getType
  have h₆ := List.canonicalize_preserves_forallᵥ p r rty'
  simp only [List.Forallᵥ] at h₆
  exact h₆ h₅

theorem well_typed_is_sound_call
{v : Value}
{request : Request}
{entities : Entities}
{xfn : ExtFun}
{args : List TypedExpr}
{ty : CedarType}
(h₁ : xfn.WellTyped args ty)
(h₂ : evaluate (Expr.call xfn (args.map₁ λ x => x.val.toExpr)) request entities = Except.ok v) :
InstanceOfType env v (TypedExpr.call xfn args ty).typeOf
:= by
  generalize hᵢ : ((args.map₁ λ x => x.val.toExpr).mapM₁ λ x => evaluate x.val request entities) = res₁
  simp only [evaluate] at h₂
  cases res₁ <;> simp [hᵢ] at h₂
  simp only [call, res, gt_iff_lt, ge_iff_le] at h₂
  simp only [TypedExpr.typeOf]
  split at h₂ <;>
  cases h₁ <;>
  try cases h₂ <;>
  try simp only [bool_is_instance_of_anyBool]
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.decimal v) .decimal := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.decimal v) .decimal this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.ipaddr v) .ipAddr := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.ipaddr v) .ipAddr this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.duration v) .duration := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.duration v) .duration this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.duration v) .duration := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.duration v) .duration this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    rename_i dt _ _
    have : InstanceOfExtType (Ext.duration dt.toTime) .duration := by
      simp only [InstanceOfExtType]
    exact InstanceOfType.instance_of_ext (Ext.duration dt.toTime) .duration this
  all_goals { exact InstanceOfType.instance_of_int }

end Cedar.Thm

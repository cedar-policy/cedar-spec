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
import Cedar.Validation.TypedExpr
import Cedar.Thm

/-!
This file contains useful definitions and lemmas about well-typedness of `TypedExpr`
-/

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Data

inductive Prim.WellTyped (env : Environment) : Prim → CedarType → Prop
  | bool (b : Bool) :
    WellTyped env (.bool b) (.bool .anyBool)
  | int (i : Int64) :
    WellTyped env (.int i) .int
  | string (s : String) :
    WellTyped env (.string s) .string
  | entityUID (uid : EntityUID)
    (h₁ : env.ets.isValidEntityUID uid || env.acts.contains uid) :
    WellTyped env (.entityUID uid) (.entity uid.ty)

inductive Var.WellTyped (env : Environment) : Var → CedarType → Prop
  | principal :
    WellTyped env .principal (.entity env.reqty.principal)
  | resource :
    WellTyped env .resource (.entity env.reqty.resource)
  | action :
    WellTyped env .action (.entity env.reqty.action.ty)
  | context:
    WellTyped env .context (.record env.reqty.context)

inductive UnaryOp.WellTyped : UnaryOp → TypedExpr → CedarType → Prop
  | not {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .bool .anyBool) :
    WellTyped .not x₁ (.bool .anyBool)
  | neg {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .int) :
    WellTyped .neg x₁ .int
  | isEmpty {x₁ : TypedExpr} {eltTy : CedarType}
    (h₁ : x₁.typeOf = .set eltTy) :
    WellTyped .isEmpty x₁ (.bool .anyBool)
  | like {x₁ : TypedExpr} {p : Pattern}
    (h₁ : x₁.typeOf = .string) :
    WellTyped (.like p) x₁ (.bool .anyBool)

inductive BinaryOp.WellTyped (env : Environment) : BinaryOp → TypedExpr → TypedExpr → CedarType → Prop
  | eq {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = x₂.typeOf) :
    WellTyped env .eq x₁ x₂ (.bool .anyBool)
  | memₑ {x₁ x₂ : TypedExpr} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₁) :
    WellTyped env .mem x₁ x₂ (.bool .anyBool)
  | memₛ {x₁ x₂ : TypedExpr} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .set (.entity ety₁)) :
    WellTyped env .mem x₁ x₂ (.bool .anyBool)
  | less_int {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .less x₁ x₂ (.bool .anyBool)
  | less_datetime {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime) :
    WellTyped env .less x₁ x₂ (.bool .anyBool)
  | less_duration {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration)
    (h₂ : x₂.typeOf = .ext .duration) :
    WellTyped env .less x₁ x₂ (.bool .anyBool)
  | lessEq_int {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | lessEq_datetime {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime) :
    WellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | lessEq_duration {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration)
    (h₂ : x₂.typeOf = .ext .duration) :
    WellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | add {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .add x₁ x₂ .int
  | sub {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .sub x₁ x₂ .int
  | mul {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .mul x₁ x₂ .int
  | contains {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .set x₂.typeOf) :
    WellTyped env .contains x₁ x₂ (.bool .anyBool)
  | containsAll {x₁ x₂ : TypedExpr} {ty : CedarType}
    (h₁ : x₁.typeOf = .set ty)
    (h₂ : x₂.typeOf = .set ty) :
    WellTyped env .containsAll x₁ x₂ (.bool .anyBool)
  | containsAny {x₁ x₂ : TypedExpr} {ty : CedarType}
    (h₁ : x₁.typeOf = .set ty)
    (h₂ : x₂.typeOf = .set ty) :
    WellTyped env .containsAny x₁ x₂ (.bool .anyBool)
  | hasTag {x₁ x₂ : TypedExpr} {ety : EntityType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string) :
    WellTyped env .hasTag x₁ x₂ (.bool .anyBool)
  | getTag {x₁ x₂ : TypedExpr} {ety : EntityType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string)
    (h₃ : env.ets.tags? ety = .some (.some ty)) :
    WellTyped env .getTag x₁ x₂ ty

inductive ExtFun.WellTyped : ExtFun → List TypedExpr → CedarType → Prop
  | decimal {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .string) :
    WellTyped .decimal [x₁] (.ext .decimal)
  | lessThan {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | lessThanOrEqual {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | greaterThan {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | greaterThanOrEqual {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | ip {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .string) :
    WellTyped .ip [x₁] (.ext .ipAddr)
  | isIpv4 {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isIpv4 [x₁] (.bool .anyBool)
  | isIpv6 {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isIpv6 [x₁] (.bool .anyBool)
  | isLoopback {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isLoopback [x₁] (.bool .anyBool)
  | isMulticast {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isMulticast [x₁] (.bool .anyBool)
  | isInRange {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr)
    (h₂ : x₂.typeOf = .ext .ipAddr):
    WellTyped .isInRange [x₁, x₂] (.bool .anyBool)
  | datetime {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .string) :
    WellTyped .datetime [x₁] (.ext .datetime)
  | duration {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .string) :
    WellTyped .duration [x₁] (.ext .duration)
  | offset {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .duration):
    WellTyped .offset [x₁, x₂] (.ext .datetime)
  | durationSince {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime):
    WellTyped .durationSince [x₁, x₂] (.ext .duration)
  | toDate {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime) :
    WellTyped .toDate [x₁] (.ext .datetime)
  | toTime {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime) :
    WellTyped .toTime [x₁] (.ext .duration)

inductive TypedExpr.WellTyped (env : Environment) : TypedExpr → Prop
| lit {p : Prim} {ty : CedarType}
  (h₁ : Prim.WellTyped env p ty) :
  WellTyped env (.lit p ty)
| var {v : Var} {ty : CedarType}
  (h₁ : Var.WellTyped env v ty) :
  WellTyped env (.var v ty)
| ite {x₁ x₂ x₃ : TypedExpr}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : WellTyped env x₃)
  (h₄ : x₁.typeOf = .bool .anyBool)
  (h₅ : x₂.typeOf = x₃.typeOf) :
  WellTyped env (.ite x₁ x₂ x₃ x₂.typeOf)
| and {x₁ x₂ : TypedExpr}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool) :
  WellTyped env (.and x₁ x₂ (.bool .anyBool))
| or {x₁ x₂ : TypedExpr}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool) :
  WellTyped env (.or x₁ x₂ (.bool .anyBool))
| unaryApp {op₁ : UnaryOp} {x₁ : TypedExpr}  {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : UnaryOp.WellTyped op₁ x₁ ty) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp {op₂ : BinaryOp} {x₁ x₂: TypedExpr}  {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : BinaryOp.WellTyped env op₂ x₁ x₂ ty) :
  WellTyped env (.binaryApp op₂ x₁ x₂ ty)
| hasAttr_entity {ety : EntityType} {x₁ : TypedExpr} {attr : Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety) :
  WellTyped env (.hasAttr x₁ attr (.bool .anyBool))
| hasAttr_record {rty : RecordType} {x₁ : TypedExpr} {attr : Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty) :
  WellTyped env (.hasAttr x₁ attr (.bool .anyBool))
| getAttr_entity {ety : EntityType} {rty : RecordType} {x₁ : TypedExpr} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety)
  (h₃ : env.ets.attrs? ety = .some rty)
  (h₄ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| getAttr_record {rty : RecordType} {x₁ : TypedExpr} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty)
  (h₃ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| set {ls : List TypedExpr} {ty : CedarType}
  (h₁ : ∀ x, x ∈ ls → WellTyped env x)
  (h₂ : ∀ x, x ∈ ls → x.typeOf = ty) :
  WellTyped env (.set ls (.set ty))
| record {rty : RecordType} {m : List (Attr × TypedExpr)}
  (h₁ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  -- should we require well-formedness of `m` and then rewrite h₁ using quantifiers?
  (h₂ : rty = Map.make (m.map (λ (a, ty) => (a, .required ty.typeOf)))) :
  WellTyped env (.record m (.record rty))
| call {xfn : ExtFun} {args : List TypedExpr} {ty : CedarType}
  (h₁ : ∀ x, x ∈ args → WellTyped env x)
  (h₂ : ExtFun.WellTyped xfn args ty) :
  WellTyped env (.call xfn args ty)

theorem typechecked_is_well_typed {v : Value} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  RequestAndEntitiesMatchEnvironment env request entities →
  TypedExpr.WellTyped env ty →
  evaluate ty.toExpr request entities = .ok v →
  InstanceOfType v ty.typeOf
:= by
  intro h₀ h₁ h₂
  cases h₁ <;> try simp only [TypedExpr.toExpr, evaluate] at h₂
  case lit p ty h₃ =>
    cases h₃ <;>
    simp only [TypedExpr.typeOf] <;>
    simp only [Except.ok.injEq] at h₂ <;>
    rw [←h₂]
    case bool => simp only [bool_is_instance_of_anyBool]
    case int => exact InstanceOfType.instance_of_int
    case string => exact InstanceOfType.instance_of_string
    case entityUID uid h =>
      have : InstanceOfEntityType uid uid.ty := by rfl
      exact InstanceOfType.instance_of_entity uid uid.ty this
  case var h₃ =>
    cases h₃ <;>
    simp only [TypedExpr.typeOf] <;>
    simp only [TypedExpr.toExpr, evaluate, Except.ok.injEq] at h₂ <;>
    rw [←h₂] <;>
    simp only [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₀
    case principal =>
      rcases h₀ with ⟨⟨h₀, _, _, _⟩, _, _⟩
      exact InstanceOfType.instance_of_entity request.principal env.reqty.principal h₀
    case resource =>
      rcases h₀ with ⟨⟨_, _, h₀, _⟩, _, _⟩
      exact InstanceOfType.instance_of_entity request.resource env.reqty.resource h₀
    case action =>
      rcases h₀ with ⟨⟨_, h₀, _, _⟩, _, _⟩
      simp only [h₀]
      have : InstanceOfEntityType env.reqty.action env.reqty.action.ty := by rfl
      exact InstanceOfType.instance_of_entity env.reqty.action env.reqty.action.ty this
    case context =>
      rcases h₀ with ⟨⟨_, _, _, h₀⟩, _, _⟩
      exact h₀
  case ite x₁ x₂ x₃ h₃ h₄ h₅ h₆ h₇ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok =>
      rename_i v₁
      have hᵢ₁' := typechecked_is_well_typed h₀ h₃ hᵢ₁
      simp only [h₆] at hᵢ₁'
      have ⟨b, hᵢ₁'⟩ := instance_of_anyBool_is_bool hᵢ₁'
      simp only [hᵢ₁'] at hᵢ₁
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
      have : (TypedExpr.ite x₁ x₂ x₃ x₂.typeOf).typeOf = x₂.typeOf := by
        simp only [TypedExpr.typeOf]
      simp only [this]
      cases b <;> simp at h₂
      case false =>
        have hᵢ₂ := typechecked_is_well_typed h₀ h₅ h₂
        rw [←h₇] at hᵢ₂
        exact hᵢ₂
      case true =>
        have hᵢ₃ := typechecked_is_well_typed h₀ h₄ h₂
        exact hᵢ₃
  case and x₁ x₂ h₃ h₄ h₅ h₆ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok =>
      have hᵢ₁' := typechecked_is_well_typed h₀ h₃ hᵢ₁
      simp only [h₅] at hᵢ₁'
      have ⟨b, hᵢ₁'⟩ := instance_of_anyBool_is_bool hᵢ₁'
      simp only [hᵢ₁'] at hᵢ₁
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
      simp only [TypedExpr.typeOf]
      cases b <;> simp at h₂
      case false =>
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      case true =>
        generalize hᵢ₂ : evaluate x₂.toExpr request entities = res₂
        cases res₂
        case error =>
          simp only [hᵢ₂, Except.map_error, reduceCtorEq] at h₂
        case ok =>
          simp only [hᵢ₂] at h₂
          have hᵢ₂' := typechecked_is_well_typed h₀ h₄ hᵢ₂
          simp only [h₆] at hᵢ₂'
          have ⟨_, hᵢ₂'⟩ := instance_of_anyBool_is_bool hᵢ₂'
          simp only [hᵢ₂', Except.map_ok, Except.ok.injEq] at h₂
          rw [←h₂]
          simp only [bool_is_instance_of_anyBool]
  case or x₁ x₂ h₃ h₄ h₅ h₆ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok =>
      have hᵢ₁' := typechecked_is_well_typed h₀ h₃ hᵢ₁
      simp only [h₅] at hᵢ₁'
      have ⟨b, hᵢ₁'⟩ := instance_of_anyBool_is_bool hᵢ₁'
      simp only [hᵢ₁'] at hᵢ₁
      simp only [Result.as, hᵢ₁, Coe.coe, Value.asBool, Except.bind_ok] at h₂
      simp only [TypedExpr.typeOf]
      cases b <;> simp at h₂
      case true =>
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      case false =>
        generalize hᵢ₂ : evaluate x₂.toExpr request entities = res₂
        cases res₂
        case error =>
          simp only [hᵢ₂, Except.map_error, reduceCtorEq] at h₂
        case ok =>
          simp only [hᵢ₂] at h₂
          have hᵢ₂' := typechecked_is_well_typed h₀ h₄ hᵢ₂
          simp only [h₆] at hᵢ₂'
          have ⟨_, hᵢ₂'⟩ := instance_of_anyBool_is_bool hᵢ₂'
          simp only [hᵢ₂', Except.map_ok, Except.ok.injEq] at h₂
          rw [←h₂]
          simp only [bool_is_instance_of_anyBool]
  case unaryApp op x₁ ty hᵢ h₃ =>
    generalize hᵢ₁ : evaluate x₁.toExpr request entities = res₁
    cases res₁
    case error => simp only [Result.as, hᵢ₁, Except.bind_err, reduceCtorEq] at h₂
    case ok v =>
      simp only [hᵢ₁, apply₁, Except.bind_ok] at h₂
      split at h₂ <;> cases h₃ <;> simp only [TypedExpr.typeOf]
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      · simp only [intOrErr] at h₂
        split at h₂
        · simp only [Except.ok.injEq] at h₂
          rw [←h₂]
          exact InstanceOfType.instance_of_int
        · cases h₂
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        simp only [bool_is_instance_of_anyBool]
      · cases h₂
      · cases h₂
      · cases h₂
      · cases h₂
  case binaryApp op₂ x₁ x₂ ty hᵢ₁ hᵢ₂ h₃ =>
    generalize hᵢ₁' : evaluate x₁.toExpr request entities = res₁
    generalize hᵢ₂' : evaluate x₂.toExpr request entities = res₂
    cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₂
    -- case ok.ok
    rename_i v₁ v₂
    simp only [apply₂] at h₂
    simp only [TypedExpr.typeOf]
    split at h₂ <;>
    cases h₃ <;>
    try cases h₂ <;>
    try simp only [bool_is_instance_of_anyBool]
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  case hasAttr_entity ety x₁ attr hᵢ h₃ =>
    generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
    cases res₁ <;> simp [hᵢ'] at h₂
    simp only [hasAttr] at h₂
    sorry
  case hasAttr_record => sorry
  case getAttr_entity => sorry
  case getAttr_record => sorry
  case set => sorry
  case record => sorry
  case call xfn args ty h₃ h₄ => sorry
    /-
    generalize hᵢ : ((args.map₁ λ x => x.val.toExpr).mapM₁ λ x => evaluate x.val request entities) = res₁
    cases res₁ <;> simp [hᵢ] at h₂
    simp only [call, res, gt_iff_lt, ge_iff_le] at h₂
    simp only [TypedExpr.typeOf]
    split at h₂ <;>
    cases h₄
    case _ v _=>
      sorry
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ => sorry
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ =>
      simp only [Except.ok.injEq] at h₂
      rw [←h₂]
      simp only [bool_is_instance_of_anyBool]
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => sorry
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
    case _ => cases h₂
  -/


theorem well_typed_bool {v : Value} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  TypedExpr.WellTyped env ty →
  ty.typeOf.isBool →
  evaluate ty.toExpr request entities = .ok v →
  ∃ b : Bool, v = b
:= by
  sorry

theorem type_of_generate_well_typed_typed_expr {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  TypedExpr.WellTyped env ty
:= by
  sorry

theorem type_lifting_preserves_expr (x : TypedExpr):
  x.toExpr = x.liftBoolTypes.toExpr
:= by
  cases x <;> simp only [TypedExpr.toExpr, TypedExpr.liftBoolTypes]
  case ite a b c _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b, type_lifting_preserves_expr c]
  case and a b _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b]
  case or a b _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b]
  case unaryApp a _ =>
    simp only [type_lifting_preserves_expr a]
  case binaryApp a b _ =>
    simp only [type_lifting_preserves_expr a, type_lifting_preserves_expr b]
  case getAttr a _ _ =>
    simp only [type_lifting_preserves_expr a]
  case hasAttr a _ _ =>
    simp only [type_lifting_preserves_expr a]
  case set s _ =>
    simp only [List.map₁_eq_map, List.map_map, Expr.set.injEq, List.map_inj_left,
      Function.comp_apply]
    exact λ x _ => type_lifting_preserves_expr x
  case record m _ =>
    simp only [Expr.record.injEq]
    have : m.attach₂.map (λ x => (x.1.fst, x.1.snd.toExpr)) =
      m.map λ x => (x.fst, x.snd.toExpr) := by
      exact List.map_attach₂ λ x : Attr × TypedExpr => (x.fst, x.snd.toExpr)
    rw [this]
    have : m.attach₂.map (λ x => (x.1.fst, x.1.snd.liftBoolTypes)) =
      m.map λ x => (x.fst, x.snd.liftBoolTypes) := by
      exact List.map_attach₂ λ x : Attr × TypedExpr => (x.fst, x.snd.liftBoolTypes)
    rw [this]
    have : (List.map (λ x => (x.fst, x.snd.liftBoolTypes)) m).attach₂.map (λ x => (x.1.fst, x.1.snd.toExpr)) =
      (List.map (λ x => (x.fst, x.snd.liftBoolTypes)) m).map (λ x => (x.fst, x.snd.toExpr)) := by
      exact List.map_attach₂ λ x : Attr × TypedExpr => (x.fst, x.snd.toExpr)
    rw [this]
    simp only [List.map_map, List.map_inj_left, Function.comp_apply, Prod.mk.injEq, true_and,
      Prod.forall]
    exact λ _ x _ => type_lifting_preserves_expr x
  case call args _ =>
    simp only [List.map₁_eq_map, List.map_map, Expr.call.injEq, List.map_inj_left,
      Function.comp_apply, true_and]
    exact λ x _ => type_lifting_preserves_expr x
  termination_by x
  decreasing_by
    all_goals simp_wf <;> try omega
    case _ h =>
      have := List.sizeOf_lt_of_mem h
      omega
    case _ h =>
      have := List.sizeOf_lt_of_mem h
      simp only [Prod.mk.sizeOf_spec] at this
      omega
    case _ h =>
      have := List.sizeOf_lt_of_mem h
      omega

theorem type_lifting_preserves_evaluation_results {x : TypedExpr} {request : Request} {entities : Entities} :
  evaluate x.toExpr request entities = evaluate x.liftBoolTypes.toExpr request entities
 := by
 simp only [type_lifting_preserves_expr x]

end Cedar.Thm

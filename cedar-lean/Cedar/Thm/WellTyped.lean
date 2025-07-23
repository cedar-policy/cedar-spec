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

import Cedar.Thm.Validation.WellTyped.Soundness
import Cedar.Thm.Validation.WellTyped.Typechecking
import Cedar.TPE.Residual
import Cedar.Data.Map

/-!
This file contains well-typedness theorems of `TypedExpr` and `Residual`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec
open Cedar.Spec.Ext
open Cedar.TPE
open Cedar.Data

/-- Successful evaluation of a well-typed expression should produce a value
of corresponding type. -/
theorem well_typed_is_sound {ty : TypedExpr} {v : Value} {env : TypeEnv} {request : Request} {entities : Entities} :
  InstanceOfWellFormedEnvironment request entities env →
  TypedExpr.WellTyped env ty →
  evaluate ty.toExpr request entities = .ok v →
  InstanceOfType env v ty.typeOf
:= by
  intro h₁ h₂ h₃
  induction h₂ generalizing v <;> simp only [TypedExpr.toExpr] at h₃
  case lit p ty h₄ =>
    exact well_typed_is_sound_lit h₄ h₃
  case var var ty h₄ =>
    exact well_typed_is_sound_var h₁ h₄ h₃
  case ite x₁ x₂ x₃ _ _ _ h₄ h₅ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact well_typed_is_sound_ite h₄ h₅ hᵢ₁ hᵢ₂ hᵢ₃ h₃
  case and x₁ x₂ _ _ h₄ h₅ hᵢ₁ hᵢ₂ =>
    exact well_typed_is_sound_and h₄ h₅ hᵢ₁ hᵢ₂ h₃
  case or x₁ x₂ _ _ h₄ h₅ hᵢ₁ hᵢ₂ =>
    exact well_typed_is_sound_or h₄ h₅ hᵢ₁ hᵢ₂ h₃
  case unaryApp op₁ x₁ ty _ h₄ _ =>
    exact well_typed_is_sound_unary_app h₄ h₃
  case binaryApp op₂ x₁ x₂ ty _ _ h₄ hᵢ₁ hᵢ₂ =>
    exact well_typed_is_sound_binary_app h₁ h₄ hᵢ₁ hᵢ₂ h₃
  case hasAttr_entity x₁ _ _ _ _ =>
    exact well_typed_is_sound_has_attr h₃
  case hasAttr_record x₁ _ _ _ _ =>
    exact well_typed_is_sound_has_attr h₃
  case getAttr_entity h₄ h₅ h₆ hᵢ =>
    exact well_typed_is_sound_get_attr_entity h₁ hᵢ h₄ h₅ h₆ h₃
  case getAttr_record h₄ h₅ hᵢ=>
    exact well_typed_is_sound_get_attr_record hᵢ h₄ h₅ h₃
  case set ls ty _ h₄ _ hᵢ =>
    exact well_typed_is_sound_set hᵢ h₄ h₃
  case record rty m hᵢ₁ h₄ hᵢ =>
    exact well_typed_is_sound_record hᵢ h₄ h₃
  case call xfn args ty _ h₄ _ =>
    exact well_typed_is_sound_call h₄ h₃

inductive UnaryResidualWellTyped : UnaryOp → Residual → CedarType → Prop
  | not {x₁ : Residual}
    (h₁ : x₁.typeOf = .bool .anyBool) :
    UnaryResidualWellTyped .not x₁ (.bool .anyBool)
  | neg {x₁ : Residual}
    (h₁ : x₁.typeOf = .int) :
    UnaryResidualWellTyped .neg x₁ .int
  | isEmpty {x₁ : Residual} {eltTy : CedarType}
    (h₁ : x₁.typeOf = .set eltTy) :
    UnaryResidualWellTyped .isEmpty x₁ (.bool .anyBool)
  | like {x₁ : Residual} {p : Pattern}
    (h₁ : x₁.typeOf = .string) :
    UnaryResidualWellTyped (.like p) x₁ (.bool .anyBool)
  | is {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₂) :
    UnaryResidualWellTyped (.is ety₁) x₁ (.bool .anyBool)

inductive BinaryResidualWellTyped (env : TypeEnv) : BinaryOp → Residual → Residual → CedarType → Prop
  | eq_val {p₁ p₂ : Value} {ty₁ ty₂ : CedarType} :
    BinaryResidualWellTyped env .eq (.val p₁ ty₁) (.val p₂ ty₂) (.bool .anyBool)
  | eq_entity {ety₁ ety₂ : EntityType} {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂) :
    BinaryResidualWellTyped env .eq x₁ x₂ (.bool .anyBool)
  | eq {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = x₂.typeOf) :
    BinaryResidualWellTyped env .eq x₁ x₂ (.bool .anyBool)
  | memₑ {x₁ x₂ : Residual} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂) :
    BinaryResidualWellTyped env .mem x₁ x₂ (.bool .anyBool)
  | memₛ {x₁ x₂ : Residual} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .set (.entity ety₂)) :
    BinaryResidualWellTyped env .mem x₁ x₂ (.bool .anyBool)
  | less_int {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    BinaryResidualWellTyped env .less x₁ x₂ (.bool .anyBool)
  | less_datetime {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime) :
    BinaryResidualWellTyped env .less x₁ x₂ (.bool .anyBool)
  | less_duration {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .duration)
    (h₂ : x₂.typeOf = .ext .duration) :
    BinaryResidualWellTyped env .less x₁ x₂ (.bool .anyBool)
  | lessEq_int {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    BinaryResidualWellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | lessEq_datetime {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime) :
    BinaryResidualWellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | lessEq_duration {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .duration)
    (h₂ : x₂.typeOf = .ext .duration) :
    BinaryResidualWellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | add {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    BinaryResidualWellTyped env .add x₁ x₂ .int
  | sub {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    BinaryResidualWellTyped env .sub x₁ x₂ .int
  | mul {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    BinaryResidualWellTyped env .mul x₁ x₂ .int
  | contains {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .set x₂.typeOf) :
    BinaryResidualWellTyped env .contains x₁ x₂ (.bool .anyBool)
  | containsAll {x₁ x₂ : Residual} {ty : CedarType}
    (h₁ : x₁.typeOf = .set ty)
    (h₂ : x₂.typeOf = .set ty) :
    BinaryResidualWellTyped env .containsAll x₁ x₂ (.bool .anyBool)
  | containsAny {x₁ x₂ : Residual} {ty : CedarType}
    (h₁ : x₁.typeOf = .set ty)
    (h₂ : x₂.typeOf = .set ty) :
    BinaryResidualWellTyped env .containsAny x₁ x₂ (.bool .anyBool)
  | hasTag {x₁ x₂ : Residual} {ety : EntityType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string) :
    BinaryResidualWellTyped env .hasTag x₁ x₂ (.bool .anyBool)
  | getTag {x₁ x₂ : Residual} {ety : EntityType} {ty : CedarType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string)
    (h₃ : env.ets.tags? ety = .some (.some ty)) :
    BinaryResidualWellTyped env .getTag x₁ x₂ ty.liftBoolTypes


inductive ExtResidualWellTyped : ExtFun → List Residual → CedarType → Prop
  | decimal {s₁ : String} {d₁ : Decimal}
    (h₁ : d₁ = Decimal.decimal s₁) :
    ExtResidualWellTyped .decimal [.val (.prim (.string s₁)) .string] (.ext .decimal)
  | lessThan {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    ExtResidualWellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | lessThanOrEqual {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    ExtResidualWellTyped .lessThanOrEqual [x₁, x₂] (.bool .anyBool)
  | greaterThan {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    ExtResidualWellTyped .greaterThan [x₁, x₂] (.bool .anyBool)
  | greaterThanOrEqual {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    ExtResidualWellTyped .greaterThanOrEqual [x₁, x₂] (.bool .anyBool)
  | ip {s₁ : String} {ip₁ : IPAddr}
    (h₁ : ip₁ =  IPAddr.ip s₁) :
    ExtResidualWellTyped .ip [.val (.prim (.string s₁)) .string] (.ext .ipAddr)
  | isIpv4 {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    ExtResidualWellTyped .isIpv4 [x₁] (.bool .anyBool)
  | isIpv6 {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    ExtResidualWellTyped .isIpv6 [x₁] (.bool .anyBool)
  | isLoopback {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    ExtResidualWellTyped .isLoopback [x₁] (.bool .anyBool)
  | isMulticast {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    ExtResidualWellTyped .isMulticast [x₁] (.bool .anyBool)
  | isInRange {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .ipAddr)
    (h₂ : x₂.typeOf = .ext .ipAddr):
    ExtResidualWellTyped .isInRange [x₁, x₂] (.bool .anyBool)
  | datetime {s₁ : String} {d₁ : Datetime}
    (h₁ : d₁ =  Datetime.parse s₁) :
    ExtResidualWellTyped .datetime [.val (.prim (.string s₁)) .string] (.ext .datetime)
  | duration {s₁ : String} {d₁ : Duration}
    (h₁ : d₁ =  Datetime.Duration.parse s₁) :
    ExtResidualWellTyped .duration [.val (.prim (.string s₁)) .string] (.ext .duration)
  | offset {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .duration):
    ExtResidualWellTyped .offset [x₁, x₂] (.ext .datetime)
  | durationSince {x₁ x₂ : Residual}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime):
    ExtResidualWellTyped .durationSince [x₁, x₂] (.ext .duration)
  | toDate {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .datetime) :
    ExtResidualWellTyped .toDate [x₁] (.ext .datetime)
  | toTime {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .datetime) :
    ExtResidualWellTyped .toTime [x₁] (.ext .duration)
  | toMilliseconds {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .duration) :
    ExtResidualWellTyped .toMilliseconds [x₁] .int
  | toSeconds {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .duration) :
    ExtResidualWellTyped .toSeconds [x₁] .int
  | toMinutes {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .duration) :
    ExtResidualWellTyped .toMinutes [x₁] .int
  | toHours {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .duration) :
    ExtResidualWellTyped .toHours [x₁] .int
  | toDays {x₁ : Residual}
    (h₁ : x₁.typeOf = .ext .duration) :
    ExtResidualWellTyped .toDays [x₁] .int


/-- Well-typedness definition for Residual expressions -/
inductive Residual.WellTyped (env : TypeEnv) : Residual → Prop
| val {v : Value} {ty : CedarType}
  (h₁ : InstanceOfType env v ty) :
  WellTyped env (.val v ty)
| var {v : Var} {ty : CedarType}
  (h₁ : v.WellTyped env ty) :
  WellTyped env (.var v ty)
| ite {x₁ x₂ x₃ : Residual}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : WellTyped env x₃)
  (h₄ : x₁.typeOf = .bool .anyBool)
  (h₅ : x₂.typeOf = x₃.typeOf) :
  WellTyped env (.ite x₁ x₂ x₃ ty)
| and {x₁ x₂ : Residual} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool)
  (h₅ : ty = .bool .anyBool) :
  WellTyped env (.and x₁ x₂ ty)
| or {x₁ x₂ : Residual} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool)
  (h₅ : ty = .bool .anyBool) :
  WellTyped env (.or x₁ x₂ ty)
| unaryApp {op₁ : UnaryOp} {x₁ : Residual} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : UnaryResidualWellTyped op₁ x₁ ty) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp {op₂ : BinaryOp} {x₁ x₂: Residual} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : BinaryResidualWellTyped env op₂ x₁ x₂ ty) :
  WellTyped env (.binaryApp op₂ x₁ x₂ ty)
| hasAttr_entity {ety : EntityType} {x₁ : Residual} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety)
  (h₃ : ty = .bool .anyBool) :
  WellTyped env (.hasAttr x₁ attr ty)
| hasAttr_record {rty : RecordType} {x₁ : Residual} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty)
  (h₃ : ty = .bool .anyBool) :
  WellTyped env (.hasAttr x₁ attr ty)
| getAttr_entity {ety : EntityType} {rty : RecordType} {x₁ : Residual} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety)
  (h₃ : (env.ets.attrs? ety).map RecordType.liftBoolTypes = .some rty)
  (h₄ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| getAttr_record {rty : RecordType} {x₁ : Residual} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty)
  (h₃ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| set {ls : List Residual} {ty eltTy : CedarType}
  (h₁ : ∀ x, x ∈ ls → WellTyped env x)
  (h₂ : ∀ x, x ∈ ls → x.typeOf = eltTy)
  (h₃ : ls != [])
  (h₄ : ty = .set eltTy) :
  WellTyped env (.set ls ty)
| record {rty : RecordType} {m : List (Attr × Residual)} {ty : CedarType}
  (h₁ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  (h₂ : rty = Map.make (m.map (λ (a, r) => (a, .required r.typeOf))))
  (h₃ : ty = .record rty) :
  WellTyped env (.record m ty)
| call {xfn : ExtFun} {args : List Residual} {ty : CedarType}
  (h₁ : ∀ x, x ∈ args → WellTyped env x)
  (h₂ : ExtResidualWellTyped xfn args ty) :
  WellTyped env (.call xfn args ty)
| error {ty : CedarType} :
  WellTyped env (.error ty)

/-- Successful evaluation of a well-typed residual should produce a value
of corresponding type. -/
theorem residual_well_typed_is_sound {r : Residual} {v : Value} {env : TypeEnv} {request : Request} {entities : Entities} :
  InstanceOfWellFormedEnvironment request entities env →
  Residual.WellTyped env r →
  r.evaluate request entities = .ok v →
  InstanceOfType env v r.typeOf
:= by
  intro h₁ h₂ h₃
  induction h₂ generalizing v
  case val v ty h₄ =>
    simp only [Residual.typeOf]
    rename_i v2
    simp [Residual.evaluate] at h₃
    rewrite [h₃] at h₄
    exact h₄
  case var var ty h₄ =>
    simp only [Residual.typeOf]
    sorry
  case ite x₁ x₂ x₃ ty h₁ h₂ h₃ h₄ h₅ h₆ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp only [Residual.typeOf, h₆]
    -- The proof would need to handle the conditional evaluation
    sorry
  case and x₁ x₂ ty h₁ h₂ h₃ h₄ h₅ hᵢ₁ hᵢ₂ =>
    simp only [Residual.typeOf, h₅]
    -- The proof would need to handle boolean evaluation
    sorry
  case or x₁ x₂ ty h₁ h₂ h₃ h₄ h₅ hᵢ₁ hᵢ₂ =>
    simp only [Residual.typeOf, h₅]
    -- The proof would need to handle boolean evaluation
    sorry
  case unaryApp op₁ x₁ ty h₁ h₂ hᵢ₁ =>
    simp only [Residual.typeOf]
    -- The proof would need to handle unary operations
    sorry
  case binaryApp op₂ x₁ x₂ ty h₁ h₂ h₃ hᵢ₁ hᵢ₂ =>
    simp only [Residual.typeOf]
    -- The proof would need to handle binary operations
    sorry
  case hasAttr_entity ety x₁ attr ty h₁ h₂ h₃ hᵢ =>
    simp only [Residual.typeOf, h₃]
    -- The proof would need to handle hasAttr evaluation
    sorry
  case hasAttr_record rty x₁ attr ty h₁ h₂ h₃ hᵢ =>
    simp only [Residual.typeOf, h₃]
    -- The proof would need to handle hasAttr evaluation
    sorry
  case getAttr_entity ety rty x₁ attr ty h₁ h₂ h₃ h₄ hᵢ =>
    simp only [Residual.typeOf]
    -- The proof would need to handle getAttr evaluation
    sorry
  case getAttr_record rty x₁ attr ty h₁ h₂ h₃ hᵢ =>
    simp only [Residual.typeOf]
    -- The proof would need to handle getAttr evaluation
    sorry
  case set ls ty eltTy h₁ h₂ h₃ h₄ hᵢ =>
    simp only [Residual.typeOf, h₄]
    -- The proof would need to handle set evaluation
    sorry
  case record rty m ty h₁ h₂ h₃ hᵢ =>
    simp only [Residual.typeOf, h₃]
    -- The proof would need to handle record evaluation
    sorry
  case call xfn args ty h₁ h₂ hᵢ =>
    simp only [Residual.typeOf]
    -- The proof would need to handle function call evaluation
    sorry
  case error ty =>
    -- Error case should not produce a successful result
    simp only [Residual.evaluate] at h₃
    -- h₃ : Except.error Error.extensionError = Except.ok v
    -- This is a contradiction since error ≠ ok
    cases h₃

end Cedar.Thm

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

import Cedar.Spec.Ext
import Cedar.Validation.TypedExpr
import Cedar.TPE.Residual
import Cedar.Thm.Validation

/-!
This file contains well-typedness definitions of `TypedExpr`
-/

namespace Cedar.Spec

open Cedar.Validation
open Cedar.Spec.Ext

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


end Cedar.Spec



namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Data

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
  WellTyped env (.ite x₁ x₂ x₃ x₂.typeOf)
| and {x₁ x₂ : Residual}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool) :
  WellTyped env (.and x₁ x₂ (.bool .anyBool))
| or {x₁ x₂ : Residual}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool):
  WellTyped env (.or x₁ x₂ (.bool .anyBool))
| unaryApp {op₁ : UnaryOp} {x₁ : Residual} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : UnaryResidualWellTyped op₁ x₁ ty) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp {op₂ : BinaryOp} {x₁ x₂: Residual} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : BinaryResidualWellTyped env op₂ x₁ x₂ ty) :
  WellTyped env (.binaryApp op₂ x₁ x₂ ty)
| hasAttr_entity {ety : EntityType} {x₁ : Residual} {attr : Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety) :
  WellTyped env (.hasAttr x₁ attr (.bool .anyBool))
| hasAttr_record {rty : RecordType} {x₁ : Residual} {attr : Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty) :
  WellTyped env (.hasAttr x₁ attr (.bool .anyBool))
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
| set {ls : List Residual} {ty : CedarType}
  (h₁ : ∀ x, x ∈ ls → WellTyped env x)
  (h₂ : ∀ x, x ∈ ls → x.typeOf = ty)
  (h₃ : ls != []) :
  WellTyped env (.set ls (.set ty))
| record {rty : RecordType} {m : List (Attr × Residual)}
  (h₁ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  (h₂ : rty = Map.make (m.map (λ (a, r) => (a, .required r.typeOf)))) :
  WellTyped env (.record m (.record rty))
| call {xfn : ExtFun} {args : List Residual} {ty : CedarType}
  (h₁ : ∀ x, x ∈ args → WellTyped env x)
  (h₂ : ExtResidualWellTyped xfn args ty) :
  WellTyped env (.call xfn args ty)
| error {ty : CedarType} :
  WellTyped env (.error ty)

end Cedar.Thm

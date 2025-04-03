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
import Cedar.Spec.Ext
import Cedar.Thm.Validation

/-!
This file contains well-typedness definitions of `TypedExpr`
-/

namespace Cedar.Spec

open Cedar.Validation
open Cedar.Spec.Ext

inductive Prim.WellTyped (env : Environment) : Prim → CedarType → Prop
  | bool (b : Bool) :
    WellTyped env (.bool b) (.bool .anyBool)
  | int (i : Int64) :
    WellTyped env (.int i) .int
  | string (s : String) :
    WellTyped env (.string s) .string
  | entityUID (uid : EntityUID)
    (h₁ : env.ets.isValidEntityUID uid ∨ env.acts.contains uid) :
    WellTyped env (.entityUID uid) (.entity uid.ty)

inductive Var.WellTyped (env : Environment) : Var → CedarType → Prop
  | principal :
    WellTyped env .principal (.entity env.reqty.principal)
  | resource :
    WellTyped env .resource (.entity env.reqty.resource)
  | action :
    WellTyped env .action (.entity env.reqty.action.ty)
  | context:
    WellTyped env .context (CedarType.liftBoolTypes (.record env.reqty.context))

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
  | is {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₂) :
    WellTyped (.is ety₁) x₁ (.bool .anyBool)

inductive BinaryOp.WellTyped (env : Environment) : BinaryOp → TypedExpr → TypedExpr → CedarType → Prop
  | eq_lit {p₁ p₂ : Prim} {ty₁ ty₂ : CedarType} :
    -- do we need hypothesis like `InstanceOfType (.prim p₁) ty₁`?
    WellTyped env .eq (.lit p₁ ty₁) (.lit p₂ ty₂) (.bool .anyBool)
  | eq_entity {ety₁ ety₂ : EntityType} {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂) :
    WellTyped env .eq x₁ x₂ (.bool .anyBool)
  | eq {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = x₂.typeOf) :
    WellTyped env .eq x₁ x₂ (.bool .anyBool)
  | memₑ {x₁ x₂ : TypedExpr} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂) :
    WellTyped env .mem x₁ x₂ (.bool .anyBool)
  | memₛ {x₁ x₂ : TypedExpr} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .set (.entity ety₂)) :
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
  | getTag {x₁ x₂ : TypedExpr} {ety : EntityType} {ty : CedarType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string)
    (h₃ : env.ets.tags? ety = .some (.some ty)) :
    WellTyped env .getTag x₁ x₂ ty.liftBoolTypes

inductive ExtFun.WellTyped : ExtFun → List TypedExpr → CedarType → Prop
  | decimal {s₁ : String} {d₁ : Decimal}
    (h₁ : d₁ = Decimal.decimal s₁) :
    WellTyped .decimal [.lit (.string s₁) .string] (.ext .decimal)
  | lessThan {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | lessThanOrEqual {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThanOrEqual [x₁, x₂] (.bool .anyBool)
  | greaterThan {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .greaterThan [x₁, x₂] (.bool .anyBool)
  | greaterThanOrEqual {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .greaterThanOrEqual [x₁, x₂] (.bool .anyBool)
  | ip {s₁ : String} {ip₁ : IPAddr}
    (h₁ : ip₁ =  IPAddr.ip s₁) :
    WellTyped .ip [.lit (.string s₁) .string] (.ext .ipAddr)
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
  | datetime {s₁ : String} {d₁ : Datetime}
    (h₁ : d₁ =  Datetime.parse s₁) :
    WellTyped .datetime [.lit (.string s₁) .string] (.ext .datetime)
  | duration {s₁ : String} {d₁ : Duration}
    (h₁ : d₁ =  Datetime.Duration.parse s₁) :
    WellTyped .duration [.lit (.string s₁) .string] (.ext .duration)
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
  | toMilliseconds {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toMilliseconds [x₁] .int
  | toSeconds {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toSeconds [x₁] .int
  | toMinutes {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toMinutes [x₁] .int
  | toHours {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toHours [x₁] .int
  | toDays {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toDays [x₁] .int

end Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Data

inductive TypedExpr.WellTyped (env : Environment) : TypedExpr → Prop
| lit {p : Prim} {ty : CedarType}
  (h₁ : p.WellTyped env ty) :
  WellTyped env (.lit p ty)
| var {v : Var} {ty : CedarType}
  (h₁ : v.WellTyped env ty) :
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
  (h₂ : op₁.WellTyped x₁ ty) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp {op₂ : BinaryOp} {x₁ x₂: TypedExpr}  {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : op₂.WellTyped env x₁ x₂ ty) :
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
  (h₃ : (env.ets.attrs? ety).map RecordType.liftBoolTypes = .some rty)
  (h₄ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| getAttr_record {rty : RecordType} {x₁ : TypedExpr} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty)
  (h₃ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| set {ls : List TypedExpr} {ty : CedarType}
  (h₁ : ∀ x, x ∈ ls → WellTyped env x)
  (h₂ : ∀ x, x ∈ ls → x.typeOf = ty)
  (h₃ : ls != []) :
  WellTyped env (.set ls (.set ty))
| record {rty : RecordType} {m : List (Attr × TypedExpr)}
  (h₁ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  (h₂ : rty = Map.make (m.map (λ (a, ty) => (a, .required ty.typeOf)))) :
  WellTyped env (.record m (.record rty))
| call {xfn : ExtFun} {args : List TypedExpr} {ty : CedarType}
  (h₁ : ∀ x, x ∈ args → WellTyped env x)
  (h₂ : xfn.WellTyped args ty) :
  WellTyped env (.call xfn args ty)

end Cedar.Thm

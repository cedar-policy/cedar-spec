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
import Cedar.Thm.TPE.ResidualEval
import Cedar.Thm.Data.Map

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

/-- Instance-of-type for ResidualValue, mirroring InstanceOfType for Value.
    ResidualValue.record can contain `.unknown` attributes, so this is not
    simply a lift of InstanceOfType through asResidualValue. -/
inductive InstanceOfResidualValueType (env : TypeEnv) : ResidualValue → CedarType → Prop where
  | instance_of_bool (b : Bool) (bty : BoolType)
      (h₁ : InstanceOfBoolType b bty) :
      InstanceOfResidualValueType env (.prim (.bool b)) (.bool bty)
  | instance_of_int :
      InstanceOfResidualValueType env (.prim (.int _)) .int
  | instance_of_string :
      InstanceOfResidualValueType env (.prim (.string _)) .string
  | instance_of_entity (e : EntityUID) (ety : EntityType)
      (h₁ : InstanceOfEntityType e ety env) :
      InstanceOfResidualValueType env (.prim (.entityUID e)) (.entity ety)
  | instance_of_set (s : Set Value) (ty : CedarType)
      (h₁ : ∀ v, v ∈ s → InstanceOfType env v ty) :
      InstanceOfResidualValueType env (.set s) (.set ty)
  | instance_of_record (r : Map Attr ResidualAttribute) (rty : RecordType)
      (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      (h₂ : ∀ (k : Attr) (rv : ResidualValue) (qty : QualifiedType),
        r.find? k = some (.present rv) → rty.find? k = some qty →
        InstanceOfResidualValueType env rv qty.getType)
      (h₃ : ∀ (k : Attr) (qty : QualifiedType),
        rty.find? k = some qty → qty.isRequired → r.contains k) :
      InstanceOfResidualValueType env (.record r) (.record rty)
  | instance_of_ext (x : Ext) (xty : ExtType)
      (h₁ : InstanceOfExtType x xty) :
      InstanceOfResidualValueType env (.ext x) (.ext xty)

/-- Lift an InstanceOfType proof to InstanceOfResidualValueType for primitive values -/
theorem InstanceOfType.toResidualValueType {env : TypeEnv} {v : Value} {ty : CedarType} :
  InstanceOfType env v ty → InstanceOfResidualValueType env v.asResidualValue ty
:= by
  intro h
  cases h with
  | instance_of_bool b bty h₁ =>
    simp only [Value.asResidualValue]
    exact .instance_of_bool b bty h₁
  | instance_of_int =>
    simp only [Value.asResidualValue]
    exact .instance_of_int
  | instance_of_string =>
    simp only [Value.asResidualValue]
    exact .instance_of_string
  | instance_of_entity e ety h₁ =>
    simp only [Value.asResidualValue]
    exact .instance_of_entity e ety h₁
  | instance_of_set s ty h₁ =>
    simp only [Value.asResidualValue]
    exact .instance_of_set s ty h₁
  | instance_of_record r rty h₁ h₂ h₃ =>
    simp only [Value.asResidualValue]
    simp only [Map.mapOnValues₂_eq_mapOnValues r (fun x => ResidualAttribute.present x.asResidualValue)]
    apply InstanceOfResidualValueType.instance_of_record
    · intro k hk
      have := Map.mapOnValues_contains (fun (x : Value) => ResidualAttribute.present x.asResidualValue) (m := r) (k := k)
      rw [← this] at hk
      exact h₁ k hk
    · intro k rv qty hfind hrty
      have := Map.find?_mapOnValues (fun (x : Value) => ResidualAttribute.present x.asResidualValue) r k
      rw [← this] at hfind
      simp only [Option.map] at hfind
      split at hfind <;> simp only [Option.some.injEq, reduceCtorEq] at hfind
      rename_i v hv
      simp only [ResidualAttribute.present.injEq] at hfind
      subst hfind
      exact InstanceOfType.toResidualValueType (h₂ k v qty hv hrty)
    · intro k qty hrty hreq
      have := Map.mapOnValues_contains (fun (x : Value) => ResidualAttribute.present x.asResidualValue) (m := r) (k := k)
      rw [← this]
      exact h₃ k qty hrty hreq
  | instance_of_ext x xty h₁ =>
    simp only [Value.asResidualValue]
    exact .instance_of_ext x xty h₁
termination_by sizeOf v
decreasing_by
  simp_wf
  have := Map.sizeOf_lt_of_find? ‹_›
  simp [Value.record.sizeOf_spec]; omega

/-- Well-typedness definition for Residual expressions -/
inductive Residual.WellTyped (env : TypeEnv) : Residual → Prop
| val {rv : ResidualValue} {ty : CedarType}
  (h₁ : InstanceOfResidualValueType env rv ty) :
  WellTyped env (.val rv ty)
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

@[simp] theorem Value.asResidualValue_prim :
  (Value.prim p).asResidualValue = .prim p
:= by simp only [Value.asResidualValue]

@[simp] theorem Value.asResidualValue_ext :
  (Value.ext e).asResidualValue = .ext e
:= by simp only [Value.asResidualValue]

@[simp] theorem Value.asResidualValue_set :
  (Value.set e).asResidualValue = .set e
:= by simp only [Value.asResidualValue]

@[simp] theorem Value.asResidualValue_prim' {v : Value} :
  v.asResidualValue = .prim p ↔ v = .prim p
:= by cases v <;> simp [Value.asResidualValue]

@[simp] theorem Value.asResidualValue_ext' {v : Value} :
  v.asResidualValue = .ext p ↔ v = .ext p
:= by cases v <;> simp [Value.asResidualValue]

@[simp] theorem Value.asResidualValue_set' {v : Value} :
  v.asResidualValue = .set vs ↔ v = .set vs
:= by cases v <;> simp [Value.asResidualValue]


@[simp]
theorem well_typed_bool {env : TypeEnv} {b : Bool}:
 Residual.WellTyped env (.val (.prim (.bool b)) (CedarType.bool BoolType.anyBool))
:= Residual.WellTyped.val (.instance_of_bool b .anyBool (by cases b <;> trivial))

@[simp]
theorem well_typed_int {env : TypeEnv} {i : Int64}:
 Residual.WellTyped env (.val (.prim (.int i)) CedarType.int)
:= Residual.WellTyped.val .instance_of_int

@[simp]
theorem well_typed_string {env : TypeEnv} {s : String}:
 Residual.WellTyped env (.val (.prim (.string s)) CedarType.string)
:= Residual.WellTyped.val .instance_of_string

@[simp]
theorem well_typed_entity {env : TypeEnv} {e : EntityUID} {ety : EntityType} :
  InstanceOfEntityType e ety env → Residual.WellTyped env (.val (.prim (.entityUID e)) (.entity ety))
:= fun h => Residual.WellTyped.val (.instance_of_entity e ety h)

@[simp]
theorem well_typed_val {env : TypeEnv} {val : Value} :
 InstanceOfType env val ty → Residual.WellTyped env (Residual.val val ty)
:= (Residual.WellTyped.val $ InstanceOfType.toResidualValueType ·)

end Cedar.Thm

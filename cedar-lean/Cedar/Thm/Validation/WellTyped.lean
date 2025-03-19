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
    all_goals (simp_wf ; try omega)
    all_goals
      rename_i h
      have := List.sizeOf_lt_of_mem h
      simp only [Prod.mk.sizeOf_spec] at this
      omega

theorem type_lifting_preserves_evaluation_results {x : TypedExpr} {request : Request} {entities : Entities} :
  evaluate x.toExpr request entities = evaluate x.liftBoolTypes.toExpr request entities
 := by
 simp only [type_lifting_preserves_expr x]

end Cedar.Thm

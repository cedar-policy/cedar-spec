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

public import Cedar.Validation.Relational.Typing

@[expose] public section

/-! # What the relational typing spec assumes of a type environment

`EnvAssumptions` asks for distinct keys where `TypeEnv.WellFormed` asks for sorted ones. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

mutual
/-- A `CedarType` whose every record subtype has distinct (duplicate-free) keys. -/
inductive TyWf : CedarType → Prop where
  | bool : ∀ b, TyWf (.bool b)
  | int : TyWf .int
  | string : TyWf .string
  | entity : ∀ e, TyWf (.entity e)
  | ext : ∀ x, TyWf (.ext x)
  | set : ∀ t, TyWf t → TyWf (.set t)
  | record : ∀ (m : Map Attr QualifiedType), (m.toList.map Prod.fst).Nodup →
      (∀ q ∈ m.toList.map Prod.snd, TyWfQ q) → TyWf (.record m)

/-- The qualified-type case of `TyWf`. -/
inductive TyWfQ : QualifiedType → Prop where
  | required : ∀ t, TyWf t → TyWfQ (.required t)
  | optional : ∀ t, TyWf t → TyWfQ (.optional t)
end

/-- Every entity type in the type is declared (the declaredness part of `CedarType.WellFormed`). -/
inductive TypeValid (env : TypeEnv) : CedarType → Prop where
  | bool : ∀ b, TypeValid env (.bool b)
  | int : TypeValid env .int
  | string : TypeValid env .string
  | ext : ∀ x, TypeValid env (.ext x)
  | entity : ∀ ety, ValidEntityType ety env.ets env.acts → TypeValid env (.entity ety)
  | set : ∀ ty, TypeValid env ty → TypeValid env (.set ty)
  | record : ∀ rts, (∀ p ∈ rts, TypeValid env p.2.getType) → TypeValid env (.record (Map.mk rts))

/-- The properties of a type environment on which `HasType` and `typeOf` agree. -/
structure EnvAssumptions (env : TypeEnv) : Prop where
  ets_keys_nodup : (env.ets.toList.map Prod.fst).Nodup
  acts_keys_nodup : (env.acts.toList.map Prod.fst).Nodup
  attrs_tyWf : ∀ {ety rty}, EntitySchema.attrs? env.ets ety = some rty → TyWf (.record rty)
  tags_tyWf : ∀ {ety ty}, EntitySchema.tags? env.ets ety = some (some ty) → TyWf ty
  context_tyWf : TyWf (.record env.reqty.context)
  attrs_typeValid :
    ∀ {ety rty}, EntitySchema.attrs? env.ets ety = some rty → TypeValid env (.record rty)
  tags_typeValid :
    ∀ {ety ty}, EntitySchema.tags? env.ets ety = some (some ty) → TypeValid env ty
  reqty_valid :
    ValidEntityType env.reqty.principal env.ets env.acts ∧
    ValidEntityType env.reqty.resource env.ets env.acts ∧
    ValidEntityType env.reqty.action.ty env.ets env.acts ∧
    TypeValid env (.record env.reqty.context)

end Cedar.Validation.Relational

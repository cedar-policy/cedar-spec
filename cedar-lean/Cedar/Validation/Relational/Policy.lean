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

/-! # Relational specification of policy validation

`ValidPolicy ets acts envs p` holds when `validate` accepts `p`. `ValidPolicyStrict` also requires
the policy to be in the image of the parser. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## The policy as an expression (`Policy.toExpr`) -/

/-- `Scope.toExpr`. -/
inductive ScopeExpr : Scope → Var → Expr → Prop where
  | any : ∀ v, ScopeExpr .any v (.lit (.bool true))
  | eq : ∀ uid v, ScopeExpr (.eq uid) v (.binaryApp .eq (.var v) (.lit (.entityUID uid)))
  | mem : ∀ uid v, ScopeExpr (.mem uid) v (.binaryApp .mem (.var v) (.lit (.entityUID uid)))
  | is : ∀ ety v, ScopeExpr (.is ety) v (.unaryApp (.is ety) (.var v))
  | isMem : ∀ ety uid v, ScopeExpr (.isMem ety uid) v
      (.and (.unaryApp (.is ety) (.var v)) (.binaryApp .mem (.var v) (.lit (.entityUID uid))))

/-- The entity-literal expressions for a list of UIDs. -/
inductive EntityUIDLits : List EntityUID → List Expr → Prop where
  | nil : EntityUIDLits [] []
  | cons : ∀ uid uids xs, EntityUIDLits uids xs →
      EntityUIDLits (uid :: uids) (.lit (.entityUID uid) :: xs)

/-- `ActionScope.toExpr`. -/
inductive ActionScopeExpr : ActionScope → Expr → Prop where
  | scope : ∀ s x, ScopeExpr s .action x → ActionScopeExpr (.actionScope s) x
  | inAny : ∀ uids xs, EntityUIDLits uids xs →
      ActionScopeExpr (.actionInAny uids) (.binaryApp .mem (.var .action) (.set xs))

/-- `Condition.toExpr`. -/
inductive ConditionExpr : Condition → Expr → Prop where
  | when : ∀ body, ConditionExpr ⟨.when, body⟩ body
  | unless : ∀ body, ConditionExpr ⟨.unless, body⟩ (.unaryApp .not body)

/-- `Conditions.toExpr`: the conditions joined by `&&` from the right, `true` when empty. -/
inductive ConditionsExpr : Conditions → Expr → Prop where
  | nil : ConditionsExpr [] (.lit (.bool true))
  | one : ∀ c x, ConditionExpr c x → ConditionsExpr [c] x
  | cons : ∀ c c' cs x rest, ConditionExpr c x → ConditionsExpr (c' :: cs) rest →
      ConditionsExpr (c :: c' :: cs) (.and x rest)

/-- `Policy.toExpr`. -/
inductive PolicyExpr : Policy → Expr → Prop where
  | mk : ∀ id eff ps as rs cs xp xa xr xc,
      ScopeExpr ps .principal xp →
      ActionScopeExpr as xa →
      ScopeExpr rs .resource xr →
      ConditionsExpr cs xc →
      PolicyExpr ⟨id, eff, .principalScope ps, as, .resourceScope rs, cs⟩
        (.and xp (.and xa (.and xr xc)))

/-! ## Replacing `action` by a literal (`substituteAction`) -/

mutual
/-- `substituteAction uid x = x'`. -/
inductive SubstAction : EntityUID → Expr → Expr → Prop where
  | lit : ∀ uid p, SubstAction uid (.lit p) (.lit p)
  | action : ∀ uid, SubstAction uid (.var .action) (.lit (.entityUID uid))
  | principal : ∀ uid, SubstAction uid (.var .principal) (.var .principal)
  | resource : ∀ uid, SubstAction uid (.var .resource) (.var .resource)
  | context : ∀ uid, SubstAction uid (.var .context) (.var .context)
  | ite : ∀ uid a b c a' b' c', SubstAction uid a a' → SubstAction uid b b' →
      SubstAction uid c c' → SubstAction uid (.ite a b c) (.ite a' b' c')
  | and : ∀ uid a b a' b', SubstAction uid a a' → SubstAction uid b b' →
      SubstAction uid (.and a b) (.and a' b')
  | or : ∀ uid a b a' b', SubstAction uid a a' → SubstAction uid b b' →
      SubstAction uid (.or a b) (.or a' b')
  | unaryApp : ∀ uid op a a', SubstAction uid a a' →
      SubstAction uid (.unaryApp op a) (.unaryApp op a')
  | binaryApp : ∀ uid op a b a' b', SubstAction uid a a' → SubstAction uid b b' →
      SubstAction uid (.binaryApp op a b) (.binaryApp op a' b')
  | getAttr : ∀ uid a k a', SubstAction uid a a' → SubstAction uid (.getAttr a k) (.getAttr a' k)
  | hasAttr : ∀ uid a k a', SubstAction uid a a' → SubstAction uid (.hasAttr a k) (.hasAttr a' k)
  | extHasAttr : ∀ uid a k ks a', SubstAction uid a a' →
      SubstAction uid (.extHasAttr a k ks) (.extHasAttr a' k ks)
  | set : ∀ uid xs xs', SubstActionList uid xs xs' → SubstAction uid (.set xs) (.set xs')
  | record : ∀ uid axs axs', SubstActionRecord uid axs axs' →
      SubstAction uid (.record axs) (.record axs')
  | call : ∀ uid f xs xs', SubstActionList uid xs xs' → SubstAction uid (.call f xs) (.call f xs')

/-- `SubstAction` on each expression of a list. -/
inductive SubstActionList : EntityUID → List Expr → List Expr → Prop where
  | nil : ∀ uid, SubstActionList uid [] []
  | cons : ∀ uid x xs x' xs', SubstAction uid x x' → SubstActionList uid xs xs' →
      SubstActionList uid (x :: xs) (x' :: xs')

/-- `SubstAction` on each field of a record literal. -/
inductive SubstActionRecord : EntityUID → List (Attr × Expr) → List (Attr × Expr) → Prop where
  | nil : ∀ uid, SubstActionRecord uid [] []
  | cons : ∀ uid a x axs x' axs', SubstAction uid x x' → SubstActionRecord uid axs axs' →
      SubstActionRecord uid ((a, x) :: axs) ((a, x') :: axs')
end

/-! ## Validation -/

/-- The policy expression is Boolean-typed in each of `envs`, with `action` replaced by that
    environment's action; `bs` are its types. -/
inductive TypedInEnvs (decl syn : Bool) : List TypeEnv → Expr → List BoolType → Prop where
  | nil : ∀ x, TypedInEnvs decl syn [] x []
  | cons : ∀ ets acts p act r ctx x x' b cout envs bs,
      SubstAction act x x' →
      HasType decl syn x' [] ⟨ets, acts, ⟨p, act, r, ctx⟩⟩ (.bool b) cout →
      TypedInEnvs decl syn envs x bs →
      TypedInEnvs decl syn (⟨ets, acts, ⟨p, act, r, ctx⟩⟩ :: envs) x (b :: bs)

/-- Some type in the list is not `.ff`. -/
inductive SomeNotFf : List BoolType → Prop where
  | here : ∀ b bs, NotFf b → SomeNotFf (b :: bs)
  | there : ∀ b bs, SomeNotFf bs → SomeNotFf (b :: bs)

/-- `validate` accepts `p` against `envs`, all sharing the schemas `ets` and `acts`. -/
inductive ValidPolicy : EntitySchema → ActionSchema → List TypeEnv → Policy → Prop where
  | mk : ∀ ets acts envs p x bs,
      PolicyExpr p x →
      EntitiesDeclared ets acts x →
      TypedInEnvs false false envs x bs →
      SomeNotFf bs →
      ValidPolicy ets acts envs p

/-- `ValidPolicy` with `HasType true true`: the policies `validate` accepts that the parser can
    produce (`validate_and_parserImage_iff_strict`). -/
inductive ValidPolicyStrict : EntitySchema → ActionSchema → List TypeEnv → Policy → Prop where
  | mk : ∀ ets acts envs p x bs,
      PolicyExpr p x →
      EntitiesDeclared ets acts x →
      TypedInEnvs true true envs x bs →
      SomeNotFf bs →
      ValidPolicyStrict ets acts envs p

end Cedar.Validation.Relational

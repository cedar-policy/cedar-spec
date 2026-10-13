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

import Cedar.Validation
import Cedar.Thm.Data
import Cedar.Thm.Validation.Pruning.EnvFilter

/-!
Template validation, and the exactness of pruning its slot candidates.

The Lean validator checks policies, not templates: a template is linked first
(`Template.link?`) and the resulting policy is validated. The Rust validator
instead typechecks a template once, without its links: for every request
environment and every candidate entity type for each slot
(`possible_slot_links` in `cedar-policy-core/src/validator/typecheck.rs`) it
types the template with the slot standing for an entity of that type. Links are
not typechecked again.

This file models that check. A slot of type `T` is instantiated with a
representative entity `rep T` of type `T`; the typechecker reads a slot entity
only through its type, so the choice of representative does not matter. A
template's outcome is the `classify` of the results over a list of
(environment, principal slot type, resource slot type) combinations.

Results:

* `template_filter_exact`: any set of combinations that keeps, for every
  environment, the combination whose slot types are that environment's own
  principal and resource types classifies the template exactly like the full
  set. Rust's `possible_slot_links` (`rust_candidates_exact`) and one-link
  pruning, which keeps only that combination (`one_link_exact`), are both
  instances.
* `template_type_error_iff`: the template has a type error exactly when some
  link with valid entities of candidate types has a type error in some
  environment. So template validation is sound (`template_sound`) and no
  stricter than validating every link.

The classification counts errors rather than reporting the first one, so it
does not depend on the order in which combinations are checked.
-/

namespace Cedar.Thm.Pruning

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

----- Instantiating a template -----

def _root_.Cedar.Spec.EntityUIDOrSlot.inst (u : EntityUID) : EntityUIDOrSlot → EntityUID
  | .entityUID e => e
  | .slot _      => u

/-- Replace the slot, if any, in a scope template by `u`. -/
def _root_.Cedar.Spec.ScopeTemplate.inst (u : EntityUID) : ScopeTemplate → Scope
  | .any          => .any
  | .eq x         => .eq (x.inst u)
  | .mem x        => .mem (x.inst u)
  | .is ety       => .is ety
  | .isMem ety x  => .isMem ety (x.inst u)

def _root_.Cedar.Spec.PrincipalScopeTemplate.scope : PrincipalScopeTemplate → ScopeTemplate
  | .principalScope s => s

def _root_.Cedar.Spec.ResourceScopeTemplate.scope : ResourceScopeTemplate → ScopeTemplate
  | .resourceScope s => s

/-- The policy obtained from `t` with principal slot `u` and resource slot `v`. -/
def _root_.Cedar.Spec.Template.inst (t : Template) (id : PolicyID) (u v : EntityUID) : Policy where
  id             := id
  effect         := t.effect
  principalScope := .principalScope (t.principalScope.scope.inst u)
  actionScope    := t.actionScope
  resourceScope  := .resourceScope (t.resourceScope.scope.inst v)
  condition      := t.condition

----- Classifying results -----

inductive Outcome where
  | typeError
  | impossible
  | ok
deriving DecidableEq, Repr

def isErr {ε α} : Except ε α → Bool
  | .error _ => true
  | .ok _    => false

def isFF {ε} : Except ε TypedExpr → Bool
  | .ok tx   => tx.typeOf == .bool .ff
  | .error _ => false

/-- A type error if any result is an error, else impossible if every result is `false`. -/
def classify {ε} (rs : List (Except ε TypedExpr)) : Outcome :=
  if rs.any isErr then .typeError
  else if rs.all isFF then .impossible
  else .ok

----- The template validator -----

/-- A combination: an environment and a candidate type for each slot. -/
abbrev Combo := TypeEnv × EntityType × EntityType

def allCombos (schema : Schema) (tys : List EntityType) : List Combo :=
  schema.environments.flatMap λ env => tys.flatMap λ pT => tys.map λ rT => (env, pT, rT)

def comboResult (t : Template) (id : PolicyID) (rep : EntityType → EntityUID) : Combo → Except ValidationError TypedExpr
  | (env, pT, rT) => typecheckPolicy (t.inst id (rep pT) (rep rT)) env

/-- Typecheck `t` on the combinations `keep` selects and classify the results. -/
def templateOutcome (keep : Combo → Bool) (t : Template) (id : PolicyID) (rep : EntityType → EntityUID)
  (schema : Schema) (tys : List EntityType) : Outcome :=
  classify (((allCombos schema tys).filter keep).map (comboResult t id rep))

/-- Rust's `possible_slot_links` for one slot, for a variable of type `ety`. -/
def rustSlotCandidate (env : TypeEnv) (ety : EntityType) : ScopeTemplate → EntityType → Bool
  | .eq (.slot _), T        => T == ety
  | .mem (.slot _), T       => env.descendentOf ety T
  | .isMem _ (.slot _), T   => env.descendentOf ety T
  | _, _                    => true

def rustKeep (t : Template) : Combo → Bool
  | (env, pT, rT) =>
    rustSlotCandidate env env.reqty.principal t.principalScope.scope pT &&
    rustSlotCandidate env env.reqty.resource t.resourceScope.scope rT

/-- One link per environment: each slot takes the type of its own variable. -/
def oneLinkKeep : Combo → Bool
  | (env, pT, rT) => pT == env.reqty.principal && rT == env.reqty.resource

----- Scope typing -----

def validUID (env : TypeEnv) (uid : EntityUID) : Bool :=
  env.ets.isValidEntityUID uid || env.acts.contains uid

/-- Every entity literal in the scope is valid. -/
def _root_.Cedar.Spec.Scope.uidsValid (env : TypeEnv) : Scope → Bool
  | .any          => true
  | .eq uid       => validUID env uid
  | .mem uid      => validUID env uid
  | .is _         => true
  | .isMem _ uid  => validUID env uid

/-- Every entity literal (not slot) in the scope template is valid. -/
def _root_.Cedar.Spec.ScopeTemplate.litsValid (env : TypeEnv) : ScopeTemplate → Bool
  | .eq (.entityUID e)       => validUID env e
  | .mem (.entityUID e)      => validUID env e
  | .isMem _ (.entityUID e)  => validUID env e
  | _                        => true

/-- The type of a principal or resource scope for a variable of type `ety`. -/
def scopeBool (env : TypeEnv) (ety : EntityType) : Scope → BoolType
  | .any            => .tt
  | .eq uid         => if ety = uid.ty then .anyBool else .ff
  | .mem uid        => if env.descendentOf ety uid.ty then .anyBool else .ff
  | .is ety'        => if ety' = ety then .tt else .ff
  | .isMem ety' uid => if ety' = ety then (if env.descendentOf ety uid.ty then .anyBool else .ff) else .ff

theorem scope_typed_exact {env : TypeEnv} {s : Scope} {v : Var} {ety : EntityType} {a : EntityUID}
  {c : Capabilities}
  (hvar : (v = .principal ∧ ety = env.reqty.principal) ∨ (v = .resource ∧ ety = env.reqty.resource))
  (hv : s.uidsValid env = true) :
  ∃ tx, typeOf (substituteAction a (s.toExpr v)) c env = .ok (tx, ∅) ∧
    tx.typeOf = .bool (scopeBool env ety s) := by
  rcases hvar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  cases s with
  | any => simp [Scope.toExpr, substituteAction, mapOnVars, typeOf, typeOfLit, ok, TypedExpr.typeOf, scopeBool]
  | eq uid =>
    simp only [Scope.uidsValid, validUID] at hv
    simp only [Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfEq, ok, TypedExpr.typeOf, lub?, scopeBool]
    split <;> simp_all
  | mem uid =>
    simp only [Scope.uidsValid, validUID] at hv
    simp only [Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, ok, TypedExpr.typeOf, scopeBool]
  | is ety' =>
    simp [Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars, typeOf, typeOfVar, typeOfUnaryApp, ok,
      TypedExpr.typeOf, scopeBool]
  | isMem ety' uid =>
    simp only [Scope.uidsValid, validUID] at hv
    simp only [Scope.toExpr, Var.inEntityUID, Var.isEntityType, substituteAction, mapOnVars, typeOf,
      typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfUnaryApp, typeOfInₑ, actionUID?, entityUID?, typeOfAnd, ok,
      TypedExpr.typeOf, scopeBool]
    first
    | (by_cases h1 : ety' = env.reqty.principal <;>
       by_cases h2 : env.descendentOf env.reqty.principal uid.ty = true <;> simp [h1, h2])
    | (by_cases h1 : ety' = env.reqty.resource <;>
       by_cases h2 : env.descendentOf env.reqty.resource uid.ty = true <;> simp [h1, h2])

theorem inst_uidsValid {env : TypeEnv} {s : ScopeTemplate} {u : EntityUID}
  (hs : s.litsValid env = true) (hu : validUID env u = true) :
  (s.inst u).uidsValid env = true := by
  cases s with
  | any => rfl
  | is _ => rfl
  | eq x | mem x | isMem _ x => cases x <;> simp_all [ScopeTemplate.inst, ScopeTemplate.litsValid,
      EntityUIDOrSlot.inst, Scope.uidsValid]

/-- A slot entity matters to `scopeBool` only through its type. -/
theorem scopeBool_inst_ty (env : TypeEnv) (ety : EntityType) (s : ScopeTemplate) {u₁ u₂ : EntityUID}
  (h : u₁.ty = u₂.ty) :
  scopeBool env ety (s.inst u₁) = scopeBool env ety (s.inst u₂) := by
  cases s with
  | any => rfl
  | is _ => rfl
  | eq x | mem x | isMem _ x => cases x <;> simp [ScopeTemplate.inst, EntityUIDOrSlot.inst, scopeBool, h]

theorem descendentOf_refl (env : TypeEnv) (ety : EntityType) : env.descendentOf ety ety = true := by
  simp [TypeEnv.descendentOf]

/--
Moving a slot to its variable's own type either leaves the scope's type
unchanged, or the scope was `false` already.
-/
theorem scopeBool_own_type (env : TypeEnv) (ety : EntityType) (s : ScopeTemplate) {u₁ u₂ : EntityUID}
  (h₂ : u₂.ty = ety) :
  scopeBool env ety (s.inst u₁) = .ff ∨ scopeBool env ety (s.inst u₁) = scopeBool env ety (s.inst u₂) := by
  cases s with
  | any => exact Or.inr rfl
  | is _ => exact Or.inr rfl
  | eq x | mem x | isMem _ x =>
    cases x with
    | entityUID _ => simp [ScopeTemplate.inst, EntityUIDOrSlot.inst]
    | slot _ =>
      simp only [ScopeTemplate.inst, EntityUIDOrSlot.inst, scopeBool, h₂, descendentOf_refl]
      split <;> simp_all

----- Relating two typings -----

/-- Both fail, or both succeed with the same type and capabilities. -/
def TyEq (r₁ r₂ : ResultType) : Prop :=
  match r₁, r₂ with
  | .error _, .error _         => True
  | .ok (t₁, c₁), .ok (t₂, c₂) => t₁.typeOf = t₂.typeOf ∧ c₁ = c₂
  | _, _                       => False

/-- The first types as `false`, or the second fails. -/
def Dom (r₁ r₂ : ResultType) : Prop :=
  (match r₁ with | .ok (t, _) => t.typeOf = .bool .ff | .error _ => False) ∨
  (match r₂ with | .error _ => True | .ok _ => False)

theorem typeOfAnd_tyeq_left {t₁ t₂ : TypedExpr} {c : Capabilities} {r : ResultType}
  (h : t₁.typeOf = t₂.typeOf) :
  TyEq (typeOfAnd (t₁, c) r) (typeOfAnd (t₂, c) r) := by
  unfold typeOfAnd
  simp only [h]
  split
  · simp [ok, TyEq, h]
  · cases r with
    | error _ => simp [bind, Except.bind, TyEq]
    | ok p =>
      simp only [bind, Except.bind]
      split <;> simp [ok, err, TyEq, TypedExpr.typeOf]
  · simp [err, TyEq]

theorem typeOfAnd_tyeq_right {t : TypedExpr} {c : Capabilities} {r₁ r₂ : ResultType}
  (h : TyEq r₁ r₂) :
  TyEq (typeOfAnd (t, c) r₁) (typeOfAnd (t, c) r₂) := by
  unfold typeOfAnd
  split
  · simp [ok, TyEq]
  · cases r₁ <;> cases r₂ <;> simp only [TyEq] at h
    · simp [bind, Except.bind, TyEq]
    · rename_i p₁ p₂
      obtain ⟨t₁, c₁⟩ := p₁
      obtain ⟨t₂, c₂⟩ := p₂
      obtain ⟨ht, rfl⟩ := h
      simp only [bind, Except.bind, ht]
      split <;> simp [ok, err, TyEq, TypedExpr.typeOf]
  · simp [err, TyEq]

theorem typeOfAnd_dom_right {t : TypedExpr} {c : Capabilities} {r₁ r₂ : ResultType}
  (h : Dom r₁ r₂) :
  Dom (typeOfAnd (t, c) r₁) (typeOfAnd (t, c) r₂) := by
  unfold typeOfAnd
  split
  · simp [ok, Dom, *]
  · rcases h with h | h
    · cases r₁ with
      | error _ => simp at h
      | ok p₁ =>
        obtain ⟨t₁, c₁⟩ := p₁
        simp only at h
        left
        simp only [bind, Except.bind, h]
        simp [ok, TypedExpr.typeOf]
    · cases r₂ with
      | ok _ => simp at h
      | error _ =>
        right
        simp [bind, Except.bind]
  · simp [err, Dom]

theorem and_tyeq_left {x x' y : Expr} {env : TypeEnv}
  (h : ∀ c, TyEq (typeOf x c env) (typeOf x' c env)) :
  ∀ c, TyEq (typeOf (.and x y) c env) (typeOf (.and x' y) c env) := by
  intro c
  have hc := h c
  rw [typeOf_and, typeOf_and]
  cases h₁ : typeOf x c env <;> cases h₂ : typeOf x' c env <;> rw [h₁, h₂] at hc <;> simp only [TyEq] at hc
  · simp [Except.bind, TyEq]
  · rename_i p₁ p₂
    obtain ⟨t₁, c₁⟩ := p₁
    obtain ⟨t₂, c₂⟩ := p₂
    obtain ⟨ht, rfl⟩ := hc
    exact typeOfAnd_tyeq_left ht

theorem and_tyeq_right {x y y' : Expr} {env : TypeEnv}
  (h : ∀ c, TyEq (typeOf y c env) (typeOf y' c env)) :
  ∀ c, TyEq (typeOf (.and x y) c env) (typeOf (.and x y') c env) := by
  intro c
  rw [typeOf_and, typeOf_and]
  cases typeOf x c env with
  | error _ => simp [Except.bind, TyEq]
  | ok p => exact typeOfAnd_tyeq_right (h _)

theorem and_dom_right {x y y' : Expr} {env : TypeEnv}
  (h : ∀ c, Dom (typeOf y c env) (typeOf y' c env)) :
  ∀ c, Dom (typeOf (.and x y) c env) (typeOf (.and x y') c env) := by
  intro c
  rw [typeOf_and, typeOf_and]
  cases typeOf x c env with
  | error _ => simp [Except.bind, Dom]
  | ok p => exact typeOfAnd_dom_right (h _)

theorem and_dom_of_false {x y y' : Expr} {env : TypeEnv} (h : TypesFalse x env) :
  ∀ c, Dom (typeOf (.and x y) c env) (typeOf (.and x' y') c env) := by
  intro c
  obtain ⟨tx, c', hx, ht⟩ := and_false_of_left (y := y) h c
  left
  rw [hx]
  exact ht

----- Relating two typechecks -----

/-- An error in the first is an error in the second, and `false` in the second is `false` in the first. -/
def W {ε} (r₁ r₂ : Except ε TypedExpr) : Prop :=
  (isErr r₁ = true → isErr r₂ = true) ∧ (isFF r₂ = true → isFF r₁ = true)

theorem W_trans {ε} {r₁ r₂ r₃ : Except ε TypedExpr} (h₁ : W r₁ r₂) (h₂ : W r₂ r₃) : W r₁ r₃ :=
  ⟨h₂.1 ∘ h₁.1, h₁.2 ∘ h₂.2⟩

theorem W_of_isFF {ε} {r₁ r₂ : Except ε TypedExpr} (h : isFF r₁ = true) : W r₁ r₂ := by
  refine ⟨λ he => ?_, λ _ => h⟩
  cases r₁ <;> simp [isFF, isErr] at h he

theorem typecheck_W_of_tyeq {p₁ p₂ : Policy} {env : TypeEnv}
  (h : TyEq (typeOf (substituteAction env.reqty.action p₁.toExpr) ∅ env)
            (typeOf (substituteAction env.reqty.action p₂.toExpr) ∅ env)) :
  W (typecheckPolicy p₁ env) (typecheckPolicy p₂ env) ∧ W (typecheckPolicy p₂ env) (typecheckPolicy p₁ env) := by
  simp only [typecheckPolicy]
  cases h₁ : typeOf (substituteAction env.reqty.action p₁.toExpr) ∅ env <;>
  cases h₂ : typeOf (substituteAction env.reqty.action p₂.toExpr) ∅ env <;>
  rw [h₁, h₂] at h <;> simp only [TyEq] at h
  · simp [W, isErr, isFF]
  · rename_i q₁ q₂
    obtain ⟨t₁, c₁⟩ := q₁
    obtain ⟨t₂, c₂⟩ := q₂
    obtain ⟨ht, _⟩ := h
    simp only [ht]
    split <;> simp_all [W, isErr, isFF]

theorem typecheck_W_of_dom {p₁ p₂ : Policy} {env : TypeEnv}
  (h : Dom (typeOf (substituteAction env.reqty.action p₁.toExpr) ∅ env)
           (typeOf (substituteAction env.reqty.action p₂.toExpr) ∅ env)) :
  W (typecheckPolicy p₁ env) (typecheckPolicy p₂ env) := by
  rcases h with h | h
  · apply W_of_isFF
    simp only [typecheckPolicy]
    cases hr : typeOf (substituteAction env.reqty.action p₁.toExpr) ∅ env with
    | error _ => rw [hr] at h; simp at h
    | ok p =>
      obtain ⟨t, c⟩ := p
      rw [hr] at h
      simp only at h
      simp [h, subty, lub?, lubBool, isFF]
  · refine ⟨λ _ => ?_, λ hf => ?_⟩
    · simp only [typecheckPolicy]
      cases hr : typeOf (substituteAction env.reqty.action p₂.toExpr) ∅ env with
      | error _ => simp [isErr]
      | ok _ => rw [hr] at h; simp at h
    · simp only [typecheckPolicy] at hf
      cases hr : typeOf (substituteAction env.reqty.action p₂.toExpr) ∅ env with
      | error _ => rw [hr] at hf; simp [isFF] at hf
      | ok _ => rw [hr] at h; simp at h

----- Changing one slot -----

theorem inst_expr (t : Template) (id : PolicyID) (u v : EntityUID) (a : EntityUID) :
  substituteAction a (t.inst id u v).toExpr =
    .and (substituteAction a ((t.principalScope.scope.inst u).toExpr .principal))
      (.and (substituteAction a t.actionScope.toExpr)
        (.and (substituteAction a ((t.resourceScope.scope.inst v).toExpr .resource))
          (substituteAction a t.condition.toExpr))) := by
  rw [substituteAction_policy]
  simp [Template.inst, PrincipalScope.toExpr, ResourceScope.toExpr]

/-- The typings of two scopes with equal `scopeBool` agree under every capability set. -/
theorem scope_tyeq {env : TypeEnv} {s₁ s₂ : Scope} {v : Var} {ety : EntityType} {a : EntityUID}
  (hvar : (v = .principal ∧ ety = env.reqty.principal) ∨ (v = .resource ∧ ety = env.reqty.resource))
  (hv₁ : s₁.uidsValid env = true) (hv₂ : s₂.uidsValid env = true)
  (hb : scopeBool env ety s₁ = scopeBool env ety s₂) :
  ∀ c, TyEq (typeOf (substituteAction a (s₁.toExpr v)) c env) (typeOf (substituteAction a (s₂.toExpr v)) c env) := by
  intro c
  obtain ⟨tx₁, h₁, ht₁⟩ := scope_typed_exact (a := a) (c := c) hvar hv₁
  obtain ⟨tx₂, h₂, ht₂⟩ := scope_typed_exact (a := a) (c := c) hvar hv₂
  rw [h₁, h₂]
  simp [TyEq, ht₁, ht₂, hb]

theorem scope_false {env : TypeEnv} {s : Scope} {v : Var} {ety : EntityType} {a : EntityUID}
  (hvar : (v = .principal ∧ ety = env.reqty.principal) ∨ (v = .resource ∧ ety = env.reqty.resource))
  (hv : s.uidsValid env = true) (hb : scopeBool env ety s = .ff) :
  TypesFalse (substituteAction a (s.toExpr v)) env := by
  intro c
  obtain ⟨tx, h, ht⟩ := scope_typed_exact (a := a) (c := c) hvar hv
  exact ⟨tx, ∅, h, by rw [ht, hb]⟩

/--
Changing the principal slot from `u₁` to `u₂`: if the principal scope with `u₁`
types as `false`, or as the same type as with `u₂`, an error with `u₁` is an
error with `u₂` and `false` with `u₂` is `false` with `u₁`.
-/
theorem principal_W {env : TypeEnv} {t : Template} {id : PolicyID} {u₁ u₂ v : EntityUID}
  (hs : t.principalScope.scope.litsValid env = true)
  (hu₁ : validUID env u₁ = true) (hu₂ : validUID env u₂ = true)
  (hb : scopeBool env env.reqty.principal (t.principalScope.scope.inst u₁) = .ff ∨
        scopeBool env env.reqty.principal (t.principalScope.scope.inst u₁) =
        scopeBool env env.reqty.principal (t.principalScope.scope.inst u₂)) :
  W (typecheckPolicy (t.inst id u₁ v) env) (typecheckPolicy (t.inst id u₂ v) env) := by
  have hvar : (Var.principal = .principal ∧ env.reqty.principal = env.reqty.principal) ∨
      (Var.principal = .resource ∧ env.reqty.principal = env.reqty.resource) := Or.inl ⟨rfl, rfl⟩
  rcases hb with hb | hb
  · apply W_of_isFF
    have hf := and_false_of_left
      (y := .and (substituteAction env.reqty.action t.actionScope.toExpr)
        (.and (substituteAction env.reqty.action ((t.resourceScope.scope.inst v).toExpr .resource))
          (substituteAction env.reqty.action t.condition.toExpr)))
      (scope_false (a := env.reqty.action) hvar (inst_uidsValid hs hu₁) hb)
    rw [← inst_expr t id] at hf
    obtain ⟨tx, htx, hff⟩ := typecheck_of_false hf
    simp [htx, isFF, hff]
  · apply And.left
    apply typecheck_W_of_tyeq
    rw [inst_expr, inst_expr]
    exact and_tyeq_left (scope_tyeq hvar (inst_uidsValid hs hu₁) (inst_uidsValid hs hu₂) hb) ∅

/-- The same for the resource slot. -/
theorem resource_W {env : TypeEnv} {t : Template} {id : PolicyID} {u v₁ v₂ : EntityUID}
  (hs : t.resourceScope.scope.litsValid env = true)
  (hv₁ : validUID env v₁ = true) (hv₂ : validUID env v₂ = true)
  (hb : scopeBool env env.reqty.resource (t.resourceScope.scope.inst v₁) = .ff ∨
        scopeBool env env.reqty.resource (t.resourceScope.scope.inst v₁) =
        scopeBool env env.reqty.resource (t.resourceScope.scope.inst v₂)) :
  W (typecheckPolicy (t.inst id u v₁) env) (typecheckPolicy (t.inst id u v₂) env) := by
  have hvar : (Var.resource = .principal ∧ env.reqty.resource = env.reqty.principal) ∨
      (Var.resource = .resource ∧ env.reqty.resource = env.reqty.resource) := Or.inr ⟨rfl, rfl⟩
  rcases hb with hb | hb
  · apply typecheck_W_of_dom
    rw [inst_expr, inst_expr]
    apply and_dom_right
    apply and_dom_right
    exact and_dom_of_false (scope_false hvar (inst_uidsValid hs hv₁) hb)
  · apply And.left
    apply typecheck_W_of_tyeq
    rw [inst_expr, inst_expr]
    apply and_tyeq_right
    apply and_tyeq_right
    exact and_tyeq_left (scope_tyeq hvar (inst_uidsValid hs hv₁) (inst_uidsValid hs hv₂) hb)

----- Classification is preserved by dropping dominated results -----

theorem classify_typeError {ε} (rs : List (Except ε TypedExpr)) :
  classify rs = .typeError ↔ rs.any isErr = true := by
  unfold classify
  split
  · simp_all
  · split <;> simp_all

/--
Dropping an element whose result is related by `W` to the result of a kept
element changes neither whether some result is an error nor whether every
result is `false`.
-/
theorem classify_filter {α ε} (f : α → Except ε TypedExpr) (keep : α → Bool) (xs : List α)
  (h : ∀ x ∈ xs, keep x = false → ∃ x' ∈ xs, keep x' = true ∧ W (f x) (f x')) :
  classify ((xs.filter keep).map f) = classify (xs.map f) := by
  have hany : ((xs.filter keep).map f).any isErr = (xs.map f).any isErr := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨r, ⟨x, ⟨hx, _⟩, rfl⟩, he⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, he⟩
    · rintro ⟨r, ⟨x, hx, rfl⟩, he⟩
      cases hk : keep x
      · obtain ⟨x', hx', hk', hw⟩ := h x hx hk
        exact ⟨f x', ⟨x', ⟨hx', hk'⟩, rfl⟩, hw.1 he⟩
      · exact ⟨f x, ⟨x, ⟨hx, hk⟩, rfl⟩, he⟩
  have hall : ((xs.filter keep).map f).all isFF = (xs.map f).all isFF := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_map, List.mem_filter]
    constructor
    · rintro hk r ⟨x, hx, rfl⟩
      cases hkx : keep x
      · obtain ⟨x', hx', hk', hw⟩ := h x hx hkx
        exact hw.2 (hk (f x') ⟨x', ⟨hx', hk'⟩, rfl⟩)
      · exact hk (f x) ⟨x, ⟨hx, hkx⟩, rfl⟩
    · rintro hk r ⟨x, ⟨hx, _⟩, rfl⟩
      exact hk (f x) ⟨x, hx, rfl⟩
  simp only [classify, hany, hall]

/-- Dropping results that are `false` changes nothing. -/
theorem classify_filter_ff {α ε} (f : α → Except ε TypedExpr) (keep : α → Bool) (xs : List α)
  (h : ∀ x ∈ xs, keep x = false → isFF (f x) = true) :
  classify ((xs.filter keep).map f) = classify (xs.map f) := by
  have hany : ((xs.filter keep).map f).any isErr = (xs.map f).any isErr := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨r, ⟨x, ⟨hx, _⟩, rfl⟩, he⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, he⟩
    · rintro ⟨r, ⟨x, hx, rfl⟩, he⟩
      cases hk : keep x
      · have hf := h x hx hk
        cases hfx : f x <;> simp [hfx, isFF, isErr] at hf he
      · exact ⟨f x, ⟨x, ⟨hx, hk⟩, rfl⟩, he⟩
  have hall : ((xs.filter keep).map f).all isFF = (xs.map f).all isFF := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_map, List.mem_filter]
    constructor
    · rintro hk r ⟨x, hx, rfl⟩
      cases hkx : keep x
      · exact h x hx hkx
      · exact hk (f x) ⟨x, ⟨hx, hkx⟩, rfl⟩
    · rintro hk r ⟨x, ⟨hx, _⟩, rfl⟩
      exact hk (f x) ⟨x, hx, rfl⟩
  simp only [classify, hany, hall]

theorem mem_allCombos {schema : Schema} {tys : List EntityType} {env : TypeEnv} {pT rT : EntityType} :
  (env, pT, rT) ∈ allCombos schema tys ↔ env ∈ schema.environments ∧ pT ∈ tys ∧ rT ∈ tys := by
  simp only [allCombos, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨_, h₁, _, h₂, _, h₃, rfl, rfl, rfl⟩
    exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨_, h₁, _, h₂, _, h₃, rfl, rfl, rfl⟩

theorem filter_true' {α} (l : List α) : l.filter (λ _ => true) = l := by simp

----- Main theorems -----

def schemaValidUID (schema : Schema) (uid : EntityUID) : Bool :=
  schema.ets.isValidEntityUID uid || schema.acts.contains uid

theorem validUID_env {schema : Schema} {env : TypeEnv} (henv : env ∈ schema.environments) (uid : EntityUID) :
  validUID env uid = schemaValidUID schema uid := by
  obtain ⟨hets, hacts, _⟩ := env_mem henv
  simp [validUID, schemaValidUID, hets, hacts]

/-- `rep` picks a valid entity of each candidate type. -/
def RepValid (schema : Schema) (tys : List EntityType) (rep : EntityType → EntityUID) : Prop :=
  ∀ T ∈ tys, (rep T).ty = T ∧ schemaValidUID schema (rep T) = true

/-- Every environment's principal and resource types are candidates. -/
def TysCover (schema : Schema) (tys : List EntityType) : Prop :=
  ∀ env ∈ schema.environments, env.reqty.principal ∈ tys ∧ env.reqty.resource ∈ tys

/-- The template's own entity literals in its scopes are valid. -/
def LitsValid (schema : Schema) (t : Template) : Prop :=
  ∀ env ∈ schema.environments,
    t.principalScope.scope.litsValid env = true ∧ t.resourceScope.scope.litsValid env = true

/--
Any set of slot combinations that keeps, for every environment, the one whose
slot types are the environment's own principal and resource types classifies
the template exactly like the full set.
-/
theorem template_filter_exact (keep : Combo → Bool) (t : Template) (id : PolicyID)
  (rep : EntityType → EntityUID) (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t)
  (hkeep : ∀ env ∈ schema.environments, keep (env, env.reqty.principal, env.reqty.resource) = true) :
  templateOutcome keep t id rep schema tys = templateOutcome (λ _ => true) t id rep schema tys := by
  unfold templateOutcome
  rw [filter_true']
  apply classify_filter
  rintro ⟨env, pT, rT⟩ hx _
  obtain ⟨henv, hpT, hrT⟩ := mem_allCombos.mp hx
  obtain ⟨hpTy, hrTy⟩ := htys env henv
  obtain ⟨hls, hlr⟩ := hlits env henv
  have hv : ∀ T ∈ tys, validUID env (rep T) = true := λ T hT => by
    rw [validUID_env henv]; exact (hrep T hT).2
  refine ⟨(env, env.reqty.principal, env.reqty.resource), mem_allCombos.mpr ⟨henv, hpTy, hrTy⟩,
    hkeep env henv, ?_⟩
  simp only [comboResult]
  exact W_trans
    (principal_W hls (hv pT hpT) (hv _ hpTy) (scopeBool_own_type _ _ _ (hrep _ hpTy).1))
    (resource_W hlr (hv rT hrT) (hv _ hrTy) (scopeBool_own_type _ _ _ (hrep _ hrTy).1))

theorem rustSlotCandidate_self (env : TypeEnv) (ety : EntityType) (s : ScopeTemplate) :
  rustSlotCandidate env ety s ety = true := by
  unfold rustSlotCandidate
  split <;> simp_all [descendentOf_refl]

/-- Rust's `possible_slot_links` pruning is exact. -/
theorem rust_candidates_exact (t : Template) (id : PolicyID) (rep : EntityType → EntityUID)
  (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t) :
  templateOutcome (rustKeep t) t id rep schema tys = templateOutcome (λ _ => true) t id rep schema tys :=
  template_filter_exact _ _ _ _ _ _ hrep htys hlits
    (λ env _ => by simp [rustKeep, rustSlotCandidate_self])

/-- One link per environment, at the variables' own types, is exact. -/
theorem one_link_exact (t : Template) (id : PolicyID) (rep : EntityType → EntityUID)
  (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t) :
  templateOutcome oneLinkKeep t id rep schema tys = templateOutcome (λ _ => true) t id rep schema tys :=
  template_filter_exact _ _ _ _ _ _ hrep htys hlits (λ env _ => by simp [oneLinkKeep])

/--
One link per environment, further restricted to environments whose scope can
admit that link (`admitsAll` from `EnvFilter`), is exact. A filter that keeps
more environments than `admitsAll` requires is exact too. This is the check the
Rust validator runs.
-/
theorem one_link_admitted_exact (keepEnv : TypeEnv → Bool) (t : Template) (id : PolicyID)
  (rep : EntityType → EntityUID) (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t)
  (hce : ∀ env ∈ schema.environments,
    checkEntities schema (t.inst id (rep env.reqty.principal) (rep env.reqty.resource)).toExpr = .ok ())
  (hkeepEnv : ∀ env ∈ schema.environments,
    admitsAll (t.inst id (rep env.reqty.principal) (rep env.reqty.resource)) env = true → keepEnv env = true) :
  templateOutcome (λ x => oneLinkKeep x && keepEnv x.1) t id rep schema tys =
  templateOutcome (λ _ => true) t id rep schema tys := by
  rw [← one_link_exact t id rep schema tys hrep htys hlits]
  unfold templateOutcome
  have hfilter : (allCombos schema tys).filter (λ x => oneLinkKeep x && keepEnv x.1) =
      ((allCombos schema tys).filter oneLinkKeep).filter (λ x => keepEnv x.1) := by
    rw [List.filter_filter]
    congr 1
    funext x
    exact Bool.and_comm _ _
  rw [hfilter]
  apply classify_filter_ff
  rintro ⟨env, pT, rT⟩ hx hk
  obtain ⟨hx, hol⟩ := List.mem_filter.mp hx
  obtain ⟨henv, _, _⟩ := mem_allCombos.mp hx
  simp only [oneLinkKeep, Bool.and_eq_true, beq_iff_eq] at hol
  obtain ⟨rfl, rfl⟩ := hol
  have hadm : admitsAll (t.inst id (rep env.reqty.principal) (rep env.reqty.resource)) env = false := by
    cases ha : admitsAll (t.inst id (rep env.reqty.principal) (rep env.reqty.resource)) env
    · rfl
    · simp [hkeepEnv env henv ha] at hk
  obtain ⟨tx, htx, hff⟩ := typecheck_unadmitted_is_false (hce env henv) henv hadm
  simp [comboResult, htx, isFF, hff]

/--
Under any exact filter, the template has a type error exactly when some
instantiation with valid entities of candidate types has a type error in some
environment.
-/
theorem template_type_error_iff (keep : Combo → Bool) (t : Template) (id : PolicyID)
  (rep : EntityType → EntityUID) (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t)
  (hkeep : ∀ env ∈ schema.environments, keep (env, env.reqty.principal, env.reqty.resource) = true) :
  templateOutcome keep t id rep schema tys = .typeError ↔
  ∃ env ∈ schema.environments, ∃ u v,
    u.ty ∈ tys ∧ v.ty ∈ tys ∧ schemaValidUID schema u = true ∧ schemaValidUID schema v = true ∧
    isErr (typecheckPolicy (t.inst id u v) env) = true := by
  rw [template_filter_exact keep t id rep schema tys hrep htys hlits hkeep]
  unfold templateOutcome
  rw [filter_true', classify_typeError]
  simp only [List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨r, ⟨⟨env, pT, rT⟩, hx, rfl⟩, he⟩
    obtain ⟨henv, hpT, hrT⟩ := mem_allCombos.mp hx
    refine ⟨env, henv, rep pT, rep rT, ?_, ?_, (hrep pT hpT).2, (hrep rT hrT).2, he⟩
    · rw [(hrep pT hpT).1]; exact hpT
    · rw [(hrep rT hrT).1]; exact hrT
  · rintro ⟨env, henv, u, v, hu, hv, huv, hvv, he⟩
    obtain ⟨hls, hlr⟩ := hlits env henv
    have hval : ∀ w, schemaValidUID schema w = true → validUID env w = true := λ w hw => by
      rw [validUID_env henv]; exact hw
    have hw := W_trans
      (principal_W (id := id) (v := v) hls (hval u huv) (hval _ (hrep _ hu).2)
        (Or.inr (scopeBool_inst_ty _ _ _ (hrep _ hu).1.symm)))
      (resource_W (id := id) (u := rep u.ty) hlr (hval v hvv) (hval _ (hrep _ hv).2)
        (Or.inr (scopeBool_inst_ty _ _ _ (hrep _ hv).1.symm)))
    exact ⟨_, ⟨(env, u.ty, v.ty), mem_allCombos.mpr ⟨henv, hu, hv⟩, rfl⟩, hw.1 he⟩

----- Links -----

theorem uidOrSlot_link {slotEnv : SlotEnv} {x : EntityUIDOrSlot} {e : EntityUID}
  (h : x.link? slotEnv = .ok e) (u₀ : EntityUID) :
  ∃ u, e = x.inst u ∧ (u = u₀ ∨ ∃ sid, slotEnv.find? sid = some u) := by
  cases x with
  | entityUID e' =>
    simp only [EntityUIDOrSlot.link?, Except.ok.injEq] at h
    exact ⟨u₀, by simp [EntityUIDOrSlot.inst, h], Or.inl rfl⟩
  | slot sid =>
    simp only [EntityUIDOrSlot.link?, Map.findOrErr] at h
    cases hf : slotEnv.find? sid with
    | none => simp [hf] at h
    | some w =>
      simp only [hf, Except.ok.injEq] at h
      exact ⟨w, by simp [EntityUIDOrSlot.inst, h], Or.inr ⟨sid, hf⟩⟩

theorem scopeTemplate_link {slotEnv : SlotEnv} {s : ScopeTemplate} {s' : Scope}
  (h : s.link? slotEnv = .ok s') (u₀ : EntityUID) :
  ∃ u, s' = s.inst u ∧ (u = u₀ ∨ ∃ sid, slotEnv.find? sid = some u) := by
  cases s with
  | any =>
    simp only [ScopeTemplate.link?, Except.ok.injEq] at h
    exact ⟨u₀, by simp [ScopeTemplate.inst, h], Or.inl rfl⟩
  | is ety =>
    simp only [ScopeTemplate.link?, Except.ok.injEq] at h
    exact ⟨u₀, by simp [ScopeTemplate.inst, h], Or.inl rfl⟩
  | eq x | mem x | isMem _ x =>
    simp only [ScopeTemplate.link?, bind, Except.bind] at h
    cases hx : x.link? slotEnv with
    | error _ => simp [hx] at h
    | ok e =>
      simp only [hx, Except.ok.injEq] at h
      obtain ⟨u, rfl, hu⟩ := uidOrSlot_link hx u₀
      exact ⟨u, by simp [ScopeTemplate.inst, h], hu⟩

/-- A successful link is an instantiation; each slot entity comes from the slot environment. -/
theorem template_link {t : Template} {id : PolicyID} {slotEnv : SlotEnv} {p : Policy}
  (h : t.link? id slotEnv = .ok p) (u₀ v₀ : EntityUID) :
  ∃ u v, p = t.inst id u v ∧
    (u = u₀ ∨ ∃ sid, slotEnv.find? sid = some u) ∧ (v = v₀ ∨ ∃ sid, slotEnv.find? sid = some v) := by
  obtain ⟨effect, ⟨ps⟩, as, ⟨rs⟩, cond⟩ := t
  simp only [Template.link?, PrincipalScopeTemplate.link?, ResourceScopeTemplate.link?, bind,
    Except.bind] at h
  cases hp : ps.link? slotEnv with
  | error _ => simp [hp] at h
  | ok ps' =>
    cases hr : rs.link? slotEnv with
    | error _ => simp [hp, hr] at h
    | ok rs' =>
      simp only [hp, hr, Except.ok.injEq] at h
      obtain ⟨u, rfl, hu⟩ := scopeTemplate_link hp u₀
      obtain ⟨v, rfl, hv⟩ := scopeTemplate_link hr v₀
      exact ⟨u, v, by simp [← h, Template.inst, PrincipalScopeTemplate.scope, ResourceScopeTemplate.scope], hu, hv⟩

/-- Every slot entity is valid and of a candidate type. -/
def SlotsValid (schema : Schema) (tys : List EntityType) (slotEnv : SlotEnv) : Prop :=
  ∀ sid u, slotEnv.find? sid = some u → u.ty ∈ tys ∧ schemaValidUID schema u = true

/--
Soundness: if the template has no type error, no link of it with valid slot
entities of candidate types has a type error in any environment.
-/
theorem template_sound (keep : Combo → Bool) (t : Template) (id : PolicyID)
  (rep : EntityType → EntityUID) (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t)
  (hkeep : ∀ env ∈ schema.environments, keep (env, env.reqty.principal, env.reqty.resource) = true)
  (hok : templateOutcome keep t id rep schema tys ≠ .typeError)
  {slotEnv : SlotEnv} {p : Policy} (hslots : SlotsValid schema tys slotEnv)
  (hlink : t.link? id slotEnv = .ok p) :
  ∀ env ∈ schema.environments, isErr (typecheckPolicy p env) = false := by
  intro env henv
  cases he : isErr (typecheckPolicy p env)
  · rfl
  · exfalso
    apply hok
    obtain ⟨hpTy, hrTy⟩ := htys env henv
    obtain ⟨u, v, rfl, hu, hv⟩ := template_link hlink (rep env.reqty.principal) (rep env.reqty.resource)
    have hu' : u.ty ∈ tys ∧ schemaValidUID schema u = true := by
      rcases hu with rfl | ⟨sid, hs⟩
      · exact ⟨by rw [(hrep _ hpTy).1]; exact hpTy, (hrep _ hpTy).2⟩
      · exact hslots sid u hs
    have hv' : v.ty ∈ tys ∧ schemaValidUID schema v = true := by
      rcases hv with rfl | ⟨sid, hs⟩
      · exact ⟨by rw [(hrep _ hrTy).1]; exact hrTy, (hrep _ hrTy).2⟩
      · exact hslots sid v hs
    exact (template_type_error_iff keep t id rep schema tys hrep htys hlits hkeep).mpr
      ⟨env, henv, u, v, hu'.1, hv'.1, hu'.2, hv'.2, he⟩

theorem mapM_ok_of_no_err {α β ε} (f : α → Except ε β) :
  ∀ xs : List α, (∀ x ∈ xs, isErr (f x) = false) → ∃ ys, xs.mapM f = .ok ys := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons x xs ih =>
    intro h
    obtain ⟨ys, hys⟩ := ih (λ x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    cases hf : f x with
    | error _ => have := h x List.mem_cons_self; simp [hf, isErr] at this
    | ok y => exact ⟨y :: ys, by simp [List.mapM_cons, hf, hys]⟩

/--
The linked policy then validates or is reported impossible, provided its
entity references pass `checkEntities`; it never has a type error.
-/
theorem linked_policy_validates (keep : Combo → Bool) (t : Template) (id : PolicyID)
  (rep : EntityType → EntityUID) (schema : Schema) (tys : List EntityType)
  (hrep : RepValid schema tys rep) (htys : TysCover schema tys) (hlits : LitsValid schema t)
  (hkeep : ∀ env ∈ schema.environments, keep (env, env.reqty.principal, env.reqty.resource) = true)
  (hok : templateOutcome keep t id rep schema tys ≠ .typeError)
  {slotEnv : SlotEnv} {p : Policy} (hslots : SlotsValid schema tys slotEnv)
  (hlink : t.link? id slotEnv = .ok p)
  (hce : checkEntities schema p.toExpr = .ok ()) :
  typecheckPolicyWithEnvironments typecheckPolicy p schema = .ok () ∨
  typecheckPolicyWithEnvironments typecheckPolicy p schema = .error (.impossiblePolicy p.id) := by
  have hno := template_sound keep t id rep schema tys hrep htys hlits hkeep hok hslots hlink
  obtain ⟨ys, hys⟩ := mapM_ok_of_no_err (typecheckPolicy p) schema.environments hno
  simp only [typecheckPolicyWithEnvironments, hce, Except.mapError, hys]
  by_cases ha : allFalse ys = true <;> simp [ha, bind, Except.bind]

end Cedar.Thm.Pruning

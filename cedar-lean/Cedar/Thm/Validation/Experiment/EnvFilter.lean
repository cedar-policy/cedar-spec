import Cedar.Validation
import Cedar.Thm.Data

/-!
Environment pruning in the validator is exact.

`typecheckPolicyWithEnvironments` typechecks a policy in every
(principal, action, resource) environment of the schema. This file proves one
generic fact: dropping any set of environments in which the policy types as
`false` returns exactly the same `ValidationResult`
(`filtered_environments_exact_of_false`). It then instantiates it with three
cheap filters that read only the policy's scope and the schema's hierarchies:

* action: the action scope cannot admit the environment's action;
* principal: the principal scope cannot admit the environment's principal type;
* resource: the resource scope cannot admit the environment's resource type.

`admitted_environments_exact` applies all three at once. The proofs rely on the
typechecker short-circuiting `&&` on a left side typed `false`.
-/

namespace Cedar.Thm.Experiment

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

----- Filters -----

def scopeAdmitsAction (acts : ActionSchema) (a : EntityUID) : Scope → Bool
  | .any           => true
  | .eq uid        => a == uid
  | .mem uid       => acts.descendentOf a uid
  | .is ety        => ety == a.ty
  | .isMem ety uid => ety == a.ty && acts.descendentOf a uid

def actionScopeAdmits (acts : ActionSchema) (a : EntityUID) : ActionScope → Bool
  | .actionScope s  => scopeAdmitsAction acts a s
  | .actionInAny ls => ls.any (acts.descendentOf a ·)

/--
An `action in [..]` list types as a set only when it is nonempty and every
member has one entity type. When it does not, the filter is not applied.
-/
def actionScopeFilterable : ActionScope → Bool
  | .actionScope _  => true
  | .actionInAny [] => false
  | .actionInAny (u :: us) => us.all (·.ty == u.ty)

/-- Can a principal or resource scope hold for a variable of type `ety`? -/
def scopeAdmitsType (env : TypeEnv) (ety : EntityType) : Scope → Bool
  | .any            => true
  | .eq uid         => ety == uid.ty
  | .mem uid        => env.descendentOf ety uid.ty
  | .is ety'        => ety' == ety
  | .isMem ety' uid => ety' == ety && env.descendentOf ety uid.ty

def admits (policy : Policy) (env : TypeEnv) : Bool :=
  !actionScopeFilterable policy.actionScope || actionScopeAdmits env.acts env.reqty.action policy.actionScope

def admitsPrincipal (policy : Policy) (env : TypeEnv) : Bool :=
  match policy.principalScope with
  | .principalScope s => scopeAdmitsType env env.reqty.principal s

/--
The resource scope is the third conjunct, so it decides the type only when the
action scope before it types as a boolean, which needs a filterable action scope.
-/
def admitsResource (policy : Policy) (env : TypeEnv) : Bool :=
  !actionScopeFilterable policy.actionScope ||
  match policy.resourceScope with
  | .resourceScope s => scopeAdmitsType env env.reqty.resource s

def admitsAll (policy : Policy) (env : TypeEnv) : Bool :=
  admits policy env && admitsPrincipal policy env && admitsResource policy env

def typecheckPolicyWithFilteredEnvironments
  (tc : Policy → TypeEnv → Except ValidationError TypedExpr) (keep : TypeEnv → Bool)
  (policy : Policy) (schema : Schema) : ValidationResult := do
  (checkEntities schema policy.toExpr).mapError (.typeError policy.id)
  let policyTypes ← (schema.environments.filter keep).mapM (tc policy)
  if allFalse policyTypes then .error (.impossiblePolicy policy.id) else .ok ()

----- Typing lemmas -----

theorem map_contains_of_mem_toList {α β} [BEq α] [LawfulBEq α] {m : Map α β} {k : α} {v : β}
  (h : (k, v) ∈ m.toList) : m.contains k = true := by
  simp only [Map.contains, Map.find?]
  cases hf : m.toList.find? (λ ⟨k', _⟩ => k' == k) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf (k, v) h
    simp at this
  | some p => simp

theorem env_mem {schema : Schema} {env : TypeEnv} (h : env ∈ schema.environments) :
  env.ets = schema.ets ∧ env.acts = schema.acts ∧ schema.acts.contains env.reqty.action = true := by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap] at h
  obtain ⟨rt, ⟨⟨a, e⟩, ha, hrt⟩, rfl⟩ := h
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrt
  exact ⟨rfl, rfl, map_contains_of_mem_toList ha⟩

theorem typeOf_lit_valid {env : TypeEnv} {uid : EntityUID} {c : Capabilities}
  (hv : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true) :
  typeOf (.lit (.entityUID uid)) c env = .ok (.lit (.entityUID uid) (.entity uid.ty), ∅) := by
  simp [typeOf, typeOfLit, ok, hv]

theorem checkEntities_lit {schema : Schema} {uid : EntityUID}
  (h : checkEntities schema (.lit (.entityUID uid)) = .ok ()) :
  (schema.ets.isValidEntityUID uid || schema.acts.contains uid) = true := by
  simp only [checkEntities] at h
  split at h <;> simp_all

theorem checkEntities_isMem {schema : Schema} {v : Var} {ety : EntityType} {uid : EntityUID}
  (hce : checkEntities schema ((Scope.isMem ety uid).toExpr v) = .ok ()) :
  (schema.ets.isValidEntityUID uid || schema.acts.contains uid) = true := by
  simp [Scope.toExpr, Var.inEntityUID, Var.isEntityType, checkEntities] at hce
  by_cases h1 : (schema.ets.contains ety = true ∨ schema.acts.actionType? ety = true) <;>
  by_cases h2 : (schema.ets.isValidEntityUID uid = true ∨ schema.acts.contains uid = true) <;>
  simp_all [bind, Except.bind]

theorem action_scope_ff {schema : Schema} {env : TypeEnv} {s : Scope} {c : Capabilities}
  (hets : env.ets = schema.ets) (hacts : env.acts = schema.acts)
  (ha : schema.acts.contains env.reqty.action = true)
  (hce : checkEntities schema (s.toExpr .action) = .ok ())
  (hadm : scopeAdmitsAction env.acts env.reqty.action s = false) :
  ∃ tx c', typeOf (substituteAction env.reqty.action (s.toExpr .action)) c env = .ok (tx, c') ∧
    tx.typeOf = .bool .ff := by
  have hva : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true := by
    simp [hacts, ha]
  have hca : env.acts.contains env.reqty.action = true := by simp [hacts, ha]
  cases s with
  | any => simp [scopeAdmitsAction] at hadm
  | eq uid =>
    have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.eqEntityUID, checkEntities] using hce)
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv,
      typeOf_lit_valid hva]
    simp [scopeAdmitsAction] at hadm
    simp [typeOfBinaryApp, typeOfEq, ok, TypedExpr.typeOf, hadm]
  | mem uid =>
    have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.inEntityUID, checkEntities] using hce)
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv,
      typeOf_lit_valid hva]
    simp [scopeAdmitsAction] at hadm
    simp [typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, ok, TypedExpr.typeOf, hadm, hca]
  | is ety =>
    simp [scopeAdmitsAction] at hadm
    simp only [Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hva]
    simp [typeOfUnaryApp, ok, TypedExpr.typeOf, hadm]
  | isMem ety uid =>
    have hv := checkEntities_isMem hce
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.inEntityUID, Var.isEntityType, substituteAction, mapOnVars, typeOf,
      typeOf_lit_valid hv, typeOf_lit_valid hva]
    simp [scopeAdmitsAction] at hadm
    by_cases h : ety = env.reqty.action.ty
    · have hd := hadm h
      simp [typeOfUnaryApp, typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, typeOfAnd, ok,
        TypedExpr.typeOf, h, hd, hca]
    · simp [typeOfUnaryApp, typeOfAnd, ok, TypedExpr.typeOf, h]

theorem checkEntities_actionInAny {schema : Schema} {ls : List EntityUID}
  (hce : checkEntities schema (ActionScope.actionInAny ls).toExpr = .ok ()) :
  ∀ u ∈ ls, (schema.ets.isValidEntityUID u || schema.acts.contains u) = true := by
  intro u hu
  simp only [ActionScope.toExpr, checkEntities] at hce
  simp only [Except.bind_ok] at hce
  have h := List.forM_ok_implies_all_ok _ _ hce
  have hm : Expr.lit (Prim.entityUID u) ∈ List.map (fun e => Expr.lit (Prim.entityUID e)) ls := List.mem_map_of_mem hu
  exact checkEntities_lit (h ⟨_, hm⟩ (List.mem_attach _ _))

theorem foldl_lub_entity (t : EntityType) :
  ∀ us : List EntityUID, us.all (·.ty == t) = true →
  List.foldlM lub? (CedarType.entity t) (us.map (λ e => CedarType.entity e.ty)) = some (.entity t) := by
  intro us
  induction us with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hx, hxs⟩ := h
    simp only [List.map_cons, List.foldlM_cons, hx]
    simp [lub?, ih hxs]

theorem mapM_typeOf_lits {env : TypeEnv} {c : Capabilities} :
  ∀ ls : List EntityUID, (∀ x ∈ ls, (env.ets.isValidEntityUID x || env.acts.contains x) = true) →
  ls.mapM (λ e => justType (typeOf (.lit (.entityUID e)) c env)) =
    .ok (ls.map (λ e => TypedExpr.lit (.entityUID e) (.entity e.ty))) := by
  intro ls
  induction ls with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have hx := h x List.mem_cons_self
    have hxs := ih (λ y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.mapM_cons, hxs]
    simp [typeOf_lit_valid hx, justType, Except.map]

theorem typeOf_lits_set {env : TypeEnv} {c : Capabilities} {u : EntityUID} {us : List EntityUID}
  (hv : ∀ x ∈ u :: us, (env.ets.isValidEntityUID x || env.acts.contains x) = true)
  (hty : us.all (·.ty == u.ty) = true) :
  ∃ tx c', typeOf (.set ((u :: us).map (λ e => .lit (.entityUID e)))) c env = .ok (tx, c') ∧
    tx.typeOf = .set (.entity u.ty) := by
  have hm : ((u :: us).map (λ e => Expr.lit (.entityUID e))).mapM₁
      (λ ⟨x, _⟩ => justType (typeOf x c env)) =
      .ok ((u :: us).map (λ e => TypedExpr.lit (.entityUID e) (.entity e.ty))) := by
    rw [List.mapM₁_eq_mapM (λ x => justType (typeOf x c env)), List.mapM_map]
    exact mapM_typeOf_lits _ hv
  simp only [typeOf, hm, Except.bind_ok]
  have hf := foldl_lub_entity u.ty us hty
  simp [Function.comp_def, TypedExpr.typeOf] at *
  simp [typeOfSet, ok, TypedExpr.typeOf, Function.comp_def, hf]

theorem substituteAction_lits_set (a : EntityUID) (ls : List EntityUID) :
  substituteAction a (.set (ls.map (λ e => .lit (.entityUID e)))) = .set (ls.map (λ e => .lit (.entityUID e))) := by
  simp only [substituteAction, mapOnVars]
  congr 1
  rw [List.map₁_eq_map (mapOnVars _)]
  simp [List.map_map, Function.comp_def, mapOnVars]

theorem action_in_any_ff {schema : Schema} {env : TypeEnv} {u : EntityUID} {us : List EntityUID} {c : Capabilities}
  (hets : env.ets = schema.ets) (hacts : env.acts = schema.acts)
  (ha : schema.acts.contains env.reqty.action = true)
  (hce : checkEntities schema (ActionScope.actionInAny (u :: us)).toExpr = .ok ())
  (hty : us.all (·.ty == u.ty) = true)
  (hadm : (u :: us).any (env.acts.descendentOf env.reqty.action ·) = false) :
  ∃ tx c', typeOf (substituteAction env.reqty.action (ActionScope.actionInAny (u :: us)).toExpr) c env = .ok (tx, c') ∧
    tx.typeOf = .bool .ff := by
  have hva : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true := by
    simp [hacts, ha]
  have hca : env.acts.contains env.reqty.action = true := by simp [hacts, ha]
  have hv : ∀ x ∈ u :: us, (env.ets.isValidEntityUID x || env.acts.contains x) = true := by
    intro x hx; rw [hets, hacts]; exact checkEntities_actionInAny hce x hx
  obtain ⟨txs, cs, hs, hst⟩ := typeOf_lits_set (c := c) hv hty
  have hsub : substituteAction env.reqty.action (ActionScope.actionInAny (u :: us)).toExpr =
      .binaryApp .mem (.lit (.entityUID env.reqty.action)) (.set ((u :: us).map (λ e => .lit (.entityUID e)))) := by
    simp only [ActionScope.toExpr, substituteAction, mapOnVars]
    congr 2
    rw [List.map₁_eq_map (mapOnVars _)]
    simp [List.map_map, Function.comp_def, mapOnVars]
  rw [hsub]
  simp only [typeOf, typeOf_lit_valid hva, hs, Except.bind_ok]
  have hids : entityUIDs? (.set ((u :: us).map (λ e => .lit (.entityUID e)))) = some (u :: us) := by
    simp only [entityUIDs?]
    generalize u :: us = ls
    induction ls with
    | nil => rfl
    | cons x xs ih => simp [List.mapM_cons, entityUID?, ih]
  simp only [typeOfBinaryApp, hst, typeOfInₛ, actionUID?, entityUID?, hca, hids]
  refine ⟨_, _, rfl, ?_⟩
  have hca' : (do let uid ← some env.reqty.action; if env.acts.contains uid = true then some uid else none) =
      some env.reqty.action := by simp [hca]
  simp only [TypedExpr.typeOf, hca', hadm]
  rfl

theorem typeOfAnd_ff_right {tx₁ tx₂ : TypedExpr} {c₁ c₂ : Capabilities} {b : BoolType}
  (h₁ : tx₁.typeOf = .bool b) (h₂ : tx₂.typeOf = .bool .ff) :
  ∃ tx c, typeOfAnd (tx₁, c₁) (.ok (tx₂, c₂)) = .ok (tx, c) ∧ tx.typeOf = .bool .ff := by
  cases b
  all_goals
    unfold typeOfAnd; rw [h₁]
    first
    | exact ⟨_, _, rfl, h₁⟩
    | (simp only [bind, Except.bind]; rw [h₂]; exact ⟨_, _, rfl, rfl⟩)

theorem typeOfAnd_ff_left {tx₁ : TypedExpr} {c₁ : Capabilities} {r : ResultType}
  (h₁ : tx₁.typeOf = .bool .ff) :
  typeOfAnd (tx₁, c₁) r = .ok (tx₁, ∅) := by
  simp only [typeOfAnd, h₁]; rfl

----- Principal and resource scopes -----

theorem scope_var_typed {schema : Schema} {env : TypeEnv} {s : Scope} {v : Var} {ety : EntityType}
  {a : EntityUID} {c : Capabilities}
  (hets : env.ets = schema.ets) (hacts : env.acts = schema.acts)
  (hvar : (v = .principal ∧ ety = env.reqty.principal) ∨ (v = .resource ∧ ety = env.reqty.resource))
  (hce : checkEntities schema (s.toExpr v) = .ok ()) :
  ∃ tx c', typeOf (substituteAction a (s.toExpr v)) c env = .ok (tx, c') ∧
    ∃ b, tx.typeOf = .bool b ∧ (scopeAdmitsType env ety s = false → b = .ff) := by
  rcases hvar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  cases s with
  | any => simp [Scope.toExpr, substituteAction, mapOnVars, typeOf, typeOfLit, ok, TypedExpr.typeOf, scopeAdmitsType]
  | eq uid =>
    have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.eqEntityUID, checkEntities] using hce)
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfEq, ok, TypedExpr.typeOf, lub?, scopeAdmitsType]
    split <;> simp_all
  | mem uid =>
    have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.inEntityUID, checkEntities] using hce)
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, ok, TypedExpr.typeOf, scopeAdmitsType]
  | is ety' =>
    simp [Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars, typeOf, typeOfVar, typeOfUnaryApp, ok,
      TypedExpr.typeOf, scopeAdmitsType]
  | isMem ety' uid =>
    have hv := checkEntities_isMem hce
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.inEntityUID, Var.isEntityType, substituteAction, mapOnVars, typeOf,
      typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfUnaryApp, typeOfInₑ, actionUID?, entityUID?, typeOfAnd, ok,
      TypedExpr.typeOf, scopeAdmitsType]
    first
    | (by_cases h1 : ety' = env.reqty.principal <;>
       by_cases h2 : env.descendentOf env.reqty.principal uid.ty = true <;> simp [h1, h2])
    | (by_cases h1 : ety' = env.reqty.resource <;>
       by_cases h2 : env.descendentOf env.reqty.resource uid.ty = true <;> simp [h1, h2])

theorem action_scope_bool {schema : Schema} {env : TypeEnv} {as : ActionScope} {c : Capabilities}
  (hets : env.ets = schema.ets) (hacts : env.acts = schema.acts)
  (ha : schema.acts.contains env.reqty.action = true)
  (hce : checkEntities schema as.toExpr = .ok ())
  (hf : actionScopeFilterable as = true) :
  ∃ tx c', typeOf (substituteAction env.reqty.action as.toExpr) c env = .ok (tx, c') ∧ ∃ b, tx.typeOf = .bool b := by
  have hva : (env.ets.isValidEntityUID env.reqty.action || env.acts.contains env.reqty.action) = true := by
    simp [hacts, ha]
  have hca : env.acts.contains env.reqty.action = true := by simp [hacts, ha]
  cases as with
  | actionScope s =>
    simp only [ActionScope.toExpr] at hce ⊢
    cases s with
    | any => simp [Scope.toExpr, substituteAction, mapOnVars, typeOf, typeOfLit, ok, TypedExpr.typeOf]
    | eq uid =>
      have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.eqEntityUID, checkEntities] using hce)
      rw [← hets, ← hacts] at hv
      simp only [Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv,
        typeOf_lit_valid hva]
      simp [typeOfBinaryApp, typeOfEq, ok, TypedExpr.typeOf]
      split <;> simp
    | mem uid =>
      have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.inEntityUID, checkEntities] using hce)
      rw [← hets, ← hacts] at hv
      simp only [Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv,
        typeOf_lit_valid hva]
      simp [typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, ok, TypedExpr.typeOf, hca]
    | is ety =>
      simp only [Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hva]
      simp [typeOfUnaryApp, ok, TypedExpr.typeOf]
    | isMem ety uid =>
      have hv := checkEntities_isMem hce
      rw [← hets, ← hacts] at hv
      simp only [Scope.toExpr, Var.inEntityUID, Var.isEntityType, substituteAction, mapOnVars, typeOf,
        typeOf_lit_valid hv, typeOf_lit_valid hva]
      by_cases h1 : ety = env.reqty.action.ty <;>
      by_cases h2 : env.acts.descendentOf env.reqty.action uid = true <;>
      simp [typeOfUnaryApp, typeOfBinaryApp, typeOfInₑ, actionUID?, entityUID?, typeOfAnd, ok,
        TypedExpr.typeOf, h1, h2, hca]
  | actionInAny ls =>
    cases ls with
    | nil => simp [actionScopeFilterable] at hf
    | cons u us =>
      by_cases hadm : (u :: us).any (env.acts.descendentOf env.reqty.action ·) = false
      · obtain ⟨tx, c', h, ht⟩ := action_in_any_ff (c := c) hets hacts ha hce hf hadm
        exact ⟨tx, c', h, _, ht⟩
      · have hv : ∀ x ∈ u :: us, (env.ets.isValidEntityUID x || env.acts.contains x) = true := by
          intro x hx; rw [hets, hacts]; exact checkEntities_actionInAny hce x hx
        obtain ⟨txs, cs, hs, hst⟩ := typeOf_lits_set (c := c) hv hf
        have hsub : substituteAction env.reqty.action (ActionScope.actionInAny (u :: us)).toExpr =
            .binaryApp .mem (.lit (.entityUID env.reqty.action)) (.set ((u :: us).map (λ e => .lit (.entityUID e)))) := by
          simp only [ActionScope.toExpr, substituteAction, mapOnVars]
          congr 2
          rw [List.map₁_eq_map (mapOnVars _)]
          simp [List.map_map, Function.comp_def, mapOnVars]
        rw [hsub]
        simp only [typeOf, typeOf_lit_valid hva, hs, Except.bind_ok]
        simp only [typeOfBinaryApp, hst]
        exact ⟨_, _, rfl, _, rfl⟩

----- Composing `&&` -----

/-- `x` types as `false` under every capability set. -/
def TypesFalse (x : Expr) (env : TypeEnv) : Prop :=
  ∀ c, ∃ tx c', typeOf x c env = .ok (tx, c') ∧ tx.typeOf = .bool .ff

/-- `x` types as some boolean under every capability set. -/
def TypesBool (x : Expr) (env : TypeEnv) : Prop :=
  ∀ c, ∃ tx c', typeOf x c env = .ok (tx, c') ∧ ∃ b, tx.typeOf = .bool b

theorem typeOf_and (x y : Expr) (c : Capabilities) (env : TypeEnv) :
  typeOf (.and x y) c env = (typeOf x c env).bind (λ p => typeOfAnd p (typeOf y (c ∪ p.2) env)) := by
  rw [typeOf]
  cases typeOf x c env <;> rfl

theorem and_false_of_left {x y : Expr} {env : TypeEnv} (h : TypesFalse x env) : TypesFalse (.and x y) env := by
  intro c
  obtain ⟨tx, cx, hx, ht⟩ := h c
  refine ⟨tx, ∅, ?_, ht⟩
  rw [typeOf_and, hx]
  exact typeOfAnd_ff_left ht

theorem and_false_of_right {x y : Expr} {env : TypeEnv} (hx : TypesBool x env) (hy : TypesFalse y env) :
  TypesFalse (.and x y) env := by
  intro c
  obtain ⟨tx, cx, hx, b, hb⟩ := hx c
  obtain ⟨ty, cy, hy, hyt⟩ := hy (c ∪ cx)
  rw [typeOf_and, hx]
  simp only [Except.bind]
  rw [hy]
  exact typeOfAnd_ff_right hb hyt

----- Per-environment fact -----

theorem substituteAction_policy (a : EntityUID) (policy : Policy) :
  substituteAction a policy.toExpr =
    .and (substituteAction a policy.principalScope.toExpr)
      (.and (substituteAction a policy.actionScope.toExpr)
        (.and (substituteAction a policy.resourceScope.toExpr) (substituteAction a policy.condition.toExpr))) := by
  simp only [Policy.toExpr, substituteAction, mapOnVars]

theorem checkEntities_scopes {schema : Schema} {policy : Policy}
  (hce : checkEntities schema policy.toExpr = .ok ()) :
  checkEntities schema policy.principalScope.toExpr = .ok () ∧
  checkEntities schema policy.actionScope.toExpr = .ok () ∧
  checkEntities schema policy.resourceScope.toExpr = .ok () := by
  simp only [Policy.toExpr, checkEntities] at hce
  cases h₁ : checkEntities schema policy.principalScope.toExpr <;>
  cases h₂ : checkEntities schema policy.actionScope.toExpr <;>
  cases h₃ : checkEntities schema policy.resourceScope.toExpr <;>
  simp_all [bind, Except.bind]

theorem typecheck_of_false {policy : Policy} {env : TypeEnv}
  (h : TypesFalse (substituteAction env.reqty.action policy.toExpr) env) :
  ∃ tx, typecheckPolicy policy env = .ok tx ∧ (tx.typeOf == .bool .ff) = true := by
  obtain ⟨tx, c, htx, htt⟩ := h ∅
  refine ⟨tx, ?_, by simp [htt]⟩
  simp only [typecheckPolicy, htx]
  simp [htt, subty, lub?, lubBool]

theorem typecheck_unadmitted_is_false
  {policy : Policy} {schema : Schema} {env : TypeEnv}
  (hce : checkEntities schema policy.toExpr = .ok ())
  (henv : env ∈ schema.environments)
  (hadm : admitsAll policy env = false) :
  ∃ tx, typecheckPolicy policy env = .ok tx ∧ (tx.typeOf == .bool .ff) = true
:= by
  have ⟨hets, hacts, ha⟩ := env_mem henv
  have ⟨hcp, hca, hcr⟩ := checkEntities_scopes hce
  apply typecheck_of_false
  rw [substituteAction_policy]
  cases hps : policy.principalScope with
  | principalScope sp =>
  cases hrs : policy.resourceScope with
  | resourceScope sr =>
  rw [hps] at hcp
  rw [hrs] at hcr
  simp only [PrincipalScope.toExpr, ResourceScope.toExpr] at hcp hcr ⊢
  have hP := λ c => scope_var_typed (a := env.reqty.action) (c := c) hets hacts (Or.inl ⟨rfl, rfl⟩) hcp
  have hR := λ c => scope_var_typed (a := env.reqty.action) (c := c) hets hacts (Or.inr ⟨rfl, rfl⟩) hcr
  have hPb : TypesBool (substituteAction env.reqty.action (sp.toExpr .principal)) env := by
    intro c; obtain ⟨tx, c', h, b, hb, _⟩ := hP c; exact ⟨tx, c', h, b, hb⟩
  simp only [admitsAll, admits, admitsPrincipal, admitsResource, hps, hrs, Bool.and_eq_false_iff,
    Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hadm
  rcases hadm with (⟨hf, hadm⟩ | hadm) | ⟨hf, hadm⟩
  · -- action scope cannot admit the environment's action
    apply and_false_of_right hPb
    apply and_false_of_left
    intro c
    cases hs : policy.actionScope with
    | actionScope s =>
      rw [hs] at hadm hca
      exact action_scope_ff hets hacts ha hca hadm
    | actionInAny ls =>
      rw [hs] at hf hadm hca
      cases ls with
      | nil => simp [actionScopeFilterable] at hf
      | cons u us => exact action_in_any_ff hets hacts ha hca hf hadm
  · -- principal scope cannot admit the environment's principal type
    apply and_false_of_left
    intro c
    obtain ⟨tx, c', h, b, hb, hff⟩ := hP c
    exact ⟨tx, c', h, by rw [hb, hff hadm]⟩
  · -- resource scope cannot admit the environment's resource type
    apply and_false_of_right hPb
    apply and_false_of_right (λ c => action_scope_bool hets hacts ha hca hf)
    apply and_false_of_left
    intro c
    obtain ⟨tx, c', h, b, hb, hff⟩ := hR c
    exact ⟨tx, c', h, by rw [hb, hff hadm]⟩

----- Generic list fact -----

/--
Dropping elements on which `f` succeeds with a `g`-true value changes neither
the first error of `mapM f` nor the `all g` of its results.
-/
theorem mapM_all_filter {α β ε} (f : α → Except ε β) (g : β → Bool) (keep : α → Bool) :
  ∀ (xs : List α),
  (∀ x ∈ xs, keep x = false → ∃ y, f x = .ok y ∧ g y = true) →
  (do let ys ← xs.mapM f; pure (ys.all g) : Except ε Bool) =
  (do let ys ← (xs.filter keep).mapM f; pure (ys.all g))
:= by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have ih' := ih (λ x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    cases hk : keep x with
    | false =>
      obtain ⟨y, hy, hg⟩ := h x List.mem_cons_self hk
      simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte, ← ih', List.mapM_cons, hy]
      cases List.mapM f xs <;> simp [hg]
    | true =>
      simp only [List.filter_cons, hk, ↓reduceIte, List.mapM_cons]
      cases hf : f x with
      | error e => rfl
      | ok y =>
        have := congrArg (λ r => r.map (g y && ·)) ih'
        cases h₁ : List.mapM f xs <;> cases h₂ : List.mapM f (List.filter keep xs) <;>
        simp_all [Except.map]

----- Main theorems -----

/--
The generic fact: any environment filter is exact when every environment it
drops types the policy as `false`. It holds for any per-environment checker `tc`.
-/
theorem filtered_environments_exact_of_false
  (tc : Policy → TypeEnv → Except ValidationError TypedExpr) (keep : TypeEnv → Bool)
  (policy : Policy) (schema : Schema)
  (h : checkEntities schema policy.toExpr = .ok () → ∀ env ∈ schema.environments, keep env = false →
    ∃ tx, tc policy env = .ok tx ∧ (tx.typeOf == .bool .ff) = true) :
  typecheckPolicyWithFilteredEnvironments tc keep policy schema =
  typecheckPolicyWithEnvironments tc policy schema
:= by
  simp only [typecheckPolicyWithFilteredEnvironments, typecheckPolicyWithEnvironments, allFalse]
  cases hce : checkEntities schema policy.toExpr with
  | error e => rfl
  | ok u =>
    cases u
    have h' := mapM_all_filter (tc policy) (TypedExpr.typeOf · == .bool .ff) keep schema.environments (h hce)
    simp only [Except.mapError, Except.bind_ok] at *
    cases h₁ : List.mapM (tc policy) schema.environments <;>
    cases h₂ : List.mapM (tc policy) (List.filter keep schema.environments) <;>
    simp_all [bind, Except.bind, pure, Except.pure]

/-- Action, principal and resource filtering together are exact, for every policy and schema. -/
theorem admitted_environments_exact (policy : Policy) (schema : Schema) :
  typecheckPolicyWithFilteredEnvironments typecheckPolicy (admitsAll policy) policy schema =
  typecheckPolicyWithEnvironments typecheckPolicy policy schema :=
  filtered_environments_exact_of_false _ _ _ _
    (λ hce _ henv hadm => typecheck_unadmitted_is_false hce henv hadm)

/-- Any filter that keeps at least the admitted environments is exact too. -/
theorem weaker_filter_exact (keep : TypeEnv → Bool) (policy : Policy) (schema : Schema)
  (hkeep : ∀ env, admitsAll policy env = true → keep env = true) :
  typecheckPolicyWithFilteredEnvironments typecheckPolicy keep policy schema =
  typecheckPolicyWithEnvironments typecheckPolicy policy schema :=
  filtered_environments_exact_of_false _ _ _ _
    (λ hce env henv hk => by
      cases ha : admitsAll policy env with
      | false => exact typecheck_unadmitted_is_false hce henv ha
      | true => simp [hkeep env ha] at hk)

/-- The action filter alone (the earlier `ActionFilter` result). -/
theorem action_filter_exact (policy : Policy) (schema : Schema) :
  typecheckPolicyWithFilteredEnvironments typecheckPolicy (admits policy) policy schema =
  typecheckPolicyWithEnvironments typecheckPolicy policy schema :=
  weaker_filter_exact _ _ _ (λ env h => by simp [admitsAll] at h; exact h.1.1)

theorem principal_filter_exact (policy : Policy) (schema : Schema) :
  typecheckPolicyWithFilteredEnvironments typecheckPolicy (admitsPrincipal policy) policy schema =
  typecheckPolicyWithEnvironments typecheckPolicy policy schema :=
  weaker_filter_exact _ _ _ (λ env h => by simp [admitsAll] at h; exact h.1.2)

theorem resource_filter_exact (policy : Policy) (schema : Schema) :
  typecheckPolicyWithFilteredEnvironments typecheckPolicy (admitsResource policy) policy schema =
  typecheckPolicyWithEnvironments typecheckPolicy policy schema :=
  weaker_filter_exact _ _ _ (λ env h => by simp [admitsAll] at h; exact h.2)

end Cedar.Thm.Experiment

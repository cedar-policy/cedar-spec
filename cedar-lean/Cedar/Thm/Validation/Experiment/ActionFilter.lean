import Cedar.Validation
import Cedar.Thm.Data

/-!
Action-scope environment pruning is exact.

`typecheckPolicyWithEnvironments` typechecks a policy in every
(principal, action, resource) environment of the schema. This file defines a
variant that first drops each environment whose action the policy's action
scope cannot admit, and proves that it returns exactly the same
`ValidationResult` for every policy and every schema.

The admission test reads only the policy's action scope and the action
hierarchy, so it costs O(#actions) rather than O(#environments) typechecks.
-/

namespace Cedar.Thm.Experiment

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

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

def admits (policy : Policy) (env : TypeEnv) : Bool :=
  !actionScopeFilterable policy.actionScope || actionScopeAdmits env.acts env.reqty.action policy.actionScope

def typecheckPolicyWithFilteredEnvironments (policy : Policy) (schema : Schema) : ValidationResult := do
  (checkEntities schema policy.toExpr).mapError (.typeError policy.id)
  let policyTypes ← (schema.environments.filter (admits policy)).mapM (typecheckPolicy policy)
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

theorem principal_scope_bool {schema : Schema} {env : TypeEnv} {s : Scope} {a : EntityUID} {c : Capabilities}
  (hets : env.ets = schema.ets) (hacts : env.acts = schema.acts)
  (hce : checkEntities schema (s.toExpr .principal) = .ok ()) :
  ∃ tx c', typeOf (substituteAction a (s.toExpr .principal)) c env = .ok (tx, c') ∧ ∃ b, tx.typeOf = .bool b := by
  cases s with
  | any => simp [Scope.toExpr, substituteAction, mapOnVars, typeOf, typeOfLit, ok, TypedExpr.typeOf]
  | eq uid =>
    have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.eqEntityUID, checkEntities] using hce)
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.eqEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfEq, ok, TypedExpr.typeOf]
    split <;> simp
  | mem uid =>
    have hv := checkEntities_lit (by simpa [Scope.toExpr, Var.inEntityUID, checkEntities] using hce)
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.inEntityUID, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, ok, TypedExpr.typeOf]
  | is ety =>
    simp [Scope.toExpr, Var.isEntityType, substituteAction, mapOnVars, typeOf, typeOfVar, typeOfUnaryApp, ok, TypedExpr.typeOf]
  | isMem ety uid =>
    have hv : (schema.ets.isValidEntityUID uid || schema.acts.contains uid) = true := by
      simp [Scope.toExpr, Var.inEntityUID, Var.isEntityType, checkEntities] at hce
      by_cases h1 : (schema.ets.contains ety = true ∨ schema.acts.actionType? ety = true) <;>
      by_cases h2 : (schema.ets.isValidEntityUID uid = true ∨ schema.acts.contains uid = true) <;>
      simp_all [bind, Except.bind]
    rw [← hets, ← hacts] at hv
    simp only [Scope.toExpr, Var.inEntityUID, Var.isEntityType, substituteAction, mapOnVars, typeOf, typeOf_lit_valid hv]
    simp [typeOfVar, typeOfBinaryApp, typeOfUnaryApp, typeOfAnd, ok, TypedExpr.typeOf]
    generalize typeOfInₑ env.reqty.principal uid.ty (Expr.var Var.principal) (Expr.lit (Prim.entityUID uid)) env = b
    by_cases h : ety = env.reqty.principal <;> cases b <;> simp [h]

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

theorem checkEntities_policy {schema : Schema} {policy : Policy}
  (hce : checkEntities schema policy.toExpr = .ok ()) :
  checkEntities schema policy.principalScope.toExpr = .ok () ∧
  checkEntities schema policy.actionScope.toExpr = .ok () := by
  simp only [Policy.toExpr, checkEntities] at hce
  cases h₁ : checkEntities schema policy.principalScope.toExpr <;>
  cases h₂ : checkEntities schema policy.actionScope.toExpr <;>
  simp_all [bind, Except.bind]

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

----- Per-environment fact -----

theorem typecheck_unadmitted_is_false
  {policy : Policy} {schema : Schema} {env : TypeEnv}
  (hce : checkEntities schema policy.toExpr = .ok ())
  (henv : env ∈ schema.environments)
  (hadm : admits policy env = false) :
  ∃ tx, typecheckPolicy policy env = .ok tx ∧ (tx.typeOf == .bool .ff) = true
:= by
  have ⟨hets, hacts, ha⟩ := env_mem henv
  have ⟨hcp, hca⟩ := checkEntities_policy hce
  -- the action scope types as `false`
  have hA : ∀ c, ∃ tx c', typeOf (substituteAction env.reqty.action policy.actionScope.toExpr) c env = .ok (tx, c') ∧
      tx.typeOf = .bool .ff := by
    intro c
    simp only [admits, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hadm
    obtain ⟨hf, hadm⟩ := hadm
    cases hs : policy.actionScope with
    | actionScope s =>
      rw [hs] at hadm hca
      exact action_scope_ff hets hacts ha hca hadm
    | actionInAny ls =>
      rw [hs] at hf hadm hca
      cases ls with
      | nil => simp [actionScopeFilterable] at hf
      | cons u us =>
        exact action_in_any_ff hets hacts ha hca hf hadm
  -- the principal scope types as some boolean
  cases hps : policy.principalScope with
  | principalScope s =>
  rw [hps] at hcp
  have ⟨txP, cP, hP, bP, hbP⟩ := principal_scope_bool (a := env.reqty.action) (c := ∅) hets hacts hcp
  have hexpr : substituteAction env.reqty.action policy.toExpr =
      .and (substituteAction env.reqty.action (s.toExpr .principal))
        (.and (substituteAction env.reqty.action policy.actionScope.toExpr)
          (substituteAction env.reqty.action (.and policy.resourceScope.toExpr policy.condition.toExpr))) := by
    simp only [Policy.toExpr, hps, PrincipalScope.toExpr, substituteAction, mapOnVars]
  obtain ⟨txA, cA, hAc, hAt⟩ := hA (∅ ∪ cP)
  have hrest : typeOf (.and (substituteAction env.reqty.action policy.actionScope.toExpr)
      (substituteAction env.reqty.action (.and policy.resourceScope.toExpr policy.condition.toExpr))) (∅ ∪ cP) env =
      .ok (txA, ∅) := by
    simp only [typeOf, hAc, Except.bind_ok]
    exact typeOfAnd_ff_left hAt
  obtain ⟨tx, c, htx, htt⟩ := typeOfAnd_ff_right (c₁ := cP) (c₂ := ∅) hbP hAt
  refine ⟨tx, ?_, by simp [htt]⟩
  have hand : ∀ x y c, typeOf (.and x y) c env =
      (typeOf x c env).bind (λ p => typeOfAnd p (typeOf y (c ∪ p.2) env)) := by
    intro x y c
    rw [typeOf]
    cases typeOf x c env <;> rfl
  simp only [typecheckPolicy, hexpr]
  rw [hand, hP]
  simp only [Except.bind]
  rw [hrest, htx]
  simp [htt, subty, lub?, lubBool]

----- Main theorem -----

theorem filtered_environments_exact (policy : Policy) (schema : Schema) :
  typecheckPolicyWithFilteredEnvironments policy schema =
  typecheckPolicyWithEnvironments typecheckPolicy policy schema
:= by
  simp only [typecheckPolicyWithFilteredEnvironments, typecheckPolicyWithEnvironments, allFalse]
  cases hce : checkEntities schema policy.toExpr with
  | error e => rfl
  | ok u =>
    cases u
    have h := mapM_all_filter (typecheckPolicy policy) (TypedExpr.typeOf · == .bool .ff)
      (admits policy) schema.environments
      (λ env henv hadm => typecheck_unadmitted_is_false hce henv hadm)
    simp only [Except.mapError, Except.bind_ok] at *
    cases h₁ : List.mapM (typecheckPolicy policy) schema.environments <;>
    cases h₂ : List.mapM (typecheckPolicy policy) (List.filter (admits policy) schema.environments) <;>
    simp_all [bind, Except.bind, pure, Except.pure]

end Cedar.Thm.Experiment

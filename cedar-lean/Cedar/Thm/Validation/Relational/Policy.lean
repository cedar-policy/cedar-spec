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

public import Cedar.Thm.Validation.EnvironmentValidation
public import Cedar.Thm.Validation.Relational.WellFormed
public import Cedar.Validation.Relational.Policy
import Batteries.Data.List.Lemmas
import all Cedar.Data.List -- unfolds `attach₂`
import all Cedar.Data.Map -- unfolds `contains`, `find`, `keys`, …
import all Cedar.Data.Set -- unfolds `all`, `any`, `contains`, …
import all Cedar.Spec.Policy -- unfolds `Conditions`, `Policies`, `eqEntityUID`, …
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.EnvironmentValidator -- unfolds `validateWellFormed`
import all Cedar.Validation.Subtyping -- unfolds `lub`, `lubBool`, `subty`
import all Cedar.Validation.Typechecker -- unfolds `entityUID`, `typeOf`
import all Cedar.Validation.TypedExpr -- unfolds `toExpr`, `typeOf`
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `actionType`, …
import all Cedar.Validation.Validator -- unfolds `allFalse`, `checkEntities`, `environment`, …

/-! # `ValidPolicy` characterizes `validate`

Each relation in `Cedar.Validation.Relational.Policy` agrees with the validator function it
mirrors, and together they give `validate_iff`. -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Policy expressions -/

theorem scopeExpr_toExpr (s : Scope) (v : Var) : ScopeExpr s v (s.toExpr v) := by
  cases s <;> simp only [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType] <;>
    constructor

theorem ScopeExpr.eq_toExpr {s v x} (h : ScopeExpr s v x) : x = s.toExpr v := by
  cases h <;> simp only [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType]

theorem entityUIDLits_map (uids : List EntityUID) :
    EntityUIDLits uids (uids.map fun e => .lit (.entityUID e)) := by
  induction uids with
  | nil => exact .nil
  | cons u us ih => exact .cons _ _ _ ih

theorem EntityUIDLits.eq_map {uids xs} (h : EntityUIDLits uids xs) :
    xs = uids.map fun e => .lit (.entityUID e) := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

theorem actionScopeExpr_toExpr (s : ActionScope) : ActionScopeExpr s s.toExpr := by
  cases s with
  | actionScope s => exact .scope _ _ (scopeExpr_toExpr s .action)
  | actionInAny uids => simp only [ActionScope.toExpr]; exact .inAny _ _ (entityUIDLits_map uids)

theorem ActionScopeExpr.eq_toExpr {s x} (h : ActionScopeExpr s x) : x = s.toExpr := by
  cases h with
  | scope s x hs => simp only [ActionScope.toExpr]; exact hs.eq_toExpr
  | inAny uids xs hl => simp only [ActionScope.toExpr, hl.eq_map]

theorem conditionExpr_toExpr (c : Condition) : ConditionExpr c c.toExpr := by
  obtain ⟨k, b⟩ := c
  cases k <;> simp only [Condition.toExpr] <;> constructor

theorem ConditionExpr.eq_toExpr {c x} (h : ConditionExpr c x) : x = c.toExpr := by
  cases h <;> simp only [Condition.toExpr]

theorem conditions_toExpr_cons_cons (c c' : Condition) (cs : Conditions) :
    Conditions.toExpr (c :: c' :: cs) = .and c.toExpr (Conditions.toExpr (c' :: cs)) := by
  unfold Conditions.toExpr
  rw [List.reverse_cons (a := c)]
  cases h : (c' :: cs).reverse with
  | nil => simp at h
  | cons d ds => simp [List.foldl_append]

theorem conditionsExpr_toExpr : ∀ cs : Conditions, ConditionsExpr cs (Conditions.toExpr cs)
  | [] => by simp only [Conditions.toExpr, List.reverse_nil]; exact .nil
  | [c] => by
    simp only [Conditions.toExpr, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.foldl_nil]
    exact .one _ _ (conditionExpr_toExpr c)
  | c :: c' :: cs => by
    rw [conditions_toExpr_cons_cons]
    exact .cons _ _ _ _ _ (conditionExpr_toExpr c) (conditionsExpr_toExpr (c' :: cs))

theorem ConditionsExpr.eq_toExpr {cs x} (h : ConditionsExpr cs x) : x = Conditions.toExpr cs := by
  induction h with
  | nil => simp [Conditions.toExpr]
  | one c x hc =>
    simp only [Conditions.toExpr, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.foldl_nil]
    exact hc.eq_toExpr
  | cons c c' cs x rest hc _ ih => rw [conditions_toExpr_cons_cons, hc.eq_toExpr, ih]

theorem policyExpr_toExpr (p : Policy) : PolicyExpr p p.toExpr := by
  obtain ⟨id, eff, ⟨ps⟩, acs, ⟨rs⟩, cs⟩ := p
  exact .mk _ _ _ _ _ _ _ _ _ _ (scopeExpr_toExpr ps .principal) (actionScopeExpr_toExpr acs)
    (scopeExpr_toExpr rs .resource) (conditionsExpr_toExpr cs)

theorem PolicyExpr.eq_toExpr {p x} (h : PolicyExpr p x) : x = p.toExpr := by
  cases h with
  | mk id eff ps acs rs cs xp xa xr xc hp ha hr hc =>
    simp only [Policy.toExpr, PrincipalScope.toExpr, ResourceScope.toExpr, hp.eq_toExpr,
      ha.eq_toExpr, hr.eq_toExpr, hc.eq_toExpr]

/-! ## Action substitution -/

theorem substituteAction_set (uid : EntityUID) (xs : List Expr) :
    substituteAction uid (.set xs) = .set (xs.map (substituteAction uid)) := by
  cases xs with
  | nil => exact Cedar.Thm.substitute_action_nil_set uid
  | cons h t => exact Cedar.Thm.substitute_action_cons_set h t uid

theorem substituteAction_call (uid : EntityUID) (f : ExtFun) (xs : List Expr) :
    substituteAction uid (.call f xs) = .call f (xs.map (substituteAction uid)) := by
  cases xs with
  | nil => exact Cedar.Thm.substitute_action_nil_call uid f
  | cons h t => exact Cedar.Thm.substitute_action_cons_call h t uid f

theorem substituteAction_record (uid : EntityUID) (axs : List (Attr × Expr)) :
    substituteAction uid (.record axs) =
      .record (axs.map fun (a, x) => (a, substituteAction uid x)) := by
  cases axs with
  | nil => exact Cedar.Thm.substitute_action_nil_record uid
  | cons h t => exact Cedar.Thm.substitute_action_cons_record h t uid

mutual
theorem SubstAction.eq_substituteAction {uid x x'} :
    SubstAction uid x x' → x' = substituteAction uid x
  | .lit _ _ | .action _ | .principal _ | .resource _ | .context _ => by
    simp only [substituteAction, mapOnVars]
  | .ite _ _ _ _ _ _ _ ha hb hc => by
    rw [ha.eq_substituteAction, hb.eq_substituteAction, hc.eq_substituteAction]
    simp only [substituteAction, mapOnVars]
  | .and _ _ _ _ _ ha hb | .or _ _ _ _ _ ha hb | .binaryApp _ _ _ _ _ _ ha hb => by
    rw [ha.eq_substituteAction, hb.eq_substituteAction]; simp only [substituteAction, mapOnVars]
  | .unaryApp _ _ _ _ ha | .getAttr _ _ _ _ ha | .hasAttr _ _ _ _ ha
  | .extHasAttr _ _ _ _ _ ha => by
    rw [ha.eq_substituteAction]; simp only [substituteAction, mapOnVars]
  | .set _ _ _ hl => by rw [substituteAction_set, hl.eq_map]
  | .call _ _ _ _ hl => by rw [substituteAction_call, hl.eq_map]
  | .record _ _ _ hr => by rw [substituteAction_record, hr.eq_map]

theorem SubstActionList.eq_map {uid xs xs'} :
    SubstActionList uid xs xs' → xs' = xs.map (substituteAction uid)
  | .nil _ => rfl
  | .cons _ _ _ _ _ hx hxs => by rw [hx.eq_substituteAction, hxs.eq_map, List.map_cons]

theorem SubstActionRecord.eq_map {uid axs axs'} :
    SubstActionRecord uid axs axs' → axs' = axs.map fun (a, x) => (a, substituteAction uid x)
  | .nil _ => rfl
  | .cons _ _ _ _ _ _ hx hxs => by rw [hx.eq_substituteAction, hxs.eq_map, List.map_cons]
end

mutual
theorem substAction_substituteAction (uid : EntityUID) :
    ∀ x : Expr, SubstAction uid x (substituteAction uid x)
  | .lit p => by simp only [substituteAction, mapOnVars]; exact .lit _ _
  | .var .action => by simp only [substituteAction, mapOnVars]; exact .action _
  | .var .principal => by simp only [substituteAction, mapOnVars]; exact .principal _
  | .var .resource => by simp only [substituteAction, mapOnVars]; exact .resource _
  | .var .context => by simp only [substituteAction, mapOnVars]; exact .context _
  | .ite a b c => by
    have h := SubstAction.ite _ _ _ _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b) (substAction_substituteAction uid c)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .and a b => by
    have h := SubstAction.and _ _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .or a b => by
    have h := SubstAction.or _ _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .unaryApp op a => by
    have h := SubstAction.unaryApp _ op _ _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .binaryApp op a b => by
    have h := SubstAction.binaryApp _ op _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .getAttr a k => by
    have h := SubstAction.getAttr _ _ k _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .hasAttr a k => by
    have h := SubstAction.hasAttr _ _ k _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .extHasAttr a k ks => by
    have h := SubstAction.extHasAttr _ _ k ks _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .set xs => by rw [substituteAction_set]; exact .set _ _ _ (substActionList_map uid xs)
  | .call f xs => by rw [substituteAction_call]; exact .call _ _ _ _ (substActionList_map uid xs)
  | .record axs => by
    rw [substituteAction_record]; exact .record _ _ _ (substActionRecord_map uid axs)

theorem substActionList_map (uid : EntityUID) :
    ∀ xs : List Expr, SubstActionList uid xs (xs.map (substituteAction uid))
  | [] => .nil _
  | x :: xs => .cons _ _ _ _ _ (substAction_substituteAction uid x) (substActionList_map uid xs)

theorem substActionRecord_map (uid : EntityUID) :
    ∀ axs : List (Attr × Expr),
      SubstActionRecord uid axs (axs.map fun (a, x) => (a, substituteAction uid x))
  | [] => .nil _
  | (_, x) :: axs =>
    .cons _ _ _ _ _ _ (substAction_substituteAction uid x) (substActionRecord_map uid axs)
end

/-! ## Declared entities -/

theorem bind_unit_ok_iff {ε : Type} {x y : Except ε Unit} :
    (x >>= fun _ => y) = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x <;> simp [bind, Except.bind]

theorem checkEntities_list_ok_iff {schema : Schema} {xs : List Expr} :
    xs.attach.forM (fun x => checkEntities schema x.val) = .ok () ↔
      ∀ x ∈ xs, checkEntities schema x = .ok () := by
  constructor
  · intro h x hx
    exact List.forM_ok_implies_all_ok _ _ h ⟨x, hx⟩ (List.mem_attach _ _)
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun y _ => h y.val y.property)

theorem checkEntities_record_ok_iff {schema : Schema} {axs : List (Attr × Expr)} :
    axs.attach₂.forM (fun p => checkEntities schema p.val.snd) = .ok () ↔
      ∀ p ∈ axs, checkEntities schema p.snd = .ok () := by
  constructor
  · intro h p hp
    have hmem : (⟨p, List.sizeOf_snd_lt_sizeOf_list hp⟩ :
        { x : Attr × Expr // sizeOf x.snd < 1 + sizeOf axs }) ∈ axs.attach₂ := by
      simp only [List.attach₂, List.mem_pmap]; exact ⟨p, hp, rfl⟩
    exact List.forM_ok_implies_all_ok _ _ h _ hmem
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun q hq => h q.val (List.mem_attach₂ hq))

theorem validEntityType_checkEntities {ets : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hnd : (ets.toList.map Prod.fst).Nodup) (h : ValidEntityType ety ets acts) :
    (ets.contains ety || acts.actionType? ety) = true := by
  cases h with
  | inSchema => rename_i hmc; simp [EntitySchema.contains, mapContains_find?_nodup hmc hnd]
  | isAction => rename_i hpk; simp [mapContainsPairKey_actionType? hpk]

theorem validEntityType_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    {ety : EntityType} (h : (ets.contains ety || acts.actionType? ety) = true) :
    ValidEntityType ety ets acts := by
  rcases Bool.or_eq_true_iff.mp h with hc | ha
  · simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨entry, hf⟩ := hc
    exact .inSchema _ _ _ _ (find?_mapContains hf)
  · obtain ⟨eid, entry, hpk⟩ := actionType?_mapContainsPairKey ha
    exact .isAction _ _ _ _ _ hpk

mutual
theorem EntitiesDeclared.checkEntities_ok {ets : EntitySchema} {acts : ActionSchema} {x : Expr}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    EntitiesDeclared ets acts x → checkEntities ⟨ets, acts⟩ x = .ok ()
  | .litBool _ _ _ | .litInt _ _ _ | .litString _ _ _ | .var _ _ _ => by simp [checkEntities]
  | .litEntity _ _ _ _ hv => by simp [checkEntities, validEntityUID_lit hv hndE hndA]
  | .ite _ _ _ _ _ ha hb hc => by
    simp [checkEntities, ha.checkEntities_ok hndE hndA, hb.checkEntities_ok hndE hndA,
      hc.checkEntities_ok hndE hndA]
  | .and _ _ _ _ ha hb | .or _ _ _ _ ha hb | .binaryApp _ _ _ _ _ ha hb => by
    simp [checkEntities, ha.checkEntities_ok hndE hndA, hb.checkEntities_ok hndE hndA]
  | .is _ _ _ _ hv ha => by
    simp [checkEntities, validEntityType_checkEntities hndE hv, ha.checkEntities_ok hndE hndA]
  | .not _ _ _ ha | .neg _ _ _ ha | .isEmpty _ _ _ ha | .like _ _ _ _ ha | .getAttr _ _ _ _ ha
  | .hasAttr _ _ _ _ ha | .extHasAttr _ _ _ _ _ ha => by
    simp [checkEntities, ha.checkEntities_ok hndE hndA]
  | .set _ _ _ hl | .call _ _ _ _ hl => by
    simp only [checkEntities]; exact checkEntities_list_ok_iff.mpr (hl.checkEntities_ok hndE hndA)
  | .record _ _ _ hr => by
    simp only [checkEntities]
    exact checkEntities_record_ok_iff.mpr (hr.checkEntities_ok hndE hndA)

theorem EntitiesDeclaredList.checkEntities_ok {ets : EntitySchema} {acts : ActionSchema}
    {xs : List Expr}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    EntitiesDeclaredList ets acts xs → ∀ x ∈ xs, checkEntities ⟨ets, acts⟩ x = .ok ()
  | .nil _ _ => by simp
  | .cons _ _ _ _ hx hxs => by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · rw [he]; exact hx.checkEntities_ok hndE hndA
    · exact hxs.checkEntities_ok hndE hndA y hy

theorem EntitiesDeclaredRecord.checkEntities_ok {ets : EntitySchema} {acts : ActionSchema}
    {axs : List (Attr × Expr)}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    EntitiesDeclaredRecord ets acts axs → ∀ p ∈ axs, checkEntities ⟨ets, acts⟩ p.snd = .ok ()
  | .nil _ _ => by simp
  | .cons _ _ _ _ _ hx hxs => by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · rw [he]; exact hx.checkEntities_ok hndE hndA
    · exact hxs.checkEntities_ok hndE hndA q hq
end

mutual
theorem entitiesDeclared_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    ∀ x : Expr, checkEntities ⟨ets, acts⟩ x = .ok () → EntitiesDeclared ets acts x
  | .lit (.bool _), _ => .litBool _ _ _
  | .lit (.int _), _ => .litInt _ _ _
  | .lit (.string _), _ => .litString _ _ _
  | .lit (.entityUID ⟨ety, eid⟩), h => by
    simp only [checkEntities] at h
    split at h
    · rename_i hcond
      exact .litEntity _ _ _ _ (validEntityUID_of_checkEntities (uid := ⟨ety, eid⟩) hcond)
    · simp at h
  | .var _, _ => .var _ _ _
  | .ite a b c, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .ite _ _ _ _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2.1) (entitiesDeclared_of_checkEntities hnd c h.2.2)
  | .and a b, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .and _ _ _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2)
  | .or a b, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .or _ _ _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2)
  | .binaryApp op a b, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .binaryApp _ _ op _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2)
  | .unaryApp (.is ety) a, h => by
    simp only [checkEntities] at h
    split at h
    · rename_i hcond
      exact .is _ _ _ _ (validEntityType_of_checkEntities hcond)
        (entitiesDeclared_of_checkEntities hnd a h)
    · simp at h
  | .unaryApp .not a, h => by
    simp only [checkEntities] at h; exact .not _ _ _ (entitiesDeclared_of_checkEntities hnd a h)
  | .unaryApp .neg a, h => by
    simp only [checkEntities] at h; exact .neg _ _ _ (entitiesDeclared_of_checkEntities hnd a h)
  | .unaryApp .isEmpty a, h => by
    simp only [checkEntities] at h
    exact .isEmpty _ _ _ (entitiesDeclared_of_checkEntities hnd a h)
  | .unaryApp (.like p) a, h => by
    simp only [checkEntities] at h
    exact .like _ _ p _ (entitiesDeclared_of_checkEntities hnd a h)
  | .getAttr a k, h => by
    simp only [checkEntities] at h
    exact .getAttr _ _ _ k (entitiesDeclared_of_checkEntities hnd a h)
  | .hasAttr a k, h => by
    simp only [checkEntities] at h
    exact .hasAttr _ _ _ k (entitiesDeclared_of_checkEntities hnd a h)
  | .extHasAttr a k ks, h => by
    simp only [checkEntities] at h
    exact .extHasAttr _ _ _ k ks (entitiesDeclared_of_checkEntities hnd a h)
  | .set xs, h => by
    simp only [checkEntities] at h
    exact .set _ _ _ (entitiesDeclaredList_of_checkEntities hnd xs (checkEntities_list_ok_iff.mp h))
  | .call f xs, h => by
    simp only [checkEntities] at h
    exact .call _ _ f _
      (entitiesDeclaredList_of_checkEntities hnd xs (checkEntities_list_ok_iff.mp h))
  | .record axs, h => by
    simp only [checkEntities] at h
    exact .record _ _ _
      (entitiesDeclaredRecord_of_checkEntities hnd axs (checkEntities_record_ok_iff.mp h))

theorem entitiesDeclaredList_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    ∀ xs : List Expr, (∀ x ∈ xs, checkEntities ⟨ets, acts⟩ x = .ok ()) →
      EntitiesDeclaredList ets acts xs
  | [], _ => .nil _ _
  | x :: xs, h => .cons _ _ _ _ (entitiesDeclared_of_checkEntities hnd x (h x (by simp)))
      (entitiesDeclaredList_of_checkEntities hnd xs (fun y hy => h y (by simp [hy])))

theorem entitiesDeclaredRecord_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    ∀ axs : List (Attr × Expr), (∀ p ∈ axs, checkEntities ⟨ets, acts⟩ p.snd = .ok ()) →
      EntitiesDeclaredRecord ets acts axs
  | [], _ => .nil _ _
  | (a, x) :: axs, h =>
    .cons _ _ a _ _ (entitiesDeclared_of_checkEntities hnd x (h (a, x) (by simp)))
      (entitiesDeclaredRecord_of_checkEntities hnd axs (fun q hq => h q (by simp [hq])))
end

/-! ## Typing in each environment -/

theorem subty_bool_anyBool {ty : CedarType} : (ty ⊑ .bool .anyBool) = true ↔ ∃ b, ty = .bool b := by
  constructor
  · intro h
    cases ty <;> simp_all [subty, lub?]
  · rintro ⟨b, rfl⟩
    cases b <;> simp [subty, lub?, lubBool]

/-- `typecheckPolicy` gives type `.bool b` exactly when `HasType false false` derives it for the
    policy expression with `action` replaced by the environment's action. -/
theorem typecheckPolicy_ok_iff {p : Policy} {env : TypeEnv} (hwf : EnvAssumptions env)
    {b : BoolType} :
    (∃ tx, typecheckPolicy p env = .ok tx ∧ tx.typeOf = .bool b) ↔
      ∃ cout, HasType false false (substituteAction env.reqty.action p.toExpr) [] env (.bool b)
        cout := by
  rw [hasType_iff_typeOf_ok hwf]
  simp only [typecheckPolicy, List.empty_eq]
  cases hto : typeOf (substituteAction env.reqty.action p.toExpr) [] env with
  | error e => simp
  | ok r =>
    obtain ⟨tx, c'⟩ := r
    simp only
    constructor
    · rintro ⟨tx', h, hty⟩
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨tx, c', rfl, hty⟩
      · simp at h
    · rintro ⟨tx', c'', h, hty⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, _⟩ := h
      subst h1
      exact ⟨tx, by simp [subty_bool_anyBool.mpr ⟨b, hty⟩], hty⟩

/-- Every environment's typed policy has a Boolean type. -/
theorem mapM_typecheckPolicy_bool {p : Policy} :
    ∀ {envs : List TypeEnv} {txs : List TypedExpr}, envs.mapM (typecheckPolicy p) = .ok txs →
      ∃ bs : List BoolType, txs.map TypedExpr.typeOf = bs.map .bool
  | [], txs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨[], rfl⟩
  | env :: envs, txs, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i tx htc
      split at h
      · simp at h
      · rename_i txs' hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨bs, hbs⟩ := mapM_typecheckPolicy_bool hrest
        simp only [typecheckPolicy] at htc
        split at htc
        · split at htc
          · rename_i hsub
            simp only [Except.ok.injEq] at htc; subst htc
            obtain ⟨b, hb⟩ := subty_bool_anyBool.mp hsub
            exact ⟨b :: bs, by simp [hb, hbs]⟩
          · simp at htc
        · simp at htc

/-- `TypedInEnvs false false` is `typecheckPolicy` succeeding in every environment. -/
theorem typedInEnvs_iff {p : Policy} :
    ∀ {envs : List TypeEnv}, (∀ env ∈ envs, EnvAssumptions env) → ∀ {bs : List BoolType},
      TypedInEnvs false false envs p.toExpr bs ↔
        ∃ txs, envs.mapM (typecheckPolicy p) = .ok txs ∧ txs.map TypedExpr.typeOf = bs.map .bool
  | [], _, bs => by
    constructor
    · intro h; cases h; exact ⟨[], rfl, rfl⟩
    · rintro ⟨txs, h, hbs⟩
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
      cases bs with
      | nil => exact .nil _
      | cons _ _ => simp at hbs
  | env :: envs, hwf, bs => by
    obtain ⟨ets, acts, ⟨pr, act, r, ctx⟩⟩ := env
    have hwf₀ := hwf _ (List.mem_cons_self ..)
    have hwf' : ∀ e ∈ envs, EnvAssumptions e := fun e he => hwf e (List.mem_cons_of_mem _ he)
    constructor
    · intro h
      cases h with
      | cons _ _ _ _ _ _ _ x' b cout _ bs' hs hht hrest =>
        obtain ⟨tx, htc, hty⟩ := (typecheckPolicy_ok_iff (b := b) hwf₀).mpr
          ⟨cout, hs.eq_substituteAction ▸ hht⟩
        obtain ⟨txs, hm, hbs⟩ := (typedInEnvs_iff (bs := bs') hwf').mp hrest
        exact ⟨tx :: txs, by simp [List.mapM_cons, htc, hm, bind, Except.bind, pure, Except.pure],
          by simp [hty, hbs]⟩
    · rintro ⟨txs, hm, hbs⟩
      simp only [List.mapM_cons, bind, Except.bind] at hm
      split at hm
      · simp at hm
      · rename_i tx htc
        split at hm
        · simp at hm
        · rename_i txs' hrest
          simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
          cases bs with
          | nil => simp at hbs
          | cons b bs' =>
            simp only [List.map_cons, List.cons.injEq] at hbs
            obtain ⟨hty, hbs'⟩ := hbs
            obtain ⟨cout, hht⟩ := (typecheckPolicy_ok_iff (b := b) hwf₀).mp
              ⟨tx, htc, hty⟩
            exact .cons _ _ _ _ _ _ _ _ _ _ _ _ (substAction_substituteAction act p.toExpr) hht
              ((typedInEnvs_iff (bs := bs') hwf').mpr ⟨txs', hrest, hbs'⟩)

/-! ## Not statically false everywhere -/

theorem notFf_iff {b : BoolType} : NotFf b ↔ b ≠ .ff := by
  constructor
  · intro h; cases h <;> simp
  · intro h
    cases b with
    | tt => exact .tt
    | ff => exact absurd rfl h
    | anyBool => exact .anyBool

theorem allFalse_eq_false_iff :
    ∀ {txs : List TypedExpr} {bs : List BoolType}, txs.map TypedExpr.typeOf = bs.map .bool →
      (allFalse txs = false ↔ SomeNotFf bs)
  | [], [], _ => by simp only [allFalse, List.all_nil, Bool.true_eq_false, false_iff]; intro h; cases h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | tx :: txs, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hty, hrest⟩ := h
    have ih := allFalse_eq_false_iff hrest
    simp only [allFalse, List.all_cons, Bool.and_eq_false_iff] at ih ⊢
    rw [ih, hty]
    constructor
    · rintro (h | h)
      · exact .here _ _ (notFf_iff.mpr (by intro hb; subst hb; simp at h))
      · exact .there _ _ h
    · intro h
      cases h with
      | here _ _ hnf => exact .inl (by have := notFf_iff.mp hnf; simpa using this)
      | there _ _ h => exact .inr h

/-! ## Validation -/

theorem mem_environments {schema : Schema} {env : TypeEnv} (h : env ∈ schema.environments) :
    env.ets = schema.ets ∧ env.acts = schema.acts := by
  simp only [Schema.environments, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem typedInEnvs_ne_nil {decl syn : Bool} {envs : List TypeEnv} {x : Expr} {bs : List BoolType}
    (h : TypedInEnvs decl syn envs x bs) (hs : SomeNotFf bs) : ∃ env, env ∈ envs := by
  cases h with
  | nil => cases hs
  | cons ets acts pr act r ctx => exact ⟨_, List.mem_cons_self ..⟩

theorem forM_singleton {ε α : Type} (f : α → Except ε Unit) (a : α) :
    [a].forM f = f a := by
  cases h : f a with
  | error e => simp [List.forM, h, bind, Except.bind]
  | ok u => cases u; simp [List.forM, h, bind, Except.bind, pure, Except.pure]

theorem typecheckPolicyWithEnvironments_ok_iff {p : Policy} {schema : Schema} :
    typecheckPolicyWithEnvironments typecheckPolicy p schema = .ok () ↔
      checkEntities schema p.toExpr = .ok () ∧
        ∃ txs, schema.environments.mapM (typecheckPolicy p) = .ok txs ∧ allFalse txs = false := by
  simp only [typecheckPolicyWithEnvironments]
  cases hce : checkEntities schema p.toExpr with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok u =>
    cases u
    cases hm : schema.environments.mapM (typecheckPolicy p) with
    | error e => simp [Except.mapError, bind, Except.bind]
    | ok txs => cases haf : allFalse txs <;> simp [haf, Except.mapError, bind, Except.bind]

/-- **Policy validation.** On a schema whose environments satisfy `EnvAssumptions`, `validate`
    accepts a policy exactly when `ValidPolicy` holds for it. -/
theorem validate_singleton_iff {schema : Schema} {p : Policy}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    validate [p] schema = .ok () ↔ ValidPolicy schema.ets schema.acts schema.environments p := by
  rw [validate, forM_singleton, typecheckPolicyWithEnvironments_ok_iff]
  constructor
  · rintro ⟨hce, txs, hm, hnf⟩
    have hent : ∀ env ∈ schema.environments, EntitiesDeclared schema.ets schema.acts p.toExpr := by
      intro env henv
      have hnd := (hwf env henv).ets_keys_nodup
      rw [(mem_environments henv).1] at hnd
      exact entitiesDeclared_of_checkEntities (acts := schema.acts) hnd _ hce
    obtain ⟨bs, hbs⟩ := mapM_typecheckPolicy_bool hm
    have hsome := (allFalse_eq_false_iff hbs).mp hnf
    have htyped := (typedInEnvs_iff hwf).mpr ⟨txs, hm, hbs⟩
    obtain ⟨env, henv⟩ := typedInEnvs_ne_nil htyped hsome
    exact .mk _ _ _ _ _ bs (policyExpr_toExpr p) (hent env henv) htyped hsome
  · intro h
    cases h with
    | mk x bs hpe hent htyped hsome =>
      rw [hpe.eq_toExpr] at hent htyped
      obtain ⟨env, henv⟩ := typedInEnvs_ne_nil htyped hsome
      obtain ⟨hets, hacts⟩ := mem_environments henv
      have hndE := (hwf env henv).ets_keys_nodup
      have hndA := (hwf env henv).acts_keys_nodup
      rw [hets] at hndE
      rw [hacts] at hndA
      obtain ⟨txs, hm, hbs⟩ := (typedInEnvs_iff hwf).mp htyped
      exact ⟨hent.checkEntities_ok hndE hndA, txs, hm, (allFalse_eq_false_iff hbs).mpr hsome⟩

/-- **Validation.** On a schema whose environments satisfy `EnvAssumptions`, `validate` accepts
    a set of policies exactly when `ValidPolicy` holds for each of them. -/
theorem validate_iff {schema : Schema} {ps : Policies}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    validate ps schema = .ok () ↔
      ∀ p ∈ ps, ValidPolicy schema.ets schema.acts schema.environments p := by
  have hone : ∀ p ∈ ps, (typecheckPolicyWithEnvironments typecheckPolicy p schema = .ok () ↔
      ValidPolicy schema.ets schema.acts schema.environments p) := by
    intro p hp
    have := validate_singleton_iff (p := p) hwf
    rwa [validate, forM_singleton] at this
  constructor
  · intro h p hp
    exact (hone p hp).mp (List.forM_ok_implies_all_ok _ _ h p hp)
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun p hp => (hone p hp).mpr (h p hp))

/-- `validate_iff` on a schema whose environments are well formed in Cedar's sense. -/
theorem validate_iff_of_wellFormed {schema : Schema} {ps : Policies}
    (hwf : ∀ env ∈ schema.environments, TypeEnv.WellFormed env) :
    validate ps schema = .ok () ↔
      ∀ p ∈ ps, ValidPolicy schema.ets schema.acts schema.environments p :=
  validate_iff (fun env henv => TypeEnv.WellFormed.envAssumptions (hwf env henv))

/-- The environments of a schema that passes Cedar's schema well-formedness check satisfy
    `EnvAssumptions`. -/
theorem envAssumptions_of_validateWellFormed {schema : Schema}
    (hwf : schema.validateWellFormed = .ok ()) :
    ∀ env ∈ schema.environments, EnvAssumptions env := fun env henv =>
  TypeEnv.WellFormed.envAssumptions
    (Cedar.Thm.env_validate_well_formed_is_sound (List.forM_ok_implies_all_ok _ _ hwf env henv))

/-- `validate_iff` on a schema that passes Cedar's schema well-formedness check. -/
theorem validate_iff_of_validateWellFormed {schema : Schema} {ps : Policies}
    (hwf : schema.validateWellFormed = .ok ()) :
    validate ps schema = .ok () ↔
      ∀ p ∈ ps, ValidPolicy schema.ets schema.acts schema.environments p :=
  validate_iff (envAssumptions_of_validateWellFormed hwf)

/-! ## Strict typing gives a valid policy -/

mutual
/-- Replacing `action` by a literal does not make an undeclared entity declared. -/
theorem SubstAction.entitiesDeclared {ets : EntitySchema} {acts : ActionSchema} {uid : EntityUID}
    {x x' : Expr} : SubstAction uid x x' → EntitiesDeclared ets acts x' → EntitiesDeclared ets acts x
  | .lit _ _, h | .principal _, h | .resource _, h | .context _, h => h
  | .action _, _ => .var _ _ _
  | .ite _ _ _ _ _ _ _ ha hb hc, .ite _ _ _ _ _ da db dc =>
    .ite _ _ _ _ _ (ha.entitiesDeclared da) (hb.entitiesDeclared db) (hc.entitiesDeclared dc)
  | .and _ _ _ _ _ ha hb, .and _ _ _ _ da db =>
    .and _ _ _ _ (ha.entitiesDeclared da) (hb.entitiesDeclared db)
  | .or _ _ _ _ _ ha hb, .or _ _ _ _ da db =>
    .or _ _ _ _ (ha.entitiesDeclared da) (hb.entitiesDeclared db)
  | .unaryApp _ _ _ _ ha, .is _ _ _ _ hv da => .is _ _ _ _ hv (ha.entitiesDeclared da)
  | .unaryApp _ _ _ _ ha, .not _ _ _ da => .not _ _ _ (ha.entitiesDeclared da)
  | .unaryApp _ _ _ _ ha, .neg _ _ _ da => .neg _ _ _ (ha.entitiesDeclared da)
  | .unaryApp _ _ _ _ ha, .isEmpty _ _ _ da => .isEmpty _ _ _ (ha.entitiesDeclared da)
  | .unaryApp _ _ _ _ ha, .like _ _ _ _ da => .like _ _ _ _ (ha.entitiesDeclared da)
  | .binaryApp _ _ _ _ _ _ ha hb, .binaryApp _ _ _ _ _ da db =>
    .binaryApp _ _ _ _ _ (ha.entitiesDeclared da) (hb.entitiesDeclared db)
  | .getAttr _ _ _ _ ha, .getAttr _ _ _ _ da => .getAttr _ _ _ _ (ha.entitiesDeclared da)
  | .hasAttr _ _ _ _ ha, .hasAttr _ _ _ _ da => .hasAttr _ _ _ _ (ha.entitiesDeclared da)
  | .extHasAttr _ _ _ _ _ ha, .extHasAttr _ _ _ _ _ da =>
    .extHasAttr _ _ _ _ _ (ha.entitiesDeclared da)
  | .set _ _ _ hl, .set _ _ _ dl => .set _ _ _ (hl.entitiesDeclared dl)
  | .record _ _ _ hr, .record _ _ _ dr => .record _ _ _ (hr.entitiesDeclared dr)
  | .call _ _ _ _ hl, .call _ _ _ _ dl => .call _ _ _ _ (hl.entitiesDeclared dl)

theorem SubstActionList.entitiesDeclared {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} {xs xs' : List Expr} :
    SubstActionList uid xs xs' → EntitiesDeclaredList ets acts xs' →
      EntitiesDeclaredList ets acts xs
  | .nil _, _ => .nil _ _
  | .cons _ _ _ _ _ hx hxs, .cons _ _ _ _ dx dxs =>
    .cons _ _ _ _ (hx.entitiesDeclared dx) (hxs.entitiesDeclared dxs)

theorem SubstActionRecord.entitiesDeclared {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} {axs axs' : List (Attr × Expr)} :
    SubstActionRecord uid axs axs' → EntitiesDeclaredRecord ets acts axs' →
      EntitiesDeclaredRecord ets acts axs
  | .nil _, _ => .nil _ _
  | .cons _ _ _ _ _ _ hx hxs, .cons _ _ _ _ _ dx dxs =>
    .cons _ _ _ _ _ (hx.entitiesDeclared dx) (hxs.entitiesDeclared dxs)
end

/-- Typing in each environment holds with weaker flags (`HasType.mono`). -/
theorem TypedInEnvs.weaken {decl syn : Bool} {envs : List TypeEnv} {x : Expr}
    {bs : List BoolType} (h : TypedInEnvs decl syn envs x bs) : TypedInEnvs false false envs x bs := by
  induction h with
  | nil => exact .nil _
  | cons _ _ _ _ _ _ _ _ _ _ _ _ hs hht _ ih => exact .cons _ _ _ _ _ _ _ _ _ _ _ _ hs hht.weaken ih

/-- A policy typed with the `decl` flag set in each of `envs` declares its entities in each. -/
theorem TypedInEnvs.entitiesDeclared {syn : Bool} {envs : List TypeEnv} {x : Expr}
    {bs : List BoolType} (h : TypedInEnvs true syn envs x bs) :
    ∀ env ∈ envs, EntitiesDeclared env.ets env.acts x := by
  induction h with
  | nil => intro _ h; nomatch h
  | cons _ _ _ _ _ _ _ _ _ _ _ _ hs hht _ ih =>
    intro env henv
    rcases List.mem_cons.mp henv with rfl | henv
    · exact hs.entitiesDeclared hht.entitiesDeclared
    · exact ih env henv

/-- **Strictly typed policies are valid.** A policy whose expression is typed by
    `HasType true syn` (in particular `HasType true true`) in every environment of `envs`, all
    sharing the schemas `ets` and `acts`, and is not `.ff` in all of them, satisfies
    `ValidPolicy`. -/
theorem TypedInEnvs.validPolicy {syn : Bool} {ets : EntitySchema} {acts : ActionSchema}
    {envs : List TypeEnv} {p : Policy} {x : Expr} {bs : List BoolType} (hx : PolicyExpr p x)
    (henvs : ∀ env ∈ envs, env.ets = ets ∧ env.acts = acts) (h : TypedInEnvs true syn envs x bs)
    (hs : SomeNotFf bs) : ValidPolicy ets acts envs p := by
  obtain ⟨env, henv⟩ := typedInEnvs_ne_nil h hs
  have hd := h.entitiesDeclared env henv
  rw [(henvs env henv).1, (henvs env henv).2] at hd
  exact .mk _ _ _ _ x bs hx hd h.weaken hs

/-- **Strictly typed policies pass `validate`.** On a schema whose environments satisfy
    `EnvAssumptions`, `validate` accepts a policy whose expression is typed by `HasType true syn`
    (in particular `HasType true true`) in every environment and is not `.ff` in all of them. -/
theorem validate_singleton_of_typedInEnvs {syn : Bool} {schema : Schema} {p : Policy} {x : Expr}
    {bs : List BoolType} (hwf : ∀ env ∈ schema.environments, EnvAssumptions env)
    (hx : PolicyExpr p x) (h : TypedInEnvs true syn schema.environments x bs)
    (hs : SomeNotFf bs) : validate [p] schema = .ok () :=
  (validate_singleton_iff hwf).mpr (h.validPolicy hx (fun _ he => mem_environments he) hs)

/-! ## Strict validation -/

mutual
/-- Replacing `action` by a declared action keeps the entities of an expression declared. -/
theorem SubstAction.entitiesDeclared_of_valid {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} {x x' : Expr} (hv : ValidEntityUID uid.ty uid.eid ets acts) :
    SubstAction uid x x' → EntitiesDeclared ets acts x → EntitiesDeclared ets acts x'
  | .lit _ _, h | .principal _, h | .resource _, h | .context _, h => h
  | .action _, _ => .litEntity _ _ _ _ hv
  | .ite _ _ _ _ _ _ _ ha hb hc, .ite _ _ _ _ _ da db dc =>
    .ite _ _ _ _ _ (ha.entitiesDeclared_of_valid hv da) (hb.entitiesDeclared_of_valid hv db)
      (hc.entitiesDeclared_of_valid hv dc)
  | .and _ _ _ _ _ ha hb, .and _ _ _ _ da db =>
    .and _ _ _ _ (ha.entitiesDeclared_of_valid hv da) (hb.entitiesDeclared_of_valid hv db)
  | .or _ _ _ _ _ ha hb, .or _ _ _ _ da db =>
    .or _ _ _ _ (ha.entitiesDeclared_of_valid hv da) (hb.entitiesDeclared_of_valid hv db)
  | .unaryApp _ _ _ _ ha, .is _ _ _ _ hve da => .is _ _ _ _ hve (ha.entitiesDeclared_of_valid hv da)
  | .unaryApp _ _ _ _ ha, .not _ _ _ da => .not _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .unaryApp _ _ _ _ ha, .neg _ _ _ da => .neg _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .unaryApp _ _ _ _ ha, .isEmpty _ _ _ da => .isEmpty _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .unaryApp _ _ _ _ ha, .like _ _ _ _ da => .like _ _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .binaryApp _ _ _ _ _ _ ha hb, .binaryApp _ _ _ _ _ da db =>
    .binaryApp _ _ _ _ _ (ha.entitiesDeclared_of_valid hv da) (hb.entitiesDeclared_of_valid hv db)
  | .getAttr _ _ _ _ ha, .getAttr _ _ _ _ da =>
    .getAttr _ _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .hasAttr _ _ _ _ ha, .hasAttr _ _ _ _ da =>
    .hasAttr _ _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .extHasAttr _ _ _ _ _ ha, .extHasAttr _ _ _ _ _ da =>
    .extHasAttr _ _ _ _ _ (ha.entitiesDeclared_of_valid hv da)
  | .set _ _ _ hl, .set _ _ _ dl => .set _ _ _ (hl.entitiesDeclared_of_valid hv dl)
  | .record _ _ _ hr, .record _ _ _ dr => .record _ _ _ (hr.entitiesDeclared_of_valid hv dr)
  | .call _ _ _ _ hl, .call _ _ _ _ dl => .call _ _ _ _ (hl.entitiesDeclared_of_valid hv dl)

theorem SubstActionList.entitiesDeclared_of_valid {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} {xs xs' : List Expr} (hv : ValidEntityUID uid.ty uid.eid ets acts) :
    SubstActionList uid xs xs' → EntitiesDeclaredList ets acts xs →
      EntitiesDeclaredList ets acts xs'
  | .nil _, _ => .nil _ _
  | .cons _ _ _ _ _ hx hxs, .cons _ _ _ _ dx dxs =>
    .cons _ _ _ _ (hx.entitiesDeclared_of_valid hv dx) (hxs.entitiesDeclared_of_valid hv dxs)

theorem SubstActionRecord.entitiesDeclared_of_valid {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} {axs axs' : List (Attr × Expr)}
    (hv : ValidEntityUID uid.ty uid.eid ets acts) :
    SubstActionRecord uid axs axs' → EntitiesDeclaredRecord ets acts axs →
      EntitiesDeclaredRecord ets acts axs'
  | .nil _, _ => .nil _ _
  | .cons _ _ _ _ _ _ hx hxs, .cons _ _ _ _ _ dx dxs =>
    .cons _ _ _ _ _ (hx.entitiesDeclared_of_valid hv dx) (hxs.entitiesDeclared_of_valid hv dxs)
end

mutual
/-- Replacing `action` by a literal does not change the keys of any record literal. -/
theorem SubstAction.parserImage_iff {uid : EntityUID} {x x' : Expr} :
    SubstAction uid x x' → (ParserImage x ↔ ParserImage x')
  | .lit _ _ | .principal _ | .resource _ | .context _ => .rfl
  | .action _ => ⟨fun _ => .lit _, fun _ => .var _⟩
  | .ite _ _ _ _ _ _ _ ha hb hc =>
    have ha := ha.parserImage_iff
    have hb := hb.parserImage_iff
    have hc := hc.parserImage_iff
    ⟨fun | .ite _ _ _ h₁ h₂ h₃ => .ite _ _ _ (ha.mp h₁) (hb.mp h₂) (hc.mp h₃),
     fun | .ite _ _ _ h₁ h₂ h₃ => .ite _ _ _ (ha.mpr h₁) (hb.mpr h₂) (hc.mpr h₃)⟩
  | .and _ _ _ _ _ ha hb =>
    have ha := ha.parserImage_iff
    have hb := hb.parserImage_iff
    ⟨fun | .and _ _ h₁ h₂ => .and _ _ (ha.mp h₁) (hb.mp h₂),
     fun | .and _ _ h₁ h₂ => .and _ _ (ha.mpr h₁) (hb.mpr h₂)⟩
  | .or _ _ _ _ _ ha hb =>
    have ha := ha.parserImage_iff
    have hb := hb.parserImage_iff
    ⟨fun | .or _ _ h₁ h₂ => .or _ _ (ha.mp h₁) (hb.mp h₂),
     fun | .or _ _ h₁ h₂ => .or _ _ (ha.mpr h₁) (hb.mpr h₂)⟩
  | .unaryApp _ _ _ _ ha =>
    have ha := ha.parserImage_iff
    ⟨fun | .unaryApp _ _ h => .unaryApp _ _ (ha.mp h),
     fun | .unaryApp _ _ h => .unaryApp _ _ (ha.mpr h)⟩
  | .binaryApp _ _ _ _ _ _ ha hb =>
    have ha := ha.parserImage_iff
    have hb := hb.parserImage_iff
    ⟨fun | .binaryApp _ _ _ h₁ h₂ => .binaryApp _ _ _ (ha.mp h₁) (hb.mp h₂),
     fun | .binaryApp _ _ _ h₁ h₂ => .binaryApp _ _ _ (ha.mpr h₁) (hb.mpr h₂)⟩
  | .getAttr _ _ _ _ ha =>
    have ha := ha.parserImage_iff
    ⟨fun | .getAttr _ _ h => .getAttr _ _ (ha.mp h),
     fun | .getAttr _ _ h => .getAttr _ _ (ha.mpr h)⟩
  | .hasAttr _ _ _ _ ha =>
    have ha := ha.parserImage_iff
    ⟨fun | .hasAttr _ _ h => .hasAttr _ _ (ha.mp h),
     fun | .hasAttr _ _ h => .hasAttr _ _ (ha.mpr h)⟩
  | .extHasAttr _ _ _ _ _ ha =>
    have ha := ha.parserImage_iff
    ⟨fun | .extHasAttr _ _ _ hp h => .extHasAttr _ _ _ hp (ha.mp h),
     fun | .extHasAttr _ _ _ hp h => .extHasAttr _ _ _ hp (ha.mpr h)⟩
  | .set _ _ _ hl =>
    have hl := hl.parserImage_iff
    ⟨fun | .set _ h => .set _ (hl.mp h), fun | .set _ h => .set _ (hl.mpr h)⟩
  | .record _ _ _ hr =>
    have ⟨hk, hv⟩ := hr.parserImage_iff
    ⟨fun | .record _ hn h => .record _ (hk ▸ hn) (hv.mp h),
     fun | .record _ hn h => .record _ (hk ▸ hn) (hv.mpr h)⟩
  | .call _ _ _ _ hl =>
    have hl := hl.parserImage_iff
    ⟨fun | .call _ _ h => .call _ _ (hl.mp h), fun | .call _ _ h => .call _ _ (hl.mpr h)⟩

theorem SubstActionList.parserImage_iff {uid : EntityUID} {xs xs' : List Expr} :
    SubstActionList uid xs xs' →
      ((∀ x ∈ xs, ParserImage x) ↔ ∀ x ∈ xs', ParserImage x)
  | .nil _ => .rfl
  | .cons _ _ _ _ _ hx hxs => by
    rw [List.forall_mem_cons, List.forall_mem_cons, hx.parserImage_iff,
      hxs.parserImage_iff]

theorem SubstActionRecord.parserImage_iff {uid : EntityUID}
    {axs axs' : List (Attr × Expr)} :
    SubstActionRecord uid axs axs' → axs.map Prod.fst = axs'.map Prod.fst ∧
      ((∀ x ∈ axs.map Prod.snd, ParserImage x) ↔
        ∀ x ∈ axs'.map Prod.snd, ParserImage x)
  | .nil _ => ⟨rfl, .rfl⟩
  | .cons _ _ _ _ _ _ hx hxs =>
    have ⟨hk, hv⟩ := hxs.parserImage_iff
    ⟨by simp only [List.map_cons, hk], by
      simp only [List.map_cons, List.forall_mem_cons, hx.parserImage_iff, hv]⟩
end

/-- The action of a schema environment is declared in the schema. -/
theorem validEntityUID_action_of_mem_environments {schema : Schema} {env : TypeEnv}
    (h : env ∈ schema.environments) :
    ValidEntityUID env.reqty.action.ty env.reqty.action.eid schema.ets schema.acts := by
  obtain ⟨_, _, entry, hmem, _⟩ := Thm.mem_environments h
  obtain ⟨e, hpk⟩ := mapContainsPairKey_of_mapContains (mem_toList_mapContains hmem)
  exact .action _ _ _ _ _ hpk

/-- **Strengthening the typing in each environment.** A policy expression typed by
    `HasType false false` in each of `envs`, with declared entities and in the parser's image, and
    each environment's action declared, is typed by `HasType true true` in each. -/
theorem TypedInEnvs.strengthen {envs : List TypeEnv} {x : Expr} {bs : List BoolType}
    (h : TypedInEnvs false false envs x bs)
    (hd : ∀ env ∈ envs, EntitiesDeclared env.ets env.acts x ∧
      ValidEntityUID env.reqty.action.ty env.reqty.action.eid env.ets env.acts)
    (hk : ParserImage x) : TypedInEnvs true true envs x bs := by
  induction h with
  | nil => exact .nil _
  | cons _ _ _ _ _ _ _ _ _ _ _ _ hs hht _ ih =>
    have ⟨hdx, hv⟩ := hd _ List.mem_cons_self
    exact .cons _ _ _ _ _ _ _ _ _ _ _ _ hs
      (hht.strengthen (hs.entitiesDeclared_of_valid hv hdx) (hs.parserImage_iff.mp hk))
      (ih (fun env henv => hd env (List.mem_cons_of_mem _ henv)) hk)

/-- A policy typed with the `syn` flag set in some environment is in the parser's image. -/
theorem TypedInEnvs.parserImage {decl : Bool} {envs : List TypeEnv} {x : Expr}
    {bs : List BoolType} (h : TypedInEnvs decl true envs x bs) (hs : SomeNotFf bs) :
    ParserImage x := by
  cases h with
  | nil => cases hs
  | cons _ _ _ _ _ _ _ _ _ _ _ _ hsub hht _ =>
    exact hsub.parserImage_iff.mpr hht.parserImage

/-- **Strict policy validation.** On a schema whose environments satisfy `EnvAssumptions`, the
    policies that `validate` accepts and that are in the image of the parser (`ParserImage`, as
    every parsed policy is) are exactly those satisfying `ValidPolicyStrict`, i.e. typed by
    `HasType true true` in every environment. -/
theorem validate_and_parserImage_iff_strict {schema : Schema} {p : Policy}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    (validate [p] schema = .ok () ∧ ParserImage p.toExpr) ↔
      ValidPolicyStrict schema.ets schema.acts schema.environments p := by
  constructor
  · rintro ⟨hv, hk⟩
    cases (validate_singleton_iff hwf).mp hv with
    | mk x bs hpe hent htyped hsome =>
      rw [← hpe.eq_toExpr] at hk
      refine .mk _ _ _ _ x bs hpe hent (htyped.strengthen (fun env henv => ?_) hk) hsome
      obtain ⟨hets, hacts⟩ := mem_environments henv
      rw [hets, hacts]
      exact ⟨hent, validEntityUID_action_of_mem_environments henv⟩
  · intro h
    cases h with
    | mk x bs hpe _ htyped hsome =>
      exact ⟨validate_singleton_of_typedInEnvs hwf hpe htyped hsome,
        hpe.eq_toExpr ▸ htyped.parserImage hsome⟩

/-- `validate_and_parserImage_iff_strict` on a schema that passes Cedar's schema well-formedness
    check. -/
theorem validate_and_parserImage_iff_strict_of_validateWellFormed {schema : Schema} {p : Policy}
    (hwf : schema.validateWellFormed = .ok ()) :
    (validate [p] schema = .ok () ∧ ParserImage p.toExpr) ↔
      ValidPolicyStrict schema.ets schema.acts schema.environments p :=
  validate_and_parserImage_iff_strict (envAssumptions_of_validateWellFormed hwf)

end Cedar.Validation.Relational

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

import CedarGenProof.ExprGen
import CedarGen.Relational.ValidIn
import Specimen.Basalt

/-! # Generators for valid policies

A policy is valid for a schema when it is well typed in every request environment of the schema and
not statically false in all of them (`ValidPolicy`). `GuidedPolicy` generates over all of them at once:
the scope in one environment, which fixes the environments where it is not statically false
(`ApplicableEnvs`); then each condition over the environments where everything before it is still live
(`CondsOver`), either Boolean in all of them or guarded by a test on the request that is false in some.

`ValidGuidedPolicy` ends by checking `ValidPolicy` with the validator (`validIn_iff`), so what it
produces is valid by construction; the guide only makes the check likely to pass. -/

namespace Cedar.Validation.Relational.PolicyGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Scoring Schedules
open ExprGen.RequestVars

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Scopes -/

/-- An action declared in `acts`. -/
inductive ActionDeclared : ActionSchema → EntityUID → Prop where
  | mk : ∀ acts uid entry, MapContains uid entry acts → ActionDeclared acts uid

inductive ActionsDeclared : ActionSchema → List EntityUID → Prop where
  | nil : ∀ acts, ActionsDeclared acts []
  | cons : ∀ acts uid uids, ActionDeclared acts uid → ActionsDeclared acts uids →
      ActionsDeclared acts (uid :: uids)

/-- Declared actions, one of which `act` is a descendant of. -/
inductive ActionAncestorIn : ActionSchema → EntityUID → List EntityUID → Prop where
  | here : ∀ acts act anc uids, ActionDescendentOf acts act anc → ActionDeclared acts (id anc) →
      ActionsDeclared acts uids → ActionAncestorIn acts act (anc :: uids)
  | there : ∀ acts act uid uids, ActionDeclared acts uid → ActionAncestorIn acts act uids →
      ActionAncestorIn acts act (uid :: uids)

/-- A principal or resource scope that is not statically false when the principal (resource)
    has entity type `ety`. Its entity literals are declared. -/
inductive ScopeFor : EntitySchema → ActionSchema → EntityType → Scope → Prop where
  | any : ∀ ets acts ety, ScopeFor ets acts ety .any
  | eq : ∀ ets acts ety eid, ValidEntityUID ety eid ets acts → ScopeFor ets acts ety (.eq ⟨ety, eid⟩)
  | mem : ∀ ets acts ety anc eid, DescendentOf ets acts ety anc → ValidEntityUID anc eid ets acts →
      ScopeFor ets acts ety (.mem ⟨anc, eid⟩)
  | is : ∀ ets acts ety, ScopeFor ets acts ety (.is ety)
  | isMem : ∀ ets acts ety anc eid, DescendentOf ets acts ety anc →
      ValidEntityUID anc eid ets acts → ScopeFor ets acts ety (.isMem ety ⟨anc, eid⟩)

/-- An action scope that is not statically false for the action `act`. -/
inductive ActionScopeFor : ActionSchema → EntityUID → ActionScope → Prop where
  | any : ∀ acts act, ActionScopeFor acts act (.actionScope .any)
  | eq : ∀ acts act, ActionScopeFor acts act (.actionScope (.eq act))
  | mem : ∀ acts act anc, ActionDescendentOf acts act anc → ActionDeclared acts (id anc) →
      ActionScopeFor acts act (.actionScope (.mem anc))
  | inAny : ∀ acts act uids, ActionAncestorIn acts act uids →
      ActionScopeFor acts act (.actionInAny uids)

/-! ## What the typechecker says in each environment

These run `typeOf`, which agrees with `HasType` (`hasType_iff_typeOf_ok`). -/

/-- The Boolean type of `x` in `env`, if it has one. -/
def boolTypeIn (env : TypeEnv) (x : Expr) : Option BoolType :=
  match typeOf x [] env with
  | .ok (tx, _) => match tx.typeOf with
    | .bool b => some b
    | _ => none
  | .error _ => none

/-- A condition of kind `k` with body `x` is live in `env`: Boolean, and not statically
    false. -/
def liveIn (k : ConditionKind) (env : TypeEnv) (x : Expr) : Bool :=
  match k, boolTypeIn env x with
  | .when, some b => b != .ff
  | .unless, some b => b != .tt
  | _, none => false

inductive BoolIn : TypeEnv → Expr → Prop where
  | mk : ∀ env x, (boolTypeIn env x).isSome = true → BoolIn env x

inductive LiveIn : ConditionKind → TypeEnv → Expr → Prop where
  | mk : ∀ k env x, liveIn k env x = true → LiveIn k env x

inductive DeadIn : ConditionKind → TypeEnv → Expr → Prop where
  | mk : ∀ k env x, liveIn k env x = false → DeadIn k env x

instance : DecOpt (BoolIn env x) where decOpt _ := .ok (boolTypeIn env x).isSome
instance : DecOpt (LiveIn k env x) where decOpt _ := .ok (liveIn k env x)
instance : DecOpt (DeadIn k env x) where decOpt _ := .ok !(liveIn k env x)

/-- The scope is not statically false in `env`. -/
def scopeLiveIn (env : TypeEnv) (ps : PrincipalScope) (acs : ActionScope) (rs : ResourceScope) :
    Bool :=
  match typecheckPolicy ⟨"", .permit, ps, acs, rs, []⟩ env with
  | .ok tx => tx.typeOf != .bool .ff
  | .error _ => false

inductive ScopeLiveIn : TypeEnv → PrincipalScope → ActionScope → ResourceScope → Prop where
  | mk : ∀ env ps acs rs, scopeLiveIn env ps acs rs = true → ScopeLiveIn env ps acs rs

inductive ScopeDeadIn : TypeEnv → PrincipalScope → ActionScope → ResourceScope → Prop where
  | mk : ∀ env ps acs rs, scopeLiveIn env ps acs rs = false → ScopeDeadIn env ps acs rs

instance : DecOpt (ScopeLiveIn env ps acs rs) where decOpt _ := .ok (scopeLiveIn env ps acs rs)
instance : DecOpt (ScopeDeadIn env ps acs rs) where decOpt _ := .ok !(scopeLiveIn env ps acs rs)

/-! The guide's checks are complete: each answers exactly whether its relation holds. -/
section GuideLaws
open Specimen.Correctness
instance : DecOptCompleteAll (BoolIn env x) :=
  ⟨fun h _ => by cases h with | mk h => exact congrArg Except.ok h⟩
instance : DecOptRefuteCompleteAll (BoolIn env x) :=
  ⟨fun h _ => congrArg Except.ok (Bool.eq_false_iff.mpr fun hb => h (.mk _ _ hb))⟩
instance : DecOptCompleteAll (LiveIn k env x) :=
  ⟨fun h _ => by cases h with | mk h => exact congrArg Except.ok h⟩
instance : DecOptRefuteCompleteAll (LiveIn k env x) :=
  ⟨fun h _ => congrArg Except.ok (Bool.eq_false_iff.mpr fun hb => h (.mk _ _ _ hb))⟩
instance : DecOptCompleteAll (DeadIn k env x) :=
  ⟨fun h _ => by cases h with | mk h => exact congrArg Except.ok (by simp [h])⟩
instance : DecOptRefuteCompleteAll (DeadIn k env x) :=
  ⟨fun h _ => congrArg Except.ok (by
    cases hb : liveIn k env x
    · exact absurd (.mk _ _ _ hb) h
    · rfl)⟩
instance : DecOptCompleteAll (ScopeLiveIn env ps acs rs) :=
  ⟨fun h _ => by cases h with | mk h => exact congrArg Except.ok h⟩
instance : DecOptRefuteCompleteAll (ScopeLiveIn env ps acs rs) :=
  ⟨fun h _ => congrArg Except.ok (Bool.eq_false_iff.mpr fun hb => h (.mk _ _ _ _ hb))⟩
instance : DecOptCompleteAll (ScopeDeadIn env ps acs rs) :=
  ⟨fun h _ => by cases h with | mk h => exact congrArg Except.ok (by simp [h])⟩
instance : DecOptRefuteCompleteAll (ScopeDeadIn env ps acs rs) :=
  ⟨fun h _ => congrArg Except.ok (by
    cases hb : scopeLiveIn env ps acs rs
    · exact absurd (.mk _ _ _ _ hb) h
    · rfl)⟩
end GuideLaws

/-! ## Environments -/

inductive EnvIn : List TypeEnv → TypeEnv → Prop where
  | here : ∀ env envs, EnvIn (env :: envs) env
  | there : ∀ env env' envs, EnvIn envs env → EnvIn (env' :: envs) env

/-- `app` are the environments of `envs` where the scope is not statically false. -/
inductive ApplicableEnvs : List TypeEnv → PrincipalScope → ActionScope → ResourceScope →
    List TypeEnv → Prop where
  | nil : ∀ ps acs rs, ApplicableEnvs [] ps acs rs []
  | keep : ∀ env envs ps acs rs app, ScopeLiveIn env ps acs rs →
      ApplicableEnvs envs ps acs rs app → ApplicableEnvs (env :: envs) ps acs rs (env :: app)
  | drop : ∀ env envs ps acs rs app, ScopeDeadIn env ps acs rs →
      ApplicableEnvs envs ps acs rs app → ApplicableEnvs (env :: envs) ps acs rs app

inductive AllBoolIn : List TypeEnv → Expr → Prop where
  | nil : ∀ x, AllBoolIn [] x
  | cons : ∀ env envs x, BoolIn env x → AllBoolIn envs x → AllBoolIn (env :: envs) x

/-- `live` are the environments of `envs` where a condition of kind `k` with body `x` is
    live. -/
inductive LiveEnvs : ConditionKind → List TypeEnv → Expr → List TypeEnv → Prop where
  | nil : ∀ k x, LiveEnvs k [] x []
  | keep : ∀ k env envs x live, LiveIn k env x → LiveEnvs k envs x live →
      LiveEnvs k (env :: envs) x (env :: live)
  | drop : ∀ k env envs x live, DeadIn k env x → LiveEnvs k envs x live →
      LiveEnvs k (env :: envs) x live

/-- Some environment's principal (resource) type is `t`. -/
inductive PrincipalTypeIn : List TypeEnv → EntityType → Prop where
  | here : ∀ ets acts p a r ctx envs, PrincipalTypeIn (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs) p
  | there : ∀ env envs p, PrincipalTypeIn envs p → PrincipalTypeIn (env :: envs) p

inductive ResourceTypeIn : List TypeEnv → EntityType → Prop where
  | here : ∀ ets acts p a r ctx envs, ResourceTypeIn (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs) r
  | there : ∀ env envs r, ResourceTypeIn envs r → ResourceTypeIn (env :: envs) r

/-- Some environment's context has attribute `k`. -/
inductive ContextAttrIn : List TypeEnv → Attr → Prop where
  | here : ∀ ets acts p a r ctx envs k qty, MapContains k qty ctx →
      ContextAttrIn (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs) k
  | there : ∀ env envs k, ContextAttrIn envs k → ContextAttrIn (env :: envs) k

/-- `ins` are the environments of `envs` whose principal type is `t`, and `outs` the rest. -/
inductive SplitPrincipal : EntityType → List TypeEnv → List TypeEnv → List TypeEnv → Prop where
  | nil : ∀ t, SplitPrincipal t [] [] []
  | keep : ∀ t ets acts a r ctx envs ins outs, SplitPrincipal t envs ins outs →
      SplitPrincipal t (⟨ets, acts, ⟨t, a, r, ctx⟩⟩ :: envs)
        (⟨ets, acts, ⟨t, a, r, ctx⟩⟩ :: ins) outs
  | drop : ∀ t ets acts p a r ctx envs ins outs, p ≠ t → SplitPrincipal t envs ins outs →
      SplitPrincipal t (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs) ins
        (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: outs)

/-- `ins` are the environments of `envs` whose resource type is `t`, and `outs` the rest. -/
inductive SplitResource : EntityType → List TypeEnv → List TypeEnv → List TypeEnv → Prop where
  | nil : ∀ t, SplitResource t [] [] []
  | keep : ∀ t ets acts p a ctx envs ins outs, SplitResource t envs ins outs →
      SplitResource t (⟨ets, acts, ⟨p, a, t, ctx⟩⟩ :: envs)
        (⟨ets, acts, ⟨p, a, t, ctx⟩⟩ :: ins) outs
  | drop : ∀ t ets acts p a r ctx envs ins outs, r ≠ t → SplitResource t envs ins outs →
      SplitResource t (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs) ins
        (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: outs)

/-- `ins` are the environments of `envs` whose context has attribute `k`, and `outs` the rest. -/
inductive SplitContext : Attr → List TypeEnv → List TypeEnv → List TypeEnv → Prop where
  | nil : ∀ k, SplitContext k [] [] []
  | keep : ∀ k ets acts p a r ctx qty envs ins outs, MapContains (id k) qty ctx →
      SplitContext k envs ins outs →
      SplitContext k (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs)
        (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: ins) outs
  | drop : ∀ k ets acts p a r ctx envs ins outs, MapNotContainsKey k ctx →
      SplitContext k envs ins outs →
      SplitContext k (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: envs) ins
        (⟨ets, acts, ⟨p, a, r, ctx⟩⟩ :: outs)

/-! ## Conditions over several environments -/

inductive NotTt : BoolType → Prop where
  | ff : NotTt .ff
  | anyBool : NotTt .anyBool

/-- A `when` body that is Boolean in each environment of `envs`, and the (nonempty)
    environments `live` where it is not statically false.

    A guard must be statically false in some environment (`o :: os`): one that holds in all
    of them only nests the condition. The `id`s keep Specimen from producing the
    environments or the body a second time where they are already known. -/
inductive WhenOver : List TypeEnv → Expr → List TypeEnv → Prop where
  | uniform : ∀ env envs body bty cout live,
      NotFf bty →
      HasType true true body [] env (.bool (id bty)) cout →
      AllBoolIn envs (id body) →
      LiveEnvs .when envs (id body) live →
      WhenOver (env :: envs) body (env :: live)
  | guardPrincipal : ∀ envs t ins o os b live,
      PrincipalTypeIn envs t →
      SplitPrincipal t envs ins (o :: os) →
      WhenOver (id ins) b live →
      WhenOver envs (.and (.unaryApp (.is t) (.var .principal)) b) live
  | guardResource : ∀ envs t ins o os b live,
      ResourceTypeIn envs t →
      SplitResource t envs ins (o :: os) →
      WhenOver (id ins) b live →
      WhenOver envs (.and (.unaryApp (.is t) (.var .resource)) b) live
  | guardContext : ∀ envs k ins o os b live,
      ContextAttrIn envs k →
      SplitContext k envs ins (o :: os) →
      WhenOver (id ins) b live →
      WhenOver envs (.and (.hasAttr (.var .context) k) b) live

/-- An `unless` body that is Boolean in each environment of `envs`, and the (nonempty)
    environments `live` where it is not statically true. -/
inductive UnlessOver : List TypeEnv → Expr → List TypeEnv → Prop where
  | uniform : ∀ env envs body bty cout live,
      NotTt bty →
      HasType true true body [] env (.bool (id bty)) cout →
      AllBoolIn envs (id body) →
      LiveEnvs .unless envs (id body) live →
      UnlessOver (env :: envs) body (env :: live)

/-- Conditions, each over the environments where the earlier ones are live. -/
inductive CondsOver : List TypeEnv → List Condition → Prop where
  | nil : ∀ envs, CondsOver envs []
  | when : ∀ envs body live rest, WhenOver (id envs) body live → CondsOver (id live) rest →
      CondsOver envs (⟨.when, body⟩ :: rest)
  | unless : ∀ envs body live rest, UnlessOver (id envs) body live → CondsOver (id live) rest →
      CondsOver envs (⟨.unless, body⟩ :: rest)

/-! ## Policies -/

/-- A policy, generated over the environments `envs` together. -/
inductive GuidedPolicy : List TypeEnv → Policy → Prop where
  /-- The scope is generated for one environment. -/
  | scoped : ∀ envs ets acts reqty pid eff ps acs rs app cs,
      EnvIn envs ⟨ets, acts, reqty⟩ →
      ScopeFor ets acts reqty.principal ps →
      ActionScopeFor acts reqty.action acs →
      ScopeFor ets acts reqty.resource rs →
      ApplicableEnvs envs (id (.principalScope ps)) (id acs) (id (.resourceScope rs)) app →
      CondsOver (id app) cs →
      GuidedPolicy envs ⟨pid, eff, .principalScope ps, acs, .resourceScope rs, cs⟩
  /-- Only the action is constrained, so the conditions range over every environment of the
      action scope. -/
  | broad : ∀ envs ets acts reqty pid eff acs app cs,
      EnvIn envs ⟨ets, acts, reqty⟩ →
      ActionScopeFor acts reqty.action acs →
      ApplicableEnvs envs (id (.principalScope .any)) (id acs) (id (.resourceScope .any)) app →
      CondsOver (id app) cs →
      GuidedPolicy envs ⟨pid, eff, .principalScope .any, acs, .resourceScope .any, cs⟩

/-- A guided policy the validator accepts for the environments `envs` of the schemas `ets` and
    `acts`: its last premise is the validator's run (`validIn`) itself, which decides `ValidPolicy` on
    well-formed environments (`ValidGuidedPolicy.valid`). -/
inductive ValidGuidedPolicy : EntitySchema → ActionSchema → List TypeEnv → Policy → Prop where
  | mk : ∀ ets acts envs p, GuidedPolicy envs p → validIn ets acts envs (id p) = true →
      ValidGuidedPolicy ets acts envs p

/-- On well-formed environments, a `ValidGuidedPolicy` is a valid policy. -/
theorem ValidGuidedPolicy.valid {ets : EntitySchema} {acts : ActionSchema} {envs : List TypeEnv}
    {p : Policy} (h : ValidGuidedPolicy ets acts envs p)
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup)
    (hwf : ∀ env ∈ envs, EnvAssumptions env) :
    ValidPolicy ets acts envs p := by
  cases h with
  | mk _ hv => exact (validIn_iff hndE hndA hwf).mp hv

/-- Raises `CondsOver.when`, so policies carry conditions more often. -/
def favorConditions (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str (.str _ "CondsOver") "when" => baseWeight * 3 + 1
  | _ => baseWeight

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.completeAllSorts true in
set_option specimen.completeDropUnreachable true in
set_option specimen.reachSimpAll false in
set_option basalt.walk.pruneDischarge false in
set_option specimen.parallelProofs true in
set_option specimen.parallelCodegen true in
set_option specimen.reportPhaseTimers true in
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "Cedar.Validation.Relational.PolicyGen.favorConditions" in
derive_mutual
  generator (fun envs => ∃ p, GuidedPolicy envs p)

set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.completeAllSorts true in
set_option specimen.completeDropUnreachable true in
set_option specimen.reachSimpAll false in
set_option basalt.walk.pruneDischarge false in
set_option specimen.parallelProofs true in
set_option specimen.parallelCodegen true in
set_option specimen.reportPhaseTimers true in
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
derive_mutual
  generator (fun ets acts envs => ∃ p, ValidGuidedPolicy ets acts envs p)

end Cedar.Validation.Relational.PolicyGen

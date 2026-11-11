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

import Cedar.Validation.Relational.Schema
import CedarGen.Relational.Instances
import Specimen.Basalt
import Specimen.Correctness.SoundOf
import Specimen.Correctness.CompleteOf
import CedarGen.Relational.SchemaLeaves

/-! # Generator for well-formed type environments

`Schema.WfTypeEnv` derived with Specimen: entity types with closed ancestor sets, attributes,
tags and enums, and actions over them with closed action ancestors. `canonicalizeEnv` then sorts
and deduplicates the maps and sets, as a parsed schema has them. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-- Every list here is `nil | cons`, and the budget-aware weights alone stop each one with
    probability about 0.57 whatever the size, so lists average under one element. `cons` is raised so
    the size, not the stopping weight, bounds them. Ancestor lists are mostly empty otherwise. Mild: `pick` competes for fuel with the rest of the
    recursion, and large multipliers on it cause backtracking for little gain. Standard entities,
    which enums cannot be ancestors of, are raised too, giving the hierarchy more nodes. -/
def favorAncestors (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str (.str _ "WfEntitiesGoR") "standard"   => baseWeight * 64 + 1
  | .str (.str _ "WfEntitiesGoR") "enum"       => baseWeight * 16 + 1
  | .str (.str _ "WfActionsGoB") "cons"        => baseWeight * 8 + 1
  | .str (.str _ "WfActionsGoR") "cons"        => baseWeight * 4 + 1
  | .str (.str _ "WfActionsGoR") "request"     => baseWeight * 2 + 1
  | .str (.str _ "BoundedTypes") "cons"        => baseWeight * 4 + 1
  | .str (.str _ "ContainsBounded") "there"    => baseWeight * 4 + 1
  | .str (.str _ "WfPrincipalTypes") "cons"    => baseWeight * 4 + 1
  | .str (.str _ "WfResourceTypes") "cons"     => baseWeight * 4 + 1
  | _                                          => baseWeight

/-- `SelectRemove xs`, uniformly: the derived `here`/`there` generator is geometric, biased to the
    head of the pool `WfActionSchema` draws action ids from. -/
instance {α} {xs : List α} : BacktrackGenFor (α × List α) (fun p => SelectRemove xs p.1 p.2) where
  gen _ _ := do
    if xs.isEmpty then Specimen.Fail.fail else
    let i ← chooseNat 0 (xs.length - 1)
    match xs[i]? with
    | some x => pure (x, xs.eraseIdx i)
    | none => Specimen.Fail.fail

/-- `DefinedEntityType ets`, uniformly: the derived `here`/`there` generator is geometric, biased to
    the most recently declared type. -/
instance {ets : List EntityType} : BacktrackGenFor EntityType (fun et => DefinedEntityType ets et) where
  gen _ _ := do
    if ets.isEmpty then Specimen.Fail.fail else
    let i ← chooseNat 0 (ets.length - 1)
    match ets[i]? with
    | some et => pure et
    | none => Specimen.Fail.fail

/-! ## A generator-shaped `WfTypeEnv`, with a budget of request environments

`WfTypeEnv` asks, last, that some action have a principal type and a resource type, the request's;
a generator meets that only by luck after drawing everything else. `GenTypeEnvB` carries the request
as pending while it builds the actions: one of them, at any position, is the request's, and declares
both. Its actions also share a budget of request environments, each action's resources bounded by
what its principals leave of it. Nothing else changes, so it describes exactly the well-formed
environments with at most `budget` request environments (`genTypeEnvB_iff`). -/

/-! ### How dense the hierarchies are

A schema's hierarchies are drawn in one of three modes, chosen per schema, so that a campaign
covers each:
* `dense`: every earlier type (action) is a parent independently with probability one half, as in
  Cedar's own schema generator; the closures come out close to complete.
* `sparse`: at most one parent, uniform among the earlier ones (or none), and its closure: a random
  recursive forest, with closures logarithmic in the number of types.
* `flat`: no parents. -/

inductive HierMode where
  | dense
  | sparse
  | flat
  deriving Repr, DecidableEq, Inhabited

/-- At most one parent, an earlier `p`, and its closed ancestors `pset`. -/
inductive PickOneAncestor : List (EntityType × List EntityType) → List EntityType → Prop where
  | none : ∀ built, PickOneAncestor built []
  | one : ∀ built p pset, (p, pset) ∈ built → PickOneAncestor built (p :: pset)

/-- `PickOneAncestor` for actions. -/
inductive PickOneActionAncestor : List (EntityUID × List EntityUID) → List EntityUID → Prop where
  | none : ∀ built, PickOneActionAncestor built []
  | one : ∀ built p pset, (p, pset) ∈ built → PickOneActionAncestor built (p :: pset)

/-- An entity type's closed ancestors, in mode `r`. -/
inductive Ancestors : HierMode → List (EntityType × List EntityType) → List EntityType → Prop where
  | dense : ∀ built ancestors, PickClosedAncestors built ancestors → Ancestors .dense built ancestors
  | sparse : ∀ built ancestors, PickOneAncestor built ancestors → Ancestors .sparse built ancestors
  | flat : ∀ built, Ancestors .flat built []

/-- An action's closed ancestors, in mode `r`. -/
inductive ActAncestors : HierMode → List (EntityUID × List EntityUID) → List EntityUID → Prop where
  | dense : ∀ built ancestors, PickClosedActionAncestors built ancestors →
      ActAncestors .dense built ancestors
  | sparse : ∀ built ancestors, PickOneActionAncestor built ancestors →
      ActAncestors .sparse built ancestors
  | flat : ∀ built, ActAncestors .flat built []

/-- `PickOneAncestor built`, uniformly: no parent, or each earlier type, with probability
    `1 / (built.length + 1)` each. -/
instance {built : List (EntityType × List EntityType)} :
    BacktrackGenFor (List EntityType) (fun ancestors => PickOneAncestor built ancestors) where
  gen _ _ := do
    let i ← chooseNat 0 built.length
    if i = 0 then pure [] else
    match built[i - 1]? with
    | some (p, pset) => pure (p :: pset)
    | none => Specimen.Fail.fail

/-- `PickOneActionAncestor built`, uniformly, as `PickOneAncestor`. -/
instance {built : List (EntityUID × List EntityUID)} :
    BacktrackGenFor (List EntityUID) (fun ancestors => PickOneActionAncestor built ancestors) where
  gen _ _ := do
    let i ← chooseNat 0 built.length
    if i = 0 then pure [] else
    match built[i - 1]? with
    | some (p, pset) => pure (p :: pset)
    | none => Specimen.Fail.fail

/-- `WfEntitiesGo`, its ancestors in mode `r`. -/
inductive WfEntitiesGoR : HierMode →
    List (EntityType × List EntityType) → List EntityType → List EntityType →
    List (EntityType × EntitySchemaEntry) → Prop where
  | nil : ∀ r built names, WfEntitiesGoR r built names names []
  | standard : ∀ r built names et ancestors attrs tags allNames rest,
      NotInET et names →
      Ancestors r built ancestors →
      WfAttrs Option.none (et :: names) attrs →
      WfTags (et :: names) tags →
      WfEntitiesGoR r ((et, ancestors) :: built) (et :: names) allNames rest →
      WfEntitiesGoR r built names allNames
        ((et, .standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
  | enum : ∀ r built names et eids allNames rest,
      NotInET et names →
      WfEntitiesGoR r built (et :: names) allNames rest →
      WfEntitiesGoR r built names allNames ((et, .enum (Set.mk eids)) :: rest)

/-- `WfEntitiesGoR` declaring at least one type. -/
inductive WfEntitiesGo1 : HierMode →
    List (EntityType × List EntityType) → List EntityType → List EntityType →
    List (EntityType × EntitySchemaEntry) → Prop where
  | standard : ∀ r built names et ancestors attrs tags allNames rest,
      NotInET et names →
      Ancestors r built ancestors →
      WfAttrs Option.none (et :: names) attrs →
      WfTags (et :: names) tags →
      WfEntitiesGoR r ((et, ancestors) :: built) (et :: names) allNames rest →
      WfEntitiesGo1 r built names allNames
        ((et, .standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
  | enum : ∀ r built names et eids allNames rest,
      NotInET et names →
      WfEntitiesGoR r built (et :: names) allNames rest →
      WfEntitiesGo1 r built names allNames ((et, .enum (Set.mk eids)) :: rest)

/-- At most `n` defined entity types. -/
inductive BoundedTypes : List EntityType → Nat → List EntityType → Prop where
  | nil : ∀ ets n, BoundedTypes ets n []
  | cons : ∀ ets n x xs,
      DefinedEntityType ets x →
      BoundedTypes ets n xs →
      BoundedTypes ets (n + 1) (x :: xs)

/-- An action's resources, given its principals and the budget `b` left: bounded so that the
    environments they make, principals times resources, fit in `b`; free if there are no
    principals, which make none. -/
inductive ResourcesWithin : List EntityType → Nat → List EntityType → List EntityType → Prop where
  | none : ∀ ets b resources, WfResourceTypes ets resources → ResourcesWithin ets b [] resources
  | some : ∀ ets b p ps resources,
      BoundedTypes ets (b / (ps.length + 1)) resources →
      ResourcesWithin ets b (p :: ps) resources

/-- At most `n` defined entity types, one of them `x`: `x` first, or after types other than it. -/
inductive ContainsBounded : List EntityType → Nat → EntityType → List EntityType → Prop where
  | here : ∀ ets n x xs,
      DefinedEntityType ets x →
      BoundedTypes ets n xs →
      ContainsBounded ets (n + 1) x (x :: xs)
  | there : ∀ ets n x y xs,
      x ≠ y →
      DefinedEntityType ets y →
      ContainsBounded ets n x xs →
      ContainsBounded ets (n + 1) x (y :: xs)

/-- `WfActionsGo` with a budget `b` of request environments. -/
inductive WfActionsGoB : HierMode →
    List EntityType → List (EntityUID × List EntityUID) → List String → Nat →
    List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ r ets built avail b, WfActionsGoB r ets built avail b []
  | cons : ∀ r ets built avail avail' b eid ancestors principals resources context rest,
      SelectRemove avail eid avail' →
      ActAncestors r built ancestors →
      WfPrincipalTypes ets principals →
      ResourcesWithin ets b principals resources →
      WfAttrs Option.none ets context →
      WfActionsGoB r ets ((⟨actionEntityType, eid⟩, ancestors) :: built) avail'
        (b - principals.length * resources.length) rest →
      WfActionsGoB r ets built avail b
        ((⟨actionEntityType, eid⟩,
          ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors)
            (Map.mk context)) :: rest)

/-- `WfActionsGoB` with the request still to place: some action, `request`, is the request's, with
    one of its principals and one of its resources; until then `cons` passes it on, keeping one
    environment of the budget for it. -/
inductive WfActionsGoR : HierMode →
    List EntityType → List (EntityUID × List EntityUID) → List String → Nat →
    List (EntityUID × ActionSchemaEntry) → RequestType → Prop where
  | cons : ∀ r ets built avail avail' b eid ancestors principals resources context rest reqty,
      SelectRemove avail eid avail' →
      ActAncestors r built ancestors →
      WfPrincipalTypes ets principals →
      ResourcesWithin ets (b - 1) principals resources →
      WfAttrs Option.none ets context →
      WfActionsGoR r ets ((⟨actionEntityType, eid⟩, ancestors) :: built) avail'
        (b - principals.length * resources.length) rest reqty →
      WfActionsGoR r ets built avail b
        ((⟨actionEntityType, eid⟩,
          ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors)
            (Map.mk context)) :: rest) reqty
  | request : ∀ r ets built avail avail' b eid ancestors principals principal resources resource
      context rest,
      SelectRemove avail eid avail' →
      ActAncestors r built ancestors →
      ContainsBounded ets b principal principals →
      ContainsBounded ets (b / principals.length) resource resources →
      WfAttrs Option.none ets context →
      WfActionsGoB r ets ((⟨actionEntityType, eid⟩, ancestors) :: built) avail'
        (b - principals.length * resources.length) rest →
      WfActionsGoR r ets built avail b
        ((⟨actionEntityType, eid⟩,
          ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors)
            (Map.mk context)) :: rest)
        (RequestType.mk principal ⟨actionEntityType, eid⟩ resource (Map.mk context))

inductive GenTypeEnvB : HierMode → Nat → TypeEnv → Prop where
  | mk : ∀ r budget names entries acts reqty,
      WfEntitiesGo1 r [] [] names entries →
      WfActionsGoR r names [] actionEidPool budget acts reqty →
      GenTypeEnvB r budget (TypeEnv.mk (Map.mk entries) (Map.mk acts) reqty)

/-! ### Lists -/

theorem _root_.Cedar.Validation.Relational.Schema.DefinedEntityType.ne_nil {ets et} (h : DefinedEntityType ets et) : ets ≠ [] := by
  cases h <;> simp

theorem BoundedTypes.length_le {ets n xs} (h : BoundedTypes ets n xs) : xs.length ≤ n := by
  induction h with
  | nil => exact Nat.zero_le _
  | cons _ _ _ _ _ ih => simp only [List.length_cons]; omega

theorem BoundedTypes.wfPrincipalTypes {ets n xs} (h : BoundedTypes ets n xs) :
    WfPrincipalTypes ets xs := by
  induction h with
  | nil => exact .nil _
  | cons _ _ _ hx _ ih => exact .cons _ _ _ hx ih

theorem BoundedTypes.wfResourceTypes {ets n xs} (h : BoundedTypes ets n xs) :
    WfResourceTypes ets xs := by
  induction h with
  | nil => exact .nil _
  | cons _ _ _ hx _ ih => exact .cons _ _ _ hx ih

theorem BoundedTypes.definedEntityType {ets n xs x} (h : BoundedTypes ets n xs)
    (hx : DefinedEntityType xs x) : DefinedEntityType ets x := by
  induction h with
  | nil => cases hx
  | cons _ _ _ hy _ ih =>
    cases hx with
    | here => exact hy
    | there _ _ _ _ hx => exact ih hx

theorem _root_.Cedar.Validation.Relational.Schema.WfPrincipalTypes.boundedTypes {ets xs} (h : WfPrincipalTypes ets xs) :
    ∀ {n}, xs.length ≤ n → BoundedTypes ets n xs := by
  induction h with
  | nil => intro _ _; exact .nil _ _
  | cons _ _ hx _ ih =>
    intro n hn
    simp only [List.length_cons] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact .cons _ _ _ _ hx (ih (by omega))

theorem _root_.Cedar.Validation.Relational.Schema.WfResourceTypes.boundedTypes {ets xs} (h : WfResourceTypes ets xs) :
    ∀ {n}, xs.length ≤ n → BoundedTypes ets n xs := by
  induction h with
  | nil => intro _ _; exact .nil _ _
  | cons _ _ hx _ ih =>
    intro n hn
    simp only [List.length_cons] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact .cons _ _ _ _ hx (ih (by omega))

theorem ResourcesWithin.wfResourceTypes {ets b ps rs} (h : ResourcesWithin ets b ps rs) :
    WfResourceTypes ets rs := by
  cases h with
  | none _ h => exact h
  | some _ _ _ h => exact h.wfResourceTypes

theorem ResourcesWithin.mul_le {ets b ps rs} (h : ResourcesWithin ets b ps rs) :
    ps.length * rs.length ≤ b := by
  cases h with
  | none => simp
  | some p ps _ h =>
    have := h.length_le
    simp only [List.length_cons]
    exact Nat.le_trans (Nat.mul_le_mul_left _ this) (Nat.mul_div_le _ _)

theorem ResourcesWithin.of_mul_le {ets b ps rs} (hrs : WfResourceTypes ets rs)
    (h : ps.length * rs.length ≤ b) : ResourcesWithin ets b ps rs := by
  cases ps with
  | nil => exact .none _ _ _ hrs
  | cons p ps =>
    refine .some _ _ _ _ _ (hrs.boundedTypes ?_)
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    simpa using h

theorem ContainsBounded.boundedTypes {ets n x xs} (h : ContainsBounded ets n x xs) :
    BoundedTypes ets n xs := by
  induction h with
  | here _ _ _ hx hxs => exact .cons _ _ _ _ hx hxs
  | there _ _ _ _ _ hy _ ih => exact .cons _ _ _ _ hy ih

theorem ContainsBounded.definedEntityType {ets n x xs} (h : ContainsBounded ets n x xs) :
    DefinedEntityType xs x := by
  induction h with
  | here => exact .here _ _
  | there _ _ _ _ hne _ _ ih => exact .there _ _ _ hne ih

theorem ContainsBounded.of_boundedTypes {ets n x xs} (h : BoundedTypes ets n xs)
    (hx : DefinedEntityType xs x) : ContainsBounded ets n x xs := by
  induction h with
  | nil => cases hx
  | cons _ _ _ hy hys ih =>
    cases hx with
    | here => exact .here _ _ _ _ hy hys
    | there _ _ _ hne hx => exact .there _ _ _ _ _ hne hy (ih hx)

/-! ### Environments -/

private theorem set_mk_toList {α : Type} (l : List α) : (Set.mk l).toList = l := rfl

/-- The request environments the actions declare. -/
def envCount (acts : List (EntityUID × ActionSchemaEntry)) : Nat :=
  (acts.map fun (_, e) => e.appliesToPrincipal.toList.length * e.appliesToResource.toList.length).sum

theorem envCount_cons (x : EntityUID × ActionSchemaEntry) (xs : List (EntityUID × ActionSchemaEntry)) :
    envCount (x :: xs) =
      x.2.appliesToPrincipal.toList.length * x.2.appliesToResource.toList.length + envCount xs := by
  simp [envCount]

theorem length_product {α β : Type} (l₁ : List α) (l₂ : List β) :
    (l₁.product l₂).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp [List.product]
  | cons a l ih => simp [List.product, List.flatMap_cons, Nat.succ_mul, Nat.add_comm] at ih ⊢ <;> omega

theorem environments_length (env : TypeEnv) :
    env.schema.environments.length = envCount env.acts.toList := by
  simp only [TypeEnv.schema, Schema.environments, List.length_map, List.length_flatMap, envCount]
  congr 1
  apply List.map_congr_left
  intro ⟨a, e⟩ _
  show ((List.product _ _).map _).length = _
  rw [List.length_map, length_product]

/-! ### Modes: every one draws closed, acyclic ancestors -/

theorem appendET_nil_right : ∀ xs : List EntityType, AppendET xs [] xs
  | [] => .nil _
  | x :: xs => .cons _ _ _ _ (appendET_nil_right xs)

theorem appendUID_nil_right : ∀ xs : List EntityUID, AppendUID xs [] xs
  | [] => .nil _
  | x :: xs => .cons _ _ _ _ (appendUID_nil_right xs)

theorem pickClosedAncestors_nil : ∀ built : List (EntityType × List EntityType),
    PickClosedAncestors built []
  | [] => .none
  | (_, _) :: built => .skip _ _ _ _ (pickClosedAncestors_nil built)

theorem pickClosedActionAncestors_nil : ∀ built : List (EntityUID × List EntityUID),
    PickClosedActionAncestors built []
  | [] => .none
  | (_, _) :: built => .skip _ _ _ _ (pickClosedActionAncestors_nil built)

theorem pickClosedAncestors_of_mem {p : EntityType} {pset : List EntityType} :
    ∀ {built : List (EntityType × List EntityType)}, (p, pset) ∈ built →
      PickClosedAncestors built (p :: pset)
  | [], h => by cases h
  | (q, qset) :: built, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact .pick _ _ _ _ _ (pickClosedAncestors_nil built) (appendET_nil_right pset)
    · exact .skip _ _ _ _ (pickClosedAncestors_of_mem h)

theorem pickClosedActionAncestors_of_mem {p : EntityUID} {pset : List EntityUID} :
    ∀ {built : List (EntityUID × List EntityUID)}, (p, pset) ∈ built →
      PickClosedActionAncestors built (p :: pset)
  | [], h => by cases h
  | (q, qset) :: built, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact .pick _ _ _ _ _ (pickClosedActionAncestors_nil built) (appendUID_nil_right pset)
    · exact .skip _ _ _ _ (pickClosedActionAncestors_of_mem h)

theorem Ancestors.toPick {r built ancestors} (h : Ancestors r built ancestors) :
    PickClosedAncestors built ancestors := by
  cases h with
  | dense _ _ h => exact h
  | sparse _ _ h =>
    cases h with
    | none => exact pickClosedAncestors_nil _
    | one _ _ hm => exact pickClosedAncestors_of_mem hm
  | flat => exact pickClosedAncestors_nil _

theorem ActAncestors.toPick {r built ancestors} (h : ActAncestors r built ancestors) :
    PickClosedActionAncestors built ancestors := by
  cases h with
  | dense _ _ h => exact h
  | sparse _ _ h =>
    cases h with
    | none => exact pickClosedActionAncestors_nil _
    | one _ _ hm => exact pickClosedActionAncestors_of_mem hm
  | flat => exact pickClosedActionAncestors_nil _

theorem WfEntitiesGoR.toWf {r built names allNames entries}
    (h : WfEntitiesGoR r built names allNames entries) : WfEntitiesGo built names allNames entries := by
  induction h with
  | nil => exact .nil _ _
  | standard _ _ _ _ _ _ _ _ h1 h2 h3 h4 _ ih => exact .standard _ _ _ _ _ _ _ _ h1 h2.toPick h3 h4 ih
  | enum _ _ _ _ _ _ h1 _ ih => exact .enum _ _ _ _ _ _ h1 ih

theorem WfEntitiesGo1.toWf {r built names allNames entries}
    (h : WfEntitiesGo1 r built names allNames entries) : WfEntitiesGo built names allNames entries := by
  cases h with
  | standard _ _ _ _ _ _ h1 h2 h3 h4 h5 => exact .standard _ _ _ _ _ _ _ _ h1 h2.toPick h3 h4 h5.toWf
  | enum _ _ _ _ h1 h2 => exact .enum _ _ _ _ _ _ h1 h2.toWf

theorem _root_.Cedar.Validation.Relational.Schema.WfEntitiesGo.toDense {built names allNames entries}
    (h : WfEntitiesGo built names allNames entries) :
    WfEntitiesGoR .dense built names allNames entries := by
  induction h with
  | nil => exact .nil _ _ _
  | standard _ _ _ _ _ _ _ _ h1 h2 h3 h4 _ ih =>
    exact .standard _ _ _ _ _ _ _ _ _ h1 (.dense _ _ h2) h3 h4 ih
  | enum _ _ _ _ _ _ h1 _ ih => exact .enum _ _ _ _ _ _ _ h1 ih

/-! ### Soundness: well formed, within the budget -/

theorem WfActionsGoB.wfActionsGo {r ets built avail b acts} (h : WfActionsGoB r ets built avail b acts) :
    WfActionsGo ets built avail acts := by
  induction h with
  | nil => exact .nil _ _ _
  | cons _ _ _ _ _ _ _ _ _ _ hsel hanc hp hr hctx _ ih =>
    exact .cons _ _ _ _ _ _ _ _ _ _ hsel hanc.toPick hp hr.wfResourceTypes hctx ih

theorem WfActionsGoB.envCount_le {r ets built avail b acts} (h : WfActionsGoB r ets built avail b acts) :
    envCount acts ≤ b := by
  induction h with
  | nil => simp [envCount]
  | cons _ _ _ b _ _ principals resources _ _ _ _ _ hr _ _ ih =>
    have := hr.mul_le
    rw [envCount_cons]
    simp only [set_mk_toList]
    generalize principals.length * resources.length = P at this ih ⊢
    omega

theorem WfActionsGoR.wfActionsGo {r ets built avail b acts reqty}
    (h : WfActionsGoR r ets built avail b acts reqty) :
    WfActionsGo ets built avail acts ∧ RequestFromAction ets acts reqty := by
  induction h with
  | cons _ _ _ _ _ _ _ _ _ _ _ hsel hanc hp hr hctx _ ih =>
    exact ⟨.cons _ _ _ _ _ _ _ _ _ _ hsel hanc.toPick hp hr.wfResourceTypes hctx ih.1, .there _ _ _ _ ih.2⟩
  | request _ _ _ _ _ _ _ _ _ _ _ _ hsel hanc hp hr hctx hrest =>
    exact ⟨.cons _ _ _ _ _ _ _ _ _ _ hsel hanc.toPick hp.boundedTypes.wfPrincipalTypes
      hr.boundedTypes.wfResourceTypes hctx hrest.wfActionsGo,
      .here _ _ _ _ _ _ _ _ _ hp.definedEntityType hr.definedEntityType⟩

theorem WfActionsGoR.envCount_le {r ets built avail b acts reqty}
    (h : WfActionsGoR r ets built avail b acts reqty) : envCount acts ≤ b := by
  induction h with
  | cons _ _ _ b _ _ principals resources _ _ _ _ _ _ hr _ _ ih =>
    have := hr.mul_le
    rw [envCount_cons]
    simp only [set_mk_toList]
    generalize principals.length * resources.length = P at this ih ⊢
    omega
  | request _ _ _ b _ _ principals _ resources _ _ _ _ _ _ hr _ hrest =>
    have hrest := hrest.envCount_le
    have : principals.length * resources.length ≤ b :=
      Nat.le_trans (Nat.mul_le_mul_left _ hr.boundedTypes.length_le) (Nat.mul_div_le _ _)
    rw [envCount_cons]
    simp only [set_mk_toList]
    generalize principals.length * resources.length = P at this hrest ⊢
    omega

theorem WfActionsGoR.principal_defined {r ets built avail b acts reqty}
    (h : WfActionsGoR r ets built avail b acts reqty) : ∃ p, DefinedEntityType ets p := by
  induction h with
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | request _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ _ _ =>
    exact ⟨_, hp.boundedTypes.definedEntityType hp.definedEntityType⟩

theorem GenTypeEnvB.wfTypeEnv {r : HierMode} {budget : Nat} {env : TypeEnv}
    (h : GenTypeEnvB r budget env) : WfTypeEnv env := by
  cases h with
  | mk names entries acts reqty hents hacts =>
    have h := hacts.wfActionsGo
    exact .mk _ _ _ _ (.mk _ _ hents.toWf) (.mk _ _ h.1) h.2

theorem GenTypeEnvB.environments_length_le {r : HierMode} {budget : Nat} {env : TypeEnv}
    (h : GenTypeEnvB r budget env) : env.schema.environments.length ≤ budget := by
  rw [environments_length]
  cases h with
  | mk names entries acts reqty _ hacts => exact hacts.envCount_le

/-! ### Completeness: every well-formed environment within the budget -/

theorem _root_.Cedar.Validation.Relational.Schema.WfActionsGo.wfActionsGoB {ets built avail acts} (h : WfActionsGo ets built avail acts) :
    ∀ {b}, envCount acts ≤ b → WfActionsGoB .dense ets built avail b acts := by
  induction h with
  | nil => intro _ _; exact .nil _ _ _ _ _
  | cons _ _ _ _ _ principals resources _ _ hsel hanc hp hr hctx _ ih =>
    intro b hb
    rw [envCount_cons] at hb
    simp only [set_mk_toList] at hb
    exact .cons _ _ _ _ _ _ _ _ _ _ _ _ hsel (.dense _ _ hanc) hp (.of_mul_le hr (by omega)) hctx
      (ih (by omega))

/-- The request's action declares at least one environment. -/
theorem _root_.Cedar.Validation.Relational.Schema.RequestFromAction.envCount_pos {ets acts reqty} (h : RequestFromAction ets acts reqty) :
    0 < envCount acts := by
  induction h with
  | here _ _ principals resources _ _ _ _ hp hr =>
    rw [envCount_cons]
    simp only [set_mk_toList]
    have : 0 < principals.length := by
      cases principals with
      | nil => exact absurd rfl hp.ne_nil
      | cons => simp
    have : 0 < resources.length := by
      cases resources with
      | nil => exact absurd rfl hr.ne_nil
      | cons => simp
    have := Nat.mul_pos ‹0 < principals.length› ‹0 < resources.length›
    omega
  | there _ _ _ _ ih => rw [envCount_cons]; omega

theorem _root_.Cedar.Validation.Relational.Schema.WfActionsGo.wfActionsGoR {ets built avail acts}
    (h : WfActionsGo ets built avail acts) :
    ∀ {ets' b reqty}, RequestFromAction ets' acts reqty → envCount acts ≤ b →
      WfActionsGoR .dense ets built avail b acts reqty := by
  induction h with
  | nil => intro _ _ _ hreq; cases hreq
  | cons _ _ _ _ _ principals resources _ rest_1 hsel hanc hp hr hctx hrest ih =>
    intro ets' b reqty hreq hb
    rw [envCount_cons] at hb
    simp only [set_mk_toList] at hb
    cases hreq with
    | here _ _ _ _ _ _ _ _ hpp hrr =>
      have hP : 0 < principals.length := by
        cases principals with
        | nil => exact absurd rfl hpp.ne_nil
        | cons => simp
      have hR : 0 < resources.length := by
        cases resources with
        | nil => exact absurd rfl hrr.ne_nil
        | cons => simp
      have hPR : principals.length ≤ principals.length * resources.length :=
        Nat.le_mul_of_pos_right _ hR
      have hrb : envCount rest_1 ≤ b - principals.length * resources.length := by
        generalize principals.length * resources.length = P at hb ⊢; omega
      refine .request _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsel (.dense _ _ hanc)
        (.of_boundedTypes (hp.boundedTypes (by omega)) hpp)
        (.of_boundedTypes (hr.boundedTypes ?_) hrr) hctx (hrest.wfActionsGoB hrb)
      rw [Nat.le_div_iff_mul_le hP, Nat.mul_comm]
      omega
    | there _ _ _ hreq =>
      have := hreq.envCount_pos
      exact .cons _ _ _ _ _ _ _ _ _ _ _ _ _ hsel (.dense _ _ hanc) hp (.of_mul_le hr (by omega)) hctx
        (ih hreq (by omega))

/-- `GenTypeEnvB`, in some mode, is exactly the well-formed environments with at most `budget`
    request environments; the `dense` mode alone already reaches all of them. -/
theorem genTypeEnvB_iff {budget : Nat} {env : TypeEnv} :
    (∃ r, GenTypeEnvB r budget env) ↔ WfTypeEnv env ∧ env.schema.environments.length ≤ budget := by
  refine ⟨fun ⟨_, h⟩ => ⟨h.wfTypeEnv, h.environments_length_le⟩, fun ⟨h, hb⟩ => ⟨.dense, ?_⟩⟩
  rw [environments_length] at hb
  cases h with
  | mk names entries acts reqty hents hacts hreq =>
    cases hacts with
    | mk hacts =>
      have hacts := hacts.wfActionsGoR hreq hb
      cases hents with
      | mk hents =>
        obtain ⟨p, hp⟩ := hacts.principal_defined
        have hents : WfEntitiesGo1 .dense [] [] names entries := by
          cases hents with
          | nil => exact absurd rfl hp.ne_nil
          | standard _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
            exact .standard _ _ _ _ _ _ _ _ _ h1 (.dense _ _ h2) h3 h4 h5.toDense
          | enum _ _ _ _ _ _ h1 h2 => exact .enum _ _ _ _ _ _ _ h1 h2.toDense
        exact .mk _ _ _ _ _ _ hents hacts

/-! ## The hand-written instances' laws

Facts for the soundness proofs `specimen.emitSound` runs on the derived generators below. -/

section Laws
open Specimen.Correctness Basalt

theorem definedEntityType_of_mem {ets : List EntityType} {x : EntityType} (h : x ∈ ets) :
    DefinedEntityType ets x := by
  induction ets with
  | nil => cases h
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy; exact .here _ _
    · exact .there _ _ _ hxy (ih ((List.mem_cons.mp h).resolve_left hxy))

@[specimen_sound]
theorem definedEntityType_gen (ets : List EntityType) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun et => DefinedEntityType ets et) (G := SGen) s l)
      (DefinedEntityType ets) := by
  show succObs.spec (do
    if ets.isEmpty then Specimen.Fail.fail else
    let i ← chooseNat 0 (ets.length - 1)
    match ets[i]? with
    | some et => pure et
    | none => Specimen.Fail.fail : SGen EntityType) _
  walk
  exact definedEntityType_of_mem (List.mem_of_getElem? ‹_›)

theorem list_lt_append {l m : List Char} (hm : m ≠ []) : l < l ++ m := by
  induction l with
  | nil => obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hm; exact List.nil_lt_cons _ _
  | cons x xs ih => simp only [List.cons_append]; exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

theorem string_lt_append (b : String) (n : Nat) (hn : 1 ≤ n) :
    b < b ++ String.ofList (List.replicate n 'a') := by
  show b.toList < (b ++ String.ofList (List.replicate n 'a')).toList
  rw [String.toList_append, String.toList_ofList]
  exact list_lt_append (by cases n <;> simp_all)

/-- The attribute generator above a bound: mostly the bound and one or more `a`s, sometimes any string above it. -/
@[specimen_sound]
theorem attr_lt_gen (b : Attr) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun a => b < a) (G := SGen) s l) (fun a => b < a) := by
  show succObs.spec (frequency [
    (3, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a ← anyString s
      return if b < a then a else b ++ String.ofList (List.replicate 1 'a'))] : SGen Attr) _
  walk
  -- The drawn string first: unifying its `if` with an append unfolds the comparison.
  all_goals first
    | (split
       · assumption
       · exact string_lt_append b 1 (Nat.le_refl 1))
    | exact string_lt_append b _ (‹1 ≤ _ ∧ _›).1

@[specimen_sound]
theorem pickOneAncestor_gen (built : List (EntityType × List EntityType)) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun a => PickOneAncestor built a) (G := SGen) s l)
      (PickOneAncestor built) := by
  show succObs.spec (do
    let i ← chooseNat 0 built.length
    if i = 0 then pure [] else
    match built[i - 1]? with
    | some (p, pset) => pure (p :: pset)
    | none => Specimen.Fail.fail : SGen (List EntityType)) _
  walk
  · exact .none _
  · exact .one _ _ _ (List.mem_of_getElem? ‹_›)

@[specimen_sound]
theorem pickOneActionAncestor_gen (built : List (EntityUID × List EntityUID)) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun a => PickOneActionAncestor built a) (G := SGen) s l)
      (PickOneActionAncestor built) := by
  show succObs.spec (do
    let i ← chooseNat 0 built.length
    if i = 0 then pure [] else
    match built[i - 1]? with
    | some (p, pset) => pure (p :: pset)
    | none => Specimen.Fail.fail : SGen (List EntityUID)) _
  walk
  · exact .none _
  · exact .one _ _ _ (List.mem_of_getElem? ‹_›)

/-! ### Their completeness -/

theorem mem_of_definedEntityType {ets : List EntityType} {x : EntityType} (h : DefinedEntityType ets x) :
    x ∈ ets := by
  induction h with
  | here => exact List.mem_cons_self
  | there _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

instance (ets : List EntityType) :
    BacktrackGenForComplete EntityType (fun et => DefinedEntityType ets et) where
  complete et h := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (mem_of_definedEntityType h)
    have hlt : i < ets.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨0, fun s l _ _ => ?_⟩
    show Produces (do
      if ets.isEmpty then Specimen.Fail.fail else
      let i ← chooseNat 0 (ets.length - 1)
      match ets[i]? with
      | some et => pure et
      | none => Specimen.Fail.fail : SGen EntityType) et
    have hne : ets.isEmpty = false := by cases ets <;> simp_all
    rw [hne]
    refine produces_bind_of (produces_chooseNat (k := i) _ (Nat.zero_le _) (by omega)) ?_
    simp only [hi]
    exact produces_pure_iff.mpr rfl

instance (built : List (EntityType × List EntityType)) :
    BacktrackGenForComplete (List EntityType) (fun a => PickOneAncestor built a) where
  complete a h := by
    refine ⟨0, fun s l _ _ => ?_⟩
    show Produces (do
      let i ← chooseNat 0 built.length
      if i = 0 then pure [] else
      match built[i - 1]? with
      | some (p, pset) => pure (p :: pset)
      | none => Specimen.Fail.fail : SGen (List EntityType)) a
    cases h with
    | none =>
      refine produces_bind_of (produces_chooseNat (k := 0) _ (Nat.le_refl _) (Nat.zero_le _)) ?_
      exact produces_pure_iff.mpr rfl
    | one p pset hmem =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      have hlt : i < built.length := (List.getElem?_eq_some_iff.mp hi).1
      refine produces_bind_of (produces_chooseNat (k := i + 1) _ (Nat.zero_le _) (by omega)) ?_
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hi]
      exact produces_pure_iff.mpr rfl

instance (built : List (EntityUID × List EntityUID)) :
    BacktrackGenForComplete (List EntityUID) (fun a => PickOneActionAncestor built a) where
  complete a h := by
    refine ⟨0, fun s l _ _ => ?_⟩
    show Produces (do
      let i ← chooseNat 0 built.length
      if i = 0 then pure [] else
      match built[i - 1]? with
      | some (p, pset) => pure (p :: pset)
      | none => Specimen.Fail.fail : SGen (List EntityUID)) a
    cases h with
    | none =>
      refine produces_bind_of (produces_chooseNat (k := 0) _ (Nat.le_refl _) (Nat.zero_le _)) ?_
      exact produces_pure_iff.mpr rfl
    | one p pset hmem =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      have hlt : i < built.length := (List.getElem?_eq_some_iff.mp hi).1
      refine produces_bind_of (produces_chooseNat (k := i + 1) _ (Nat.zero_le _) (by omega)) ?_
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hi]
      exact produces_pure_iff.mpr rfl

end Laws

deriving instance Basalt.ArbitrarySized for HierMode

open Specimen.Correctness in
instance : ArbitrarySizedComplete HierMode where
  complete r := ⟨0, fun s _ => produces_of_reach (by
    dsimp only [Basalt.ArbitrarySized.arbitrarySized]
    unfold_derived_arbitrary
    cases r <;> cases s <;> walk)⟩

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
set_option specimen.weightModifier "Cedar.Validation.Relational.SchemaGen.favorAncestors" in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.reportPhaseTimers true in
derive_mutual
  generator (fun budget => ∃ r env, GenTypeEnvB r budget env)

/-! ## Canonical form: sorted, deduplicated maps and sets -/

private partial def canonicalizeCedarType : CedarType → CedarType
  | .record rty => .record (Map.make (rty.toList.map fun (a, qt) =>
      (a, qt.map canonicalizeCedarType)))
  | .set ty => .set (canonicalizeCedarType ty)
  | ty => ty

private def canonicalizeAttrs (rty : RecordType) : RecordType :=
  Map.make (rty.toList.map fun (a, qt) => (a, qt.map canonicalizeCedarType))

private def canonicalizeEntityEntry : EntitySchemaEntry → EntitySchemaEntry
  | .standard entry => .standard {
      ancestors := Set.make entry.ancestors.toList,
      attrs := canonicalizeAttrs entry.attrs,
      tags := entry.tags.map canonicalizeCedarType }
  | .enum eids => .enum (Set.make eids.toList)

private def canonicalizeActionEntry (entry : ActionSchemaEntry) : ActionSchemaEntry :=
  { appliesToPrincipal := Set.make entry.appliesToPrincipal.toList,
    appliesToResource := Set.make entry.appliesToResource.toList,
    ancestors := Set.make entry.ancestors.toList,
    context := canonicalizeAttrs entry.context }

/-- Sort and deduplicate a generated environment's maps and sets. -/
def canonicalizeEnv (env : TypeEnv) : TypeEnv :=
  { ets := Map.make (env.ets.toList.map fun (et, entry) => (et, canonicalizeEntityEntry entry)),
    acts := Map.make (env.acts.toList.map fun (uid, entry) => (uid, canonicalizeActionEntry entry)),
    reqty := { env.reqty with context := canonicalizeAttrs env.reqty.context } }

end Cedar.Validation.Relational.SchemaGen

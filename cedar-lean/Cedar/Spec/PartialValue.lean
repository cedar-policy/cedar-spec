/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Data.Map
import Cedar.Spec.Ext.IPAddr
import Cedar.Spec.ExtFun
import Cedar.Spec.PartialExpr
import Cedar.Spec.Value

/-!
This file defines Cedar partial values.
-/

namespace Cedar.Spec

open Cedar.Data

inductive PartialValue where
  | value (v : Value)
  | residual (r : PartialExpr)

deriving instance Repr, DecidableEq, Inhabited for PartialValue

def PartialValue.asPartialExpr (v : PartialValue) : PartialExpr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r

/--
  Like `PartialValue`, but cannot contain residual expressions which depend on
  vars or entity data
-/
inductive RestrictedPartialValue where
  | value (v : Value)
  | residual (r : RestrictedPartialExpr)

deriving instance Inhabited for RestrictedPartialValue

def RestrictedPartialValue.asPartialExpr (v : RestrictedPartialValue) : PartialExpr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r.asPartialExpr

def RestrictedPartialValue.asRestrictedPartialExpr (v : RestrictedPartialValue) : RestrictedPartialExpr :=
  match v with
  | .value v    => v.asRestrictedPartialExpr
  | .residual r => r

def RestrictedPartialValue.asPartialValue (v : RestrictedPartialValue) : PartialValue :=
  match v with
  | .value v    => .value v
  | .residual r => .residual (r.asPartialExpr)

/--
  termination helper lemma for ite
-/
theorem PartialExpr.ite_termination {x₁ x₂ x₃ : PartialExpr} :
  x₁.subexpressions.length < (PartialExpr.ite x₁ x₂ x₃).subexpressions.length ∧
  x₂.subexpressions.length < (PartialExpr.ite x₁ x₂ x₃).subexpressions.length ∧
  x₃.subexpressions.length < (PartialExpr.ite x₁ x₂ x₃).subexpressions.length
:= by
  repeat (any_goals (apply And.intro))
  all_goals {
    conv => rhs ; unfold subexpressions
    simp [List.length_append]
    omega
  }

/--
  termination helper lemma for and
-/
theorem PartialExpr.and_termination {x₁ x₂ : PartialExpr} :
  x₁.subexpressions.length < (PartialExpr.and x₁ x₂).subexpressions.length ∧
  x₂.subexpressions.length < (PartialExpr.and x₁ x₂).subexpressions.length
:= by
  apply And.intro
  all_goals {
    conv => rhs ; unfold subexpressions
    simp [List.length_append]
    omega
  }

/--
  termination helper lemma for or
-/
theorem PartialExpr.or_termination {x₁ x₂ : PartialExpr} :
  x₁.subexpressions.length < (PartialExpr.or x₁ x₂).subexpressions.length ∧
  x₂.subexpressions.length < (PartialExpr.or x₁ x₂).subexpressions.length
:= by
  apply And.intro
  all_goals {
    conv => rhs ; unfold subexpressions
    simp [List.length_append]
    omega
  }

/--
  termination helper lemma for unaryApp
-/
theorem PartialExpr.unaryApp_termination {x₁ : PartialExpr} {op : UnaryOp} :
  x₁.subexpressions.length < (PartialExpr.unaryApp op x₁).subexpressions.length
:= by
  conv => rhs ; unfold subexpressions
  simp [List.length_append]

/--
  termination helper lemma for binaryApp
-/
theorem PartialExpr.binaryApp_termination {x₁ x₂ : PartialExpr} {op : BinaryOp} :
  x₁.subexpressions.length < (PartialExpr.binaryApp op x₁ x₂).subexpressions.length ∧
  x₂.subexpressions.length < (PartialExpr.binaryApp op x₁ x₂).subexpressions.length
:= by
  apply And.intro
  all_goals {
    conv => rhs ; unfold subexpressions
    simp [List.length_append]
    omega
  }

/--
  termination helper lemma for getAttr
-/
theorem PartialExpr.getAttr_termination {x₁ : PartialExpr} {attr : String} :
  x₁.subexpressions.length < (PartialExpr.getAttr x₁ attr).subexpressions.length
:= by
  conv => rhs ; unfold subexpressions
  simp [List.length_append]

/--
  termination helper lemma for hasAttr
-/
theorem PartialExpr.hasAttr_termination {x₁ : PartialExpr} {attr : String} :
  x₁.subexpressions.length < (PartialExpr.hasAttr x₁ attr).subexpressions.length
:= by
  conv => rhs ; unfold subexpressions
  simp [List.length_append]

/--
  termination helper lemma for set
-/
theorem PartialExpr.set_termination {xs : List PartialExpr} :
  --∀ x ∈ xs, x.subexpressions.length < (PartialExpr.set xs).subexpressions.length
  ∀ (x : {x : PartialExpr // x ∈ xs}), x.val.subexpressions.length < (PartialExpr.set xs).subexpressions.length
:= by
  intro x
  replace ⟨x, h⟩ := x
  conv => rhs ; unfold subexpressions
  simp [List.length_append]
  sorry -- `omega` can't discharge this directly, need to use h somehow

/--
  termination helper lemma for record
-/
theorem PartialExpr.record_termination {pairs : List (Attr × PartialExpr)} :
  --∀ kv ∈ pairs, kv.snd.subexpressions.length < (PartialExpr.record pairs).subexpressions.length
  ∀ (kv : {kv : Attr × PartialExpr // kv ∈ pairs}), kv.val.snd.subexpressions.length < (PartialExpr.record pairs).subexpressions.length
:= by
  intro x
  replace ⟨x, h⟩ := x
  conv => rhs ; unfold subexpressions
  simp [List.length_append]
  sorry -- `omega` can't discharge this directly, need to use h somehow

/--
  termination helper lemma for call
-/
theorem PartialExpr.call_termination {xs : List PartialExpr} {xfn : ExtFun} :
  --∀ x ∈ xs, x.subexpressions.length < (PartialExpr.call xfn xs).subexpressions.length
  ∀ (x : {x : PartialExpr // x ∈ xs}), x.val.subexpressions.length < (PartialExpr.call xfn xs).subexpressions.length
:= by
  intro x
  replace ⟨x, h⟩ := x
  conv => rhs ; unfold subexpressions
  simp [List.length_append]
  sorry -- `omega` can't discharge this directly, need to use h somehow

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialExpr.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialExpr` will still contain some unknowns.
-/
-- NB: this function can't live in PartialExpr.lean because it needs PartialValue, and
-- PartialExpr.lean can't import PartialValue, cyclic dependency
def PartialExpr.subst (x : PartialExpr) (subsmap : Map String RestrictedPartialValue) : PartialExpr :=
  match x with
  | .lit _ => x -- no unknowns, nothing to substitute
  | .var _ => x -- no unknowns, nothing to substitute
  | .ite x₁ x₂ x₃ =>
    have ⟨_, _, _⟩ := @PartialExpr.ite_termination x₁ x₂ x₃
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    let x₃' := x₃.subst subsmap
    .ite x₁' x₂' x₃'
  | .and x₁ x₂ =>
    have ⟨_, _⟩ := @PartialExpr.and_termination x₁ x₂
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .and x₁' x₂'
  | .or x₁ x₂ =>
    have ⟨_, _⟩ := @PartialExpr.or_termination x₁ x₂
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .or x₁' x₂'
  | .unaryApp op x₁ =>
    have _ := @PartialExpr.unaryApp_termination x₁ op
    let x₁' := x₁.subst subsmap
    .unaryApp op x₁'
  | .binaryApp op x₁ x₂ =>
    have ⟨_, _⟩ := @PartialExpr.binaryApp_termination x₁ x₂ op
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .binaryApp op x₁' x₂'
  | .getAttr x₁ attr =>
    have _ := @PartialExpr.getAttr_termination x₁ attr
    let x₁' := x₁.subst subsmap
    .getAttr x₁' attr
  | .hasAttr x₁ attr =>
    have _ := @PartialExpr.hasAttr_termination x₁ attr
    let x₁' := x₁.subst subsmap
    .hasAttr x₁' attr
  | .set xs =>
    have h₁ := @PartialExpr.set_termination xs
    let xs' := xs.map₁ λ x =>
      have _ := h₁ x
      PartialExpr.subst x subsmap
    .set xs'
  | .record pairs =>
    have h₁ := @PartialExpr.record_termination pairs
    let pairs' := pairs.map₁ λ kv =>
      have _ := h₁ kv
      (kv.val.fst, kv.val.snd.subst subsmap)
    .record pairs'
  | .call xfn xs =>
    have h₁ := @PartialExpr.call_termination xs xfn
    let xs' := xs.map₁ λ x =>
      have _ := h₁ x
      PartialExpr.subst x subsmap
    .call xfn xs'
  | unknown name => match subsmap.find? name with
    | some val => val.asPartialExpr
    | none => x -- no substitution available, return `x` unchanged
termination_by PartialExpr.subst x subsmap => x.subexpressions.length

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing an Expr.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
-- NB: this function can't live in PartialExpr.lean because it needs PartialValue, and
-- PartialExpr.lean can't import PartialValue, cyclic dependency
def PartialExpr.fullSubst (x : PartialExpr) (subsmap : Map String Value) : Option Expr :=
  match x with
  | .lit p => some (.lit p)
  | .var v => some (.var v)
  | .ite x₁ x₂ x₃ => do
    have ⟨_, _, _⟩ := @PartialExpr.ite_termination x₁ x₂ x₃
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    let x₃' ← x₃.fullSubst subsmap
    some (.ite x₁' x₂' x₃')
  | .and x₁ x₂ => do
    have ⟨_, _⟩ := @PartialExpr.and_termination x₁ x₂
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    some (.and x₁' x₂')
  | .or x₁ x₂ => do
    have ⟨_, _⟩ := @PartialExpr.or_termination x₁ x₂
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    some (.or x₁' x₂')
  | .unaryApp op x₁ => do
    have _ := @PartialExpr.unaryApp_termination x₁ op
    let x₁' ← x₁.fullSubst subsmap
    some (.unaryApp op x₁')
  | .binaryApp op x₁ x₂ => do
    have ⟨_, _⟩ := @PartialExpr.binaryApp_termination x₁ x₂ op
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    some (.binaryApp op x₁' x₂')
  | .getAttr x₁ attr => do
    have _ := @PartialExpr.getAttr_termination x₁ attr
    let x₁' ← x₁.fullSubst subsmap
    some (.getAttr x₁' attr)
  | .hasAttr x₁ attr => do
    have _ := @PartialExpr.hasAttr_termination x₁ attr
    let x₁' ← x₁.fullSubst subsmap
    some (.hasAttr x₁' attr)
  | .set xs => do
    have h₁ := @PartialExpr.set_termination xs
    let xs' ← xs.mapM₁ λ x =>
      have _ := h₁ x
      PartialExpr.fullSubst x subsmap
    some (.set xs')
  | .record pairs => do
    have h₁ := @PartialExpr.record_termination pairs
    let pairs' ← pairs.mapM₁ λ kv =>
      have _ := h₁ kv
      kv.val.snd.fullSubst subsmap >>= λ v' => some (kv.val.fst, v')
    some (.record pairs')
  | .call xfn xs => do
    have h₁ := @PartialExpr.call_termination xs xfn
    let xs' ← xs.mapM₁ λ x =>
      have _ := h₁ x
      PartialExpr.fullSubst x subsmap
    some (.call xfn xs')
  | unknown name => match subsmap.find? name with
    | some val => val.asExpr
    | none => none -- no substitution available, return `none`
termination_by PartialExpr.fullSubst x subsmap => x.subexpressions.length

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new RestrictedPartialExpr.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `RestrictedPartialExpr` will still contain some unknowns.
-/
-- NB: this function can't live in PartialExpr.lean because it needs RestrictedPartialValue,
-- and PartialExpr.lean can't import RestrictedPartialValue, cyclic dependency
def RestrictedPartialExpr.subst (x : RestrictedPartialExpr) (subsmap : Map String RestrictedPartialValue) : RestrictedPartialExpr :=
  match x with
  | .lit p => .lit p
  | .set xs => .set (xs.map (RestrictedPartialExpr.subst · subsmap))
  | .record attrs => .record (attrs.map λ (k, v) => (k, v.subst subsmap))
  | .call xfn args => .call xfn args
  | .unknown name => match subsmap.find? name with
    | some val => val.asRestrictedPartialExpr
    | none => x -- no substitution available, return `x` unchanged
decreasing_by sorry

mutual

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values and fully evaluate, producing a Value.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).

  Also returns `none` if an extension constructor fails to evaluate.
-/
-- NB: this function can't live in PartialExpr.lean because it needs RestrictedPartialValue,
-- and PartialExpr.lean can't import RestrictedPartialValue, cyclic dependency
def RestrictedPartialExpr.fullSubst (x : RestrictedPartialExpr) (subsmap : Map String Value) : Option Value :=
  match x with
  | .lit p => some (.prim p)
  | .set xs => do
      let xs' ← xs.mapM (RestrictedPartialExpr.fullSubst · subsmap)
      some (.set (Set.make xs'))
  | .record attrs => do
      let attrs' ← attrs.mapM λ (k, v) => v.fullSubst subsmap >>= λ v' => some (k, v')
      some (.record (Map.make attrs'))
  | .call xfn args => match ExtFun.call xfn args with
    | .ok v => some v
    | .error _ => none
  | .unknown name => subsmap.find? name -- if no substitution is available, returns `none`

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialValue.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialValue` will still contain some unknowns.
-/
def PartialValue.subst (v : PartialValue) (subsmap : Map String RestrictedPartialValue) : PartialValue :=
  match v with
  | .residual r => .residual (r.subst subsmap)
  | .value v    => .value v -- doesn't contain unknowns, nothing to substitute

/- Hard to define PartialValue.fullSubst, because it could be an arbitrary residual depending on variables / entity data etc.
  Probably should return Option Expr if we need this. But hopefully we can do without this.
/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a Value.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
def PartialValue.fullSubst (v : PartialValue) (subsmap : Map String Value) : Option Value :=
  match v with
  | .residual r => r.fullSubst subsmap
  | .value v    => some v
-/

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new RestrictedPartialValue.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `RestrictedPartialValue` will still contain some unknowns.
-/
def RestrictedPartialValue.subst (v : RestrictedPartialValue) (subsmap : Map String RestrictedPartialValue) : RestrictedPartialValue :=
  match v with
  | .residual r => .residual (r.subst subsmap)
  | .value v    => .value v -- doesn't contain unknowns, nothing to substitute

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a Value.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
def RestrictedPartialValue.fullSubst (v : RestrictedPartialValue) (subsmap : Map String Value) : Option Value :=
  match v with
  | .residual r => r.fullSubst subsmap
  | .value v    => some v -- doesn't contain unknowns, nothing to substitute

end
decreasing_by sorry

/--
  If converting a Value to PartialExpr gives a primitive, the Value was that
  primitive
-/
theorem Value.prim_prim {v : Value} {p : Prim} :
  v.asPartialExpr = .lit p ↔ v = .prim p
:= by
  unfold Value.asPartialExpr
  constructor
  case mp =>
    intro h₁
    cases v <;> simp at *
    case prim => trivial
    case ext x => cases x <;> simp at h₁
  case mpr => intro h₁ ; simp [h₁]

/--
  subst on an Expr is id
-/
theorem subs_expr_id {expr : Expr} {subsmap : Map String RestrictedPartialValue} :
  expr.asPartialExpr.subst subsmap = expr.asPartialExpr
:= by
  unfold PartialExpr.subst
  cases expr <;> simp [Expr.asPartialExpr]
  case and x₁ x₂ =>
    -- inductive argument needed
    sorry
  all_goals {
    sorry
  }

end Cedar.Spec

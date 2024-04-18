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

import Cedar.Partial.Expr
import Cedar.Spec.Value

/-!
This file defines Cedar partial values.
-/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr BinaryOp ExtFun UnaryOp)

inductive Value where
  | value (v : Spec.Value)
  | residual (r : Partial.Expr)

deriving instance Repr, DecidableEq, Inhabited for Value

def Value.asPartialExpr (v : Partial.Value) : Partial.Expr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r

/--
  Like `Partial.Value`, but cannot contain residual expressions which depend on
  vars or entity data
-/
inductive RestrictedValue where
  | value (v : Spec.Value)
  | residual (r : Partial.RestrictedExpr)

deriving instance Inhabited for RestrictedValue

def RestrictedValue.asPartialExpr (v : Partial.RestrictedValue) : Partial.Expr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r.asPartialExpr

def RestrictedValue.asPartialRestrictedExpr (v : Partial.RestrictedValue) : Partial.RestrictedExpr :=
  match v with
  | .value v    => v.asPartialRestrictedExpr
  | .residual r => r

def RestrictedValue.asPartialValue (v : RestrictedValue) : Partial.Value :=
  match v with
  | .value v    => .value v
  | .residual r => .residual (r.asPartialExpr)

/--
  termination helper lemma for ite
-/
theorem Expr.ite_termination {x₁ x₂ x₃ : Partial.Expr} :
  x₁.subexpressions.length < (Partial.Expr.ite x₁ x₂ x₃).subexpressions.length ∧
  x₂.subexpressions.length < (Partial.Expr.ite x₁ x₂ x₃).subexpressions.length ∧
  x₃.subexpressions.length < (Partial.Expr.ite x₁ x₂ x₃).subexpressions.length
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
theorem Expr.and_termination {x₁ x₂ : Partial.Expr} :
  x₁.subexpressions.length < (Partial.Expr.and x₁ x₂).subexpressions.length ∧
  x₂.subexpressions.length < (Partial.Expr.and x₁ x₂).subexpressions.length
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
theorem Expr.or_termination {x₁ x₂ : Partial.Expr} :
  x₁.subexpressions.length < (Partial.Expr.or x₁ x₂).subexpressions.length ∧
  x₂.subexpressions.length < (Partial.Expr.or x₁ x₂).subexpressions.length
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
theorem Expr.unaryApp_termination {x₁ : Partial.Expr} {op : UnaryOp} :
  x₁.subexpressions.length < (Partial.Expr.unaryApp op x₁).subexpressions.length
:= by
  conv => rhs ; unfold subexpressions
  simp [List.length_append]

/--
  termination helper lemma for binaryApp
-/
theorem Expr.binaryApp_termination {x₁ x₂ : Partial.Expr} {op : BinaryOp} :
  x₁.subexpressions.length < (Partial.Expr.binaryApp op x₁ x₂).subexpressions.length ∧
  x₂.subexpressions.length < (Partial.Expr.binaryApp op x₁ x₂).subexpressions.length
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
theorem Expr.getAttr_termination {x₁ : Partial.Expr} {attr : Attr} :
  x₁.subexpressions.length < (Partial.Expr.getAttr x₁ attr).subexpressions.length
:= by
  conv => rhs ; unfold subexpressions
  simp [List.length_append]

/--
  termination helper lemma for hasAttr
-/
theorem Expr.hasAttr_termination {x₁ : Partial.Expr} {attr : Attr} :
  x₁.subexpressions.length < (Partial.Expr.hasAttr x₁ attr).subexpressions.length
:= by
  conv => rhs ; unfold subexpressions
  simp [List.length_append]

/--
  termination helper lemma for set
-/
theorem Expr.set_termination {xs : List Partial.Expr} :
  --∀ x ∈ xs, x.subexpressions.length < (Partial.Expr.set xs).subexpressions.length
  ∀ (x : {x : Partial.Expr // x ∈ xs}), x.val.subexpressions.length < (Partial.Expr.set xs).subexpressions.length
:= by
  intro x
  replace ⟨x, h⟩ := x
  conv => rhs ; unfold subexpressions
  simp [List.length_append]
  sorry -- `omega` can't discharge this directly, need to use h somehow

/--
  termination helper lemma for record
-/
theorem Expr.record_termination {pairs : List (Attr × Partial.Expr)} :
  --∀ kv ∈ pairs, kv.snd.subexpressions.length < (Partial.Expr.record pairs).subexpressions.length
  ∀ (kv : {kv : Attr × Partial.Expr // kv ∈ pairs}), kv.val.snd.subexpressions.length < (Partial.Expr.record pairs).subexpressions.length
:= by
  intro x
  replace ⟨x, h⟩ := x
  conv => rhs ; unfold subexpressions
  simp [List.length_append]
  sorry -- `omega` can't discharge this directly, need to use h somehow

/--
  termination helper lemma for call
-/
theorem Expr.call_termination {xs : List Partial.Expr} {xfn : ExtFun} :
  --∀ x ∈ xs, x.subexpressions.length < (Partial.Expr.call xfn xs).subexpressions.length
  ∀ (x : {x : Partial.Expr // x ∈ xs}), x.val.subexpressions.length < (Partial.Expr.call xfn xs).subexpressions.length
:= by
  intro x
  replace ⟨x, h⟩ := x
  conv => rhs ; unfold subexpressions
  simp [List.length_append]
  sorry -- `omega` can't discharge this directly, need to use h somehow

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new Partial.Expr.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Expr` will still contain some unknowns.
-/
-- NB: this function can't live in Partial/Expr.lean because it needs Partial.Value, and
-- Partial/Expr.lean can't import Partial/Value.lean, cyclic dependency
def Expr.subst (x : Partial.Expr) (subsmap : Map Unknown Partial.RestrictedValue) : Partial.Expr :=
  match x with
  | .lit _ => x -- no unknowns, nothing to substitute
  | .var _ => x -- no unknowns, nothing to substitute
  | .ite x₁ x₂ x₃ =>
    have ⟨_, _, _⟩ := @Expr.ite_termination x₁ x₂ x₃
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    let x₃' := x₃.subst subsmap
    .ite x₁' x₂' x₃'
  | .and x₁ x₂ =>
    have ⟨_, _⟩ := @Expr.and_termination x₁ x₂
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .and x₁' x₂'
  | .or x₁ x₂ =>
    have ⟨_, _⟩ := @Expr.or_termination x₁ x₂
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .or x₁' x₂'
  | .unaryApp op x₁ =>
    have _ := @Expr.unaryApp_termination x₁ op
    let x₁' := x₁.subst subsmap
    .unaryApp op x₁'
  | .binaryApp op x₁ x₂ =>
    have ⟨_, _⟩ := @Expr.binaryApp_termination x₁ x₂ op
    let x₁' := x₁.subst subsmap
    let x₂' := x₂.subst subsmap
    .binaryApp op x₁' x₂'
  | .getAttr x₁ attr =>
    have _ := @Expr.getAttr_termination x₁ attr
    let x₁' := x₁.subst subsmap
    .getAttr x₁' attr
  | .hasAttr x₁ attr =>
    have _ := @Expr.hasAttr_termination x₁ attr
    let x₁' := x₁.subst subsmap
    .hasAttr x₁' attr
  | .set xs =>
    have h₁ := @Expr.set_termination xs
    let xs' := xs.map₁ λ x =>
      have _ := h₁ x
      Partial.Expr.subst x subsmap
    .set xs'
  | .record pairs =>
    have h₁ := @Expr.record_termination pairs
    let pairs' := pairs.map₁ λ kv =>
      have _ := h₁ kv
      (kv.val.fst, kv.val.snd.subst subsmap)
    .record pairs'
  | .call xfn xs =>
    have h₁ := @Expr.call_termination xs xfn
    let xs' := xs.map₁ λ x =>
      have _ := h₁ x
      Partial.Expr.subst x subsmap
    .call xfn xs'
  | .unknown u => match subsmap.find? u with
    | some val => val.asPartialExpr
    | none => x -- no substitution available, return `x` unchanged
termination_by x.subexpressions.length

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing an Expr.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
-- NB: this function can't live in Partial/Expr.lean because it needs Partial.Value, and
-- Partial/Expr.lean can't import Partial/Value.lean, cyclic dependency
def Expr.fullSubst (x : Partial.Expr) (subsmap : Map Unknown Spec.Value) : Option Spec.Expr :=
  match x with
  | .lit p => some (.lit p)
  | .var v => some (.var v)
  | .ite x₁ x₂ x₃ => do
    have ⟨_, _, _⟩ := @Expr.ite_termination x₁ x₂ x₃
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    let x₃' ← x₃.fullSubst subsmap
    some (.ite x₁' x₂' x₃')
  | .and x₁ x₂ => do
    have ⟨_, _⟩ := @Expr.and_termination x₁ x₂
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    some (.and x₁' x₂')
  | .or x₁ x₂ => do
    have ⟨_, _⟩ := @Expr.or_termination x₁ x₂
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    some (.or x₁' x₂')
  | .unaryApp op x₁ => do
    have _ := @Expr.unaryApp_termination x₁ op
    let x₁' ← x₁.fullSubst subsmap
    some (.unaryApp op x₁')
  | .binaryApp op x₁ x₂ => do
    have ⟨_, _⟩ := @Expr.binaryApp_termination x₁ x₂ op
    let x₁' ← x₁.fullSubst subsmap
    let x₂' ← x₂.fullSubst subsmap
    some (.binaryApp op x₁' x₂')
  | .getAttr x₁ attr => do
    have _ := @Expr.getAttr_termination x₁ attr
    let x₁' ← x₁.fullSubst subsmap
    some (.getAttr x₁' attr)
  | .hasAttr x₁ attr => do
    have _ := @Expr.hasAttr_termination x₁ attr
    let x₁' ← x₁.fullSubst subsmap
    some (.hasAttr x₁' attr)
  | .set xs => do
    have h₁ := @Expr.set_termination xs
    let xs' ← xs.mapM₁ λ x =>
      have _ := h₁ x
      Partial.Expr.fullSubst x subsmap
    some (.set xs')
  | .record pairs => do
    have h₁ := @Expr.record_termination pairs
    let pairs' ← pairs.mapM₁ λ kv =>
      have _ := h₁ kv
      kv.val.snd.fullSubst subsmap >>= λ v' => some (kv.val.fst, v')
    some (.record pairs')
  | .call xfn xs => do
    have h₁ := @Expr.call_termination xs xfn
    let xs' ← xs.mapM₁ λ x =>
      have _ := h₁ x
      Partial.Expr.fullSubst x subsmap
    some (.call xfn xs')
  | .unknown u => match subsmap.find? u with
    | some val => val.asExpr
    | none => none -- no substitution available, return `none`
termination_by x.subexpressions.length

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new Partial.RestrictedExpr.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.RestrictedExpr` will still contain some unknowns.
-/
-- NB: this function can't live in Partial/Expr.lean because it needs Partial.RestrictedValue,
-- and Partial/Expr.lean can't import Partial/Value.lean, cyclic dependency
def RestrictedExpr.subst (x : Partial.RestrictedExpr) (subsmap : Map Unknown Partial.RestrictedValue) : Partial.RestrictedExpr :=
  match x with
  | .lit p => .lit p
  | .set xs => .set (xs.map (Partial.RestrictedExpr.subst · subsmap))
  | .record attrs => .record (attrs.map λ (k, v) => (k, v.subst subsmap))
  | .call xfn args => .call xfn args
  | .unknown u => match subsmap.find? u with
    | some val => val.asPartialRestrictedExpr
    | none => x -- no substitution available, return `x` unchanged
decreasing_by all_goals sorry

mutual

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values and fully evaluate, producing a Spec.Value.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).

  Also returns `none` if an extension constructor fails to evaluate.
-/
-- NB: this function can't live in Partial/Expr.lean because it needs Partial.RestrictedValue,
-- and Partial/Expr.lean can't import Partial/Value.lean, cyclic dependency
def RestrictedExpr.fullSubst (x : Partial.RestrictedExpr) (subsmap : Map Unknown Spec.Value) : Option Spec.Value :=
  match x with
  | .lit p => some (.prim p)
  | .set xs => do
      let xs' ← xs.mapM (Partial.RestrictedExpr.fullSubst · subsmap)
      some (.set (Set.make xs'))
  | .record attrs => do
      let attrs' ← attrs.mapM λ (k, v) => v.fullSubst subsmap >>= λ v' => some (k, v')
      some (.record (Map.make attrs'))
  | .call xfn args => match Spec.call xfn args with
    | .ok v => some v
    | .error _ => none
  | .unknown u => subsmap.find? u -- if no substitution is available, returns `none`
decreasing_by all_goals sorry

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new Partial.Value.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialValue` will still contain some unknowns.
-/
def Value.subst (v : Partial.Value) (subsmap : Map Unknown Partial.RestrictedValue) : Partial.Value :=
  match v with
  | .residual r => .residual (r.subst subsmap)
  | .value v    => .value v -- doesn't contain unknowns, nothing to substitute

/- Hard to define Partial.Value.fullSubst, because it could be an arbitrary residual depending on variables / entity data etc.
  Probably should return Option Expr if we need this. But hopefully we can do without this.
/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a Value.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
def Partial.Value.fullSubst (v : Partial.Value) (subsmap : Map Unknown Spec.Value) : Option Spec.Value :=
  match v with
  | .residual r => r.fullSubst subsmap
  | .value v    => some v
-/

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new Partial.RestrictedValue.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.RestrictedValue` will still contain some unknowns.
-/
def RestrictedValue.subst (v : Partial.RestrictedValue) (subsmap : Map Unknown Partial.RestrictedValue) : Partial.RestrictedValue :=
  match v with
  | .residual r => .residual (r.subst subsmap)
  | .value v    => .value v -- doesn't contain unknowns, nothing to substitute

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a Value.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
def RestrictedValue.fullSubst (v : Partial.RestrictedValue) (subsmap : Map Unknown Spec.Value) : Option Spec.Value :=
  match v with
  | .residual r => r.fullSubst subsmap
  | .value v    => some v -- doesn't contain unknowns, nothing to substitute

end

/--
  subst on a Spec.Expr is id
-/
theorem subs_expr_id {expr : Spec.Expr} {subsmap : Map Unknown Partial.RestrictedValue} :
  expr.asPartialExpr.subst subsmap = expr.asPartialExpr
:= by
  unfold Partial.Expr.subst
  cases expr <;> simp [Spec.Expr.asPartialExpr]
  case and x₁ x₂ =>
    -- inductive argument needed
    sorry
  all_goals sorry

end Cedar.Partial

namespace Cedar.Spec

/--
  If converting a Spec.Value to Partial.Expr gives a primitive, the Value was that
  primitive
-/
theorem Value.prim_prim {v : Spec.Value} {p : Prim} :
  v.asPartialExpr = .lit p ↔ v = .prim p
:= by
  unfold Spec.Value.asPartialExpr
  constructor
  case mp =>
    intro h₁
    cases v <;> simp at *
    case prim => trivial
    case ext x => cases x <;> simp at h₁
  case mpr => intro h₁ ; simp [h₁]

end Cedar.Spec

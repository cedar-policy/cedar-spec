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

import Cedar.SymCC.Env
import Cedar.SymCC.ExtFun
import Cedar.SymCC.Factory

/-!

This file defines the Cedar symbolic compiler.

The symbolic compiler takes as input a Cedar expression and a symbolic
environment. Given these inputs, it produces a Term encoding of the expression.

If the compiler returns a Term, this Term represents a sound and complete
encoding of the input expression's semantics with respect to the given
environment: using this Term for verification will neither miss bugs
(soundness) nor produce false positives (completeness).
-/

namespace Cedar.SymCC

open Cedar.Data Cedar.Spec Cedar.Validation
open Factory

prefix:0 "⊙" => someOf

def compilePrim (p : Prim) (εs : SymEntities) : Result Term :=
  match p with
  | .bool b        => ⊙b
  | .int i         => ⊙i
  | .string s      => ⊙s
  | .entityUID uid => if εs.isValidEntityUID uid then ⊙uid else .error .typeError

def compileVar (v : Var) (req : SymRequest) : Result Term :=
  match v with
  | .principal => if req.principal.typeOf.isEntityType then ⊙req.principal else .error .typeError
  | .action    => if req.action.typeOf.isEntityType then ⊙req.action else .error .typeError
  | .resource  => if req.resource.typeOf.isEntityType then ⊙req.resource else .error .typeError
  | .context   => if req.context.typeOf.isRecordType then ⊙req.context else .error .typeError

def compileApp₁ (op₁ : UnaryOp) (t : Term) : Result Term := do
  match op₁, t.typeOf with
  | .not, .bool            => ⊙not t
  | .neg, .bitvec 64       => ifFalse (bvnego t) (bvneg t)
  | .like p, .string       => ⊙string.like t p
  | .is ety₁, .entity ety₂ => ⊙(ety₁ = ety₂ : Bool)
  | .isEmpty, .set _       => ⊙set.isEmpty t
  | _, _                   => .error .typeError

/-
Returns true if terms of type ty₁ = ty₂, so terms of types ty₁ / ty₂ can be
compared using the homogeneous equality operator `eq`. Returns false if ty₁ ≠
ty₂ but it can be soundly decided, from types alone, that terms of type ty₁ and
ty₂ can never be equal.  For now, we make this determination only for primitive
types, to match validator behavior.  We can make this determination more often
if needed. In general, we cannot decide if two terms of different set types are
never equal because they could both evaluate to the empty set and would be
considered equal under Cedar's dynamic semantics. Returns a type error if the
types are unequal and not known to be always unequal.
-/
def reducibleEq (ty₁ ty₂ : TermType) : Result Bool :=
  if ty₁ = ty₂ then true
  else if ty₁.isPrimType && ty₂.isPrimType then false
  else .error .typeError

def compileInₑ (t₁ t₂ : Term) (ancs? : Option UnaryFunction) : Term :=
  let isEq := if t₁.typeOf = t₂.typeOf then eq t₁ t₂ else false
  let isIn := if let some ancs := ancs? then set.member t₂ (app ancs t₁) else false
  or isEq isIn

def compileInₛ (t ts : Term) (ancs? : Option UnaryFunction) : Term :=
  let isIn₁ := if ts.typeOf = .set t.typeOf then set.member t ts else false
  let isIn₂ := if let some ancs := ancs? then set.intersects ts (app ancs t) else false
  or isIn₁ isIn₂

def compileHasTag (entity tag : Term) : Option (Option SymTags) → Result Term
  | .none            => .error .noSuchEntityType
  | .some .none      => ⊙false
  | .some (.some τs) => ⊙τs.hasTag entity tag

def compileGetTag (entity tag : Term) : Option (Option SymTags) → Result Term
  | .none            => .error .noSuchEntityType
  | .some .none      => .error .typeError -- no tags declared
  | .some (.some τs) => τs.getTag entity tag

def compileApp₂ (op₂ : BinaryOp) (t₁ t₂ : Term) (εs : SymEntities) : Result Term := do
  match op₂, t₁.typeOf, t₂.typeOf with
  | .eq, ty₁, ty₂                           => if (← reducibleEq ty₁ ty₂) then ⊙eq t₁ t₂ else ⊙false
  | .less, .bitvec 64, .bitvec 64           => ⊙bvslt t₁ t₂
  | .less, .ext .datetime, .ext .datetime   => ⊙bvslt (ext.datetime.val t₁) (ext.datetime.val t₂)
  | .less, .ext .duration, .ext .duration   => ⊙bvslt (ext.duration.val t₁) (ext.duration.val t₂)
  | .lessEq, .bitvec 64, .bitvec 64         => ⊙bvsle t₁ t₂
  | .lessEq, .ext .datetime, .ext .datetime => ⊙bvsle (ext.datetime.val t₁) (ext.datetime.val t₂)
  | .lessEq, .ext .duration, .ext .duration => ⊙bvsle (ext.duration.val t₁) (ext.duration.val t₂)
  | .add, .bitvec 64, .bitvec 64            => ifFalse (bvsaddo t₁ t₂) (bvadd t₁ t₂)
  | .sub, .bitvec 64, .bitvec 64            => ifFalse (bvssubo t₁ t₂) (bvsub t₁ t₂)
  | .mul, .bitvec 64, .bitvec 64            => ifFalse (bvsmulo t₁ t₂) (bvmul t₁ t₂)
  | .contains, .set ty₁, ty₂                => if ty₁ = ty₂ then ⊙set.member t₂ t₁ else .error .typeError
  | .containsAll, .set ty₁, .set ty₂        => if ty₁ = ty₂ then ⊙set.subset t₂ t₁ else .error .typeError
  | .containsAny, .set ty₁, .set ty₂        => if ty₁ = ty₂ then ⊙set.intersects t₁ t₂ else .error .typeError
  | .mem, .entity ety₁, .entity ety₂        => ⊙compileInₑ t₁ t₂ (εs.ancestorsOfType ety₁ ety₂)
  | .mem, .entity ety₁, .set (.entity ety₂) => ⊙compileInₛ t₁ t₂ (εs.ancestorsOfType ety₁ ety₂)
  | .hasTag, .entity ety, .string           => compileHasTag t₁ t₂ (εs.tags ety)
  | .getTag, .entity ety, .string           => compileGetTag t₁ t₂ (εs.tags ety)
  | _, _, _                                 => .error .typeError

def compileAttrsOf (t : Term) (εs : SymEntities) : Result Term := do
  match t.typeOf with
  | .entity ety => if let some attrs := εs.attrs ety then app attrs t else .error .noSuchEntityType
  | .record _   => t
  | _           => .error .typeError

def compileHasAttr (t : Term) (a : Attr) (εs : SymEntities) : Result Term := do
  let attrs ← compileAttrsOf t εs
  match attrs.typeOf with
  | .record rty =>
    match rty.find? a with
    | .some (.option _) => ⊙isSome (record.get attrs a)
    | .some _           => ⊙true
    | .none             => ⊙false
  | _ => .error .typeError

def compileGetAttr (t : Term) (a : Attr) (εs : SymEntities) : Result Term := do
  let attrs ← compileAttrsOf t εs
  match attrs.typeOf with
  | .record rty =>
    match rty.find? a with
    | .some (.option _) => record.get attrs a
    | .some _           => ⊙(record.get attrs a)
    | .none             => .error .noSuchAttribute
  | _ => .error .typeError

def compileIf (t₁ : Term) (r₂ r₃ : Result Term) : Result Term := do
  match t₁, t₁.typeOf with
  | .some (.prim (.bool true)), _  => r₂
  | .some (.prim (.bool false)), _ => r₃
  | _, .option .bool =>
    let t₂ ← r₂
    let t₃ ← r₃
    if t₂.typeOf = t₃.typeOf
    then ifSome t₁ (ite (option.get t₁) t₂ t₃)
    else .error .typeError
  | _, _ => .error .typeError

def compileAnd (t₁ : Term) (r₂ : Result Term) : Result Term := do
  match t₁, t₁.typeOf with
  | .some (.prim (.bool false)), _ => t₁
  | _, .option .bool =>
    let t₂ ← r₂
    if t₂.typeOf = .option .bool
    then ifSome t₁ (ite (option.get t₁) t₂ (⊙ false))
    else .error .typeError
  | _, _ => .error .typeError

def compileOr (t₁ : Term) (r₂ : Result Term) : Result Term := do
  match t₁, t₁.typeOf with
  | .some (.prim (.bool true)), _ => t₁
  | _, .option .bool =>
    let t₂ ← r₂
    if t₂.typeOf = .option .bool
    then ifSome t₁ (ite (option.get t₁) (⊙ true) t₂)
    else .error .typeError
  | _, _ => .error .typeError

def compileSet (ts : List Term) : Result Term := do
   match ts with
    | []     => .error .unsupportedError  -- reject empty set literals
    | t :: _ =>
      match t.typeOf with
      | .option ty =>
        if ts.all (Term.typeOf · = .option ty)
        then ifAllSome ts (⊙setOf (ts.map option.get) ty)
        else .error .typeError
      | _ => .error .typeError

def compileRecord (ats : List (Attr × Term)) : Term :=
  ifAllSome (ats.map Prod.snd) (⊙recordOf (ats.map (Prod.map id option.get)))

def compileCall₀ {α} [Coe α Ext] (mk : String → Option α) : Term → Result Term
  | .some (.prim (.string s)) =>
    match (mk s) with
    | .some v => ⊙ .prim (.ext v)
    | .none   => .error .typeError
  | _         => .error .typeError

def compileCallWithError₁ (xty : ExtType) (enc : Term -> Term) (t₁ : Term) : Result Term := do
  if t₁.typeOf = .option (.ext xty)
  then ifSome t₁ (enc (option.get t₁))
  else .error .typeError

def compileCall₁ (xty : ExtType) (enc : Term → Term) (t₁ : Term) : Result Term :=
  compileCallWithError₁ xty (λ t₁ => ⊙ enc t₁) t₁

def compileCallWithError₂ (xty₁ xty₂ : ExtType) (enc : Term → Term → Term) (t₁ t₂ : Term) : Result Term := do
  let ty₁ := .option (.ext xty₁)
  let ty₂ := .option (.ext xty₂)
  if t₁.typeOf = ty₁ && t₂.typeOf = ty₂
  then ifSome t₁ (ifSome t₂ (enc (option.get t₁) (option.get t₂)))
  else .error .typeError

def compileCall₂ (xty : ExtType) (enc : Term → Term → Term) (t₁ t₂ : Term) : Result Term :=
  compileCallWithError₂ xty xty (λ t₁ t₂ => ⊙ enc t₁ t₂) t₁ t₂

def compileCall (xfn : ExtFun) (ts : List Term) : Result Term := do
  match xfn, ts with
  | .decimal, [t₁]                => compileCall₀ Ext.Decimal.decimal t₁
  | .lessThan, [t₁, t₂]           => compileCall₂ .decimal Decimal.lessThan t₁ t₂
  | .lessThanOrEqual, [t₁, t₂]    => compileCall₂ .decimal Decimal.lessThanOrEqual t₁ t₂
  | .greaterThan, [t₁, t₂]        => compileCall₂ .decimal Decimal.greaterThan t₁ t₂
  | .greaterThanOrEqual, [t₁, t₂] => compileCall₂ .decimal Decimal.greaterThanOrEqual t₁ t₂
  | .ip, [t₁]                     => compileCall₀ Ext.IPAddr.ip t₁
  | .isIpv4, [t₁]                 => compileCall₁ .ipAddr IPAddr.isIpv4 t₁
  | .isIpv6, [t₁]                 => compileCall₁ .ipAddr IPAddr.isIpv6 t₁
  | .isLoopback, [t₁]             => compileCall₁ .ipAddr IPAddr.isLoopback t₁
  | .isMulticast, [t₁]            => compileCall₁ .ipAddr IPAddr.isMulticast t₁
  | .isInRange, [t₁, t₂]          => compileCall₂ .ipAddr IPAddr.isInRange t₁ t₂
  | .datetime, [t₁]               => compileCall₀ Ext.Datetime.datetime t₁
  | .duration, [t₁]               => compileCall₀ Ext.Datetime.duration t₁
  | .offset, [t₁, t₂]             => compileCallWithError₂ .datetime .duration Datetime.offset t₁ t₂
  | .durationSince, [t₁, t₂]      => compileCallWithError₂ .datetime .datetime Datetime.durationSince t₁ t₂
  | .toDate, [t₁]                 => compileCallWithError₁ .datetime Datetime.toDate t₁
  | .toTime, [t₁]                 => compileCall₁ .datetime Datetime.toTime t₁
  | .toMilliseconds, [t₁]         => compileCall₁ .duration Duration.toMilliseconds t₁
  | .toSeconds, [t₁]              => compileCall₁ .duration Duration.toSeconds t₁
  | .toMinutes, [t₁]              => compileCall₁ .duration Duration.toMinutes t₁
  | .toHours, [t₁]                => compileCall₁ .duration Duration.toHours t₁
  | .toDays, [t₁]                 => compileCall₁ .duration Duration.toDays t₁
  | _, _                          => .error .typeError

/--
Given an expression `x` that has type `τ` with respect to a type environment
`Γ`, and given a well-formed symbolic environment `εnv` that conforms to `Γ`,
`compile x εnv` succeeds and produces a well-formed term of type `.option τ.toTermType`.
-/
def compile (x : Expr) (εnv : SymEnv) : Result Term := do
  match x with
  | .lit l => compilePrim l εnv.entities
  | .var v => compileVar v εnv.request
  | .ite x₁ x₂ x₃ =>
    compileIf (← compile x₁ εnv) (compile x₂ εnv) (compile x₃ εnv)
  | .and x₁ x₂ =>
    compileAnd (← compile x₁ εnv) (compile x₂ εnv)
  | .or x₁ x₂ =>
    compileOr (← compile x₁ εnv) (compile x₂ εnv)
  | .unaryApp op₁ x₁ =>
    let t₁ ← compile x₁ εnv
    ifSome t₁ (← compileApp₁ op₁ (option.get t₁))
  | .binaryApp op₂ x₁ x₂ =>
    let t₁ ← compile x₁ εnv
    let t₂ ← compile x₂ εnv
    ifSome t₁ (ifSome t₂ (← compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities))
  | .hasAttr x a =>
    let t ← compile x εnv
    ifSome t (← compileHasAttr (option.get t) a εnv.entities)
  | .getAttr x a =>
    let t ← compile x εnv
    ifSome t (← compileGetAttr (option.get t) a εnv.entities)
  | .set xs =>
    let ts ← xs.mapM₁ (λ ⟨x₁, _⟩ => compile x₁ εnv)
    compileSet ts
  | .record axs =>
    let ats ← axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do .ok (a₁, ← compile x₁ εnv))
    compileRecord ats
  | .call xfn xs =>
    let ts ← xs.mapM₁ (λ ⟨x₁, _⟩ => compile x₁ εnv)
    compileCall xfn ts

namespace Cedar.SymCC

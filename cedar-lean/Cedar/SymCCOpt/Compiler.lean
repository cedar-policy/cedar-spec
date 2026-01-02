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

import Cedar.SymCC.Compiler
import Cedar.SymCC.Env
import Cedar.SymCC.ExtFun
import Cedar.SymCC.Factory

/-!
This file defines an optimized Cedar symbolic compiler, which computes the
actual compiled `Term` and the `footprint` simultaneously, avoiding the
inefficiencies in the `footprint` function in SymCC/Enforcer.lean, which
repeatedly calls `compile` on certain subexpressions, making it quadratic or
worse in policy size, at least for certain policies.

For notes on the meaning of compile or footprint, see SymCC/Compiler.lean and
SymCC/Enforcer.lean, which have clearer, unoptimized implementations.
-/

namespace Cedar.SymCC.Opt

open Cedar.Data Cedar.Spec Cedar.Validation
open Factory

/--
Structure returned by the optimized compiler, as opposed to the unoptimized
compiler which just produces a `Term`
-/
structure CompileResult where
  /-- Well-formed term of the appropriate type, representing the compiled expression -/
  term : Term
  /--
  The "footprint" of the compiled expression.

  This is the terms corresponding to subexpressions of the compiled expression
  of the following form:

  * A variable term with an entity type
  * An entity reference literal
  * An attribute access expression with an entity type
  * A binary (`getTag`) expression with an entity type

  These are the only basic expressions in Cedar that may evaluate to an entity.
  All other expressions that evaluate to an entity are built up from the above
  basic expresions.

  All terms in the `footprint` are of type `TermType.option .entity`.
  -/
  footprint : Set Term

/-- Map on the `Term`, leaving the `footprint` unchanged -/
def CompileResult.mapTerm (f : Term → Term) : CompileResult → CompileResult
  | { term, footprint } => { term := f term, footprint }

/--
Return the footprint of this compiled term _itself_ (not counting its subexpressions).
Only terms of option-entity type have any direct footprint.

This corresponds to `ofEntity` in the `footprint` function in
SymCC/Enforcer.lean, except that we only call it when compiling to `Term` was
successful, so it takes a `Term` argument rather than `Result Term`.
-/
def directFootprint (t : Term) : Set Term :=
  if t.typeOf.isOptionEntityType then Set.singleton t else Set.empty

def compilePrim (p : Prim) (εs : SymEntities) : Result CompileResult :=
  match p with
  | .bool b        => .ok { term := ⊙b, footprint := ∅ }
  | .int i         => .ok { term := ⊙i, footprint := ∅ }
  | .string s      => .ok { term := ⊙s, footprint := ∅ }
  | .entityUID uid =>
      if εs.isValidEntityUID uid then
        -- essentially inlining our `directFootprint` function, no need to
        -- compute `.typeOf`, we know the term is option-entity type
        let term := ⊙uid
        .ok { term, footprint := Set.singleton term }
      else
        .error .typeError

def compileVar (v : Var) (req : SymRequest) : Result CompileResult :=
  match v with
  | .principal =>
      if req.principal.typeOf.isEntityType then
        -- essentially inlining our `directFootprint` function, no need to
        -- compute `.typeOf`, we know the term is option-entity type
        let term := ⊙req.principal
        .ok { term, footprint := Set.singleton term }
      else
        .error .typeError
  | .action    =>
      if req.action.typeOf.isEntityType then
        -- essentially inlining our `directFootprint` function, no need to
        -- compute `.typeOf`, we know the term is option-entity type
        let term := ⊙req.action
        .ok { term, footprint := Set.singleton term }
      else
        .error .typeError
  | .resource  =>
      if req.resource.typeOf.isEntityType then
        -- essentially inlining our `directFootprint` function, no need to
        -- compute `.typeOf`, we know the term is option-entity type
        let term := ⊙req.resource
        .ok { term, footprint := Set.singleton term }
      else
        .error .typeError
  | .context   =>
      if req.context.typeOf.isRecordType then
        -- essentially inlining our `directFootprint` function, no need to
        -- compute `.typeOf`, we know the term is _not_ option-entity type
        .ok { term := ⊙req.context, footprint := ∅ }
      else
        .error .typeError

def compileApp₁ (op₁ : UnaryOp) (arg : CompileResult) : Result CompileResult := do
  match op₁, arg.term.typeOf with
  | .not, .bool            => arg.mapTerm λ term => ⊙not term
  | .neg, .bitvec 64       => arg.mapTerm λ term => ifFalse (bvnego term) (bvneg term)
  | .like p, .string       => arg.mapTerm λ term => ⊙string.like term p
  | .is ety₁, .entity ety₂ => arg.mapTerm λ _ => ⊙(ety₁ = ety₂ : Bool)
  | .isEmpty, .set _       => arg.mapTerm λ term => ⊙set.isEmpty term
  | _, _                   => .error .typeError

def compileApp₂ (op₂ : BinaryOp) (arg₁ arg₂ : CompileResult) (εs : SymEntities) : Result CompileResult := do
  -- compute the footprint of the arguments, not counting the contribution of the `directFootprint` of
  -- the binaryOp term (if any) (particularly relevant for `getTag`)
  let argsFootprint := arg₁.footprint ∪ arg₂.footprint
  -- mimicking the behavior of the unoptimized compiler in how the direct
  -- footprint for the binaryOp term itself is computed.
  -- Assuming everything is well-typed, this will be ∅ in all cases except `getTag` (because none of
  -- the other binary operators can have entity type), but we still add this in every case because:
  -- (1) we want the two compilers to agree even on non-well-typed inputs, for ease of proofs; and
  -- (2) the unoptimized compiler adds this
  let binaryOpFootprint := λ term => directFootprint (ifSome arg₁.term (ifSome arg₂.term term))
  -- for the rest of this function, we consider only the `option.get`-ed args.
  -- see detailed note in the toplevel optimized `compile` function below.
  let t₁ := option.get arg₁.term
  let t₂ := option.get arg₂.term
  match op₂, t₁.typeOf, t₂.typeOf with
  | .eq, ty₁, ty₂                           => let term := if (← reducibleEq ty₁ ty₂) then ⊙eq t₁ t₂ else ⊙false
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .less, .bitvec 64, .bitvec 64           => let term := ⊙bvslt t₁ t₂
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .less, .ext .datetime, .ext .datetime   => let term := ⊙bvslt (ext.datetime.val t₁) (ext.datetime.val t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .less, .ext .duration, .ext .duration   => let term := ⊙bvslt (ext.duration.val t₁) (ext.duration.val t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .lessEq, .bitvec 64, .bitvec 64         => let term := ⊙bvsle t₁ t₂
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .lessEq, .ext .datetime, .ext .datetime => let term := ⊙bvsle (ext.datetime.val t₁) (ext.datetime.val t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .lessEq, .ext .duration, .ext .duration => let term := ⊙bvsle (ext.duration.val t₁) (ext.duration.val t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .add, .bitvec 64, .bitvec 64            => let term := ifFalse (bvsaddo t₁ t₂) (bvadd t₁ t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .sub, .bitvec 64, .bitvec 64            => let term := ifFalse (bvssubo t₁ t₂) (bvsub t₁ t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .mul, .bitvec 64, .bitvec 64            => let term := ifFalse (bvsmulo t₁ t₂) (bvmul t₁ t₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .contains, .set ty₁, ty₂                => if ty₁ = ty₂
                                                then
                                                  let term := ⊙set.member t₂ t₁
                                                  .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
                                                else .error .typeError
  | .containsAll, .set ty₁, .set ty₂        => if ty₁ = ty₂
                                                then
                                                  let term := ⊙set.subset t₂ t₁
                                                  .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
                                                else .error .typeError
  | .containsAny, .set ty₁, .set ty₂        => if ty₁ = ty₂
                                                then
                                                  let term := ⊙set.intersects t₁ t₂
                                                  .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
                                                else .error .typeError
  | .mem, .entity ety₁, .entity ety₂        => let term := ⊙compileInₑ t₁ t₂ (εs.ancestorsOfType ety₁ ety₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .mem, .entity ety₁, .set (.entity ety₂) => let term := ⊙compileInₛ t₁ t₂ (εs.ancestorsOfType ety₁ ety₂)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .hasTag, .entity ety, .string           => let term ← compileHasTag t₁ t₂ (εs.tags ety)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | .getTag, .entity ety, .string           => let term ← compileGetTag t₁ t₂ (εs.tags ety)
                                               .ok { term, footprint := argsFootprint ∪ binaryOpFootprint term }
  | _, _, _                                 => .error .typeError

def compileHasAttr (arg : CompileResult) (a : Attr) (εs : SymEntities) : Result CompileResult := do
  let attrs ← compileAttrsOf arg.term εs
  match attrs.typeOf with
  | .record rty =>
    match rty.find? a with
    | .some (.option _) => .ok { term := ⊙isSome (record.get attrs a), footprint := arg.footprint }
    | .some _           => .ok { term := ⊙true, footprint := arg.footprint }
    | .none             => .ok { term := ⊙false, footprint := arg.footprint }
  | _ => .error .typeError

def compileGetAttr (arg : CompileResult) (a : Attr) (εs : SymEntities) : Result CompileResult := do
  -- mimicking the behavior of the unoptimized compiler in how the direct
  -- footprint for the getAttr term itself is computed
  let getAttrFootprint := λ term => directFootprint (ifSome arg.term term)
  -- for the rest of this function, we consider only the `option.get`-ed args.
  -- see detailed note in the toplevel optimized `compile` function below.
  let term := option.get arg.term
  let attrs ← compileAttrsOf term εs
  match attrs.typeOf with
  | .record rty =>
    let term ← match rty.find? a with
    | .some (.option _) => record.get attrs a
    | .some _           => ⊙(record.get attrs a)
    | .none             => .error .noSuchAttribute
    .ok { term, footprint := getAttrFootprint term ∪ arg.footprint }
  | _ => .error .typeError

def compileIf (arg₁ : CompileResult) (arg₂ arg₃ : Result CompileResult) : Result CompileResult := do
  match arg₁.term, arg₁.term.typeOf with
  | .some (.prim (.bool true)), _  => arg₂ -- omitting arg₁.footprint is sound: unoptimized `SymCC.footprint` does that in this case, and our proofs show it's sound
  | .some (.prim (.bool false)), _ => arg₃ -- omitting arg₁.footprint is sound: unoptimized `SymCC.footprint` does that in this case, and our proofs show it's sound
  | _, .option .bool =>
    let arg₂ ← arg₂
    let arg₃ ← arg₃
    if arg₂.term.typeOf = arg₃.term.typeOf
    then .ok {
      term := ifSome arg₁.term (ite (option.get arg₁.term) arg₂.term arg₃.term)
      footprint := arg₁.footprint ∪ arg₂.footprint ∪ arg₃.footprint
    }
    else .error .typeError
  | _, _ => .error .typeError

def compileAnd (arg₁ : CompileResult) (arg₂ : Result CompileResult) : Result CompileResult := do
  match arg₁.term, arg₁.term.typeOf with
  | .some (.prim (.bool false)), _ => .ok { term := arg₁.term, footprint := ∅ } -- we could just do `.ok arg₁`, but the unoptimized `SymCC.footprint` returns an empty footprint in this case, which is also sound (as our proofs show)
  | _, .option .bool =>
    let arg₂ ← arg₂
    if arg₂.term.typeOf = .option .bool
    then
      let footprint := if arg₁.term = .some (.prim (.bool true))
        then arg₂.footprint -- omitting arg₁.footprint is sound: unoptimized `SymCC.footprint` does that in this case, and our proofs show it's sound
        else arg₁.footprint ∪ arg₂.footprint
      .ok {
        term := ifSome arg₁.term (ite (option.get arg₁.term) arg₂.term (⊙false))
        footprint
      }
    else .error .typeError
  | _, _ => .error .typeError

def compileOr (arg₁ : CompileResult) (arg₂ : Result CompileResult) : Result CompileResult := do
  match arg₁.term, arg₁.term.typeOf with
  | .some (.prim (.bool true)), _  => .ok { term := arg₁.term, footprint := ∅ } -- we could just do `.ok arg₁`, but the unoptimized `SymCC.footprint` returns an empty footprint in this case, which is also sound (as our proofs show)
  | _, .option .bool =>
    let arg₂ ← arg₂
    if arg₂.term.typeOf = .option .bool
    then
      let footprint := if arg₁.term = .some (.prim (.bool false))
        then arg₂.footprint -- omitting arg₁.footprint is sound: unoptimized `SymCC.footprint` does that in this case, and our proofs show it's sound
        else arg₁.footprint ∪ arg₂.footprint
      .ok {
        term := ifSome arg₁.term (ite (option.get arg₁.term) (⊙true) arg₂.term)
        footprint
      }
    else .error .typeError
  | _, _ => .error .typeError

def compileSet (args : List CompileResult) : Result CompileResult := do
   match args with
    | []     => .error .unsupportedError  -- reject empty set literals
    | arg :: _ =>
      match arg.term.typeOf with
      | .option ty =>
        let terms := args.map CompileResult.term
        if terms.all (Term.typeOf · = .option ty)
        then .ok {
          term := ifAllSome terms (⊙setOf (terms.map option.get) ty)
          footprint := args.mapUnion CompileResult.footprint
        }
        else .error .typeError
      | _ => .error .typeError

def compileRecord (ats : List (Attr × CompileResult)) : CompileResult :=
  let terms := ats.map λ ⟨_, { term, .. }⟩ => term
  {
    term := ifAllSome terms (⊙recordOf (ats.map (Prod.map id (λ { term, .. } => option.get term))))
    footprint := ats.mapUnion λ ⟨_, { footprint, .. }⟩ => footprint
  }

def compileCall₀ {α} [Coe α Ext] (mk : String → Option α) : CompileResult → Result CompileResult
  | { term := .some (.prim (.string s)), footprint } =>
    match (mk s) with
    | .some v => .ok { term := ⊙ .prim (.ext v), footprint }
    | .none   => .error .typeError
  | _         => .error .typeError

def compileCallWithError₁ (xty : ExtType) (enc : Term -> Term) (arg₁ : CompileResult) : Result CompileResult := do
  if arg₁.term.typeOf = .option (.ext xty)
  then .ok {
    term := ifSome arg₁.term (enc (option.get arg₁.term))
    footprint := arg₁.footprint
  }
  else .error .typeError

def compileCall₁ (xty : ExtType) (enc : Term → Term) (arg₁ : CompileResult) : Result CompileResult :=
  compileCallWithError₁ xty (λ t₁ => ⊙ enc t₁) arg₁

def compileCallWithError₂ (xty₁ xty₂ : ExtType) (enc : Term → Term → Term) (arg₁ arg₂ : CompileResult) : Result CompileResult := do
  let ty₁ := .option (.ext xty₁)
  let ty₂ := .option (.ext xty₂)
  if arg₁.term.typeOf = ty₁ && arg₂.term.typeOf = ty₂
  then .ok {
    term := ifSome arg₁.term (ifSome arg₂.term (enc (option.get arg₁.term) (option.get arg₂.term)))
    footprint := arg₁.footprint ∪ arg₂.footprint
  }
  else .error .typeError

def compileCall₂ (xty : ExtType) (enc : Term → Term → Term) (arg₁ arg₂ : CompileResult) : Result CompileResult :=
  compileCallWithError₂ xty xty (λ t₁ t₂ => ⊙ enc t₁ t₂) arg₁ arg₂

def compileCall (xfn : ExtFun) (args : List CompileResult) : Result CompileResult := do
  match xfn, args with
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
def compile (x : Expr) (εnv : SymEnv) : Result CompileResult := do
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
    let res₁ ← compile x₁ εnv
    let res ← compileApp₁ op₁ (res₁.mapTerm option.get)
    res.mapTerm (ifSome res₁.term ·)
  | .binaryApp op₂ x₁ x₂ =>
    let res₁ ← compile x₁ εnv
    let res₂ ← compile x₂ εnv
    -- subtlety:
    -- the unoptimized _compiler_ calls `option.get` on the terms passed to `compileApp₂`,
    -- similar to how it's done for `compileApp₁`, `compileHasAttr`, etc.
    -- However, for _footprint_ purposes, the unoptimized `footprint` function expresses
    -- the footprint in terms of the original terms, without the `option.get`.
    -- In order to give our optimized `compileApp₂` easy access to both the original and
    -- `option.get` terms, we pass the original ones here.
    let res ← compileApp₂ op₂ res₁ res₂ εnv.entities
    res.mapTerm λ term => (ifSome res₁.term (ifSome res₂.term term))
  | .hasAttr x a =>
    let res₁ ← compile x εnv
    let res ← compileHasAttr (res₁.mapTerm option.get) a εnv.entities
    res.mapTerm (ifSome res₁.term ·)
  | .getAttr x a =>
    -- subtlety:
    -- similar to the comment above in the `binaryApp` case
    let res₁ ← compile x εnv
    let res ← compileGetAttr res₁ a εnv.entities
    res.mapTerm (ifSome res₁.term ·)
  | .set xs =>
    let ress ← xs.mapM₁ (λ ⟨x₁, _⟩ => compile x₁ εnv)
    compileSet ress
  | .record axs =>
    let ats ← axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do .ok (a₁, ← compile x₁ εnv))
    compileRecord ats
  | .call xfn xs =>
    let ress ← xs.mapM₁ (λ ⟨x₁, _⟩ => compile x₁ εnv)
    compileCall xfn ress

namespace Cedar.SymCC

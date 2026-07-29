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

public import Cedar.Frontend.Cst
public import Cedar.Frontend.Cst.Semantics
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
public import Cedar.Spec.Response
public import Cedar.Spec.Value
public import Cedar.Spec.Evaluator
public import Cedar.Frontend.Cst.ToAst

namespace Cedar.Spec

open Cedar.Data

/-! ### A total order on `Error` (so we can build `Set Error`)

`Error` only derives `DecidableEq`, but `Set` needs `LT`/`DecidableLT`.  We
induce a strict order by ranking each constructor with a `Nat`.  (`StrictLT`
can be added later when we prove theorems about the collected sets; the
collector *definitions* need only `LT`/`DecidableLT`.) -/

public def CstError.rank : CstError → Nat
  | .stringError      => 0
  | .nameError        => 1
  | .unsupportedError => 2
  | .arityError       => 3
  | .translationError => 4
  | .primaryOverflowError => 5

public def Error.rank : Error → Nat
  | .entityDoesNotExist => 0
  | .attrDoesNotExist   => 1
  | .tagDoesNotExist    => 2
  | .typeError          => 3
  | .arithBoundsError   => 4
  | .extensionError     => 5
  | .cstError c         => 6 + CstError.rank c

public instance : LT Error := ⟨fun a b => Error.rank a < Error.rank b⟩

public instance (a b : Error) : Decidable (a < b) :=
  inferInstanceAs (Decidable (Error.rank a < Error.rank b))

theorem CstError.rank_inj (a b : CstError) (h : CstError.rank a = CstError.rank b) : a = b := by
  cases a <;> cases b <;> simp_all [CstError.rank]

theorem Error.rank_inj (a b : Error) (h : Error.rank a = Error.rank b) : a = b := by
  cases a <;> cases b <;> simp only [Error.rank] at h <;>
    first
      | rfl
      | omega
      | exact congrArg Error.cstError (CstError.rank_inj _ _ (by omega))

public instance : StrictLT Error where
  asymmetric a b h := by
    have hab : Error.rank a < Error.rank b := h
    intro hba
    have hba' : Error.rank b < Error.rank a := hba
    omega
  transitive a b c h1 h2 := by
    have h1' : Error.rank a < Error.rank b := h1
    have h2' : Error.rank b < Error.rank c := h2
    show Error.rank a < Error.rank c
    omega
  connected a b hne := by
    rcases Nat.lt_trichotomy (Error.rank a) (Error.rank b) with h | h | h
    · exact Or.inl h
    · exact absurd (Error.rank_inj a b h) hne
    · exact Or.inr h

end Cedar.Spec

namespace Cedar.Frontend.Cst

open Cedar.Data
open Cedar.Spec

/-- Result of the error collector: the set of errors found while
    (comprehensively) walking a CST node, paired with the value the ordinary
    evaluator produces (`none` exactly when evaluation errors).  `.1` is the
    error set, `.2` the optional value. -/
public abbrev CollectResult := Set Error × Option Value

/-- Lift one evaluator result into a `CollectResult`. -/
public def CollectResult.ofResult : Result Value → CollectResult
  | .ok v    => (∅, some v)
  | .error e => (Set.singleton e, none)

mutual

public def collectExprList (xs : List Expr) (req : Request) (es : Entities) :
    Set Error × List (Option Value) :=
  match xs with
  | [] => (∅, [])
  | x :: rest =>
    let hd := x.collectErrors req es
    let tl := collectExprList rest req es
    (hd.1 ∪ tl.1, hd.2 :: tl.2)
termination_by sizeOf xs

public def collectRInits (r : List RecInit) (req : Request) (es : Entities) : Set Error :=
  match r with
  | [] => ∅
  | ⟨k, v⟩ :: rest =>
    (match k.toAttr? with
     | some _ => ∅
     | none   => Set.singleton (Error.cstError .stringError))
    ∪ (v.collectErrors req es).1
    ∪ collectRInits rest req es
termination_by sizeOf r

public def collectMults (xs : List (MultOp × Unary)) (req : Request) (es : Entities) : Set Error :=
  match xs with
  | [] => ∅
  | (op, u) :: rest =>
    (match op with
     | .mTimes => ∅
     | _       => Set.singleton (Error.cstError .unsupportedError))
    ∪ (u.collectErrors req es).1
    ∪ collectMults rest req es
termination_by sizeOf xs

public def collectAdds (xs : List (AddOp × MultExpr)) (req : Request) (es : Entities) : Set Error :=
  match xs with
  | [] => ∅
  | (_, m) :: rest => (m.collectErrors req es).1 ∪ collectAdds rest req es
termination_by sizeOf xs

public def collectRels (xs : List (RelOp × AddExpr)) (req : Request) (es : Entities) : Set Error :=
  match xs with
  | [] => ∅
  | (_, a) :: rest => (a.collectErrors req es).1 ∪ collectRels rest req es
termination_by sizeOf xs

public def collectRelations (xs : List Relation) (req : Request) (es : Entities) : Set Error :=
  match xs with
  | [] => ∅
  | r :: rest => (r.collectErrors req es).1 ∪ collectRelations rest req es
termination_by sizeOf xs

public def collectAndExprs (xs : List AndExpr) (req : Request) (es : Entities) : Set Error :=
  match xs with
  | [] => ∅
  | a :: rest => (a.collectErrors req es).1 ∪ collectAndExprs rest req es
termination_by sizeOf xs

/--
Error collector for `Primary`, mirroring `Primary.evaluate` but never
short-circuiting.  The value channel (`.2`) always equals the evaluator's.
-/
public def Primary.collectErrors (e : Primary) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  match e with
  | .expr ex  => ((ex.collectErrors req es).1, evalres.2)
  | .eList xs => ((collectExprList xs req es).1, evalres.2)
  | .rInits r => (collectRInits r req es, evalres.2)
  | .literal _ | .name _ | .ref _ | .slot _ => evalres
termination_by sizeOf e
decreasing_by all_goals simp_wf

/--
Collect errors along an accessor spine, mirroring `Member.evalAccessors`.
Threads the value like the evaluator, but continues past a `none` head so
structural and method-argument errors further down the spine aren't hidden.
-/
public def Member.collectAccessors
    (head : Option Value) (accs : List MemAccess) (req : Request) (es : Entities) : CollectResult :=
  match accs with
  | [] => (∅, head)
  | .field i :: .call args :: rest =>
      let argErrs := (collectExprList args req es).1
      match Ident.toUnreservedString? i with
      | none =>
          (Set.singleton (Error.cstError .stringError) ∪ argErrs ∪ (Member.collectAccessors none rest req es).1, none)
      | some m =>
          match String.toMethodOp? m with
          | some (.inl bop) =>
              match args with
              | [arg] =>
                  let step : CollectResult :=
                    match head, (arg.collectErrors req es).2 with
                    | some hv, some av => CollectResult.ofResult (apply₂ bop hv av es)
                    | _, _             => (∅, none)
                  let rst := Member.collectAccessors step.2 rest req es
                  (argErrs ∪ step.1 ∪ rst.1, rst.2)
              | _ =>
                  (Set.singleton (Error.cstError .arityError) ∪ argErrs ∪ (Member.collectAccessors none rest req es).1, none)
          | some (.inr uop) =>
              if args.isEmpty then
                let step : CollectResult :=
                  match head with
                  | some hv => CollectResult.ofResult (apply₁ uop hv)
                  | none    => (∅, none)
                let rst := Member.collectAccessors step.2 rest req es
                (step.1 ∪ rst.1, rst.2)
              else
                (Set.singleton (Error.cstError .arityError) ∪ argErrs ∪ (Member.collectAccessors none rest req es).1, none)
          | none =>
              (Set.singleton (Error.cstError .unsupportedError) ∪ argErrs ∪ (Member.collectAccessors none rest req es).1, none)
  | .field i :: rest =>
      match Ident.toUnreservedString? i with
      | none =>
          (Set.singleton (Error.cstError .stringError) ∪ (Member.collectAccessors none rest req es).1, none)
      | some attr =>
          let step : CollectResult :=
            match head with
            | some hv => CollectResult.ofResult (getAttr hv attr es)
            | none    => (∅, none)
          let rst := Member.collectAccessors step.2 rest req es
          (step.1 ∪ rst.1, rst.2)
  | .index ex :: rest =>
      match Expr.toUnescapedStringLiteral? ex with
      | none =>
          (Set.singleton (Error.cstError .stringError) ∪ (Member.collectAccessors none rest req es).1, none)
      | some attr =>
          let step : CollectResult :=
            match head with
            | some hv => CollectResult.ofResult (getAttr hv attr es)
            | none    => (∅, none)
          let rst := Member.collectAccessors step.2 rest req es
          (step.1 ∪ rst.1, rst.2)
  | .call _ :: _ => (Set.singleton (Error.cstError .unsupportedError), none)
termination_by sizeOf accs
decreasing_by all_goals (simp_wf; omega)

/-- Error collector for `Member`, mirroring `Member.evaluate`. -/
public def Member.collectErrors (e : Member) (req : Request) (es : Entities) : CollectResult :=
  match e with
  | { item := .name { path := [], name := .idIdent s _ }, access := .call args :: rest } =>
      let ec := collectExprList args req es
      match String.toExtFun? s with
      | none =>
          (Set.singleton (Error.cstError .unsupportedError) ∪ ec.1 ∪ (Member.collectAccessors none rest req es).1, none)
      | some xfn =>
          let hd : CollectResult :=
            if ec.2.all Option.isSome
            then CollectResult.ofResult (call xfn (ec.2.filterMap id))
            else (∅, none)
          let rst := Member.collectAccessors hd.2 rest req es
          (ec.1 ∪ hd.1 ∪ rst.1, rst.2)
  | { item := item, access := access } =>
      let hd := item.collectErrors req es
      let rst := Member.collectAccessors hd.2 access req es
      (hd.1 ∪ rst.1, rst.2)
termination_by sizeOf e
decreasing_by all_goals (simp_wf; omega)

public def Unary.collectErrors (e : Unary) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let itemerrs := e.item.collectErrors req es
  (evalres.1 ∪ itemerrs.1, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf; omega)

public def MultExpr.collectErrors (e : MultExpr) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let initerr := (e.initial.collectErrors req es).1
  (evalres.1 ∪ initerr ∪ collectMults e.extended req es, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf; omega)

public def AddExpr.collectErrors (e : AddExpr) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let initerr := (e.initial.collectErrors req es).1
  (evalres.1 ∪ initerr ∪ collectAdds e.extended req es, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf; omega)

public def Relation.collectErrors (e : Relation) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let errs := match e with
    | .rCommon initial extended =>
        (initial.collectErrors req es).1 ∪ collectRels extended req es
    | .rHas target field =>
        (target.collectErrors req es).1 ∪
        (match field.toAttrs? with
         | some (_ :: _) => ∅
         | _             => Set.singleton (Error.cstError .unsupportedError))
    | .rLike target pattern =>
        (target.collectErrors req es).1 ∪
        (match pattern.toPatternString? with
         | none   => Set.singleton (Error.cstError .stringError)
         | some s => match toPattern? s with
                     | some _ => ∅
                     | none   => Set.singleton (Error.cstError .stringError))
    | .rIsIn target entityType inEntity =>
        (target.collectErrors req es).1 ∪
        (match entityType.toEntityType? with
         | some _ => ∅
         | none   => Set.singleton (Error.cstError .nameError)) ∪
        (match inEntity with
         | none    => ∅
         | some ie => (ie.collectErrors req es).1)
  (evalres.1 ∪ errs, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (simp_wf; omega)

public def AndExpr.collectErrors (e : AndExpr) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let initerr := (e.initial.collectErrors req es).1
  (evalres.1 ∪ initerr ∪ collectRelations e.extended req es, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf; omega)

public def OrExpr.collectErrors (e : OrExpr) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let initerr := (e.initial.collectErrors req es).1
  (evalres.1 ∪ initerr ∪ collectAndExprs e.extended req es, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf; omega)

public def ExprData.collectErrors (e : ExprData) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let errs := match e with
    | .edOr oe    => (oe.collectErrors req es).1
    | .edIf i t f =>
        (i.collectErrors req es).1 ∪ (t.collectErrors req es).1 ∪ (f.collectErrors req es).1
  (evalres.1 ∪ errs, evalres.2)
termination_by sizeOf e
decreasing_by all_goals (simp_wf; try omega)

public def ExprImpl.collectErrors (e : ExprImpl) (req : Request) (es : Entities) : CollectResult :=
  e.expr.collectErrors req es
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf)

public def Expr.collectErrors (e : Expr) (req : Request) (es : Entities) : CollectResult :=
  match e with
  | .expr ei => ei.collectErrors req es
termination_by sizeOf e
decreasing_by all_goals simp_wf

end

public def collectConds (conds : List Cond) (req : Request) (es : Entities) : Set Error :=
  match conds with
  | [] => ∅
  | c :: rest =>
    (match c.kind.toConditionKind? with
     | some _ => ∅
     | none   => Set.singleton (Error.cstError .translationError))
    ∪ (c.body.collectErrors req es).1
    ∪ collectConds rest req es
termination_by sizeOf conds

public def PolicyImpl.collectErrors (p : PolicyImpl) (req : Request) (es : Entities) : Set Error :=
  (match Ident.toEffect? p.effect with
   | some _ => ∅
   | none   => Set.singleton (Error.cstError .translationError))
  ∪ (match extractScope? p.vars with
     | some _ => ∅
     | none   => Set.singleton (Error.cstError .translationError))
  ∪ collectConds p.conds req es

public def Policy.collectErrors (p : Policy) (req : Request) (es : Entities) : Set Error :=
  match p with
  | .policy pi => pi.collectErrors req es

public def collectPolicies (ps : List Policy) (req : Request) (es : Entities) : Set Error :=
  match ps with
  | [] => ∅
  | p :: rest => p.collectErrors req es ∪ collectPolicies rest req es

public def Policies.collectErrors (ps : Policies) (req : Request) (es : Entities) : Set Error :=
  collectPolicies ps.ps req es

end Cedar.Frontend.Cst


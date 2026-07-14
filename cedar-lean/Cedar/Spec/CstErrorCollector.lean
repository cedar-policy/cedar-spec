module

public import Cedar.Spec.Cst
public import Cedar.Spec.CstSemantics
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
public import Cedar.Spec.Response
public import Cedar.Spec.Value
public import Cedar.Spec.Evaluator
public import Cedar.Spec.CstToAst

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

end Cedar.Spec

namespace Cedar.Spec.Cst

open Cedar.Data

/-- Result of the error collector: the set of errors found while
    (comprehensively) walking a CST node, paired with the value the ordinary
    evaluator produces (`none` exactly when evaluation errors).  `.1` is the
    error set, `.2` the optional value. -/
public abbrev CollectResult := Set Error × Option Value

/-- Union a list of error sets. -/
public def unionErrs (ss : List (Set Error)) : Set Error :=
  ss.foldl (· ∪ ·) (∅ : Set Error)

/-- Lift one evaluator result into a `CollectResult`. -/
public def CollectResult.ofResult : Result Value → CollectResult
  | .ok v    => (∅, some v)
  | .error e => (Set.singleton e, none)

mutual

/-- TODO: real comprehensive collector for the expr family. -/
public def Expr.collectErrors (e : Expr) (req : Request) (es : Entities) : CollectResult :=
  sorry

/--
Error collector for `Primary`, mirroring `Primary.evaluate` but never
short-circuiting: it visits every sub-expression and accumulates all errors.
The value channel (`.2`) always equals the ordinary evaluator's result.
-/
public def Primary.collectErrors (e : Primary) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  match e with
  | .expr ex  => ((ex.collectErrors req es).1, evalres.2)
  | .eList xs => (unionErrs (xs.attach.map (fun ⟨x, _⟩ => (x.collectErrors req es).1)), evalres.2)
  | .rInits r =>
      ( unionErrs (r.attach.map (fun ⟨ri, _⟩ =>
          (match ri.key.toAttr? with
           | some _ => ∅
           | none   => Set.singleton (Error.cstError .stringError))
          ∪ (ri.value.collectErrors req es).1))
      , evalres.2 )
  | .literal _ | .name _ | .ref _ => evalres

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
      let argErrs := unionErrs (args.attach.map (fun ⟨a, _⟩ => (a.collectErrors req es).1))
      match CstCommon.Ident.toUnreservedString? i with
      | none =>
          (Set.singleton (Error.cstError .stringError) ∪ argErrs ∪ (Member.collectAccessors none rest req es).1, none)
      | some m =>
          match CstCommon.String.toMethodOp? m with
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
      match CstCommon.Ident.toUnreservedString? i with
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
      match CstCommon.Expr.toUnescapedStringLiteral? ex with
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

/--
Error collector for `Member`, mirroring `Member.evaluate` but never
short-circuiting.  The value channel mirrors the evaluator.
-/
public def Member.collectErrors (e : Member) (req : Request) (es : Entities) : CollectResult :=
  match e with
  | { item := .name { path := [], name := .idIdent s }, access := .call args :: rest } =>
      let argErrs := unionErrs (args.attach.map (fun ⟨a, _⟩ => (a.collectErrors req es).1))
      match CstCommon.String.toExtFun? s with
      | none =>
          (Set.singleton (Error.cstError .unsupportedError) ∪ argErrs ∪ (Member.collectAccessors none rest req es).1, none)
      | some xfn =>
          let argVals := args.attach.map (fun ⟨a, _⟩ => (a.collectErrors req es).2)
          let hd : CollectResult :=
            if argVals.all Option.isSome
            then CollectResult.ofResult (call xfn (argVals.filterMap id))
            else (∅, none)
          let rst := Member.collectAccessors hd.2 rest req es
          (argErrs ∪ hd.1 ∪ rst.1, rst.2)
  | { item := item, access := access } =>
      let hd := item.collectErrors req es
      let rst := Member.collectAccessors hd.2 access req es
      (hd.1 ∪ rst.1, rst.2)

public def Unary.collectErrors (e : Unary) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let itemerrs := e.item.collectErrors req es
  (evalres.1 ∪ itemerrs.1, evalres.2)

public def MultExpr.collectErrors (e : MultExpr) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let initerr := e.initial.collectErrors req es
  let exterrs := unionErrs (e.extended.map (fun (op, b) => match op with
    | .mTimes => (b.collectErrors req es).1
    | _ => Set.singleton (Error.cstError .unsupportedError) ∪ (b.collectErrors req es).1))
  (evalres.1 ∪ initerr.1 ∪ exterrs, evalres.2)

public def AddExpr.collectErrors (e : AddExpr) (req : Request) (es : Entities) : CollectResult :=
  let evalres := CollectResult.ofResult (e.evaluate req es)
  let initerr := e.initial.collectErrors req es
  let exterrs := unionErrs (e.extended.map (fun (_, b) => (b.collectErrors req es).1))
  (evalres.1 ∪ initerr.1 ∪ exterrs, evalres.2)


end

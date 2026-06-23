module

public import Cedar.Spec.Cst
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
public import Cedar.Spec.Response
public import Cedar.Spec.Value
public import Cedar.Spec.Evaluator
public import Cedar.Spec.CstToAst

namespace Cedar.Spec.Cst

open Cedar.Data

-- The hierarchy of Expr in the CST
-- Expr → ExprImpl → ExprData → OrExpr → AndExpr → Relation
-- → AddExpr → MultExpr → Unary → Member → Primary

/- Evaluator helpers -/

public abbrev Ident.toString : Ident → String := CstCommon.Ident.toString

public def AttrChain? (ms : List MemAccess) : Option (List Attr) :=
  match ms with
  | [] => some []
  | m :: ms => match m with
    | .field i => match (CstCommon.Ident.toUnreservedString? i) with
      | none => none
      | some s => (AttrChain? ms).map (s :: ·)
    | .index e => match (CstCommon.Expr.toUnescapedStringLiteral? e) with
      | none => none
      | some s => (AttrChain? ms).map (s :: ·)
    | .call _ => none

private def Member.toAttrs? (e : Member) : Option (List Attr) :=
  match AttrChain? e.access with
  | none => none
  | some attrs => match e.item with
    | .literal (.liStr s) =>
      if attrs.isEmpty then some [s] else none
    | .literal _ => none
    | .name { path := [], name := id } => match (CstCommon.Ident.toUnreservedString? id) with
      | some s => some (s :: attrs)
      | none   => none
    | .name _ => none
    | _ => none

/-- Attribute name of an identifier used as a record key, read structurally
    (no translation).  Reserved keywords map to their spellings; ordinary
    identifiers map to themselves; `true`/`false`/`in`/`has`/… are rejected. -/
public def Ident.toAttr? : Ident → Option Attr
  | .idPrincipal => some "principal"
  | .idAction    => some "action"
  | .idResource  => some "resource"
  | .idContext   => some "context"
  | .idPermit    => some "permit"
  | .idForbid    => some "forbid"
  | .idWhen      => some "when"
  | .idUnless    => some "unless"
  | .idIdent s   => some s
  | _            => none

/-- Attribute name of a `Primary` used as a record key. -/
public def Primary.toAttr? (p : Primary) : Option Attr :=
  match p with
  | .literal (.liStr s)              => CstCommon.unescape? s
  | .name { path := [], name := id } => Ident.toAttr? id
  | _                                => none

/-- Extract a record-key attribute name from a CST expression, without
    translating it: the key must be a "bare" primary (no operators other than a
    no-op `-0`, no extended chains, no member accesses) that is a string literal
    or an identifier name.  This matches the keys the translator accepts. -/
public def Expr.toAttr? (e : Expr) : Option Attr :=
  match e with
  | .expr ⟨.edIf _ _ _⟩ => none
  | .expr ⟨.edOr o⟩ =>
    if !o.extended.isEmpty || !o.initial.extended.isEmpty then none
    else match o.initial.initial with
      | .rCommon ae ext =>
        if !ext.isEmpty || !ae.extended.isEmpty || !ae.initial.extended.isEmpty
            || !ae.initial.initial.item.access.isEmpty then none
        else match ae.initial.initial.op with
          | none            => Primary.toAttr? ae.initial.initial.item.item
          | some (.nDash 0) => Primary.toAttr? ae.initial.initial.item.item
          | _               => none
      | _ => none

-- RelOp: rLess, rLessEq, rGreaterEq, rGreater, rNotEq, rEq, rIn
-- `rGreater`/`rGreaterEq` use the `not (less/lessEq v₁ v₂)` pattern to match
-- the translator's `constructExprRel`. Behaviorally equivalent on totally-
-- comparable values; for other values, the `apply₂` errors propagate through
-- the `not` consistently with the translator's AST output.
public def applyRelOp (op : RelOp) (v₁ v₂ : Value) (es : Entities) : Result Value :=
  match op with
  | .rLess => apply₂ .less v₁ v₂ es
  | .rLessEq => apply₂ .lessEq v₁ v₂ es
  | .rGreater => do
    let r ← apply₂ .lessEq v₁ v₂ es
    apply₁ .not r
  | .rGreaterEq => do
    let r ← apply₂ .less v₁ v₂ es
    apply₁ .not r
  | .rEq => apply₂ .eq v₁ v₂ es
  | .rNotEq => do
    let eq ← apply₂ .eq v₁ v₂ es
    apply₁ .not eq
  | .rIn => apply₂ .mem v₁ v₂ es

-- When the list is all `.field id` with `id` unreserved, return the converted
-- list of `Attr`s. Otherwise return `none`. Matches the translator's
-- `constructAttrsAux?` filter.
public def fieldChain? : List MemAccess → Option (List Attr)
  | [] => some []
  | .field id :: xs => do
      let head ← Cedar.Spec.CstCommon.Ident.toUnreservedString? id
      let tail ← fieldChain? xs
      some (head :: tail)
  | _ :: _ => none

-- Head string for a name appearing at the start of a `has` field chain.
-- Mirrors the translator's two paths:
--   * `.var v` arm (when `n.toVar? = some v`): use `v.toString` directly,
--     allowing the four var idents through without an unreserved check.
--   * `.name an` arm (when `n.toVar? = none`): filter via `toUnreservedId?`,
--     accepting only `.idIdent s` with `s` unreserved.
public def Ident.toHasHead? : Cst.Ident → Option String
  | .idPrincipal => some "principal"
  | .idAction    => some "action"
  | .idResource  => some "resource"
  | .idContext   => some "context"
  | .idIdent s   => if Cedar.Spec.CstCommon.Unreserved? s then some s else none
  | _            => none

public def AddExpr.toAttrs? (e : AddExpr) : Option (List Attr) :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some _ => none
  | none => let member := unary.item
    match fieldChain? member.access with
    | none => none
    | some fields => match member.item with
      | .literal (.liStr s) =>
        -- Apply unescape? to mirror the translator's `(unescape? lit).map .inl`.
        if fields.isEmpty then (Cedar.Spec.CstCommon.unescape? s).map (fun s' => [s'])
        else none
      | .literal _ => none
      | .name { path := [], name := id } =>
        -- Mirror the translator's combined `.var v` / `.name n` arms via
        -- the helper above.
        match Ident.toHasHead? id with
        | some idStr => some (idStr :: fields)
        | none       => none
      | .name _ => none
      | _ => none

-- Only Literal.liStr s is allowed
-- Mirrors the translator's `Cst.AddExpr.toPattern?`: the unary `op` may be
-- `none` or `some (.nDash 0)` (a structural no-op that the translator allows).
public def AddExpr.toPatternString? (e : AddExpr) : Option String :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some (.nDash 0) | none =>
    let member := unary.item
    if !member.access.isEmpty then none else
    let item := member.item
    match item with
    | .literal (.liStr s) => some s
    | _ => none
  | some _ => none

-- Extracts an EntityType (Spec.Name) from an AddExpr that is a bare name.
public def AddExpr.toEntityTypeName? (e : AddExpr) : Option EntityType :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some (.nDash 0) | none =>
    let member := unary.item
    if !member.access.isEmpty then none else
    match member.item with
    | .name n => CstCommon.Name.toAName? n
    | _ => none
  | some _ => none

/- Evaluators -/

public def Str.toUnescapedString : Str → Result String
  | .string s => match Cedar.Spec.CstCommon.unescape? s with
    | some s' => .ok s'
    | none    => .error .typeError

/-- Evaluate the chain of attribute checks for `r has a₀.a₁.….aₙ` with
    short-circuiting on the inner `hasAttr` returning `false`. Mirrors the
    translator's `extendedHasAttr`, which builds nested `.and (hasAttr ...) ...`. -/
public def rHasChain (v : Value) (a : Attr) (rest : List Attr) (es : Entities) : Result Value :=
  match rest with
  | [] => hasAttr v a es
  | b :: bs => do
    let h ← hasAttr v a es
    match h with
    | .prim (.bool false) => .ok (.prim (.bool false))
    | _ => do
      let v' ← getAttr v a es
      rHasChain v' b bs es
termination_by sizeOf rest

mutual

public def Primary.evaluate (e : Primary) (req : Request) (es : Entities) : Result Value :=
  match e with
  | .literal l => match l with
    | .liTrue => .ok (.prim (.bool true))
    | .liFalse => .ok (.prim (.bool false))
    | .liNum n => match Int64.ofInt? n.toNat with
      | some i => .ok (.prim (.int i))
      | none => .error .arithBoundsError
    | .liStr s => do
      let s' ← Str.toUnescapedString (.string s)
      .ok (.prim (.string s'))
  | .name n =>
    -- Not implementing names with non-empty paths for now
    if !n.path.isEmpty then .error .typeError
    else match n.name with
      | .idPrincipal => .ok (.prim (.entityUID req.principal))
      | .idAction => .ok (.prim (.entityUID req.action))
      | .idResource => .ok (.prim (.entityUID req.resource))
      | .idContext => .ok (.record req.context)
      | _ => .error .typeError
  | .expr e => e.evaluate req es
  | .eList xs => do
    let vs ← xs.mapM (fun x => x.evaluate req es)
    .ok (.set (Set.make vs))
  | .ref r => match r with
    | .uid path eid => do
      let eid' ← Str.toUnescapedString eid
      match CstCommon.Name.toAName? path with
      | some etype => .ok (.prim (.entityUID { ty := etype, eid := eid' }))
      | none       => .error .typeError
    | .ref _ _ => .error .typeError
  | .rInits r => do
    let avs ← r.mapM₁ (fun ⟨ri, hmem⟩ =>
      have : sizeOf ri.value < 1 + sizeOf r := by
        have h1 := List.sizeOf_lt_of_mem hmem
        obtain ⟨k, v⟩ := ri
        simp only [RecInit.mk.sizeOf_spec] at h1
        show sizeOf v < 1 + sizeOf r
        omega
      match ri.key.toAttr? with
      | none => .error .typeError
      | some attr => do
          let val ← ri.value.evaluate req es
          .ok (attr, val))
    .ok (.record (Map.make avs))
termination_by sizeOf e

public def Member.evaluate (e : Member) (req : Request) (es : Entities) : Result Value :=
  match e with
  -- Function calls
  | { item := .name { path := [], name := .idIdent s }, access := .call args :: rest } =>
    match CstCommon.String.toExtFun? s with
    | none => .error .typeError
    | some xfn => do
      let args ← args.mapM (fun a => a.evaluate req es)
      let v ← call xfn args
      Member.evalAccessors v rest req es
  -- Accessors
  | { item := item, access := access } => do
    let head ← item.evaluate req es
    Member.evalAccessors head access req es
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)

public def Member.evalAccessors (head : Value) (accs : List MemAccess)
    (req : Request) (es : Entities) : Result Value :=
  match accs with
  | [] => .ok head
  -- Method call `recv.m(args)`: a field naming the method, then its arguments.
  | .field i :: .call args :: rest =>
    match CstCommon.Ident.toUnreservedString? i with
    | none => .error .typeError
    | some m => match CstCommon.String.toMethodOp? m with
      | some (.inl bop) => match args with
        | [arg] => do
          let argVal ← arg.evaluate req es
          let v ← apply₂ bop head argVal es
          Member.evalAccessors v rest req es
        | _ => .error .typeError
      | some (.inr uop) =>
        if args.isEmpty then do
          let v ← apply₁ uop head
          Member.evalAccessors v rest req es
        else .error .typeError
      | none => .error .typeError
  -- Attribute access `recv.attr`.
  | .field i :: rest =>
    match CstCommon.Ident.toUnreservedString? i with
    | none => .error .typeError
    | some attr => do
      let v ← getAttr head attr es
      Member.evalAccessors v rest req es
  -- Indexed attribute access `recv["attr"]`.
  | .index ex :: rest =>
    match CstCommon.Expr.toUnescapedStringLiteral? ex with
    | none => .error .typeError
    | some attr => do
      let v ← getAttr head attr es
      Member.evalAccessors v rest req es
  -- A call with no preceding field accessor is a call on a non-name value,
  -- which the translator rejects.
  | .call _ :: _ => .error .typeError
termination_by sizeOf accs
decreasing_by
  all_goals simp_wf
  all_goals omega

-- NegOp: nBang i, nOverBang, nDash i, nOverDash
-- The `.nDash` numeric-literal case is handled specially so that the value
-- `-(Int64.MAX + 1) = Int64.MIN` is representable, matching the AST translator.
public def Unary.evaluate (e : Unary) (req : Request) (es : Entities) : Result Value :=
  match e.op with
  | none => e.item.evaluate req es
  | some (.nBang n) =>
      if n == 0 then e.item.evaluate req es else do
        let mval ← e.item.evaluate req es
        -- error the non-bool
        match mval with
        | .prim (.bool b) =>
            if n % 2 == 0 then .ok (.prim (.bool b)) else .ok (.prim (.bool !b))
        | _ => .error .typeError
  | some (.nDash n) =>
      if n == 0 then e.item.evaluate req es else
      match CstCommon.Member.toLit? e.item with
      | some (.liNum x) =>
        let xNat := x.toNat
        let minMagnitude := (Int64.MAX + 1).toNat
        match compare xNat minMagnitude with
        | .eq =>
          -- AST translates to `(lit Int64.MIN).dashN (n-1)`.  Since
          -- `Int64.MIN.neg?` fails, only `n = 1` succeeds (zero further
          -- negations applied); any larger `n` errors on the first negation.
          if n == 1
          then .ok (.prim (.int Int64.MIN.toInt64))
          else .error .arithBoundsError
        | .lt =>
          match Int64.ofInt? (Int.ofNat xNat) with
          | some y =>
            if n % 2 == 0 then .ok (.prim (.int y)) else .ok (.prim (.int (-y)))
          | none => .error .arithBoundsError
        | .gt => .error .arithBoundsError
      | _ => do
          let mval ← e.item.evaluate req es
          -- Force the type check and error the non-ints. We must also check
          -- `i.neg?` *before* the parity shortcut: when `i = Int64.MIN`, the
          -- AST iterates `apply₁ .neg` and errors on the first step, so this
          -- case must error regardless of parity.
          match mval with
          | .prim (.int i) =>
              match i.neg? with
              | none => .error .arithBoundsError
              | some j =>
                  if n % 2 == 0 then .ok (.prim (.int i))
                  else .ok (.prim (.int j))
          | _ => .error .typeError
  | some _ => .error .arithBoundsError
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

public def MultExpr.evaluate (e : MultExpr) (req : Request) (es : Entities) : Result Value := do
  let b ← e.initial.evaluate req es
  MultExpr.foldOps b e.extended req es
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

-- Division and Modulo are rejected in cst_to_ast.rs
public def MultExpr.foldOps (acc : Value) (xs : List (MultOp × Unary))
    (req : Request) (es : Entities) : Result Value :=
  match xs with
  | [] => .ok acc
  | (op, u) :: rest => do
    let aval ← u.evaluate req es
    let acc' ← match op with
      | .mTimes => apply₂ .mul acc aval es
      | _ => .error .typeError
    MultExpr.foldOps acc' rest req es
termination_by sizeOf xs

public def AddExpr.evaluate (e : AddExpr) (req : Request) (es : Entities) : Result Value := do
  let b ← e.initial.evaluate req es
  AddExpr.foldOps b e.extended req es
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

public def AddExpr.foldOps (acc : Value) (xs : List (AddOp × MultExpr))
    (req : Request) (es : Entities) : Result Value :=
  match xs with
  | [] => .ok acc
  | (op, m) :: rest => do
    let aval ← m.evaluate req es
    let acc' ← match op with
      | .aPlus  => apply₂ .add acc aval es
      | .aMinus => apply₂ .sub acc aval es
    AddExpr.foldOps acc' rest req es
termination_by sizeOf xs

public def Relation.evaluate (e : Relation) (req : Request) (es : Entities) : Result Value :=
  match e with
  -- Currently assuming that the `RelOp` cannot be chained
  | .rCommon x xs => match xs with
    | [] => x.evaluate req es
    | [(op, y)] => do
      let v₁ ← x.evaluate req es
      let v₂ ← y.evaluate req es
      applyRelOp op v₁ v₂ es
    | _ => .error .typeError
  | .rHas t f => do
      let v ← t.evaluate req es
      match f.toAttrs? with
      | none => .error .typeError
      | some [] => .error .typeError
      | some (a :: as) =>
        -- For `r has x.y.z`: short-circuit on `false` between getAttr steps,
        -- mirroring the translator's `.and (hasAttr ...) (extendedHasAttr ...)`
        -- which short-circuits on the inner `hasAttr` returning `false`.
        rHasChain v a as es
  | .rLike t p => match p.toPatternString? with
    | none => .error .typeError
    | some s => do
      let v ← t.evaluate req es
      match Cedar.Spec.CstCommon.toPattern? s with
      | some p => apply₁ (.like p) v
      | none => .error .typeError
  | .rIsIn t ety inEntity => match ety.toEntityType? with
    | none => .error .typeError
    | some etyName => do
      let v ← t.evaluate req es
      let isResult ← apply₁ (.is etyName) v
      match inEntity with
      | none => .ok isResult
      | some ie =>
        -- Strengthening: fail the evaluation when the `in` branch does not
        -- translate, even if the `is` branch short-circuits to `false`. Under a
        -- successful translation `ie.toAExpr?.isSome` holds, so this guard is a
        -- no-op and the evaluator still agrees with the short-circuiting AST;
        -- but it lets a successful evaluation witness that `ie` translates,
        -- which is needed for translation completeness.
        if ie.toAExpr?.isNone then .error .typeError
        else do
          let b ← isResult.asBool
          if !b then .ok false
          else do
            let v₂ ← ie.evaluate req es
            apply₂ .mem v v₂ es
termination_by sizeOf e

public def AndExpr.evaluate (e : AndExpr) (req : Request) (es : Entities) : Result Value :=
  -- Strengthening (mirrors the `rIsIn` guard): fail when some
  -- conjunct does not translate, even if `foldOps` short-circuits past it on a
  -- `false`. Under a successful translation every conjunct translates, so this
  -- guard is a no-op and the evaluator still agrees with the short-circuiting
  -- AST; but it lets a successful evaluation witness that every conjunct
  -- translates, which completeness needs.
  if e.extended.all (fun r => r.toAExpr?.isSome) then do
    let acc ← e.initial.evaluate req es
    AndExpr.foldOps acc e.extended req es
  else .error .typeError
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

-- Mirrors the AST `Expr.and acc rel` evaluation: coerce acc to Bool, short-circuit
-- on `false`, otherwise coerce rel.evaluate to Bool, wrap as a Value, recurse.
public def AndExpr.foldOps (acc : Value) (xs : List Relation)
    (req : Request) (es : Entities) : Result Value :=
  match xs with
  | [] => .ok acc
  | x :: rest => do
    let b ← acc.asBool
    if !b then .ok (.prim (.bool false)) else do
      let b' ← (x.evaluate req es).as Bool
      AndExpr.foldOps (.prim (.bool b')) rest req es
termination_by sizeOf xs

public def OrExpr.evaluate (e : OrExpr) (req : Request) (es : Entities) : Result Value :=
  -- Strengthening (mirrors `AndExpr.evaluate`): fail when some disjunct does not
  -- translate, even if `foldOps` short-circuits past it on a `true`. Under a
  -- successful translation every disjunct translates, so this guard is a no-op
  -- and the evaluator still agrees with the short-circuiting AST; but it lets a
  -- successful evaluation witness that every disjunct translates.
  if e.extended.all (fun r => r.toAExpr?.isSome) then do
    let acc ← e.initial.evaluate req es
    OrExpr.foldOps acc e.extended req es
  else .error .typeError
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

-- Mirrors the AST `Expr.or acc rhs` evaluation: coerce acc to Bool, short-circuit
-- on `true`, otherwise coerce rhs.evaluate to Bool, wrap as a Value, recurse.
public def OrExpr.foldOps (acc : Value) (xs : List AndExpr)
    (req : Request) (es : Entities) : Result Value :=
  match xs with
  | [] => .ok acc
  | x :: rest => do
    let b ← acc.asBool
    if b then .ok (.prim (.bool true)) else do
      let b' ← (x.evaluate req es).as Bool
      OrExpr.foldOps (.prim (.bool b')) rest req es
termination_by sizeOf xs

public def ExprData.evaluate (e : ExprData) (req : Request) (es : Entities) : Result Value :=
  match e with
  | .edOr e => e.evaluate req es
  | .edIf i t f =>
    -- Strengthening (mirrors the `rIsIn` `in` guard): the guard `i` is always
    -- evaluated, but only one of `t`/`f` is (the conditional short-circuits), so
    -- we only fail when a *branch* `t`/`f` does not translate. Under a successful
    -- translation both branches translate, so this guard is a no-op and the
    -- evaluator still agrees with the AST `ite`; but it lets a successful
    -- evaluation witness that both branches translate (completeness recovers
    -- `i`'s translatability from the fact that `i` is always evaluated).
    if t.toAExpr?.isSome && f.toAExpr?.isSome then do
      let b ← (i.evaluate req es).as Bool
      if b then t.evaluate req es else f.evaluate req es
    else .error .typeError
termination_by sizeOf e

public def ExprImpl.evaluate (e : ExprImpl) (req : Request) (es : Entities) : Result Value :=
  e.expr.evaluate req es
termination_by sizeOf e
decreasing_by cases e; simp_wf

public def Expr.evaluate (e : Expr) (req : Request) (es : Entities) : Result Value :=
  match e with
  | .expr e => e.evaluate req es
termination_by sizeOf e

end

/- Lifting helpers -/

public def Expr.toPrimary (e : Expr) : Primary :=
  .expr e

public def Primary.toMember (p : Primary) : Member :=
  {item := p, access := []}

public def Member.toUnary (m : Member) : Unary :=
  {op := none, item := m}

public def Unary.toMultExpr (u : Unary) : MultExpr :=
  {initial := u, extended := []}

public def MultExpr.toAddExpr (m : MultExpr) : AddExpr :=
  {initial := m, extended := []}

public def AddExpr.toRelation (a : AddExpr) : Relation :=
  .rCommon a []

public def Relation.toAndExpr (r : Relation) : AndExpr :=
  {initial := r, extended := []}

public def AndExpr.toOrExpr (a : AndExpr) : OrExpr :=
  {initial := a, extended := []}

public def OrExpr.toExpr (o : OrExpr) : Expr :=
  .expr {expr := .edOr o}

public def Expr.lift (e : Expr) : Expr :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

/- Other lifting helpers -/

public def Expr.toRelation (e : Expr) : Relation :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation

public def Expr.toAddExpr (e : Expr) : AddExpr :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr

public def Ident.varToAddExpr (id : Ident) : AddExpr :=
  (Primary.name {path := [], name := id}).toMember.toUnary.toMultExpr.toAddExpr

/- Constants and Combinators on Expr -/

public def Relation.tt : Relation :=
  (Primary.literal Literal.liTrue).toMember.toUnary.toMultExpr.toAddExpr.toRelation

public def Relation.ff : Relation :=
  (Primary.literal Literal.liFalse).toMember.toUnary.toMultExpr.toAddExpr.toRelation

public def Expr.tt : Expr :=
  (Primary.literal Literal.liTrue).toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

public def Expr.ff : Expr :=
  (Primary.literal Literal.liFalse).toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

public def Expr.not (e : Expr) : Expr :=
  let e' : Unary := {op := NegOp.nBang 1, item := e.toPrimary.toMember}
  e'.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

public def Expr.and (e1 e2 : Expr) : Expr :=
  let e1' := e1.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation
  let e2' := e2.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation
  let e' : AndExpr := {initial := e1', extended := [e2']}
  e'.toOrExpr.toExpr

public def Expr.or (e1 e2 : Expr) : Expr :=
  let e1' := e1.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr
  let e2' := e2.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr
  let e' : OrExpr := {initial := e1', extended := [e2']}
  e'.toExpr

-- Check whether this is needed
-- public def andReduce : List Expr → List Expr
--   | [] => []
--   | Expr.tt :: es => andReduce es
--   | e :: es => e :: (andReduce es)

public def Expr.foldAnd : List Expr → Expr
  | []      => Expr.tt
  | [e]     => e
  | e :: es =>
    let e' := e.toRelation
    let es' := es.map Expr.toRelation
    let a : AndExpr := { initial := e', extended := es' }
    a.toOrExpr.toExpr

/- Conversion to Expr -/

public def VariableDef.toAndExpr (vd : VariableDef) : AndExpr :=
  let var' := vd.var.varToAddExpr
  match vd.entityType, vd.ineq with
  | some et, some (.rIn, e) =>
    {initial := Relation.rIsIn var' et (some e.toAddExpr), extended := []}
  | some et, none =>
    {initial := Relation.rIsIn var' et none, extended := []}
  | none, some (op, e) =>
    {initial := Relation.rCommon var' [(op, e.toAddExpr)], extended := []}
  | none, none =>
    {initial := Relation.tt, extended := []}
  | some _, some (_, _) =>
    -- entityType with a non-`in` operator (e.g., `==`) is not valid
    {initial := Relation.ff, extended := []}

public def VariableDef.toExpr (vd : VariableDef) : Expr :=
  vd.toAndExpr.toOrExpr.toExpr

public def Cond.toExpr (c : Cond) : Expr :=
  match c.cond, c.expr with
  | .idWhen, some e => e
  | .idUnless, some e => Expr.not e
  | _, _ => Expr.tt

-- The `effect` field is not considered in this translation
public def PolicyImpl.toExpr (p : PolicyImpl) : Expr :=
  let varExprs := List.map VariableDef.toExpr p.vars
  let condExprs := List.map Cond.toExpr p.conds
  Expr.foldAnd (varExprs ++ condExprs)

public def Policy.toExpr : Policy → Expr
  | policy p => PolicyImpl.toExpr p

public def Policies.toExpr (ps : Policies) : Expr :=
  let exprs := List.map Policy.toExpr ps.ps
  Expr.foldAnd exprs

/- Authorizer -/

public def Policy.id : Policy → PolicyID
  | .policy p => p.id

public def satisfied (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  policy.toExpr.evaluate req entities = .ok true

-- To avoid returning an `Option Bool`, this function returns `false`
-- when the `effect` field of `policy` is not an effect
public def satisfiedWithEffect (effect : Effect) (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  if satisfied policy req entities then
  match policy with
  | .policy p => match CstCommon.Ident.toEffect? p.effect with
    | none => false
    | some eff => eff = effect
  else false

public def satisfiedPolicies (effect : Effect) (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (List.filterMap
    (fun p => if satisfiedWithEffect effect p req entities then some p.id else none)
    policies.ps)

public def hasError (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  match policy with
  | .policy p =>
    -- Strengthening: a policy whose scope variables don't form a valid
    -- (principal, action, resource) triple has no AST translation
    -- (`extractScope?` fails), so we treat it as an error.  Under a successful
    -- translation `extractScope?` succeeds, so this guard is a no-op and
    -- agreement with the AST (`policy_hasError_agrees`) is preserved.
    if (extractScope? p.vars).isNone then true
    else match policy.toExpr.evaluate req entities with
         | .ok _ => false
         | .error _ => true

public def errorPolicies (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (List.filterMap
    (fun p => if hasError p req entities then some p.id else none)
    policies.ps)

public def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  let erroringPolicies := errorPolicies policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then {decision := .allow, determiningPolicies := permits, erroringPolicies}
  else {decision := .deny, determiningPolicies := forbids, erroringPolicies}

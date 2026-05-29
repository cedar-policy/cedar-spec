module

public import Cedar.Spec.Wildcard

@[expose] public section

namespace Cedar.Spec.Cst

public inductive Ident where
  | idPrincipal
  | idAction
  | idResource
  | idContext
  | idTrue
  | idFalse
  | idPermit
  | idForbid
  | idWhen
  | idUnless
  | idIn
  | idHas
  | idLike
  | idIs
  | idIf
  | idThen
  | idElse
  | idIdent (s : String)

-- Should the type of n match the Rust implementation (i.e. UInt64)?
-- Why are true and false in both Ident and Literal?
public inductive Literal where
  | liTrue
  | liFalse
  | liNum (n : UInt64)
  | liStr (s : String)

public inductive RelOp where
  | rLess
  | rLessEq
  | rGreaterEq
  | rGreater
  | rNotEq
  | rEq
  | rIn

public inductive AddOp where
  | aPlus
  | aMinus

public inductive MultOp where
  | mTimes
  | mDivide
  | mMod

-- The types for n does not match the Rust implementation (`UInt8`)
-- `Int` is used for simplicity
-- Are overBang and overDash for error cases?
public inductive NegOp where
  | nBang (n : UInt8)
  | nOverBang
  | nDash (n : UInt8)
  | nOverDash

-- `inductive` is still used for single-constructor definitions that
-- are defined using enum in cst.rs so that it is easier to add
-- constructors in the future

mutual

-- There is no correspondence of Rust's `SmolStr` in LEAN
public inductive Str where
  | string (s : String)

public structure Policies where
  ps : List Policy

public inductive Policy where
  | policy (p : PolicyImpl)

public structure PolicyImpl where
  -- annotations : List Annotation
  -- annotations not formalized at this stage
  effect : Ident
  vars : List VariableDef
  conds : List Cond

-- `variable` is a LEAN keyword
public structure VariableDef where
  var : Ident
  -- unusedTypeName : Option Name
  -- This is not used other than error reporting
  entityType : Option AddExpr
  ineq : Option (RelOp × Expr)

public structure Cond where
  cond : Ident
  expr : Option Expr

public inductive Expr where
  | expr (e : ExprImpl)

-- The `Box` data structure is dropped
public structure ExprImpl where
  expr : ExprData

public inductive ExprData where
  | edOr (expr : OrExpr)
  | edIf (i t e : Expr) -- `if` is a LEAN keyword

-- Corresponds to `Or` in cst.rs
-- `Or` has already been declared in LEAN
public structure OrExpr where
  initial : AndExpr
  extended : List AndExpr

-- Same as `OrExpr`
public structure AndExpr where
  initial : Relation
  extended : List Relation

-- Do we want to formalize all of these at this stage?
public inductive Relation where
  | rCommon (initial : AddExpr) (extended : List (RelOp × AddExpr))
  | rHas (target : AddExpr) (field : AddExpr)
  | rLike (target : AddExpr) (pattern : AddExpr)
  -- | rIsIn (target : AddExpr) (entityType : AddExpr) (inEntity : Option AddExpr)
  -- A syntactic sugar for Principal is ... in ...

public structure AddExpr where
  initial : MultExpr
  extended : List (AddOp × MultExpr)

public structure MultExpr where
  initial : Unary
  extended : List (MultOp × Unary)

public structure Unary where
  op : Option NegOp
  item : Member

public structure Member where
  item : Primary
  access : List MemAccess

public inductive MemAccess where
  | field (i : Ident)
  -- | call (fs : List Expr)
  -- Function call not implemented at this stage
  | index (e : Expr)

public inductive Primary where
  | literal (l : Literal)
  | ref (r : Ref)
  | name (n : Name)
  -- | slot (s : Slot)
  -- Slots not implemented at this stage
  | expr (e : Expr)
  | eList (es : List Expr)
  -- | rInits (r : List RecInit)
  -- Constructed record not implemented at this stage

public structure Name where
  path : List Ident
  name : Ident

public inductive Ref where
  | uid (path : Name) (eid : Str)
  | ref (path : Name) (rinits : List RefInit)

public structure RefInit where
  id : Ident
  lit : Literal

end

end Cedar.Spec.Cst

namespace Cedar.Spec.CstCommon

public def Member.toLit? (e : Cst.Member) : Option Cst.Literal :=
  if !e.access.isEmpty then none else
  match e.item with
  | .literal l => some l
  | _ => none

-- TODO: Review this function, written by Claude

public def hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

public def toPatternAux (input : List Char) : Option Pattern :=
  match input with
  | [] => some []
  | '\\' :: '*'  :: cs => do let tail ← toPatternAux cs; some (.justChar '*' :: tail)
  | '\\' :: '\\' :: cs => do let tail ← toPatternAux cs; some (.justChar '\\' :: tail)
  | '\\' :: 'n'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\n' :: tail)
  | '\\' :: 'r'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\r' :: tail)
  | '\\' :: 't'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\t' :: tail)
  | '\\' :: '0'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\x00' :: tail)
  | '\\' :: '"'  :: cs => do let tail ← toPatternAux cs; some (.justChar '"' :: tail)
  | '\\' :: '\'' :: cs => do let tail ← toPatternAux cs; some (.justChar '\'' :: tail)
  | '\\' :: 'u'  :: '{' :: cs =>
    let digits := cs.takeWhile (· ≠ '}')
    let afterBrace := cs.drop digits.length
    match h : afterBrace with
    | '}' :: remaining => do
      if digits.isEmpty ∨ digits.length > 6 then none else do
      let codepoint ← digits.foldlM (fun acc d => do
        let v ← hexDigitToNat? d
        some (acc * 16 + v)) 0
      if codepoint > 0x10FFFF then none
      let tail ← toPatternAux remaining
      some (.justChar (Char.ofNat codepoint) :: tail)
    | _ => none
  | '\\' :: _ => none
  | '*' :: cs => do let tail ← toPatternAux cs; some (.star :: tail)
  | c :: cs => do let tail ← toPatternAux cs; some (.justChar c :: tail)
termination_by input.length
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  · have h1 : digits.length ≤ cs.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    have h2 : afterBrace.length = cs.length - digits.length := by
      simp [afterBrace, List.length_drop]
    have h3 : remaining.length + 1 = afterBrace.length := by
      simp [h]
    omega

public def toPattern? (s : String) : Option Pattern :=
  toPatternAux s.toList

public def unescapeAux (input : List Char) : Option (List Char) :=
  match input with
  | [] => some []
  | '\\' :: 'n'  :: cs => do let tail ← unescapeAux cs; some ('\n' :: tail)
  | '\\' :: 'r'  :: cs => do let tail ← unescapeAux cs; some ('\r' :: tail)
  | '\\' :: 't'  :: cs => do let tail ← unescapeAux cs; some ('\t' :: tail)
  | '\\' :: '0'  :: cs => do let tail ← unescapeAux cs; some ('\x00' :: tail)
  | '\\' :: '\\' :: cs => do let tail ← unescapeAux cs; some ('\\' :: tail)
  | '\\' :: '"'  :: cs => do let tail ← unescapeAux cs; some ('"' :: tail)
  | '\\' :: '\'' :: cs => do let tail ← unescapeAux cs; some ('\'' :: tail)
  | '\\' :: 'u'  :: '{' :: cs =>
    let digits := cs.takeWhile (· ≠ '}')
    let afterBrace := cs.drop digits.length
    match h : afterBrace with
    | '}' :: remaining => do
      if digits.isEmpty ∨ digits.length > 6 then none else do
      let codepoint ← digits.foldlM (fun acc d => do
        let v ← hexDigitToNat? d
        some (acc * 16 + v)) 0
      if codepoint > 0x10FFFF then none
      let tail ← unescapeAux remaining
      some (Char.ofNat codepoint :: tail)
    | _ => none
  | '\\' :: _ => none
  | c :: cs => do
    let tail ← unescapeAux cs
    some (c :: tail)
termination_by input.length
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  · have h1 : digits.length ≤ cs.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    have h2 : afterBrace.length = cs.length - digits.length := by
      simp [afterBrace, List.length_drop]
    have h3 : remaining.length + 1 = afterBrace.length := by
      simp [h]
    omega

public def unescape? (s : String) : Option String := do
  let chars ← unescapeAux s.toList
  some (String.ofList chars)

public def Ident.toString : Cst.Ident → String
  | .idPrincipal => "principal"
  | .idAction => "action"
  | .idResource => "resource"
  | .idContext => "context"
  | .idTrue => "true"
  | .idFalse => "false"
  | .idPermit => "permit"
  | .idForbid => "forbid"
  | .idWhen => "when"
  | .idUnless => "unless"
  | .idIn => "in"
  | .idHas => "has"
  | .idLike => "like"
  | .idIs => "is"
  | .idIf => "if"
  | .idThen => "then"
  | .idElse => "else"
  | .idIdent s => s

public def Unreserved? (s : String) : Bool :=
  match s with
  | "principal" => false
  | "action" => false
  | "resource" => false
  | "context" => false
  | "true" => false
  | "false" => false
  | "permit" => false
  | "forbid" => false
  | "when" => false
  | "unless" => false
  | "in" => false
  | "has" => false
  | "like" => false
  | "is" => false
  | "if" => false
  | "then" => false
  | "else" => false
  | "__cedar" => false
  | _ => true

public def Ident.toUnreservedString? : Cst.Ident → Option String
  | .idIdent s => if (Unreserved? s) then some s else none
  | _ => none

public def Expr.toStringLiteral? : Cst.Expr → Option String
  | .expr e => match e.expr with
    | .edIf _ _ _ => none
    | .edOr e => match e.initial.initial with
      | .rHas _ _ => none
      | .rLike _ _ => none
      | .rCommon i _ => match i.initial.initial.item.item with
        | .literal l => match l with
          | .liStr s => some s
          | _ => none
        | _ => none

public def Expr.toUnescapedStringLiteral? (e : Cst.Expr) : Option String := do
  let s ← Expr.toStringLiteral? e
  unescape? s

end Cedar.Spec.CstCommon

module

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

-- Should the type of n match the Rust implementation (i.e. UInt64)?
-- Why are true and false in both Ident and Literal?
public inductive Literal where
  | liTrue
  | liFalse
  | liNum (n : Int)
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
  | nBang (n : Int)
  | nOverBang
  | nDash (n : Int)
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
  op : NegOp
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

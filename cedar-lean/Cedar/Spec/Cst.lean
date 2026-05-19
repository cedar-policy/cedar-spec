module

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
  | roLess
  | roLessEq
  | roGreaterEq
  | roGreater
  | roNotEq
  | roEq
  | roIn

public inductive AddOp where
  | aoPlus
  | aoMinus

public inductive MultOp where
  | moTimes
  | moDivide
  | moMod

-- Should the type of n match the Rust implementation (i.e. UInt8),
-- or can I use Int for simplicity?
-- Are overBang and overDash for error cases?
public inductive NegOp where
  | noBang (n : Int)
  | noOverBang
  | noDash (n : Int)
  | noOverDash

-- I tried to not use the mutual block, but there are circular definitions
-- (e.g. Expr -> ExprData ->(If) Expr )
-- `inductive` is still used for single-constructor definitions that defined
-- using enum in cst.rs so that it is easier to add constructores in the future

mutual

-- There is no correspondence of Rust's `SmolStr` in LEAN
public inductive Str where
  | string (s : String)

public structure Policies where
  ps : List Policy

public inductive Policy where
  | policy (p : PolicyImpl)

public structure PolicyImpl where
  effect : Ident
  vars : List VariableDef
  conds : Cond

-- `variable` is a LEAN keyword
public structure VariableDef where
  var : Ident
  typeName : Name
  entityType : AddExpr
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
  | rIsIn (target : AddExpr) (entityType : AddExpr) (inEntity : Option AddExpr)

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
  -- | ref (r : Ref)
  -- Is this for record references?
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

end

end Cedar.Spec.Cst

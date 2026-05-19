module

public inductive Ident where
  | principal
  | action
  | resource
  | context
  | true_   -- `true` is a LEAN keyword
  | false_  -- `false` is a LEAN keyword
  | permit
  | forbid
  | when
  | unless
  | in_    -- `in` is a LEAN keyword
  | has
  | like
  | is
  | if_     -- `if` is a LEAN keyword
  | then_   -- `then` is a LEAN keyword
  | else_   -- `else` is a LEAN keyword

-- Should the type of n match the Rust implementation (i.e. UInt64)?
-- Why are true and false in both Ident and Literal?
public inductive Literal where
  | true_
  | false_
  | num (n : Int)
  | str (s : String)

public inductive RelOp where
  | less
  | lessEq
  | greaterEq
  | greater
  | notEq
  | eq
  | in_ -- `in` is a LEAN keyword

public inductive AddOp where
  | plus
  | minus

public inductive MultOp where
  | times
  | divide
  | mod

-- Should the type of n match the Rust implementation (i.e. UInt8),
-- or can I use Int for simplicity?
-- Are overBang and overDash for error cases?
public inductive NegOp where
  | bang (n : Int)
  | overBang
  | dash (n : Int)
  | overDash

-- I tried to not use the mutual block, but there are circular definitions
-- (e.g. Expr -> ExprData ->(If) Expr )
-- `inductive` is still used for single-constructor definitions so that
-- it is easier to add constructores in the future (e.g. for allowing errors)

mutual

-- There is no correspondence of Rust's `SmolStr` in LEAN
public inductive Str where
  | string (s : String)

public inductive Policies where
  | policies (ps : List Policy)

public inductive Policy where
  | policy (p : PolicyImpl)

public inductive PolicyImpl where
  | policyImpl (effect : Ident) (vars : List VariableDef) (conds : Cond)

-- `variable` is a LEAN keyword
public inductive VariableDef where
  | variableDef (var : Ident) (typeName : Name) (entityType : AddExpr) (ineq : Option (RelOp × Expr))

public inductive Cond where
  | cond (cond : Ident) (expr : Option Expr)

public inductive Expr where
  | expr (e : ExprImpl)

-- The `Box` data structure is dropped
public inductive ExprImpl where
  | exprImpl (expr : ExprData)

public inductive ExprData where
  | or (expr : OrExpr)
  | if_ (i t e : Expr) -- `if` is a LEAN keyword

-- Corresponds to `Or` in cst.rs
-- `Or` has already been declared in LEAN
public inductive OrExpr where
  | orExpr (initial : AndExpr) (extended : List AndExpr)

-- Same as `OrExpr`
public inductive AndExpr where
  | andExpr (initial : Relation) (extended : List Relation)

-- Do we want to formalize all of these at this stage?
public inductive Relation where
  | common (initial : AddExpr) (extended : List (RelOp × AddExpr))
  | has (target : AddExpr) (field : AddExpr)
  | like (target : AddExpr) (pattern : AddExpr)
  | isIn (target : AddExpr) (entityType : AddExpr) (inEntity : Option AddExpr)

public inductive AddExpr where
  | addExpr (initial : MultExpr) (extended : List (AddOp × MultExpr))

public inductive MultExpr where
  | multExpr (initial : Unary) (extended : List (MultOp × Unary))

public inductive Unary where
  | unary (op : NegOp) (item : Member)

public inductive Member where
  | member (item : Primary) (access : List MemAccess)

public inductive MemAccess where
  | field (i : Ident)
  -- | call (fs : List Expr) Function call not implemented at this stage
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

public inductive Name where
  | name (path : List Ident) (name : Ident)

end

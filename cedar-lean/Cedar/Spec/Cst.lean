module

public import Cedar.Spec.Policy
public import Cedar.Spec.Wildcard

@[expose] public section

namespace Cedar.Spec.Cst

-- The CST follows the Cedar grammar defined in grammar.lalrpop:
--
--   Policies    := {Policy}
--   Policy      := {Annotation} Ident '(' [VariableDef {',' VariableDef}] ')' {Cond} ';'
--   Annotation  := '@' Ident ['(' Str ')']
--   VariableDef := Ident [':' Name] ['is' Add] [RelOp Expr]
--   Cond        := Ident '{' Expr '}'
--   Expr        := Or | 'if' Expr 'then' Expr 'else' Expr
--   Or          := And {'||' And}
--   And         := Relation {'&&' Relation}
--   Relation    := Add {RelOp Add} | Add 'has' Add | Add 'like' Add | Add 'is' Add ['in' Add]
--   RelOp       := '<' | '<=' | '>=' | '>' | '!=' | '==' | 'in'
--   Add         := Mult {('+' | '-') Mult}
--   Mult        := Unary {('*' | '/' | '%') Unary}
--   Unary       := ['!' {'!'} | '-' {'-'}] Member
--   Member      := Primary {MemAccess}
--   MemAccess   := '.' Ident | '(' [Expr {',' Expr}] ')' | '[' Expr ']'
--   Primary     := Literal | Ref | Name | Slot | '(' Expr ')' | '[' [Expr {',' Expr}] ']' | '{' [RecInit {',' RecInit}] '}'
--   Name        := Ident {'::' Ident}
--   Ref         := Name '::' (Str | '{' [RefInit {',' RefInit}] '}')
--   RefInit     := Ident ':' Literal
--   RecInit     := Expr ':' Expr
--   Literal     := 'true' | 'false' | Number | Str
--
-- Generally, the cst::* concrete syntax tree structures are represented without location
-- information in Lean. We also omit elements that are useful in Rust only for nice error reporting.

-- Identifiers of the Cedar language, including special ones
public inductive Ident where
  -- rust cst::Ident::Principal
  | idPrincipal
  -- cst::Ident::Action
  | idAction
  -- cst::Ident::Resource
  | idResource
  -- cst::Ident::Context
  | idContext
  -- cst::Ident::True
  | idTrue
  -- cst::Ident::False
  | idFalse
  -- cst::Ident::Permit
  | idPermit
  -- cst::Ident::Forbid
  | idForbid
  -- cst::Ident::When
  | idWhen
  -- cst::Ident::Unless
  | idUnless
  -- cst::Ident::In
  | idIn
  -- cst::Ident::Has
  | idHas
  -- cst::Ident::Like
  | idLike
  -- cst::Ident::Is
  | idIs
  -- cst::Ident::If
  | idIf
  -- cst::Ident::Then
  | idThen
  -- cst::Ident::Else
  | idElse
  -- cst::Ident::Ident(SmoltStr)
  | idIdent (s : String)
  -- Note: the cst::Ident::Invalid(String) is not represented in Lean

-- This is a cst::Literal in Rust.
-- Should the type of n match the Rust implementation (i.e. UInt64)?
-- Why are true and false in both Ident and Literal?
public inductive Literal where
  -- cst::Literal::True
  | liTrue
  -- cst::Literal::False
  | liFalse
  -- cst::Literal::Num(u64)
  | liNum (n : UInt64)
  -- cst::Literal::String(Node<Str>)
  | liStr (s : String)

-- This is a cst::RelOp
public inductive RelOp where
  -- cst::RelOp::Less
  | rLess
  -- cst::RelOp::LessEq
  | rLessEq
  -- cst::RelOp::GreaterEq
  | rGreaterEq
  -- cst::RelOp::Greater
  | rGreater
  -- cst::RelOp::NotEq
  | rNotEq
  -- cst::RelOp::Eq
  | rEq
  -- cst::RelOp::In
  | rIn
  -- cst::InvalidSingleEq is not represented in Lean

-- This is a cst::AddOp
public inductive AddOp where
  -- cst::AddOp::Plus
  | aPlus
  -- cst::AddOp::Minus
  | aMinus

-- This is a cst::MultOp
public inductive MultOp where
  -- cst::MultOp::Times
  | mTimes
  -- cst::MultOp::Divide
  | mDivide
  -- cst::MultOp::Mod
  | mMod

-- This matches the cst::NegOp where operators are counted with `u8` in Rust, `UInt8` in Lean
public inductive NegOp where
  -- cst::NegOp::Bang(u8)
  | nBang (n : UInt8)
  -- cst::NegOp::Dash(u8)
  | nDash (n : UInt8)
  | nOverBang
  | nOverDash
  -- cst::NegOp::OverBand and cst::NegOp::OverDash are not represented in Lean, they are used
  -- to return nice errors

-- `inductive` is still used for single-constructor definitions that
-- are defined using enum in cst.rs so that it is easier to add
-- constructors in the future

mutual

-- This is a cst::Str
-- There is no correspondence of Rust's `SmolStr` in LEAN
public inductive Str where
  -- cst::Str::String(SmolStr)
  | string (s : String)
  -- Note: cst::Str::Invalid(SmolStr) is not represented in Lean

-- This is a cst::Policies
public structure Policies where
  ps : List Policy

-- This is a cst::Policy
public inductive Policy where
  -- cst::Policy::Policy(PolicyImpl)
  | policy (p : PolicyImpl)
  -- Note: cst::Policy::PolicyError (tolerant-ast feature) is not represented in Lean

-- This is a cst::PolicyImpl
public structure PolicyImpl where
  -- annotations : List Annotation
  -- cst::PolicyImpl::annotations not formalized at this stage
  effect : Ident
  vars : List VariableDef
  conds : List Cond
  id : String

-- This is a cst::VariableDef
-- `variable` is a LEAN keyword
public structure VariableDef where
  -- cst::VariableDef::variable
  var : Ident
  -- cst::VariableDef::unused_type_name is not represented, only used for error reporting
  -- cst::VariableDef::entity_type
  entityType : Option AddExpr
  -- cst::VariableDef::ineq
  ineq : Option (RelOp × Expr)

public structure Cond where
  cond : Ident
  expr : Option Expr

-- This is a cst::Expr
public inductive Expr where
  -- cst::Expr::Expr(ExprImpl)
  | expr (e : ExprImpl)
  -- Note: cst::Expr::ErrorExpr (tolerant-ast feature) is not represented in Lean

-- This is a cst::ExprImpl
-- The `Box` data structure is dropped
public structure ExprImpl where
  expr : ExprData

-- This is a cst::ExprData
public inductive ExprData where
  -- cst::ExprData::Or(Node<Or>)
  | edOr (expr : OrExpr)
  -- cst::ExprData::If(Node<Expr>, Node<Expr>, Node<Expr>)
  | edIf (i t e : Expr) -- `if` is a LEAN keyword

-- This is a cst::Or
-- `Or` has already been declared in LEAN
public structure OrExpr where
  initial : AndExpr
  extended : List AndExpr

-- This is a cst::And
public structure AndExpr where
  initial : Relation
  extended : List Relation

-- This is a cst::Relation
public inductive Relation where
  -- cst::Relation::Common { initial, extended }
  | rCommon (initial : AddExpr) (extended : List (RelOp × AddExpr))
  -- cst::Relation::Has { target, field }
  | rHas (target : AddExpr) (field : AddExpr)
  -- cst::Relation::Like { target, pattern }
  | rLike (target : AddExpr) (pattern : AddExpr)
  -- cst::Relation::IsIn { target, entity_type, in_entity }
  | rIsIn (target : AddExpr) (entityType : AddExpr) (inEntity : Option AddExpr)

-- This is a cst::Add
public structure AddExpr where
  initial : MultExpr
  extended : List (AddOp × MultExpr)

-- This is a cst::Mult
public structure MultExpr where
  initial : Unary
  extended : List (MultOp × Unary)

-- This is a cst::Unary
public structure Unary where
  op : Option NegOp
  item : Member

-- This is a cst::Member
public structure Member where
  item : Primary
  access : List MemAccess

-- This is a cst::MemAccess
public inductive MemAccess where
  -- cst::MemAccess::Field(Node<Ident>)
  | field (i : Ident)
  -- cst::MemAccess::Call(Vec<Node<Expr>>) is not represented in Lean
  -- Supporting function calls will require thinking about extension functions
  | call (fs : List Expr)
  -- cst::MemAccess::Index(Node<Expr>)
  | index (e : Expr)

-- This is a cst::Primary
public inductive Primary where
  -- cst::Primary::Literal(Node<Literal>)
  | literal (l : Literal)
  -- cst::Primary::Ref(Node<Ref>)
  | ref (r : Ref)
  -- cst::Primary::Name(Node<Name>)
  | name (n : Name)
  -- cst::Primary::Slot(Node<Slot>) is not represented in Lean (support will be added later)
  -- | slot (s : Slot)
  -- cst::Primary::Expr(Node<Expr>)
  | expr (e : Expr)
  -- cst::Primary::EList(Vec<Node<Expr>>)
  | eList (es : List Expr)
  -- cst::Primary::RInits(Vec<Node<RecInit>>) is not represented in Lean (support will be added later)
  | rInits (r : List RecInit)

-- This is a cst::Name
public structure Name where
  path : List Ident
  name : Ident

-- This is a cst::Ref
public inductive Ref where
  -- cst::Ref::Uid { path, eid }
  | uid (path : Name) (eid : Str)
  -- cst::Ref::Ref { path, rinits }
  | ref (path : Name) (rinits : List RefInit)

-- This is a cst::RefInit(Node<Ident>, Node<Literal>)
public structure RefInit where
  id : Ident
  lit : Literal

public structure RecInit where
  key : Expr
  value : Expr

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

public def Ident.toEffect? : Cst.Ident → Option Effect
  | .idPermit => some .permit
  | .idForbid => some .forbid
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
      | .rIsIn _ _ _ => none

public def Expr.toUnescapedStringLiteral? (e : Cst.Expr) : Option String := do
  let s ← Expr.toStringLiteral? e
  unescape? s

public def String.isFunctionName? : String → Bool
  | "decimal"             ----- Decimal functions -----
  | "lessThan"
  | "lessThanOrEqual"
  | "greaterThan"
  | "greaterThanOrEqual"
  | "ip"                  ----- IpAddr functions -----
  | "isIpv4"
  | "isIpv6"
  | "isLoopback"
  | "isMulticast"
  | "isInRange"
  | "datetime"           ----- Datetime functions -----
  | "duration"
  | "offset"
  | "durationSince"
  | "toDate"
  | "toTime"
  | "toMilliseconds"
  | "toSeconds"
  | "toMinutes"
  | "toHours"
  | "toDays" => true
  | _ => false

public def String.toExtFun? : String → Option ExtFun
  | "decimal" => some .decimal
  | "lessThan" => some .lessThan
  | "lessThanOrEqual" => some .lessThanOrEqual
  | "greaterThan" => some .greaterThan
  | "greaterThanOrEqual" => some .greaterThanOrEqual
  | "ip" => some .ip
  | "isIpv4" => some .isIpv4
  | "isIpv6" => some .isIpv6
  | "isLoopback" => some .isLoopback
  | "isMulticast" => some .isMulticast
  | "isInRange" => some .isInRange
  | "datetime" => some .datetime
  | "duration" => some .duration
  | "offset" => some .offset
  | "durationSince" => some .durationSince
  | "toDate" => some .toDate
  | "toTime" => some .toTime
  | "toMilliseconds" => some .toMilliseconds
  | "toSeconds" => some .toSeconds
  | "toMinutes" => some .toMinutes
  | "toHours" => some .toHours
  | "toDays" => some .toDays
  | _ => none

public def String.isMethodName? : String → Bool
  | "contains"
  | "containsAll"
  | "containsAny"
  | "isEmpty"
  | "getTag"
  | "hasTag" => true
  | _ => false

public def String.toMethodOp? : String → Option (BinaryOp ⊕ UnaryOp)
  | "contains" => some (.inl .contains)
  | "containsAll" => some (.inl .containsAll)
  | "containsAny" => some (.inl .containsAny)
  | "getTag" => some (.inl .getTag)
  | "hasTag" => some (.inl .hasTag)
  | "isEmpty" => some (.inr .isEmpty)
  | _ => none



end Cedar.Spec.CstCommon

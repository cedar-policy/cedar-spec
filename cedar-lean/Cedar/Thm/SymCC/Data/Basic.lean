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

import Cedar.Spec
import Cedar.SymCC
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set
import Cedar.Thm.Data.Map
import Cedar.Thm.SymCC.Data.BitVec

/-!

# Well-formedness and interpretations

This file defines well-formedness constraints and relations on concrete and
symbolic structures. We prove correctness properties of the symbolic compiler
with respect to these defintions.

Well-formedness of a concrete structure is defined with respect to a set of
concrete entities `es : Entities`.  A `Value`, `Request`, or `EntityData`
structure is well-formed with respect to `es` if it references only entity UIDs
that are in the _domain_ of `es`; i.e., if the structure references a `uid`,
then `uid ∈ es`. The set `es` is well-formed if it consists of well-formed
`EntityData` structures, which amounts to saying that there are no dangling
references in the entities set `es`. Finally, an environment `Env` consisting of
a request `req` and entities `es` is _well-formed for_ an expression `x` if `es`
is well-formed, `req` is well-formed with respect to `es`, and `es` supports
`x`. We say that `es` _supports_ `x` if all entity UIDs referenced by `x` are in
the domain of `es`. If `env` is well-formed for `x`, then evaluating `x` against
`env` cannot result in an `entityDoesNotExist` error.

Well-formed symbolic structures are defined analagously to well-formed concrete
structures. In particular, well-formedness of a symbolic structure is defined
with respect to a set of symbolic entity declarations `εs : SymEntities`. A
`Term`, `SymRequest`, or `SymEntityData` structure is well-formed with respect
to `εs` if it references only entity types and UIDs that are in the _domain_ of
`εs`, and if all referenced term types represent valid Cedar types. An entity
type `ety` is in the domain of `εs` if `ety ∈ εs`, and entity UID `uid` is in
the domain of `εs` if `εs.isValidEntityUID uid`.  The set `εs` is well-formed if
it consists of well-formed `SymEntityData` structures. A symbolic environment
`SymEnv` consisting of a symbolic request `ρeq` and entities `εs` is
_well-formed for_ an expression `x` if `εs` is well-formed, `ρeq` is well-formed
with respect to `εs`, and `εs` _supports_ `x`.  We say that `εs` supports `x` if
`εs.isValidEntityUID uid` for every entity `uid` referenced by `x`.

A well-formed symbolic structure represents a _set_ of well-formed symbolic
_literal_ structures, which, in turn, represent corresponding well-formed Cedar
structures. A _literal_ symbolic structure contains no term variables or
uninterpreted functions. Symbolic structures are related to literals through
_interpretations_. An `Interpretation` binds term variables to literal terms and
uninterpreted functions (`UUF`) to interpreted ones (`UDF`). When a well-formed
symbolic structure is interpreted with respect to a well-formed Interpretation,
the result is a well-formed literal symbolic structure. Interpreting a literal
against any Interpretation returns the same literal.

A literal term or symbolic request represent a single corresponding Cedar
structure (i.e., a `Value`, `Outcome Value`, or `Request`). A well-formed
literal symbolic environment `εnv : SymEnv` represents a set of well-formed
concrete environments that lead to equivalent evaluation outcomes. In
particular, if `εnv` is a literal symbolic environment that is well-formed for
an expression `x`, then `x` produces the same outcome when evaluated against any
concrete environment `env ∈ εnv` that is well-formed for `x`. We write `env ∈ εnv`
to denote that exists a well-formed interpretation `I` such that
`εnv.interpret I` is a literal that represents `env`.
-/

namespace Cedar.Spec

open Data

------ Well-formed concrete structures ------

def Prim.WellFormed (es : Entities) : Prim → Prop
  | .entityUID uid => es.contains uid
  | _              => true

inductive Value.WellFormed (es : Entities) : Value → Prop
  | prim_wf {p : Prim}
    (h₁ : p.WellFormed es) :
    WellFormed es (.prim p)
  | set_wf {s : Set Value}
    (h₁ : ∀ v, v ∈ s → v.WellFormed es)
    (h₂ : s.WellFormed) :
    WellFormed es (.set s)
  | record_wf {r : Map Attr Value}
    (h₁ : ∀ a v, r.find? a = some v → v.WellFormed es)
    (h₂ : r.WellFormed) :
    WellFormed es (.record r)
  | ext_wf {xv : Ext} :
    WellFormed es (.ext xv)

def Request.WellFormed (es : Entities) (req : Request) : Prop :=
  es.contains req.principal ∧
  es.contains req.action ∧
  es.contains req.resource ∧
  (Value.record req.context).WellFormed es

def EntityData.WellFormed (es : Entities) (d : EntityData) : Prop :=
  (Value.record d.attrs).WellFormed es ∧
  d.ancestors.WellFormed ∧
  (∀ uid, uid ∈ d.ancestors → es.contains uid) ∧
  d.tags.WellFormed ∧
  (∀ t v, d.tags.find? t = some v → v.WellFormed es)

def Entities.WellFormed (es : Entities) : Prop :=
  Map.WellFormed es ∧
  ∀ uid d, es.find? uid = .some d → d.WellFormed es

def Prim.ValidRef (validRef : EntityUID → Prop) : Prim → Prop
  | .entityUID uid => validRef uid
  | _              => True

inductive Expr.ValidRefs (validRef : EntityUID → Prop) : Expr → Prop
  | lit_valid {p : Prim}
    (h₁ : p.ValidRef validRef) :
    ValidRefs validRef (.lit p)
  | var_valid {v : Var} :
    ValidRefs validRef (.var v)
  | ite_valid {x₁ x₂ x₃ : Expr}
    (h₁ : ValidRefs validRef x₁)
    (h₂ : ValidRefs validRef x₂)
    (h₃ : ValidRefs validRef x₃) :
    ValidRefs validRef (.ite x₁ x₂ x₃)
  | and_valid {x₁ x₂ : Expr}
    (h₁ : ValidRefs validRef x₁)
    (h₂ : ValidRefs validRef x₂) :
    ValidRefs validRef (.and x₁ x₂)
  | or_valid {x₁ x₂ : Expr}
    (h₁ : ValidRefs validRef x₁)
    (h₂ : ValidRefs validRef x₂) :
    ValidRefs validRef (.or x₁ x₂)
  | binaryApp_valid {op₂ : BinaryOp} {x₁ x₂ : Expr}
    (h₁ : ValidRefs validRef x₁)
    (h₂ : ValidRefs validRef x₂) :
    ValidRefs validRef (.binaryApp op₂ x₁ x₂)
  | unaryApp_valid {op₁ : UnaryOp} {x₁ : Expr}
    (h₁ : ValidRefs validRef x₁) :
    ValidRefs validRef (.unaryApp op₁ x₁)
  | hasAttr_valid {x₁ : Expr} {a : Attr}
    (h₁ : ValidRefs validRef x₁) :
    ValidRefs validRef (.hasAttr x₁ a)
  | getAttr_valid {x₁ : Expr} {a : Attr}
    (h₁ : ValidRefs validRef x₁) :
    ValidRefs validRef (.getAttr x₁ a)
  | set_valid {xs : List Expr}
    (h₁ : ∀ x ∈ xs, ValidRefs validRef x) :
    ValidRefs validRef (.set xs)
  | record_valid {axs : List (Attr × Expr)}
    (h₁ : ∀ ax ∈ axs, ValidRefs validRef ax.snd) :
    ValidRefs validRef (.record axs)
  | call_valid {xfn : ExtFun} {xs : List Expr}
    (h₁ : ∀ x ∈ xs, ValidRefs validRef x) :
    ValidRefs validRef (.call xfn xs)

def Env.WellFormed (env : Env) : Prop :=
  env.request.WellFormed env.entities ∧
  env.entities.WellFormed

abbrev Entities.ValidRefsFor (es : Entities) (x : Expr) : Prop :=
  x.ValidRefs (λ uid => es.contains uid)

def Env.WellFormedFor (env : Env) (x : Expr) : Prop :=
  env.WellFormed ∧ env.entities.ValidRefsFor x

def Env.WellFormedForPolicies (env : Env) (ps : Policies) : Prop :=
  env.WellFormed ∧ ∀ p ∈ ps, env.entities.ValidRefsFor p.toExpr

------ Well-structured values ------

inductive Value.WellStructured : Value → Prop
  | prim_ws {p : Prim} :
    WellStructured (.prim p)
  | set_ws {s : Set Value}
    (h₁ : ∀ v, v ∈ s → v.WellStructured)
    (h₂ : s.WellFormed) :
    WellStructured (.set s)
  | record_ws {r : Map Attr Value}
    (h₁ : ∀ a v, r.find? a = some v → v.WellStructured)
    (h₂ : r.WellFormed) :
    WellStructured (.record r)
  | ext_ws {xv : Ext} :
    WellStructured (.ext xv)

def Entities.ClosedFor (es : Entities) (uids : Set EntityUID) : Prop :=
  ∀ uid ∈ uids, es.contains uid

------ Utilites ------

abbrev Outcome (α) := Except Unit α

def SameOutcomes (res : Result Value) (out : Outcome Value) : Prop :=
  match res, out with
  | .ok v₁,   .ok v₂    => v₁ = v₂
  | .error e, .error () => e ≠ .entityDoesNotExist
  | _, _                => False

def SameDecisions (resp : Response) (dec : Decision) : Prop :=
  resp.decision = dec

/--
The notation typeclass for the heterogenous sameness (equivalence) relation.
This enables the notation `a ∼ b : Prop` where `a : α`, `b : β`.
-/
class Same (α : Type u) (β : Type v) where
  /-- `a ∼ b` relates `a` and `b`. The meaning of this notation is type-dependent. -/
  same : α → β → Prop


infix:100 " ∼ " => Same.same

instance : Same (Result Value) (Outcome Value) where
  same := SameOutcomes

instance : Same Response Decision where
  same := SameDecisions

end Cedar.Spec

namespace Cedar.SymCC

open Data Factory Spec Validation

------ Well-formed (literal) symbolic structures ------

def TermType.cedarType? : TermType → Option CedarType
  | .bool             => .some (.bool .anyBool)
  | .bitvec 64        => .some .int
  | .string           => .some .string
  | .entity ety       => .some (.entity ety)
  | .set ty           => do .some (.set (← ty.cedarType?))
  | .record (.mk rty) => do
    let crty ← rty.mapM₃ λ ⟨(aᵢ, tyᵢ), _⟩ => do .some (aᵢ, ← qualifiedType? tyᵢ)
    .some (.record (Map.mk crty))
  | .ext xty          => .some (.ext xty)
  | _                 => .none
where
  qualifiedType? : TermType → Option QualifiedType
    | .option ty => do Qualified.optional (← ty.cedarType?)
    | ty         => do Qualified.required (← ty.cedarType?)

def TermType.isCedarRecordType (ty : TermType) : Bool :=
  match ty.cedarType? with
  | .some (.record _) => true
  | _                 => false

def TermType.isCedarType (ty : TermType) : Bool :=
  ty.cedarType?.isSome

inductive TermType.WellFormed (εs : SymEntities) : TermType → Prop
  | bool_wf :
    WellFormed εs .bool
  | bitvec_wf {n : Nat} :
    WellFormed εs (.bitvec n)
  | string_wf :
    WellFormed εs .string
  | option_wf {ty : TermType}
    (h₁ : WellFormed εs ty) :
    WellFormed εs (.option ty)
  | entity_wf {ety : EntityType}
    (h₁ : εs.isValidEntityType ety) :
    WellFormed εs (.entity ety)
  | set_wf {ty : TermType}
    (h₁ : WellFormed εs ty) :
    WellFormed εs (.set ty)
  | record_wf {rty : Map Attr TermType}
    (h₁ : ∀ a ty, rty.find? a = some ty → WellFormed εs ty)
    (h₂ : rty.WellFormed):
    WellFormed εs (.record rty)
  | ext_wf {xty : ExtType} :
    WellFormed εs (.ext xty)

inductive TermPrim.WellFormed (εs : SymEntities) : TermPrim → Prop
  | bool_wf {b : Bool} :
    WellFormed εs (.bool b)
  | bitvec_wf {n : Nat} {bv : BitVec n} :
    WellFormed εs (.bitvec bv)
  | string_wf {s : String} :
    WellFormed εs (.string s)
  | entity_wf {uid : EntityUID}
    (h₁ : εs.isValidEntityUID uid) :
    WellFormed εs (.entity uid)
  | ext_wf {x : Ext} :
    WellFormed εs (.ext x)

def TermVar.WellFormed (εs : SymEntities) (v : TermVar) : Prop :=
  v.ty.WellFormed εs

inductive ExtOp.WellTyped : ExtOp → List Term → TermType → Prop
  | decimal.val_wt {t : Term}
    (h₁ : t.typeOf = (.ext .decimal)) :
    WellTyped .decimal.val [t] (.bitvec 64)
  | ipaddr.isV4_wt {t : Term}
    (h₁ : t.typeOf = (.ext .ipAddr)) :
    WellTyped ipaddr.isV4 [t] .bool
  | ipaddr.addrV4_wt {t : Term}
    (h₁ : t.typeOf = (.ext .ipAddr)) :
    WellTyped ipaddr.addrV4 [t] (.bitvec 32)
  | ipaddr.prefixV4_wt {t : Term}
    (h₁ : t.typeOf = (.ext .ipAddr)) :
    WellTyped ipaddr.prefixV4 [t] (.option (.bitvec 5))
  | ipaddr.addrV6_wt {t : Term}
    (h₁ : t.typeOf = (.ext .ipAddr)) :
    WellTyped ipaddr.addrV6 [t] (.bitvec 128)
  | ipaddr.prefixV6_wt {t : Term}
    (h₁ : t.typeOf = (.ext .ipAddr)) :
    WellTyped ipaddr.prefixV6 [t] (.option (.bitvec 7))
  | datetime.val_wt {t : Term}
    (h₁ : t.typeOf = (.ext .datetime)) :
    WellTyped datetime.val [t] (.bitvec 64)
  | datetime.ofBitVec_wt {t : Term}
    (h₁ : t.typeOf = (.bitvec 64)) :
    WellTyped datetime.ofBitVec [t] (.ext .datetime)
  | duration.val_wt {t : Term}
    (h₁ : t.typeOf = (.ext .duration)) :
    WellTyped duration.val [t] (.bitvec 64)
  | duration.ofBitVec_wt {t : Term}
    (h₁ : t.typeOf = (.bitvec 64)) :
    WellTyped duration.ofBitVec [t] (.ext .duration)

def UUF.WellFormed (εs : SymEntities) (f : UUF) : Prop :=
  f.arg.WellFormed εs ∧
  f.out.WellFormed εs

inductive Op.WellTyped (εs : SymEntities) : Op → List Term → TermType → Prop
  | not_wt {t : Term}
    (h₁ : t.typeOf = .bool) :
    WellTyped εs .not [t] .bool
  | and_wt {t₁ t₂ : Term}
    (h₁ : t₁.typeOf = .bool)
    (h₂ : t₂.typeOf = .bool) :
    WellTyped εs .and [t₁, t₂] .bool
  | or_wt {t₁ t₂ : Term}
    (h₁ : t₁.typeOf = .bool)
    (h₂ : t₂.typeOf = .bool) :
    WellTyped εs .or [t₁, t₂] .bool
  | eq_wt {t₁ t₂ : Term}
    (h₁ : t₁.typeOf = t₂.typeOf) :
    WellTyped εs .eq [t₁, t₂] .bool
  | ite_wt {t₁ t₂ t₃ : Term}
    (h₁ : t₁.typeOf = .bool)
    (h₂ : t₂.typeOf = t₃.typeOf) :
    WellTyped εs .ite [t₁, t₂, t₃] t₂.typeOf
  | uuf_wt {f : UUF} {t : Term}
    (h₁ : t.typeOf = f.arg)
    (h₂ : f.WellFormed εs) :
    WellTyped εs (.uuf f) [t] f.out
  | bvneg_wt {t : Term} {n : Nat}
    (h₁ : t.typeOf = .bitvec n) :
    WellTyped εs .bvneg [t] (.bitvec n)
  | bvnego_wt {t : Term} {n : Nat}
    (h₁ : t.typeOf = .bitvec n) :
    WellTyped εs .bvnego [t] .bool
  | bvadd_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvadd [t₁, t₂] (.bitvec n)
  | bvsub_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsub [t₁, t₂] (.bitvec n)
  | bvmul_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvmul [t₁, t₂] (.bitvec n)
  | bvsdiv_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsdiv [t₁, t₂] (.bitvec n)
  | bvudiv_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvudiv [t₁, t₂] (.bitvec n)
  | bvsrem_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsrem [t₁, t₂] (.bitvec n)
  | bvsmod_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsmod [t₁, t₂] (.bitvec n)
  | bvumod_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvumod [t₁, t₂] (.bitvec n)
  | bvshl_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvshl [t₁, t₂] (.bitvec n)
  | bvlshr_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvlshr [t₁, t₂] (.bitvec n)
  | bvsaddo_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsaddo [t₁, t₂] .bool
  | bvssubo_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvssubo [t₁, t₂] .bool
  | bvsmulo_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsmulo [t₁, t₂] .bool
  | bvslt_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvslt [t₁, t₂] .bool
  | bvsle_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvsle [t₁, t₂] .bool
  | bvult_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvult [t₁, t₂] .bool
  | bvule_wt {t₁ t₂ : Term} {n : Nat}
    (h₁ : t₁.typeOf = .bitvec n)
    (h₂ : t₂.typeOf = .bitvec n) :
    WellTyped εs .bvule [t₁, t₂] .bool
  | zero_extend_wt {t : Term} {n m : Nat}
    (h₁ : t.typeOf = .bitvec m) :
    WellTyped εs (.zero_extend n) [t] (.bitvec (n + m))
  | set.member_wt {t₁ t₂ : Term}
    (h₁ : t₂.typeOf = .set (t₁.typeOf)) :
    WellTyped εs .set.member [t₁, t₂] .bool
  | set.subset_wt {t₁ t₂ : Term} {ty : TermType}
    (h₁ : t₁.typeOf = .set ty)
    (h₂ : t₂.typeOf = .set ty) :
    WellTyped εs .set.subset [t₁, t₂] .bool
  | set.inter_wt {t₁ t₂ : Term} {ty : TermType}
    (h₁ : t₁.typeOf = .set ty)
    (h₂ : t₂.typeOf = .set ty) :
    WellTyped εs .set.inter [t₁, t₂] (.set ty)
  | option.get_wt {t : Term} {ty : TermType}
    (h₁ : t.typeOf = .option ty) :
    WellTyped εs .option.get [t] ty
  | record.get_wt {t : Term} {a : Attr} {ty : TermType} {rty : Map Attr TermType}
    (h₁ : t.typeOf = .record rty)
    (h₂ : rty.find? a = .some ty) :
    WellTyped εs (.record.get a) [t] ty
  | string.like_wt {t : Term} {p : Pattern}
    (h₁ : t.typeOf = .string) :
    WellTyped εs (.string.like p) [t] .bool
  | ext_wt {xop : ExtOp} {ts : List Term} {ty : TermType}
    (h₁ : xop.WellTyped ts ty) :
    WellTyped εs (.ext xop) ts ty

inductive Term.WellFormed (εs : SymEntities) : Term → Prop
  | prim_wf {p : TermPrim}
    (h₁ : p.WellFormed εs) :
    WellFormed εs (.prim p)
  | var_wf {v : TermVar}
    (h₁ : v.WellFormed εs) :
    WellFormed εs (.var v)
  | none_wf {ty : TermType}
    (h₁ : ty.WellFormed εs):
    WellFormed εs (.none ty)
  | some_wf {t : Term}
    (h₁ : t.WellFormed εs):
    WellFormed εs (.some t)
  | app_wf {op : Op} {ts : List Term} {ty : TermType}
    (h₁ : ∀ t, t ∈ ts → t.WellFormed εs)
    (h₂ : op.WellTyped εs ts ty) :
    WellFormed εs (.app op ts ty)
  | set_wf {s : Set Term} {ty : TermType}
    (h₁ : ∀ t, t ∈ s → t.WellFormed εs)
    (h₂ : ∀ t, t ∈ s → t.typeOf = ty)
    (h₃ : ty.WellFormed εs)
    (h₄ : s.WellFormed) :
    WellFormed εs (.set s ty)
  | record_wf {r : Map Attr Term}
    (h₁ : ∀ a t, (a, t) ∈ r.toList → t.WellFormed εs)
    (h₂ : r.WellFormed):
    WellFormed εs (.record r)

def Term.WellFormedLiteral (εs : SymEntities) (t : Term) : Prop :=
  t.WellFormed εs ∧ t.isLiteral

def UDF.WellFormed (εs : SymEntities) (f : UDF) : Prop :=
  f.default.WellFormedLiteral εs ∧
  f.default.typeOf = f.out ∧
  f.table.WellFormed ∧
  ∀ tᵢ tₒ, (tᵢ, tₒ) ∈ f.table.toList →
    (tᵢ.WellFormedLiteral εs ∧
     tᵢ.typeOf = f.arg ∧
     tₒ.WellFormedLiteral εs ∧
     tₒ.typeOf = f.out)

def UnaryFunction.WellFormed (εs : SymEntities) : UnaryFunction → Prop
  | .uuf f => f.WellFormed εs
  | .udf f => f.WellFormed εs

def SymRequest.WellFormed (εs : SymEntities) (req : SymRequest) : Prop :=
  req.principal.WellFormed εs ∧
  req.principal.typeOf.isEntityType ∧
  req.action.WellFormed εs ∧
  req.action.typeOf.isEntityType ∧
  req.resource.WellFormed εs ∧
  req.resource.typeOf.isEntityType ∧
  req.context.WellFormed εs ∧
  req.context.typeOf.isCedarRecordType

def SymTags.WellFormed (εs : SymEntities) (ety : EntityType) (τs : SymTags) : Prop :=
  τs.keys.WellFormed εs ∧
  τs.keys.argType = .entity ety ∧
  τs.keys.outType = .set .string ∧
  τs.vals.WellFormed εs ∧
  τs.vals.argType = TermType.tagFor ety ∧
  τs.vals.outType.isCedarType

def SymEntityData.WellFormed (εs : SymEntities) (ety : EntityType) (d : SymEntityData) : Prop :=
  d.attrs.WellFormed εs ∧
  d.attrs.argType = .entity ety ∧
  d.attrs.outType.isCedarRecordType ∧
  (∀ pty f, d.ancestors.find? pty = some f →
    (f.WellFormed εs ∧
     f.argType = .entity ety ∧
     f.outType = .set (.entity pty))) ∧
  d.ancestors.WellFormed ∧
  (∀ τs, d.tags = some τs → τs.WellFormed εs ety) ∧
  (∀ mems, d.members = some mems → ¬ mems.isEmpty)

def SymEntities.WellFormed (εs : SymEntities) : Prop :=
  Map.WellFormed εs ∧
  ∀ ety d, εs.find? ety = some d → d.WellFormed εs ety

def SymEnv.WellFormed (εnv : SymEnv) : Prop :=
  εnv.request.WellFormed εnv.entities ∧
  εnv.entities.WellFormed

abbrev SymEntities.ValidRefsFor (εs : SymEntities) (x : Expr) : Prop :=
  x.ValidRefs (εs.isValidEntityUID ·)

def SymEnv.WellFormedFor (εnv : SymEnv) (x : Expr) : Prop :=
  εnv.WellFormed ∧ εnv.entities.ValidRefsFor x

def SymEnv.WellFormedLiteralFor (εnv : SymEnv) (x : Expr) : Prop :=
  εnv.WellFormedFor x ∧ εnv.isLiteral

def SymEnv.WellFormedForPolicies (εnv : SymEnv) (ps : Policies) : Prop :=
  εnv.WellFormed ∧ ∀ p ∈ ps, εnv.entities.ValidRefsFor p.toExpr

def Asserts.WellFormed (εs : SymEntities) (asserts : Asserts) : Prop :=
  ∀ t ∈ asserts, t.WellFormed εs ∧ t.typeOf = .bool

------ Relating concrete and symbolic structures ------

def SameValues (v : Value) (t : Term) : Prop :=
  t.value? = .some v

def SameOutcomes : Outcome Value → Term → Prop
  | .ok v, .some t     => SameValues v t
  | .error _, .none _  => True
  | _, _               => False

def SameResults : Spec.Result Value → Term → Prop
  | .ok v, .some t     => SameValues v t
  | .error e, .none _  => e ≠ .entityDoesNotExist
  | _, _               => False

def SameDecisions : Spec.Decision → Term → Prop
  | .allow, .bool true
  | .deny,  .bool false => True
  | _, _                => False

def SameResponses (resp : Response) (t : Term) : Prop :=
  SameDecisions resp.decision t

def SameRequests (req : Request) (ρeq : SymRequest) : Prop :=
   ρeq.principal = .prim (.entity req.principal) ∧
   ρeq.action = .prim (.entity req.action) ∧
   ρeq.resource = .prim (.entity req.resource) ∧
   SameValues (.record req.context) ρeq.context

def SameTags (uid : EntityUID) (d : EntityData) (δ : SymEntityData) : Prop :=
  match δ.tags with
  | .none    => d.tags = Map.empty
  | .some τs =>
    (∀ tag, d.tags.find? tag = .none ↔ τs.hasTag (.entity uid) (.string tag) = false) ∧
    (∀ tag val, d.tags.find? tag = .some val →
      τs.hasTag (.entity uid) (.string tag) = true ∧
      SameValues val (τs.getTag! (.entity uid) (.string tag)))

def SameEntityData (uid : EntityUID) (d : EntityData) (δ : SymEntityData) : Prop :=
  SameValues (.record d.attrs) (app δ.attrs uid) ∧
  (∀ anc, anc ∈ d.ancestors → InSymAncestors anc) ∧
  (∀ ancTy ancUF, δ.ancestors.find? ancTy = .some ancUF → InAncestors ancUF ancTy) ∧
  (∀ mems, δ.members = .some mems → uid.eid ∈ mems) ∧
  SameTags uid d δ
where
  InSymAncestors (anc : EntityUID) : Prop :=
    ∃ ancUF,
      δ.ancestors.find? anc.ty = .some ancUF ∧
      ∃ ts, app ancUF uid = .set ts (.entity anc.ty) ∧ .prim (.entity anc) ∈ ts
  InAncestors (ancUF : UnaryFunction) (ancTy : EntityType) : Prop :=
    ∃ ts,
      app ancUF uid = .set ts (.entity ancTy) ∧
      ∀ t ∈ ts, ∃ anc, t = .prim (.entity anc) ∧ anc ∈ d.ancestors

def SameEntities (es : Entities) (εs : SymEntities) : Prop :=
  ∀ uid d,
    es.find? uid = .some d →
    ∃ δ,
      εs.find? uid.ty = .some δ ∧
      SameEntityData uid d δ

def SameEnvs (env : Env) (εnv : SymEnv) : Prop :=
  SameRequests env.request εnv.request ∧
  SameEntities env.entities εnv.entities

instance : Same (Outcome Value) Term where
  same := SameOutcomes

instance : Same (Spec.Result Value) Term where
  same := SameResults

instance : Same Value Term where
  same := SameValues

instance : Same Spec.Decision Term where
  same := SameDecisions

instance : Same Response Term where
  same := SameResponses

instance : Same Request SymRequest where
  same := SameRequests

instance : Same Entities SymEntities where
  same := SameEntities

instance : Same Env SymEnv where
  same := SameEnvs



------ Well-formed interpretations ------

inductive Term.WellFormedPartialApp (εs : SymEntities) : Term → Prop
  | none_wfp {ty : TermType}
    (h₁ : ty.WellFormed εs) :
    Term.WellFormedPartialApp εs (Term.app .option.get [.none ty] ty)
  | ext_ipddr_addr4_wfp {ip : IPAddr}
    (h₁ : ¬ ip.isV4) :
    Term.WellFormedPartialApp εs (Term.app (.ext .ipaddr.addrV4) [.prim (.ext (.ipaddr ip))] (.bitvec 32))
  | ext_ipddr_prefix4_wfp {ip : IPAddr}
    (h₁ : ¬ ip.isV4) :
    Term.WellFormedPartialApp εs (Term.app (.ext .ipaddr.prefixV4) [.prim (.ext (.ipaddr ip))] (.option (.bitvec 5)))
  | ext_ipddr_addr6_wfp {ip : IPAddr}
    (h₁ : ¬ ip.isV6) :
    Term.WellFormedPartialApp εs (Term.app (.ext .ipaddr.addrV6) [.prim (.ext (.ipaddr ip))] (.bitvec 128))
  | ext_ipddr_prefix6_wfp {ip : IPAddr}
    (h₁ : ¬ ip.isV6) :
    Term.WellFormedPartialApp εs (Term.app (.ext .ipaddr.prefixV6) [.prim (.ext (.ipaddr ip))] (.option (.bitvec 7)))

def Interpretation.WellFormed (I : Interpretation) (εs : SymEntities) : Prop :=
  (∀ v, v.WellFormed εs → WellFormedVarInterpretation v (I.vars v)) ∧
  (∀ f, f.WellFormed εs → WellFormedUUFInterpretation f (I.funs f)) ∧
  (∀ t, t.WellFormedPartialApp εs → WellFormedPartialAppInterpretation t (I.partials t))
where
  WellFormedVarInterpretation (v : TermVar) (t : Term) : Prop :=
    t.WellFormedLiteral εs ∧
    t.typeOf = v.ty
  WellFormedUUFInterpretation (uf : UUF) (df : UDF) : Prop :=
    df.WellFormed εs ∧
    uf.arg = df.arg ∧
    uf.out = df.out
  WellFormedPartialAppInterpretation (t : Term) (out : Term) : Prop :=
    out.WellFormedLiteral εs ∧
    out.typeOf = t.typeOf

def Asserts.satisfiedBy (I : Interpretation) (asserts : Asserts) : Bool :=
  asserts.all λ t => t.interpret I = true

def Asserts.Satisfiable (env : SymEnv) (asserts : Asserts) : Prop :=
  ∃ I, I.WellFormed env.entities ∧ asserts.satisfiedBy I

def Asserts.Unsatisfiable (env : SymEnv) (asserts : Asserts) : Prop :=
  ¬ asserts.Satisfiable env

infix:100 " ⊧ " => Asserts.Satisfiable
infix:100 " ⊭ " => Asserts.Unsatisfiable


------ Relating concrete structures to symbolic structures via interpretations ------

structure Term.Outcome (εnv : SymEnv) where
  term : Term
deriving Repr, DecidableEq

instance instCoeTermOutcome {εnv} : CoeOut (Term.Outcome εnv) Term where
  coe t := t.term

def memOfTermOutcome {α} {εnv} [Same α Term] (o : α) (o' : Term.Outcome εnv) : Prop :=
  ∃ I, I.WellFormed εnv.entities ∧ o ∼ (o'.term.interpret I)

infixl:50 "∈ₒ" => memOfTermOutcome

def memOfSymEnv (env : Env) (εnv : SymEnv) : Prop :=
  ∃ I, I.WellFormed εnv.entities ∧ env ∼ (εnv.interpret I)

infixl:50 "∈ᵢ" => memOfSymEnv

/--
This is a condition that `env` contains all enum entities
(including actions) specified in `εnv`. It's required for
completeness (of `SymEnv.ofEnv`) and satisfied by the
concretizer, but it's not required for the soundness, so
we keep it as a separate definition here.
-/
def Env.EnumCompleteFor (env : Env) (εnv : SymEnv) : Prop :=
  ∀ (uid : EntityUID) (δ : SymEntityData) (eids : Set String),
    εnv.entities.find? uid.ty = .some δ →
    δ.members = .some eids →
    uid.eid ∈ eids →
    ∃ data, env.entities.find? uid = .some data

end Cedar.SymCC

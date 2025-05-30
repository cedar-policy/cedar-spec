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
import Cedar.SymCC.Function

/-!
This file defines an API for construcing well-formed Terms. In this basic
implementation, the factory functions perform only basic partial
evaluation---constant folding along with a few other rewrites.  In an optimized
implementation, the factory functions would include more rewrite rules, and
share a cache of partially cannonicalized terms that have been constructed so
far.

The factory functions are total. If given well-formed and type-correct
arguments, a factory function will return a well-formed and type-correct output.
Otherwise, the output is an arbitrary term.

This design lets us minimize the number of error paths in the overall
specification of symbolic evaluation, which makes for nicer code and proofs, and
it more closely tracks the specification of the concrete evaluator.

See `Evaluator.lean` to see how the symbolic evaluator uses this API.
-/

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec

namespace Factory

---------- Term constructors ----------

def noneOf (ty : TermType) : Term := .none ty

def someOf (t : Term) : Term := .some t

def setOf (ts : List Term) (ty : TermType) : Term := .set (Set.make ts) ty

def recordOf (ats : List (Attr × Term)) : Term := .record (Map.make ats)

def tagOf (entity tag : Term) : Term := .record (EntityTag.mk entity tag)

---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------

def not : Term → Term
  | .prim (.bool b)  => ! b
  | .app .not [t'] _ => t'
  | t                => .app .not [t] .bool

def opposites : Term → Term → Bool
  | t₁, .app .not [t₂] _
  | .app .not [t₁] _, t₂ => t₁ = t₂
  | _, _                 => false

def and (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = true
  then t₁
  else if t₁ = true
  then t₂
  else if t₁ = false || t₂ = false || opposites t₁ t₂
  then false
  else .app .and [t₁, t₂] .bool

def or (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = false
  then t₁
  else if t₁ = false
  then t₂
  else if t₁ = true || t₂ = true || opposites t₁ t₂
  then true
  else .app .or [t₁, t₂] .bool

def implies (t₁ t₂ : Term) : Term :=
  or (not t₁) t₂

def eq (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .some t₁', .some t₂' => simplify t₁' t₂'
  | .some _, .none _     => false
  | .none _, .some _     => false
  | _, _                 => simplify t₁ t₂
where
  simplify (t₁ t₂ : Term) : Term :=
    if t₁ = t₂
    then true
    else if t₁.isLiteral && t₂.isLiteral
    then false
    else if t₁ = true && t₂.typeOf = .bool
    then t₂
    else if t₂ = true && t₁.typeOf = .bool
    then t₁
    else if t₁ = false && t₂.typeOf = .bool
    then not t₂
    else if t₂ = false && t₁.typeOf = .bool
    then not t₁
    else .app .eq [t₁, t₂] .bool

def ite (t₁ t₂ t₃ : Term) : Term :=
  match t₂, t₃ with
  | .some t₂', .some t₃' => .some (simplify t₂' t₃')
  | _, _                 => simplify t₂ t₃
where
  simplify (t₂ t₃ : Term) : Term :=
    if t₁ = true || t₂ = t₃
    then t₂
    else if t₁ = false
    then t₃
    else match t₂, t₃ with
    | .bool true,  .bool false => t₁
    | .bool false, .bool true  => not t₁
    | t₂,          .bool false => and t₁ t₂
    | .bool true,  t₃          => or t₁ t₃
    | t₂, t₃                   => .app .ite [t₁, t₂, t₃] t₂.typeOf

/-
Returns the result of applying a UUF or a UDF to a term. UDFs can be applied to
both literals and non-literal terms. The latter will result in the creation of a
chained `ite` expression that encodes the semantics of table lookup on an
unknown value.
-/
def app : UnaryFunction → Term → Term
  | .uuf f, t => .app (.uuf f) [t] f.out
  | .udf f, t =>
  if t.isLiteral
  then match f.table.find? t with
    | .some t' => t'
    | .none    => f.default
  else f.table.toList.foldr (λ ⟨t₁, t₂⟩ t₃ => ite (eq t t₁) t₂ t₃) f.default

---------- SMTLib theory of finite bitvectors (`BV`) ----------

-- We are doing very weak partial evaluation for bitvectors: just constant
-- propagation. If more rewrites are needed, we can add them later.  This simple
-- approach is sufficient for the strong PE property we care about:  if given a
-- fully concrete input, the symbolic evaluator returns a fully concrete output.

def bvneg : Term → Term
  | .prim (.bitvec b)  => b.neg
  | t                  => .app .bvneg [t] t.typeOf

def bvapp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → BitVec n) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] t₁.typeOf

def bvadd := bvapp .bvadd BitVec.add
def bvsub := bvapp .bvsub BitVec.sub
def bvmul := bvapp .bvmul BitVec.mul
def bvsdiv := bvapp .bvsdiv BitVec.smtSDiv
def bvudiv := bvapp .bvudiv BitVec.smtUDiv
def bvsrem := bvapp .bvsrem BitVec.srem
def bvsmod := bvapp .bvsmod BitVec.smod
def bvumod := bvapp .bvumod BitVec.umod

def bvshl  := bvapp .bvshl (λ b₁ b₂ => b₁ <<< b₂)
def bvlshr := bvapp .bvlshr (λ b₁ b₂ => b₁ >>> b₂)

def bvcmp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → Bool) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] .bool

def bvslt := bvcmp .bvslt BitVec.slt
def bvsle := bvcmp .bvsle BitVec.sle
def bvult := bvcmp .bvult BitVec.ult
def bvule := bvcmp .bvule BitVec.ule

def bvnego : Term → Term
  | .prim (@TermPrim.bitvec n b₁) => BitVec.overflows n (-b₁.toInt)
  | t                             => .app .bvnego [t] .bool

def bvso (op : Op) (fn : Int → Int → Int) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    BitVec.overflows n (fn b₁.toInt b₂.toInt)
  | _, _ => .app op [t₁, t₂] .bool

def bvsaddo := bvso .bvsaddo (· + ·)
def bvssubo := bvso .bvssubo (· - ·)
def bvsmulo := bvso .bvsmulo (· * ·)

/-
Note that BitVec defines zero_extend differently from SMTLib,
so we compensate for the difference in partial evaluation.
-/
def zero_extend (n : Nat) : Term → Term
  | .prim (@TermPrim.bitvec m b) =>
    BitVec.zeroExtend (n + m) b
  | t =>
    match t.typeOf with
    | .bitvec m => .app (.zero_extend n) [t] (.bitvec (n + m))
    | _         => t -- should be ruled out by callers


---------- CVC theory of finite sets (`FS`) ----------

def set.member (t ts : Term) : Term :=
  match ts with
  | .set (Set.mk []) _ => false
  | .set s _ =>
    if t.isLiteral && ts.isLiteral
    then s.contains t
    else .app .set.member [t, ts] .bool
  | _ => .app .set.member [t, ts] .bool

def set.subset (sub sup : Term) : Term :=
  if sub = sup
  then true
  else match sub, sup with
    | .set (Set.mk []) _, _ => true
    | .set s₁ _, .set s₂ _  =>
      if sub.isLiteral && sup.isLiteral
      then s₁.subset s₂
      else .app .set.subset [sub, sup] .bool
    | _, _ => .app .set.subset [sub, sup] .bool

def set.inter (ts₁ ts₂ : Term) : Term :=
  if ts₁ = ts₂
  then ts₁
  else match ts₁, ts₂ with
    | .set (Set.mk []) _, _ => ts₁
    | _, .set (Set.mk []) _ => ts₂
    | .set s₁ ty, .set s₂ _  =>
      if ts₁.isLiteral && ts₂.isLiteral
      then .set (s₁.intersect s₂) ty
      else .app .set.inter [ts₁, ts₂] (.set ty)
    | _, _ => .app .set.inter [ts₁, ts₂] ts₁.typeOf

def set.isEmpty : Term → Term
  | .set (Set.mk []) _     => true
  | .set (Set.mk (_::_)) _ => false
  | ts =>
    match ts.typeOf with
    | .set ty => eq ts (.set (Set.mk []) ty)
    | _       => false

def set.intersects (ts₁ ts₂ : Term) : Term :=
  not (set.isEmpty (set.inter ts₁ ts₂))

---------- Core ADT operators with a trusted mapping to SMT ----------

def option.get : Term → Term
  | .some t  => t
  | t        =>
    match t.typeOf with
    | .option ty => .app .option.get [t] ty
    | _          => t

def record.get (t : Term) (a : Attr) : Term :=
  match t with
  | .record r => if let some tₐ := r.find? a then tₐ else t
  | _         =>
    match t.typeOf with
    | .record rty => if let some ty := rty.find? a then .app (.record.get a) [t] ty else t
    | _           => t

def string.like (t : Term) (p : Pattern) : Term :=
  match t with
  | .prim (.string s) => wildcardMatch s p
  | _                 => .app (.string.like p) [t] .bool

---------- Extension ADT operators with a trusted mapping to SMT ----------

def ext.decimal.val : Term → Term
  | .prim (.ext (.decimal d)) => d
  | t                         => .app (.ext .decimal.val) [t] (.bitvec 64)

def ext.ipaddr.isV4 : Term → Term
  | .prim (.ext (.ipaddr ip)) => ip.isV4
  | t                         => .app (.ext .ipaddr.isV4) [t] .bool

def ext.ipaddr.addrV4 : Term → Term
  | .prim (.ext (.ipaddr (.V4 ⟨v4, _⟩))) => v4
  | t                                    => .app (.ext .ipaddr.addrV4) [t] (.bitvec 32)

def ext.ipaddr.prefixV4 : Term → Term
  | .prim (.ext (.ipaddr (.V4 ⟨_, p4⟩))) =>
    match p4 with
    | .none     => noneOf (.bitvec 5)
    | .some pre => someOf pre
  | t => .app (.ext .ipaddr.prefixV4) [t] (.option (.bitvec 5))

def ext.ipaddr.addrV6 : Term → Term
  | .prim (.ext (.ipaddr (.V6 ⟨v6, _⟩))) => v6
  | t                                    => .app (.ext .ipaddr.addrV6) [t] (.bitvec 128)

def ext.ipaddr.prefixV6 : Term → Term
  | .prim (.ext (.ipaddr (.V6 ⟨_, p6⟩))) =>
    match p6 with
    | .none     => noneOf (.bitvec 7)
    | .some pre => someOf pre
  | t => .app (.ext .ipaddr.prefixV6) [t] (.option (.bitvec 7))

def ext.datetime.val : Term → Term
  | .prim (.ext (.datetime d)) => d.val
  | t                          => .app (.ext .datetime.val) [t] (.bitvec 64)

def ext.datetime.ofBitVec : Term -> Term
  | .prim (@TermPrim.bitvec 64 bv) => .prim (.ext (.datetime (Int64.ofInt bv.toInt)))
  | t                              => .app (.ext .datetime.ofBitVec) [t] (.ext .datetime)

def ext.duration.val : Term → Term
  | .prim (.ext (.duration d)) => d.val
  | t                          => .app (.ext .duration.val) [t] (.bitvec 64)

def ext.duration.ofBitVec : Term -> Term
  | .prim (@TermPrim.bitvec 64 bv) => .prim (.ext (.duration (Int64.ofInt bv.toInt)))
  | t                              => .app (.ext .duration.ofBitVec) [t] (.ext .duration)

---------- Helper functions for constructing compound terms ----------

def isNone : Term → Term
  | .none _  => true
  | .some _  => false
  | .app .ite [_, .some _, .some _] _ => false
  | .app .ite [g, .some _, .none _] _ => not g
  | .app .ite [g, .none _, .some _] _ => g
  | t =>
    match t.typeOf with
    | .option ty => eq t (.none ty)
    | _          => false

def isSome (t : Term) : Term :=
  not (isNone t)

def ifFalse (g t : Term) : Term :=
  ite g (noneOf t.typeOf) (someOf t)

def ifTrue (g t : Term) : Term :=
  ite g (someOf t) (noneOf t.typeOf)

def ifSome (g t : Term) : Term :=
  if let .option ty := t.typeOf
  then ite (isNone g) (noneOf ty) t
  else ifFalse (isNone g) t

def anyTrue (f : Term → Term) (ts : List Term) : Term :=
  ts.foldl (λ acc t => or (f t) acc) false

def anyNone (gs : List Term) : Term := anyTrue isNone gs

def ifAllSome (gs : List Term) (t : Term) : Term :=
  let g := anyNone gs
  if let .option ty := t.typeOf
  then ite g (noneOf ty) t
  else ifFalse g t

def bvaddChecked t₁ t₂ := ifFalse (bvsaddo t₁ t₂) (bvadd t₁ t₂)
def bvsubChecked t₁ t₂ := ifFalse (bvssubo t₁ t₂) (bvsub t₁ t₂)
def bvmulChecked t₁ t₂ := ifFalse (bvsmulo t₁ t₂) (bvmul t₁ t₂)

end Factory

end Cedar.SymCC

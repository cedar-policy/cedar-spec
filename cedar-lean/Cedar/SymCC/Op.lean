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

import Cedar.SymCC.TermType

/-!
This file defines the operators on Cedar Terms. See `Term.lean` for the
definition of the Term language.

There are three kinds of term operators:
1. Operators that map directly to an underlying SMT theory
2. Operators for constructing and destructing core ADTs that are lowered to SMT
   by a trusted code generation pass. This also includes core operators whose
   semantics we don't model in the Term language (but rather directly in SMT),
   such as `like`.
3. Operators for destructing extension ADTs, also lowered by the trusted pass.

We separate extension operators into their own ADT (`ExtOp`) to make it easier
to add more such operators in the future in a way that's fairly independent of
the other operators.

We embed SMT and core ADT operators directly into the top-level `Op` ADT, to
simplify pattern matching against them within rewrite rules.
-/

namespace Cedar.SymCC

open Cedar.Spec

structure UUF where         -- uninterpreted unary function
  id : String
  arg : TermType
  out : TermType

inductive ExtOp : Type where -- extension ADT operators
  | decimal.val
  | ipaddr.isV4
  | ipaddr.addrV4
  | ipaddr.prefixV4
  | ipaddr.addrV6
  | ipaddr.prefixV6
  | datetime.val
  | datetime.ofBitVec
  | duration.val
  | duration.ofBitVec

inductive Op : Type where
  ---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------
  | not
  | and
  | or
  | eq
  | ite
  | uuf : UUF → Op
  ---------- SMTLib theory of finite bitvectors (`BV`) ----------
  | bvneg
  | bvadd
  | bvsub
  | bvmul
  | bvsdiv  -- signed bit-vector division
  | bvudiv  -- unsigned bit-vector division
  | bvsrem  -- signed remainder (remainder of division rounded towards zero) (copies sign from dividend)
  | bvsmod  -- signed modulus (remainder of division rounded towards negative infinity) (copies sign from divisor)
  | bvumod  -- unsigned modulus
  | bvshl
  | bvlshr
  | bvslt
  | bvsle
  | bvult
  | bvule
  | bvnego  -- bit-vector negation overflow predicate
  | bvsaddo -- bit-vector signed addition overflow predicate
  | bvssubo -- bit-vector signed subtraction overflow predicate
  | bvsmulo -- bit-vector signed multiplication overflow predicate
  | zero_extend : Nat → Op
  ---------- CVC theory of finite sets (`FS`) ----------
  | set.member
  | set.subset
  | set.inter
  ---------- Core ADT operators with a trusted mapping to SMT ----------
  | option.get
  | record.get  : Attr → Op
  | string.like : Pattern → Op
  ---------- Extension ADT operators with a trusted mapping to SMT ----------
  | ext : ExtOp → Op

deriving instance Repr, DecidableEq, Inhabited for UUF
deriving instance Repr, DecidableEq, Inhabited for ExtOp
deriving instance Repr, DecidableEq, Inhabited for Op

def UUF.lt (uf uf' : UUF) : Bool :=
  uf.id < uf'.id ||
  (uf.id = uf'.id && uf.arg < uf'.arg) ||
  (uf.id = uf'.id && uf.arg = uf'.arg && uf.out < uf'.out)

instance : LT UUF where
  lt := fun x y => UUF.lt x y

instance UUF.decLt (x y : UUF) : Decidable (x < y) :=
  if h : UUF.lt x y then isTrue h else isFalse h

def ExtOp.mkName : ExtOp → String
  | ExtOp.decimal.val       => "decimal.val"
  | ExtOp.ipaddr.isV4       => "ipaddr.isV4"
  | ExtOp.ipaddr.addrV4     => "ipaddr.addrV4"
  | ExtOp.ipaddr.prefixV4   => "ipaddr.prefixV4"
  | ExtOp.ipaddr.addrV6     => "ipaddr.addrV6"
  | ExtOp.ipaddr.prefixV6   => "ipaddr.prefixV6"
  | ExtOp.datetime.val      => "datetime.val"
  | ExtOp.datetime.ofBitVec => "datetime.ofBitVec"
  | ExtOp.duration.val      => "duration.val"
  | ExtOp.duration.ofBitVec => "duration.ofBitVec"

def ExtOp.lt : ExtOp → ExtOp → Bool
  | ty₁, ty₂    => ty₁.mkName < ty₂.mkName

instance : LT ExtOp where
  lt := fun x y => ExtOp.lt x y

instance ExtOp.decLt (x y : ExtOp) : Decidable (x < y) :=
  if h : ExtOp.lt x y then isTrue h else isFalse h

def Op.mkName : Op → String
  | .not           => "not"
  | .and           => "and"
  | .or            => "or"
  | .eq            => "eq"
  | .ite           => "ite"
  | .uuf _         => "uuf"
  | .bvneg         => "bvneg"
  | .bvadd         => "bvadd"
  | .bvsub         => "bvsub"
  | .bvmul         => "bvmul"
  | .bvsdiv        => "bvsdiv"
  | .bvudiv        => "bvudiv"
  | .bvsrem        => "bvsrem"
  | .bvsmod        => "bvsmod"
  | .bvumod        => "bvurem"
  | .bvshl         => "bvshl"
  | .bvlshr        => "bvlshr"
  | .bvslt         => "bvslt"
  | .bvsle         => "bvsle"
  | .bvult         => "bvult"
  | .bvule         => "bvule"
  | .bvnego        => "bvnego"
  | .bvsaddo       => "bvsaddo"
  | .bvssubo       => "bvssubo"
  | .bvsmulo       => "bvsmulo"
  | .zero_extend _ => "zero_extend"
  | Op.set.member    => "set.member"
  | Op.set.subset    => "set.subset"
  | Op.set.inter     => "set.inter"
  | Op.option.get    => "option.get"
  | Op.record.get _  => "record.get"
  | Op.string.like _ => "string.like"
  | .ext _         => "ext"

def Op.lt : Op → Op → Bool
  | .uuf f₁, uuf f₂                  => f₁ < f₂
  | .zero_extend n₁, .zero_extend n₂ => n₁ < n₂
  | Op.record.get a₁, Op.record.get a₂   => a₁ < a₂
  | Op.string.like p₁, Op.string.like p₂ => p₁ < p₂
  | .ext xty₁, .ext xty₂             => xty₁ < xty₂
  | ty₁, ty₂                         => ty₁.mkName < ty₂.mkName

instance : LT Op where
  lt := fun x y => Op.lt x y

instance Op.decLt (x y : Op) : Decidable (x < y) :=
  if h : Op.lt x y then isTrue h else isFalse h

end Cedar.SymCC

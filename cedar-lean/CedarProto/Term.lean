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
import Cedar.Validation
import Protobuf.Enum
import Protobuf.Message
import Protobuf.Packed
import Protobuf.String

-- Message Dependencies
import CedarProto.EntityUID
import CedarProto.TermType

open Proto

namespace Cedar.SymCC.Proto

structure UUF where
  id: String
  arg: TermType
  out: TermType
deriving Repr, Inhabited

namespace UUF
  @[inline]
  def merge (f₁ f₂ : UUF) : UUF :=
    UUF.mk (Field.merge f₁.id f₂.id) (Field.merge f₁.arg f₂.arg) (Field.merge f₁.out f₂.out)

  def parseField (t : Tag) : BParsec (MergeFn UUF) := do
    match t.fieldNum with
    | 1 => parseFieldElement t id (update id)
    | 2 => parseFieldElement t arg (update arg)
    | 3 => parseFieldElement t out (update out)
    | _ => t.wireType.skip ; pure ignore

  instance : Message UUF := {
     parseField := parseField
     merge := merge
  }

  def toCedar (f : UUF) : Cedar.SymCC.UUF :=
     Cedar.SymCC.UUF.mk f.id f.arg.toCedarTermType f.out.toCedarTermType
end UUF

inductive ExtOp where
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
deriving Repr, Inhabited

namespace ExtOp
  @[inline]
  def fromInt(n : Int) : Except String ExtOp :=
    match n with
    | 0 => .ok .decimal.val
    | 1 => .ok .ipaddr.isV4
    | 2 => .ok .ipaddr.addrV4
    | 3 => .ok .ipaddr.prefixV4
    | 4 => .ok .ipaddr.addrV6
    | 5 => .ok .ipaddr.prefixV6
    | 6 => .ok .datetime.val
    | 7 => .ok .datetime.ofBitVec
    | 8 => .ok .duration.val
    | 9 => .ok .duration.ofBitVec
    | _ => .error s!"Field {n} does not exist in enum"

  def merge (_xop₁ xop₂ : ExtOp) : ExtOp := xop₂

  instance : ProtoEnum ExtOp := {
     fromInt := fromInt
  }

  def toCedar (xop : ExtOp) : Cedar.SymCC.ExtOp :=
    match xop with
    | .decimal.val => .decimal.val
    | .ipaddr.isV4 => .ipaddr.isV4
    | .ipaddr.addrV4 => .ipaddr.addrV4
    | .ipaddr.prefixV4 => .ipaddr.prefixV4
    | .ipaddr.addrV6 => .ipaddr.addrV6
    | .ipaddr.prefixV6 => .ipaddr.prefixV6
    | .datetime.val => .datetime.val
    | .datetime.ofBitVec => .datetime.ofBitVec
    | .duration.val => .duration.val
    | .duration.ofBitVec => .duration.ofBitVec
end ExtOp

inductive BaseOp where
  | not
  | and
  | or
  | eq
  | ite
  | bvneg
  | bvadd
  | bvsub
  | bvmul
  | bvsdiv
  | bvudiv
  | bvsrem
  | bvsmod
  | bvumod
  | bvshl
  | bvlshr
  | bvslt
  | bvsle
  | bvult
  | bvule
  | bvnego
  | bvsaddo
  | bvssubo
  | bvsmulo
  | set.member
  | set.subset
  | set.inter
  | option.get
deriving Repr, Inhabited

namespace BaseOp
  @[inline]
  def fromInt(n : Int) : Except String BaseOp :=
    match n with
    | 0 => .ok .not
    | 1 => .ok .and
    | 2 => .ok .or
    | 3 => .ok .eq
    | 4 => .ok .ite
    | 5 => .ok .bvneg
    | 6 => .ok .bvadd
    | 7 => .ok .bvsub
    | 8 => .ok .bvmul
    | 9 => .ok .bvsdiv
    | 10 => .ok .bvudiv
    | 11 => .ok .bvsrem
    | 12 => .ok .bvsmod
    | 13 => .ok .bvumod
    | 14 => .ok .bvshl
    | 15 => .ok .bvlshr
    | 16 => .ok .bvslt
    | 17 => .ok .bvsle
    | 18 => .ok .bvult
    | 19 => .ok .bvule
    | 20 => .ok .bvnego
    | 21 => .ok .bvsaddo
    | 22 => .ok .bvssubo
    | 23 => .ok .bvsmulo
    | 24 => .ok .set.member
    | 25 => .ok .set.subset
    | 26 => .ok .set.inter
    | 27 => .ok .option.get
    | _ => .error s!"Field {n} does not exist in enum"

  def merge (_op₁ op₂ : BaseOp) : BaseOp := op₂

  instance : ProtoEnum BaseOp := {
     fromInt := fromInt
  }

  def toCedar (bop : BaseOp) : Cedar.SymCC.Op :=
    match bop with
    | .not => .not
    | .and => .and
    | .or => .or
    | .eq => .eq
    | .ite => .ite
    | .bvneg => .bvneg
    | .bvadd => .bvadd
    | .bvsub => .bvsub
    | .bvmul => .bvmul
    | .bvsdiv => .bvsdiv
    | .bvudiv => .bvudiv
    | .bvsrem => .bvsrem
    | .bvsmod => .bvsmod
    | .bvumod => .bvumod
    | .bvshl => .bvshl
    | .bvlshr => .bvlshr
    | .bvslt => .bvslt
    | .bvsle => .bvsle
    | .bvult => .bvult
    | .bvule => .bvule
    | .bvnego => .bvnego
    | .bvsaddo => .bvsaddo
    | .bvssubo => .bvssubo
    | .bvsmulo => .bvsmulo
    | .set.member => .set.member
    | .set.subset => .set.subset
    | .set.inter => .set.inter
    | .option.get => .option.get
end BaseOp

inductive PatElem where
  | star
  | char : Char -> PatElem
deriving Repr, Inhabited

namespace PatElem
  @[inline]
  def merge (elem₁ elem₂ : PatElem) : PatElem :=
    match elem₁, elem₂ with
    | .star, .star => .star
    | .char _, .char c₂ => .char c₂
    | _, _ => elem₂

  def parseField (t : Tag) : BParsec (MergeFn PatElem) := do
    match t.fieldNum with
    | 1 =>
      let _x : Bool ← Field.guardedParse t
      pureMergeFn (merge · .star)
    | 2 =>
      let x : UInt32 ← Field.guardedParse t
      pureMergeFn (merge · (.char (Char.ofNat x.toNat)))
    | _ => t.wireType.skip ; pure ignore

  instance : Message PatElem := {
    parseField := parseField
    merge := merge
  }

  def toCedar (elem : PatElem) : Cedar.Spec.PatElem :=
    match elem with
    | .star => .star
    | .char c => .justChar c
end PatElem

abbrev Pattern := List PatElem

namespace Pattern
  @[inline]
  def merge (p₁ p₂ : Pattern) : Pattern := p₁ ++ p₂

  def parseField (t : Tag) : BParsec (MergeFn Pattern) := do
    have : Field (List PatElem) := Field.fromInterField (λ (elems : Repeated PatElem) => elems.toList) (· ++ ·)
    match t.fieldNum with
    | 1 =>
      let x : List PatElem ← Field.guardedParse t
      pureMergeFn (merge · x)
    | _ => t.wireType.skip ; pure ignore

  instance : Message Pattern := {
    parseField := parseField
    merge := merge
  }

  def toCedar (p : Pattern) : Cedar.Spec.Pattern := p.map PatElem.toCedar
end Pattern

inductive Op where
  | base : BaseOp -> Op
  | uuf : UUF -> Op
  | zero_extend : Nat -> Op
  | record.get : String -> Op
  | string.like : Pattern -> Op
  | ext : ExtOp -> Op
deriving Repr, Inhabited

namespace Op
  @[inline]
  def merge (op₁ op₂ : Op) : Op :=
    match op₁, op₂ with
    | .base bop₁, .base bop₂ => .base (Field.merge bop₁ bop₂)
    | .uuf f₁, .uuf f₂ => .uuf (Field.merge f₁ f₂)
    | .zero_extend _, .zero_extend n => .zero_extend n
    | .record.get s, .record.get t => .record.get (Field.merge s t)
    | .string.like p₁, .string.like p₂ => .string.like (Field.merge p₁ p₂)
    | .ext xop₁, .ext xop₂ => .ext (Field.merge xop₁ xop₂)
    | _, _ => op₂

  def parseField (t: Tag) : BParsec (MergeFn Op) := do
    match t.fieldNum with
    | 1 =>
      let x : BaseOp ← Field.guardedParse t
      pureMergeFn (merge · (.base x))
    | 2 =>
      let x : UUF ← Field.guardedParse t
      pureMergeFn (merge · (.uuf x))
    | 3 =>
      let x : UInt32 ← Field.guardedParse t
      pureMergeFn (merge · (.zero_extend x.toNat))
    | 4 =>
      let x : String ← Field.guardedParse t
      pureMergeFn (merge · (.record.get x))
    | 5 =>
      let x : Pattern ← Field.guardedParse t
      pureMergeFn (merge · (.string.like x))
    | 6 =>
      let x : ExtOp ← Field.guardedParse t
      pureMergeFn (merge · (.ext x))
    | _ => t.wireType.skip ; pure ignore

  instance : Message Op := {
    parseField := parseField
    merge := merge
  }

  def toCedar (op : Op) : Cedar.SymCC.Op :=
    match op with
    | .base bop => bop.toCedar
    | .uuf f => .uuf f.toCedar
    | .zero_extend n => .zero_extend n
    | .record.get attr => .record.get attr
    | .string.like p => .string.like p.toCedar
    | .ext xop => .ext xop.toCedar
end Op

structure Bitvec where
  width : UInt32
  /- `val` is the string representation of the bitvec's `Nat` value  -/
  val : String
deriving Repr, Inhabited

namespace Bitvec
  @[inline]
  def merge (_bv₁ bv₂ : Bitvec) : Bitvec := bv₂

  def parseField (t: Tag) : BParsec (MergeFn Bitvec) := do
    match t.fieldNum with
    | 1 => parseFieldElement t Bitvec.width (update width)
    | 2 => parseFieldElement t Bitvec.val (update val)
    | _ => t.wireType.skip ; pure ignore

  instance : Message Bitvec := {
    parseField := parseField
    merge := merge
  }

  def toCedar (bv : Bitvec) : Option (Σ (n : Nat), BitVec n) := do
    let n ← bv.width.toNat
    let bv ← bv.val.toNat?
    return ⟨n, bv⟩
end Bitvec

structure Decimal where
  val : Proto.Int64
deriving Repr, Inhabited

namespace Decimal
  @[inline]
  def merge (_d₁ d₂ : Decimal) : Decimal := d₂

  def parseField (t : Tag) : BParsec (MergeFn Decimal) := do
    match t.fieldNum with
    | 1 => parseFieldElement t Decimal.val (update val)
    | _ => t.wireType.skip ; pure ignore

  instance : Message Decimal := {
    parseField := parseField
    merge := merge
  }

  def toCedar (d : Decimal) : Cedar.Spec.Ext.Decimal := d.val.toInt64
end Decimal

structure Cidr where
  addr : Bitvec
  pre : Option Bitvec
deriving Repr, Inhabited

namespace Cidr
  @[inline]
  def merge (cidr₁ cidr₂ : Cidr) : Cidr :=
    let addr := Field.merge cidr₁.addr cidr₂.addr
    let pre := match cidr₁.pre, cidr₂.pre with
      | .some pre₁, .some pre₂ => .some (Field.merge pre₁ pre₂)
      | .some pre₁, .none => .some pre₁
      | _, _ => cidr₂.pre
    Cidr.mk addr pre

  def parseField (t: Tag) : BParsec (MergeFn Cidr) := do
    match t.fieldNum with
    | 1 => parseFieldElement t addr (update addr)
    | 2 => parseFieldElement t pre (update pre)
    | _ => t.wireType.skip ; pure ignore

  instance : Message Cidr := {
    parseField := parseField
    merge := merge
  }

  /- Converts Cidr to CIDR w. Returns none if cannot parse c as CIDR w -/
  def toCedar (c : Cidr) (w : Nat) : Option (Cedar.Spec.Ext.IPAddr.CIDR w) := do
    let ⟨w₁, addr⟩ ← c.addr.toCedar
    if h₁: 2^w = w₁ then
      let addr : Spec.Ext.IPAddr.IPNetAddr w := cast (by subst h₁; rfl) addr
      let pre : Spec.Ext.IPAddr.IPNetPrefix w ←
        match c.pre with
        | .none => .some .none
        | .some pre =>
          match pre.toCedar with
          | .none => .none
          | .some ⟨w₂, pre⟩ =>
            if h₂ : w = w₂ then
              .some (.some (cast (by subst h₂; rfl) pre))
            else
              .none
      .some (Spec.Ext.IPAddr.CIDR.mk addr pre)
    else
      .none
end Cidr

inductive IpAddr where
  | v4 : Cidr -> IpAddr
  | v6 : Cidr -> IpAddr
deriving Repr, Inhabited

namespace IpAddr
  @[inline]
  def merge (ip₁ ip₂ : IpAddr) : IpAddr :=
    match ip₁, ip₂ with
    | .v4 cidr₁, .v4 cidr₂ => .v4 (Field.merge cidr₁ cidr₂)
    | .v6 cidr₁, .v6 cidr₂ => .v6 (Field.merge cidr₁ cidr₂)
    | _, _ => ip₂

  def parseField (t : Tag) : BParsec (MergeFn IpAddr) := do
    match t.fieldNum with
    | 1 =>
      let x : Cidr ← Field.guardedParse t
      pureMergeFn (merge · (.v4 x))
    | 2 =>
      let x : Cidr ← Field.guardedParse t
      pureMergeFn (merge · (.v6 x))
    | _ => t.wireType.skip ; pure ignore

  instance : Message IpAddr := {
    parseField := parseField
    merge := merge
  }

  def toCedar (ip : IpAddr) : Option Cedar.Spec.Ext.IPAddr.IPNet := do
    match ip with
    | .v4 cidr =>
      let cidr ← cidr.toCedar 5
      return .V4 cidr
    | .v6 cidr =>
      let cidr ← cidr.toCedar 7
      return .V6 cidr
end IpAddr

structure Datetime where
  val : Proto.Int64
deriving Repr, Inhabited

namespace Datetime
  @[inline]
  def merge (_dt₁ dt₂ : Datetime) : Datetime := dt₂

  def parseField (t : Tag) : BParsec (MergeFn Datetime) := do
    match t.fieldNum with
    | 1 => parseFieldElement t Datetime.val (update val)
    | _ => t.wireType.skip ; pure ignore

  instance : Message Datetime := {
    parseField := parseField
    merge := merge
  }

  def toCedar (d : Datetime) : Cedar.Spec.Ext.Datetime:=
    Cedar.Spec.Ext.Datetime.mk d.val.toInt64
end Datetime

structure Duration where
  val : Proto.Int64
deriving Repr, Inhabited

namespace Duration
  @[inline]
  def merge (_dur₁ dur₂ : Duration) : Duration := dur₂

  def parseField (t : Tag) : BParsec (MergeFn Duration) := do
    match t.fieldNum with
    | 1 => parseFieldElement t Duration.val (update val)
    | _ => t.wireType.skip ; pure ignore

  instance : Message Duration := {
    parseField := parseField
    merge := merge
  }

  def toCedar (d : Duration) : Cedar.Spec.Ext.Datetime.Duration :=
    Cedar.Spec.Ext.Datetime.Duration.mk d.val.toInt64
end Duration


structure TermVar where
  id : String
  ty : TermType
deriving Repr, Inhabited

namespace TermVar
  @[inline]
  def merge (v₁ v₂ : TermVar) : TermVar :=
    TermVar.mk (Field.merge v₁.id v₂.id) (Field.merge v₁.ty v₂.ty)

  def parseField (t: Tag) : BParsec (MergeFn TermVar) := do
    match t.fieldNum with
    | 1 => parseFieldElement t id (update id)
    | 2 => parseFieldElement t ty (update ty)
    | _ => t.wireType.skip ; pure ignore

  instance : Message TermVar := {
    parseField := parseField
    merge := merge
  }

  def toCedar (v : TermVar) : Cedar.SymCC.TermVar :=
    Cedar.SymCC.TermVar.mk v.id v.ty.toCedarTermType
end TermVar

inductive Ext where
  | decimal : Decimal -> Ext
  | ipaddr : IpAddr -> Ext
  | datetime : Datetime -> Ext
  | duration : Duration -> Ext
deriving Repr, Inhabited

namespace Ext
  @[inline]
  def merge (ext₁ ext₂ : Ext) : Ext :=
    match ext₁, ext₂ with
    | .decimal d₁, .decimal d₂ => .decimal (Field.merge d₁ d₂)
    | .ipaddr ip₁, .ipaddr ip₂ => .ipaddr (Field.merge ip₁ ip₂)
    | .datetime dt₁, .datetime dt₂ => .datetime (Field.merge dt₁ dt₂)
    | .duration dur₁, .duration dur₂ => .duration (Field.merge dur₁ dur₂)
    | _, _ => ext₂

  def parseField (t : Tag) : BParsec (MergeFn Ext) := do
    match t.fieldNum with
    | 1 =>
      let x : Decimal ← Field.guardedParse t
      pureMergeFn (merge · (.decimal x))
    | 2 =>
      let x : IpAddr ← Field.guardedParse t
      pureMergeFn (merge · (.ipaddr x))
    | 3 =>
      let x : Datetime ← Field.guardedParse t
      pureMergeFn (merge · (.datetime x))
    | 4 =>
      let x : Duration ← Field.guardedParse t
      pureMergeFn (merge · (.duration x))
    | _ => t.wireType.skip ; pure ignore

  instance : Message Ext := {
    parseField := parseField
    merge := merge
  }

  def toCedar (ext : Ext) : Option (Cedar.Spec.Ext) := do
    match ext with
    | .decimal d => .some (.decimal d.toCedar)
    | .ipaddr ip =>
      let ip ← ip.toCedar
      .some (.ipaddr ip)
    | .datetime dt => .some (.datetime dt.toCedar)
    | .duration dur => .some (.duration dur.toCedar)
end Ext

inductive TermPrim where
  | bool : Bool -> TermPrim
  | bitvec : Bitvec -> TermPrim
  | string : String -> TermPrim
  | entity : Cedar.Spec.EntityUID -> TermPrim
  | ext : Ext -> TermPrim
deriving Repr, Inhabited

namespace TermPrim
  @[inline]
  def merge (t₁ t₂ : TermPrim) : TermPrim :=
    match t₁, t₂ with
    | .bool b₁, .bool b₂ => .bool (Field.merge b₁ b₂)
    | .bitvec bv₁, .bitvec bv₂ => .bitvec (Field.merge bv₁ bv₂)
    | .string s₁, .string s₂ => .string (Field.merge s₁ s₂)
    | .entity euid₁, .entity euid₂ => .entity (Field.merge euid₁ euid₂)
    | .ext ext₁, .ext ext₂ => .ext (Field.merge ext₁ ext₂)
    | _, _ => t₂

  def parseField (t : Tag) : BParsec (MergeFn TermPrim) := do
    match t.fieldNum with
    | 1 =>
      let x : Bool ← Field.guardedParse t
      pureMergeFn (merge · (.bool x))
    | 2 =>
      let x : Bitvec ← Field.guardedParse t
      pureMergeFn (merge · (.bitvec x))
    | 3 =>
      let x : String ← Field.guardedParse t
      pureMergeFn (merge · (.string x))
    | 4 =>
      let x : Cedar.Spec.EntityUID ← Field.guardedParse t
      pureMergeFn (merge · (.entity x))
    | 5 =>
      let x : Ext ← Field.guardedParse t
      pureMergeFn (merge · (.ext x))
    | _ => t.wireType.skip ; pure ignore

  instance : Message TermPrim := {
    parseField := parseField
    merge := merge
  }

  def toCedar (t : TermPrim) : Option Cedar.SymCC.TermPrim := do
    match t with
    | .bool b => .some (.bool b)
    | .bitvec bv =>
      let ⟨_, bv⟩ ← bv.toCedar
      .some (.bitvec bv)
    | .string s => .some (.string s)
    | .entity euid => .some (.entity euid)
    | .ext xt =>
      let xt ← xt.toCedar
      .some (.ext xt)
end TermPrim

mutual
  inductive Term where
    | prim : TermPrim -> Term
    | var : TermVar -> Term
    | none : TermType -> Term
    | some : Term -> Term
    | set : Set -> Term
    | record : Record -> Term
    | app : App -> Term
  deriving Repr, Inhabited

  structure Asserts where
    asserts: List Term
  deriving Repr, Inhabited

  structure Set where
    elts : List Term
    ty : TermType
  deriving Repr, Inhabited

  structure RecordField where
    attr : String
    term : Term
  deriving Repr, Inhabited

  structure Record where
    fields : List RecordField
  deriving Repr, Inhabited

  structure App where
    op : Op
    args : List Term
    ty : TermType
  deriving Repr, Inhabited
end

mutual
  @[inline]
  def RecordField.merge (rf₁ rf₂ : RecordField) : RecordField :=
    RecordField.mk (Field.merge rf₁.attr rf₂.attr) (Term.merge rf₁.term rf₂.term)

  @[inline]
  def Record.merge (r₁ r₂ : Record) : Record :=
    Record.mk (r₁.fields ++ r₂.fields)

  @[inline]
  def Asserts.merge (a₁ a₂ : Asserts) : Asserts :=
    Asserts.mk (a₁.asserts ++ a₂.asserts)

  @[inline]
  def Set.merge (s₁ s₂ : Set) : Set :=
    Set.mk (s₁.elts ++ s₂.elts) (Field.merge s₁.ty s₂.ty)

  @[inline]
  def App.merge (app₁ app₂ : App) : App :=
    App.mk (Field.merge app₁.op app₂.op) (app₁.args ++ app₂.args) (Field.merge app₁.ty app₂.ty)

  @[inline]
  def Term.merge (t₁ t₂ : Term) : Term :=
    match t₁, t₂ with
    | .prim p₁, .prim p₂ => .prim (Field.merge p₁ p₂)
    | .var v₁, .var v₂ => .var (Field.merge v₁ v₂)
    | .none ty₁, .none ty₂ => .none (Field.merge ty₁ ty₂)
    | .some t₁, .some t₂ => .some (Term.merge t₁ t₂)
    | .set s₁, .set s₂ => .set (Set.merge s₁ s₂)
    | .record r₁, .record r₂ => .record (Record.merge r₁ r₂)
    | .app app₁, .app app₂ => .app (App.merge app₁ app₂)
    | _, _ => t₂
end

mutual
  partial def RecordField.parseField (t : Tag) : BParsec (MergeFn RecordField) := do
    have : Message Term := { parseField := Term.parseField, merge := Term.merge }
    match t.fieldNum with
    | 1 => parseFieldElement t RecordField.attr (update attr)
    | 2 => parseFieldElement t RecordField.term (update term)
    | _ => t.wireType.skip ; pure ignore

  partial def Record.parseField (t : Tag) : BParsec (MergeFn Record) := do
    have : Message RecordField := { parseField := RecordField.parseField, merge := RecordField.merge }
    have : Field (List RecordField) := Field.fromInterField (λ (fields : Repeated RecordField) => fields.toList) (· ++ ·)
    match t.fieldNum with
    | 1 =>
      let x : List RecordField ← Field.guardedParse t
      pureMergeFn (Record.merge · (Record.mk x))
    | _ => t.wireType.skip ; pure ignore

  partial def Asserts.parseField (t : Tag) : BParsec (MergeFn Asserts) := do
    have : Message Term := { parseField := Term.parseField, merge := Term.merge }
    have : Field (List Term) := Field.fromInterField (λ (terms : Repeated Term) => terms.toList) (· ++ ·)
    match t.fieldNum with
    | 1 => parseFieldElement t Asserts.asserts (update asserts)
    | _ => t.wireType.skip ; pure ignore

  partial def Set.parseField (t : Tag) : BParsec (MergeFn Set) := do
    have : Message Term := { parseField := Term.parseField, merge := Term.merge }
    have : Field (List Term) := Field.fromInterField (λ (terms : Repeated Term) => terms.toList) (· ++ ·)
    match t.fieldNum with
    | 1 => parseFieldElement t Set.elts (update elts)
    | 2 => parseFieldElement t Set.ty (update ty)
    | _ => t.wireType.skip ; pure ignore

  partial def App.parseField (t : Tag) : BParsec (MergeFn App) := do
    have : Message Term := { parseField := Term.parseField, merge := Term.merge }
    have : Field (List Term) := Field.fromInterField (λ (terms : Repeated Term) => terms.toList) (· ++ ·)
    match t.fieldNum with
    | 1 => parseFieldElement t App.op (update op)
    | 2 => parseFieldElement t App.args (update args)
    | 3 => parseFieldElement t App.ty (update ty)
    | _ => t.wireType.skip ; pure ignore

  partial def Term.parseField (t : Tag) : BParsec (MergeFn Term) := do
    have : Message Record := { parseField := Record.parseField, merge := Record.merge }
    have : Message Set := { parseField := Set.parseField, merge := Set.merge }
    have : Message App := { parseField := App.parseField, merge := App.merge }
    have : Message Term := { parseField := Term.parseField, merge := Term.merge }
    match t.fieldNum with
    | 1 =>
      let x : TermPrim ← Field.guardedParse t
      pureMergeFn (Term.merge · (.prim x))
    | 2 =>
      let x : TermVar ← Field.guardedParse t
      pureMergeFn (Term.merge · (.var x))
    | 3 =>
      let x : TermType ← Field.guardedParse t
      pureMergeFn (Term.merge · (.none x))
    | 4 =>
      let x : Term ← Field.guardedParse t
      pureMergeFn (Term.merge · (.some x))
    | 5 =>
      let x : Set ← Field.guardedParse t
      pureMergeFn (Term.merge · (.set x))
    | 6 =>
      let x : Record ← Field.guardedParse t
      pureMergeFn (Term.merge · (.record x))
    | 7 =>
      let x : App ← Field.guardedParse t
      pureMergeFn (Term.merge · (.app x))
    | _ => t.wireType.skip ; pure ignore
end

namespace RecordField
  instance : Message RecordField := {
    parseField := parseField
    merge := merge
  }
end RecordField

namespace Record
  instance : Message Record := {
    parseField := parseField
    merge := merge
  }
end Record

namespace Set
  instance : Message Set := {
    parseField := parseField
    merge := merge
  }
end Set

namespace App
  instance : Message App := {
    parseField := parseField
    merge := merge
  }
end App

namespace Term
  instance : Message Term := {
    parseField := parseField
    merge := merge
  }
end Term

namespace Asserts
  instance : Message Asserts := {
    parseField := parseField
    merge := merge
  }
end Asserts

mutual
  partial def Record.toCedar (r : Record) : Option (Cedar.Data.Map Cedar.Spec.Attr Cedar.SymCC.Term) := do
    let attrs ← r.fields.mapM (λ rf =>
      match rf.term.toCedar with
      | .none => .none
      | .some t => .some ⟨rf.attr, t⟩
    )
    return Cedar.Data.Map.mk attrs

  partial def Set.toCedar (s : Set) : Option (Cedar.Data.Set Cedar.SymCC.Term × Cedar.SymCC.TermType) := do
    let elts ← s.elts.mapM Term.toCedar
    return ⟨Cedar.Data.Set.mk elts, s.ty.toCedarTermType⟩

  partial def Term.toCedar (t : Term) : Option Cedar.SymCC.Term := do
    match t with
    | .prim p =>
      let p ← p.toCedar
      return .prim p
    | .var v =>
      let v ← v.toCedar
      return .var v
    | .none ty => return (.none ty.toCedarTermType)
    | .some t =>
      let t ← t.toCedar
      return .some t
    | .set s =>
      let ⟨s, ty⟩ ← s.toCedar
      return .set s ty
    | .app a =>
      let op := a.op.toCedar
      let ret_ty := a.ty.toCedarTermType
      let cedar_args ← a.args.mapM Term.toCedar
      return .app op cedar_args ret_ty
    | .record r => return .record (← r.toCedar)

  partial def Asserts.toCedar (a : Asserts) : Option Cedar.SymCC.Asserts :=
    a.asserts.mapM Term.toCedar
end

end Cedar.SymCC.Proto

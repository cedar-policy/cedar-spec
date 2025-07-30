import Lean.Data.Json.FromToJson

import Cedar.Spec
import Cedar.SymCC

namespace CedarFFI

open Cedar.Spec
open Cedar.SymCC

abbrev x := Term

/- Serialize a Map as a JSON Array of values -/
instance {α} [Lean.ToJson α] : Lean.ToJson (Cedar.Data.Set α) where
  toJson
  | .mk lst => Lean.Json.arr (List.toArray (lst.map Lean.toJson))

/- Serialize a Map as a JSON Array of key-value pairs (JSON Array of size 2) -/
instance {α β} [Lean.ToJson α] [Lean.ToJson β] : Lean.ToJson (Cedar.Data.Map α β) where
  toJson
  | .mk lst =>
    Lean.Json.arr (List.toArray (lst.map (fun (k, v) =>
      Lean.Json.arr #[Lean.toJson k, Lean.toJson v]
    )))

/- Serialize a bv : Bitvec n as the object {"size": n, "value": "repr bv"} -/
instance {n : Nat} : Lean.ToJson (BitVec n) where
  toJson bv :=
    Lean.Json.mkObj [
      ("size", Lean.Json.num n),
      ("value", Lean.Json.str (toString bv))
    ]

/- Serialize a char as its Nat representation -/
instance : Lean.ToJson Char where
 toJson c := Lean.Json.num c.val.toNat

/- Serialize a Decimal as the underlying Int64 representation -/
instance : Lean.ToJson Ext.Decimal where
  toJson d := Lean.Json.num d

/- Derive JSON represenatations for Term and its underlying types -/
deriving instance Lean.ToJson for Cedar.Validation.ExtType
deriving instance Lean.ToJson for TermPrimType
deriving instance Lean.ToJson for TermType
deriving instance Lean.ToJson for UUF
deriving instance Lean.ToJson for PatElem

/- Don't deriving default implementatation which serializes compound constructors
   (e.g., .decimal.val) as the final constructor element (e.g., Lean.Json.str ".val")
 -/
instance : Lean.ToJson ExtOp where
  toJson op :=
  match op with
  | .decimal.val => Lean.Json.str "decimal.val"
  | .ipaddr.isV4 => Lean.Json.str "ipaddr.isV4"
  | .ipaddr.addrV4 => Lean.Json.str "ipaddr.addrV4"
  | .ipaddr.prefixV4 => Lean.Json.str "ipaddr.prefixV4"
  | .ipaddr.addrV6 => Lean.Json.str "ipaddr.addrV6"
  | .ipaddr.prefixV6 => Lean.Json.str "ipaddr.prefixV6"
  | .datetime.val => Lean.Json.str "datetime.val"
  | .datetime.ofBitVec => Lean.Json.str "datetime.ofBitVec"
  | .duration.val => Lean.Json.str "duration.val"
  | .duration.ofBitVec => Lean.Json.str "duration.ofBitVec"

/- Don't deriving default implementatation which serializes compound constructors
   (e.g., .option.get) as the final constructor element (e.g., Lean.Json.str ".get")
 -/
instance : Lean.ToJson Op where
  toJson op :=
  match op with
  | .not => Lean.Json.str "not"
  | .and => Lean.Json.str "and"
  | .or => Lean.Json.str "or"
  | .eq => Lean.Json.str "eq"
  | .ite => Lean.Json.str "ite"
  | .uuf f => Lean.Json.mkObj [("uuf", Lean.toJson f)]
  | .bvneg => Lean.Json.str "bvneg"
  | .bvadd => Lean.Json.str "bvadd"
  | .bvsub => Lean.Json.str "bvsub"
  | .bvmul => Lean.Json.str "bvmul"
  | .bvsdiv => Lean.Json.str "bvsdiv"
  | .bvudiv => Lean.Json.str "bvudiv"
  | .bvsrem => Lean.Json.str "bvsrem"
  | .bvsmod => Lean.Json.str "bvsmod"
  | .bvumod => Lean.Json.str "bvumod"
  | .bvshl => Lean.Json.str "bvshl"
  | .bvlshr => Lean.Json.str "bvlshr"
  | .bvslt => Lean.Json.str "bvslt"
  | .bvsle => Lean.Json.str "bvsle"
  | .bvult => Lean.Json.str "bvult"
  | .bvule => Lean.Json.str "bvule"
  | .bvnego => Lean.Json.str "bvnego"
  | .bvsaddo => Lean.Json.str "bvsaddo"
  | .bvssubo => Lean.Json.str "bvssubo"
  | .bvsmulo => Lean.Json.str "bvsmulo"
  | .zero_extend n => Lean.Json.mkObj [("zero_extend", Lean.Json.num n)]
  ---------- CVC theory of finite sets (`FS`) ----------
  | .set.member => Lean.Json.str "set.member"
  | .set.subset => Lean.Json.str "set.subset"
  | .set.inter => Lean.Json.str "set.inter"
  ---------- Core ADT operators with a trusted mapping to SMT ----------
  | .option.get => Lean.Json.str "option.get"
  | .record.get attr => Lean.Json.mkObj [("record.get", Lean.Json.str attr)]
  | .string.like pattern => Lean.Json.mkObj [("string.like", pattern.toJson)]
  ---------- Extension ADT operators with a trusted mapping to SMT ----------
  | .ext xop => Lean.Json.mkObj [("ext", Lean.toJson xop)]

deriving instance Lean.ToJson for Ext.Datetime.Duration
deriving instance Lean.ToJson for Ext.Datetime
deriving instance Lean.ToJson for Ext.IPAddr.CIDR
deriving instance Lean.ToJson for Ext.IPAddr.IPNet
deriving instance Lean.ToJson for Ext
deriving instance Lean.ToJson for TermPrim
deriving instance Lean.ToJson for TermVar
deriving instance Lean.ToJson for Term

deriving instance Lean.ToJson for Cedar.SymCC.Error

end CedarFFI

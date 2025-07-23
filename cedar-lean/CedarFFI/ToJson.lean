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
deriving instance Lean.ToJson for ExtOp
deriving instance Lean.ToJson for PatElem
deriving instance Lean.ToJson for Op
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

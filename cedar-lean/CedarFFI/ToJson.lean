import Lean.Data.Json.FromToJson
import Std.Data.HashMap

import Cedar.Spec
import Cedar.SymCC
import Cedar.Data
import Cedar.TPE.Authorizer
import Cedar.TPE
import Cedar.TPE.Residual

namespace CedarFFI

open Cedar.Spec
open Cedar.SymCC
open Cedar.Data
open Cedar

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
      ("value", Lean.Json.str (toString bv.toNat))
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
  | ExtOp.decimal.val => Lean.Json.str "decimal.val"
  | ExtOp.ipaddr.isV4 => Lean.Json.str "ipaddr.isV4"
  | ExtOp.ipaddr.addrV4 => Lean.Json.str "ipaddr.addrV4"
  | ExtOp.ipaddr.prefixV4 => Lean.Json.str "ipaddr.prefixV4"
  | ExtOp.ipaddr.addrV6 => Lean.Json.str "ipaddr.addrV6"
  | ExtOp.ipaddr.prefixV6 => Lean.Json.str "ipaddr.prefixV6"
  | ExtOp.datetime.val => Lean.Json.str "datetime.val"
  | ExtOp.datetime.ofBitVec => Lean.Json.str "datetime.ofBitVec"
  | ExtOp.duration.val => Lean.Json.str "duration.val"
  | ExtOp.duration.ofBitVec => Lean.Json.str "duration.ofBitVec"

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
  | .bvurem => Lean.Json.str "bvurem"
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
  | Op.set.member => Lean.Json.str "set.member"
  | Op.set.subset => Lean.Json.str "set.subset"
  | Op.set.inter => Lean.Json.str "set.inter"
  ---------- Core ADT operators with a trusted mapping to SMT ----------
  | Op.option.get => Lean.Json.str "option.get"
  | Op.record.get attr => Lean.Json.mkObj [("record.get", Lean.Json.str attr)]
  | Op.string.like pattern => Lean.Json.mkObj [("string.like", Lean.toJson pattern)]
  ---------- Extension ADT operators with a trusted mapping to SMT ----------
  | .ext xop => Lean.Json.mkObj [("ext", Lean.toJson xop)]

deriving instance Lean.ToJson for Ext.Datetime.Duration
deriving instance Lean.ToJson for Ext.Datetime
deriving instance Lean.ToJson for Ext.IPAddr.CIDR
deriving instance Lean.ToJson for Ext.IPAddr.IPNet
deriving instance Lean.ToJson for Ext

/- We need to manually implement the type class because of the `.bitvec` variant
   The derived implementation converts it into a list
-/
instance : Lean.ToJson TermPrim where
  toJson
  | .bitvec bv => Lean.Json.mkObj [("bitvec", Lean.toJson bv)]
  | .bool b => Lean.Json.mkObj [("bool", Lean.toJson b)]
  | .string s => Lean.Json.mkObj [("string", Lean.toJson s)]
  | .entity e => Lean.Json.mkObj [("entity", Lean.toJson e)]
  | .ext e => Lean.Json.mkObj [("ext", Lean.toJson e)]

deriving instance Lean.ToJson for TermVar

/- Add ToJson instance for Cedar Value -/
instance : Lean.ToJson Cedar.Spec.Prim where
  toJson
  | .bool b => Lean.Json.mkObj [("bool", Lean.toJson b)]
  | .int i => Lean.Json.mkObj [("int", Lean.toJson i.toInt)]
  | .string s => Lean.Json.mkObj [("string", Lean.toJson s)]
  | .entityUID uid => Lean.Json.mkObj [("entityUID", Lean.toJson uid)]

/--
  Local hashable for Terms.
  This is only used by the bottom-up serialization: no large terms should be hashed with this.
-/
instance : Hashable Term where
  hash t := hash (reprStr t)

/--
  An environment with bindings, with already converted Json terms, and the
  next id to use for a new binding.
-/
structure BindingEnv where
  memo : Std.HashMap Term String
  defs : List Lean.Json
  next : Nat

def BindingEnv.empty : BindingEnv := ⟨Std.HashMap.emptyWithCapacity, [], 0⟩

/-- Build a reference to a compound term that has already been bound. -/
private def idRef (id : String) : Lean.Json :=
  Lean.Json.mkObj [("ref", Lean.Json.str id)]

/--
  Given the already-computed shallow `body` json for a compound term `t`,
  bind `t` in the table under a fresh id and return a reference `{"tid": <id>}`
  to be used in place of `body`.
-/
private def BindingEnv.bind (s : BindingEnv) (t : Term) (body : Lean.Json) :
    (Lean.Json × BindingEnv) :=
  let id := s!"t{s.next}" -- a fresh id
  let definition := Lean.Json.mkObj [("id", Lean.Json.str id), ("body", body)]
  let s := { s with
    memo := s.memo.insert t id,
    defs := definition :: s.defs,
    next := s.next + 1 }
  (idRef id, s)

/-
  Bottom-up serialization of a `Term` with memoization of compound terms.

  Compound terms (`some`, `set`, `record`, `app`) are memoized:
  shared terms are emitted as definitions: `{"id": <id>, "body": <shallow json>}`,
  terms that reference those shared terms use the reference `{"ref": <id>}`.
-/
mutual

def termToJsonBindings : Term → BindingEnv → (Lean.Json × BindingEnv)
  | .prim p, s => (Lean.Json.mkObj [("prim", Lean.toJson p)], s)
  | .var v,  s => (Lean.Json.mkObj [("var",  Lean.toJson v)], s)
  | .none t, s => (Lean.Json.mkObj [("none", Lean.toJson t)], s)
  | t@(.some inner), s =>
    match s.memo[t]? with
    | .some id => (idRef id, s)
    | .none =>
      let (ref, s) := termToJsonBindings inner s
      s.bind t (Lean.Json.mkObj [("some", ref)])
  | t@(.set elts eltsTy), s =>
    match s.memo[t]? with
    | .some id => (idRef id, s)
    | .none =>
      let (refs, s) := termListToJsonBindings elts.elts s
      let body := Lean.Json.mkObj [
        ("set",
          Lean.Json.mkObj [
            ("elts", Lean.Json.arr refs.toArray),
            ("eltsTy", Lean.toJson eltsTy)
          ])
      ]
      s.bind t body
  | t@(.record m), s =>
    match s.memo[t]? with
    | .some id => (idRef id, s)
    | .none =>
      let (entries, s) := termRecordToJsonBindings m.toList s
      s.bind t (Lean.Json.mkObj [("record", Lean.Json.arr entries.toArray)])
  | t@(.app op args retTy), s =>
    match s.memo[t]? with
    | .some id => (idRef id, s)
    | .none =>
      let (refs, s) := termListToJsonBindings args s
      let main := Lean.Json.mkObj [
        ("app",
          Lean.Json.mkObj [
            ("op",   Lean.toJson op),
            ("args", Lean.Json.arr refs.toArray),
            ("retTy", Lean.toJson retTy)
          ])
      ]
      s.bind t main
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := Set.sizeOf_lt_of_elts elts
    omega
  · have := Map.sizeOf_lt_of_toList m
    omega
  · omega

/-- Serialize a list of child terms left to right, threading state. -/
def termListToJsonBindings : List Term → BindingEnv → (List Lean.Json × BindingEnv)
  | [], s => ([], s)
  | t :: ts, s =>
    let (ref, s) := termToJsonBindings t s
    let (refs, s) := termListToJsonBindings ts s
    (ref :: refs, s)
termination_by ts => sizeOf ts

/-- Serialize record entries as `[key, ref]` pairs left to right, threading state. -/
def termRecordToJsonBindings : List (Attr × Term) → BindingEnv → (List Lean.Json × BindingEnv)
  | [], s => ([], s)
  | (k, v) :: ats, s =>
    let (ref, s) := termToJsonBindings v s
    let (entries, s) := termRecordToJsonBindings ats s
    (Lean.Json.arr #[Lean.Json.str k, ref] :: entries, s)
termination_by ats => sizeOf ats

end

/--
  The shared JSON serialization of a `Term` produces an object `{"defs": [...], "root": <ref>}`
  where:
  * `defs` is the list of shared terms definition in dependency order (terms can only reference
     shared terms that appear earlier in the list), and
  * `root` is the reference to the main term being serialized.
  A deserializer can take advantage of the structure by building terms left-to-right, using shared
  memory representations following the explicit term sharing.
-/
def termToJson (t : Term) : Lean.Json :=
  let (root, s) := termToJsonBindings t BindingEnv.empty
  Lean.Json.mkObj [
    ("defs", Lean.Json.arr s.defs.reverse.toArray),
    ("root", root)
  ]

instance : Lean.ToJson Term where
  toJson := termToJson

deriving instance Lean.ToJson for Cedar.SymCC.Error

/- Serializing `Request` and `Entities` -/
deriving instance Lean.ToJson for Value
deriving instance Lean.ToJson for Request
deriving instance Lean.ToJson for EntityData
deriving instance Lean.ToJson for Entities

/- Serializing `Env` -/
deriving instance Lean.ToJson for Env

/- Serializing `TPE.Response` -/
deriving instance Lean.ToJson for Validation.BoolType
deriving instance Lean.ToJson for Validation.Qualified
deriving instance Lean.ToJson for Validation.CedarType
deriving instance Lean.ToJson for BinaryOp
deriving instance Lean.ToJson for UnaryOp
deriving instance Lean.ToJson for Var
deriving instance Lean.ToJson for Spec.ExtFun
deriving instance Lean.ToJson for Residual
deriving instance Lean.ToJson for Effect
deriving instance Lean.ToJson for TPE.ResidualPolicy
deriving instance Lean.ToJson for TPE.Response
deriving instance Lean.ToJson for Spec.Error


end CedarFFI

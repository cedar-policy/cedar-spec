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

def termToJson : Term → Lean.Json
  | .prim p => Lean.Json.mkObj [("prim", Lean.toJson p)]
  | .var v  => Lean.Json.mkObj [("var",  Lean.toJson v)]
  | .none t => Lean.Json.mkObj [("none", Lean.toJson t)]
  | .some t => Lean.Json.mkObj [("some", termToJson t)]
  | .set elts eltsTy =>
    Lean.Json.mkObj [
      ("set",
        Lean.Json.mkObj [
          ("elts",
            Lean.Json.arr (List.map₁ elts.elts (fun ⟨t,_⟩ => termToJson t) |>.toArray)),
          ("eltsTy", Lean.toJson eltsTy)
        ])
    ]
  | .record m =>
    Lean.Json.mkObj [
      ("record",
        Lean.Json.arr (m.toList.map₂ (fun ⟨(k,v), _⟩ =>
          Lean.Json.arr [Lean.Json.str k, termToJson v].toArray)).toArray)
    ]
  | .app op args retTy =>
    Lean.Json.mkObj [
      ("app",
        Lean.Json.mkObj [
          ("op",   Lean.toJson op),
          ("args", Lean.Json.arr (List.map₁ args (fun ⟨t,_⟩ => termToJson t) |>.toArray)),
          ("retTy", Lean.toJson retTy)
        ])
    ]
decreasing_by
  all_goals simp_wf
  case _ h₁ =>
    have := Set.sizeOf_lt_of_mem h₁
    omega
  case _ h₁ =>
    cases m
    simp only [Map.toList_mk_id] at h₁
    simp only [Map.mk.sizeOf_spec]
    omega
  case _ h₁ =>
    have := List.sizeOf_lt_of_mem h₁
    omega

/--
  A local `Hashable Term` instance, used only for memoized serialization.
  We already have `DecidableEq Term` (hence `BEq`), so a `Hashable` instance is
  all that is additionally required to key a `Std.HashMap Term _` on terms.

  We derive the hash from the term's `Repr`. This is trivially consistent with
  the derived `DecidableEq` (equal terms have identical `Repr`), avoids any
  termination obligations, and is kept local to `CedarFFI` because it is only
  needed for serialization -- the verified core does not depend on it. Hash
  collisions are resolved by `BEq`, so correctness does not rely on the hash
  being injective.
-/
instance : Hashable Term where
  hash t := hash (reprStr t)

/--
  State threaded through the memoized serialization.

  * `memo`  maps an already-serialized (compound) term to its generated id.
  * `defs`  accumulates the emitted definitions in *reverse* dependency order
            (most recently emitted first).  Because children are always emitted
            before their parents, reversing `defs` at the end yields a list
            ordered so that every term only refers to ids that appear earlier.
  * `next`  is the counter used to mint fresh ids.
-/
structure MemoState where
  memo : Std.HashMap Term String
  defs : List Lean.Json
  next : Nat

def MemoState.empty : MemoState := ⟨Std.HashMap.emptyWithCapacity, [], 0⟩

/-- Build a reference to a compound term that has already been emitted. -/
private def tidRef (id : String) : Lean.Json :=
  Lean.Json.mkObj [("tid", Lean.Json.str id)]

/--
  Given the already-computed shallow `main` json for a compound term `t`,
  register `t` in the memo table under a fresh id, append the definition
  `{"gid": <id>, "main": <main>}` to the (reversed) `defs`
  accumulator, and return a reference `{"tid": <id>}`.
-/
private def emitDef (t : Term) (main : Lean.Json) (s : MemoState) :
    (Lean.Json × MemoState) :=
  let id := s!"t{s.next}"
  let definition := Lean.Json.mkObj [("gid", Lean.Json.str id), ("main", main)]
  let s := { s with
    memo := s.memo.insert t id,
    defs := definition :: s.defs,
    next := s.next + 1 }
  (tidRef id, s)

/-
  Bottom-up serialization of a `Term` with memoization of compound terms.

  Compound terms (`some`, `set`, `record`, `app`) are memoized:
  shared terms are emitted as definitions: `{"gid": <id>, "main": <shallow json>}`,
  terms that reference those shared terms use the reference `{"tid": <id>}`.
-/
mutual

def termToJsonMemo : Term → MemoState → (Lean.Json × MemoState)
  | .prim p, s => (Lean.Json.mkObj [("prim", Lean.toJson p)], s)
  | .var v,  s => (Lean.Json.mkObj [("var",  Lean.toJson v)], s)
  | .none t, s => (Lean.Json.mkObj [("none", Lean.toJson t)], s)
  | t@(.some inner), s =>
    match s.memo[t]? with
    | .some id => (tidRef id, s)
    | .none =>
      let (ref, s) := termToJsonMemo inner s
      emitDef t (Lean.Json.mkObj [("some", ref)]) s
  | t@(.set elts eltsTy), s =>
    match s.memo[t]? with
    | .some id => (tidRef id, s)
    | .none =>
      let (refs, s) := termToJsonMemoList elts.elts s
      let main := Lean.Json.mkObj [
        ("set",
          Lean.Json.mkObj [
            ("elts", Lean.Json.arr refs.toArray),
            ("eltsTy", Lean.toJson eltsTy)
          ])
      ]
      emitDef t main s
  | t@(.record m), s =>
    match s.memo[t]? with
    | .some id => (tidRef id, s)
    | .none =>
      let (entries, s) := termToJsonMemoProd m.toList s
      emitDef t (Lean.Json.mkObj [("record", Lean.Json.arr entries.toArray)]) s
  | t@(.app op args retTy), s =>
    match s.memo[t]? with
    | .some id => (tidRef id, s)
    | .none =>
      let (refs, s) := termToJsonMemoList args s
      let main := Lean.Json.mkObj [
        ("app",
          Lean.Json.mkObj [
            ("op",   Lean.toJson op),
            ("args", Lean.Json.arr refs.toArray),
            ("retTy", Lean.toJson retTy)
          ])
      ]
      emitDef t main s
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := Set.sizeOf_lt_of_elts elts
    omega
  · have := Map.sizeOf_lt_of_toList m
    omega
  · omega

/-- Serialize a list of child terms left to right, threading state. -/
def termToJsonMemoList : List Term → MemoState → (List Lean.Json × MemoState)
  | [], s => ([], s)
  | t :: ts, s =>
    let (ref, s) := termToJsonMemo t s
    let (refs, s) := termToJsonMemoList ts s
    (ref :: refs, s)
termination_by ts => sizeOf ts

/-- Serialize record entries as `[key, ref]` pairs left to right, threading state. -/
def termToJsonMemoProd : List (Attr × Term) → MemoState → (List Lean.Json × MemoState)
  | [], s => ([], s)
  | (k, v) :: ats, s =>
    let (ref, s) := termToJsonMemo v s
    let (entries, s) := termToJsonMemoProd ats s
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
def termToJsonSharing (t : Term) : Lean.Json :=
  let (root, s) := termToJsonMemo t MemoState.empty
  Lean.Json.mkObj [
    ("defs", Lean.Json.arr s.defs.reverse.toArray),
    ("root", root)
  ]

instance : Lean.ToJson Term where
  toJson := termToJsonSharing

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

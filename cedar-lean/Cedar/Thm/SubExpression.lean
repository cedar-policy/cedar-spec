import Cedar.Spec.Value
import Cedar.Data.Map
import Cedar.Data.List

namespace Cedar.Thm
open Cedar.Data
open Cedar.Spec


inductive InValue : Value → Value → Prop :=
  | inSet : ∀ v vs,
    v ∈ vs →
    InValue v (.set vs)
  | inRecord : ∀ k v kvs,
    kvs.find? k = some v →
    InValue v (.record kvs)

inductive SubValue : Value → Value → Prop :=
  | refl : ∀ v, SubValue v v
  | direct : ∀ v v',
    InValue v v' →
    SubValue v v'
  | trans : ∀ a b c,
    SubValue a b →
    SubValue b c →
    SubValue a c

def SubValue.inSet v vs (h : v ∈ vs) : SubValue v (.set vs) := by
  apply SubValue.direct
  apply InValue.inSet
  assumption

def SubValue.inRecord k v kvs (h : kvs.find? k = some v ) : SubValue v (.record kvs) := by
  apply SubValue.direct
  apply InValue.inRecord
  assumption

end Cedar.Thm

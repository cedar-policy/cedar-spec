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
  | direct : ∀ v v',
    InValue v v' →
    SubValue v v'
  | trans : ∀ a b c,
    InValue a b →
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


theorem supervalues_are_sets_or_records (v₁ v₂ : Value)
  (h : SubValue v₁ v₂) :
  (∃ members, v₂ = .set members) ∨ (∃ kvs, v₂ = .record kvs)
  := by
  induction h
  case direct v v' h =>
    cases h
    case inSet members h =>
      apply Or.inl
      exists members
    case inRecord kvs h =>
      apply Or.inr
      exists kvs
  case trans _ b c _ h₂ ih =>
    cases ih
    case _ h =>
      simp [h]
    case _ h =>
      simp [h]

theorem sets_with_subvalues_are_nonempty (v₁ v₂ : Value) (s : Set Value)
  (h₁ : v₂ = .set s)
  (h₂ : SubValue v₁ v₂ ) :
  s ≠ (Set.mk [])
  := by
  induction h₂
  case _ v' v'' h =>
    subst h₁
    cases h
    rename_i h
    simp
    unfold Not
    intros h'
    subst h'
    cases h
  case _ _ _ c _ _ ih  =>
    apply ih
    apply h₁












end Cedar.Thm

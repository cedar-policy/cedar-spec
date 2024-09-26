import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Validation.Typechecker.Set
import Cedar.Thm.Validation.Typechecker.Call
import Cedar.Thm.Validation.Typechecker

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_non_infite {l : Level} :
  l < .infinite →
  (l == .infinite) = false := by
  intros h
  cases h
  simp
  unfold Not
  intros
  contradiction

theorem entity_find {entities : Entities} {attrs : Map Attr Value} {uid : EntityUID}
  (h : entities.attrs uid = Except.ok attrs) :
  ∃ e, entities.find? uid = some e
  := by
  unfold Entities.attrs at h
  unfold Map.findOrErr at h
  cases hfind : (Map.find? entities uid) <;> rw [hfind] at h <;> simp at h
  rename_i val
  exists val

theorem lt_trans {l₁ l₂ l₃ : Level}
  (h₁ : l₁ < l₂)
  (h₂ : l₂ < l₃) :
  l₁ < l₃ := by
  cases h₁ <;> cases h₂
  case _ n₁ n₂ h₁ n₂' h₂ =>
    apply LevelLT.finite₁
    omega
  case _ h₁ h₂ =>
    apply LevelLT.finite₂

theorem le_trans {l₁ l₂ l₃ : Level}
  (h₁ : l₁ ≤ l₂)
  (h₂ : l₂ ≤ l₃) :
  l₁ ≤ l₃ := by
  simp [LE.le] at h₁
  simp [LE.le] at h₂
  simp [LE.le]
  cases h₁ <;> cases h₂
  case _ h₁ h₂ =>
    simp [h₁, h₂]
  case _ h₁ h₂ =>
    simp [h₁, h₂]
  case _ h₁ h₂ =>
    subst h₂
    simp [h₁]
  case _ h₁ h₂ =>
    apply Or.inr
    apply lt_trans
    repeat assumption

theorem le_infinite {l : Level} :
  .infinite ≤ l →
  l = .infinite := by
  intros h
  cases l <;> try rfl
  cases h

theorem zero_le_all : ∀ (l : Level),
  .finite 0 ≤ l := by
  intros l
  simp [LE.le]
  cases l
  case _ =>
    apply Or.inr
    apply LevelLT.finite₂
  case _ n =>
    cases n
    case _ =>
      simp [Level.finite]
    case _ =>
      apply Or.inr
      apply LevelLT.finite₁
      omega

theorem le_lift : ∀ (n₁ n₂ : Nat),
  n₁ ≤ n₂ →
  Level.finite n₁ ≤ .finite n₂ := by
  intros n₁ n₂ h
  cases heq : decide (n₁ = n₂)  <;> simp at heq
  case _ =>
    have lt : n₁ < n₂ := by omega
    simp [LE.le]
    apply Or.inr
    apply LevelLT.finite₁
    assumption
  case _ =>
    subst heq
    simp [LE.le]

theorem all_le_infinit : ∀ (l : Level),
  l ≤ .infinite := by
  intros l
  simp [LE.le]
  cases l
  case _ =>
    simp [Level.infinite]
  case _ =>
    apply Or.inr
    apply LevelLT.finite₂

theorem lub_not_record : ∀ rty₁ rty₂ ty,
  (.record rty₁ ⊔ .record rty₂) = some ty →
  (match ty with
    | .record _ => false
    | _ =>true
  ) = true →
  False
  := by
  intros rty₁ rty₂ ty h₁ h₂
  unfold lub? at h₁
  cases hlub : lubRecordType rty₁.1 rty₂.1
  case _ =>
    simp [hlub] at h₁
  case _ =>
    simp [hlub] at h₁
    subst h₁
    simp at h₂

-- macro "solve_var" v:(ident) l₁:(ident) l₂:(ident) : tactic => do
macro "not_record" : tactic => do
  `(tactic | (
    exfalso
    apply lub_not_record
    assumption
    simp
  ))

theorem qualitype_lub_lifts  {qty₁ qty₂ qty : QualifiedType}
  (h : lubQualifiedType qty₁ qty₂ = some qty) :
  (qty₁.getType ⊔ qty₂.getType) = some qty.getType
  := by
  cases qty₁ <;> cases qty₂
    <;> simp [lubQualifiedType, Option.bind] at h
    <;> rename_i ty₁ ty₂
    <;> cases hlub : (ty₁ ⊔ ty₂) <;> simp [hlub] at h
    <;> subst h
    <;> simp [Qualified.getType]
    <;> assumption

theorem bounded_above {l₁ l₂ : Level} :
  l₁ < .infinite →
  l₁ ≥ l₂ →
  l₂ < .infinite
  := by
  intros h₁ h₂
  cases l₁ <;> cases l₂ <;> try cases h₁
  cases h₂
  apply LevelLT.finite₂

theorem lt_zero_gt_zero_false {l : Level}
  (h₁ : l > .finite 0)
  (h₂ : l ≤ .finite 0) :
  False := by
  cases l
  case none => -- l = infinity
    cases h₂
  case some n =>
    simp [LE.le] at h₂
    cases h₂
    case _ heq =>
      simp [Level.finite] at heq
      subst heq
      cases h₁
      omega
    case _ hlt =>
      cases h₁
      cases hlt
      omega

theorem lt_zero_helper {l₁ l₂ : Level}
  (h₁ : l₂ > .finite 0)
  (h₂ : l₁ ≥ l₂) :
  l₁ ≠ .finite 0
  := by
  simp at h₁
  simp [LE.le] at h₂
  cases h₂
  case _ h₂ =>
    subst h₂
    simp
    intros h
    subst h
    cases h₁
    omega
  case _ h₂ =>
    cases l₁ <;> cases l₂
    case _ =>
      simp
      contradiction
    case _ n₁  =>
      simp
      intros h
      contradiction
    case _ n₂ =>
      cases h₂
    case _ n₁ n₂ =>
      cases h₂
      rename_i h₂
      cases h₁
      rename_i h₁
      have hzero : n₁ ≠ 0 := by omega
      simp
      intros contra
      apply hzero
      simp [Level.finite] at contra
      assumption

theorem gt_zero_helper
  (l : Level)
  (h₁ : l > .finite 0) :
  l ≠ .finite 0 := by
  cases l
  case _ =>
    simp [Level.finite]
  case _ n =>
    cases h₁
    simp [Level.finite]
    omega

theorem zero_contra {l : Level}
  (h₁ : l > .finite 0)
  (h₂ : l ≤ .finite 0) :
  False
  := by
  simp [LE.le] at h₂
  cases h₂
  case _ h₂ =>
    subst h₂
    cases h₁
    omega
  case _ h₂ =>
    simp at h₁
    cases l
    case _ =>
      cases h₂
    case _ n =>
      cases h₂
      omega

-- We repeat this proof a lot
macro "type_soundness" : tactic =>
  `(tactic | (
    apply type_of_is_sound
    assumption
    apply request_and_entity_match_level_implies_regular
    assumption
    repeat assumption
  ))

-- Repeat case analysis
macro "dril_to_value" hsound₂:(ident) h₅:(ident) : tactic =>
  `(tactic |  (
      have hsound₂ := $hsound₂
      have h₅ := $h₅
      cases hsound₂ <;> rename_i hsound₂ <;> try simp [hsound₂] at h₅
      cases hsound₂ <;> rename_i hsound₂ <;> try simp [hsound₂] at h₅
      cases hsound₂ <;> rename_i hsound₂ <;> try simp [hsound₂] at h₅
      clear hsound₂
      subst h₅
  ))

-- Lisp style car,caar,cddr macros but for ∨

macro "inrr" : tactic =>
  `(tactic | (
    apply Or.inr
    apply Or.inr
    ))

macro "inrrl" : tactic =>
  `(tactic | (
    apply Or.inr
    apply Or.inr
    apply Or.inl
    ))

macro "inrrr" : tactic =>
  `(tactic | (
    apply Or.inr
    apply Or.inr
    apply Or.inr
    ))

macro "inrl" : tactic =>
  `(tactic | (
    apply Or.inr
    apply Or.inl
    ))

macro "inl" : tactic =>
  `(tactic | (
    apply Or.inl
    ))

end Cedar.Thm

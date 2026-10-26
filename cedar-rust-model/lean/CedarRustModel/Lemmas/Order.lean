module

public import CedarRustModel.Lemmas.Basic
import all Cedar.Spec.Value
import all Cedar.Data.LT

/-! The model's ordering functions coincide with the Lean ordering. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

theorem Name.lt_iff' (a b : Cedar.Spec.Name) : a < b ↔ (a.id :: a.path) < (b.id :: b.path) := by
  show Cedar.Spec.Name.lt a b = true ↔ _
  simp [Cedar.Spec.Name.lt]

theorem EntityUID.lt_iff' (a b : Cedar.Spec.EntityUID) :
    a < b ↔ a.ty < b.ty ∨ (a.ty = b.ty ∧ a.eid < b.eid) := by
  show Cedar.Spec.EntityUID.lt a b = true ↔ _
  simp [Cedar.Spec.EntityUID.lt]

theorem Prim.lt_iff' (a b : Cedar.Spec.Prim) : a < b ↔ Cedar.Spec.Prim.lt a b = true := Iff.rfl

theorem Value.lt_iff' (a b : Cedar.Spec.Value) : a < b ↔ Cedar.Spec.Value.lt a b = true := Iff.rfl

theorem char_lt_ok (c d : Char) : value.char_lt c d = ok (decide (c < d)) := by
  simp [value.char_lt, Char.lt_def]

theorem str_lt_ok_toList (a b : value.List Char) :
    value.str_lt a b = ok (decide (List.toList a < List.toList b)) := by
  induction a generalizing b with
  | Nil => cases b <;> rw [value.str_lt.eq_def] <;> simp
  | Cons c a ih =>
    cases b with
    | Nil => rw [value.str_lt.eq_def]; simp
    | Cons d b =>
      rw [value.str_lt.eq_def]
      simp only [char_lt_ok, List.toList_cons, _root_.List.cons_lt_cons_iff]
      by_cases h : c < d
      · simp [h]
      · by_cases h' : c = d <;> simp [h, h', ih]

theorem str_lt_ok (a b : value.List Char) :
    value.str_lt a b = ok (decide (Str.toSpec a < Str.toSpec b)) := by
  rw [str_lt_ok_toList]; simp [String.lt_iff]

theorem strs_lt_ok (a b : value.List (value.List Char)) :
    value.strs_lt a b =
      ok (decide ((List.toList a).map Str.toSpec < (List.toList b).map Str.toSpec)) := by
  induction a generalizing b with
  | Nil => cases b <;> rw [value.strs_lt.eq_def] <;> simp
  | Cons s a ih =>
    cases b with
    | Nil => rw [value.strs_lt.eq_def]; simp
    | Cons t b =>
      rw [value.strs_lt.eq_def]
      simp only [str_lt_ok, str_eq_ok, List.toList_cons, _root_.List.map_cons,
        _root_.List.cons_lt_cons_iff]
      by_cases h : Str.toSpec s < Str.toSpec t
      · simp [h]
      · by_cases h' : Str.toSpec s = Str.toSpec t <;> simp [h, h', ih]

theorem name_lt_ok (a b : value.Name) :
    value.name_lt a b = ok (decide (Name.toSpec a < Name.toSpec b)) := by
  simp only [value.name_lt, str_lt_ok, str_eq_ok]
  have : (Name.toSpec a < Name.toSpec b) ↔
      (Str.toSpec a.id < Str.toSpec b.id ∨ (Str.toSpec a.id = Str.toSpec b.id ∧
        (List.toList a.path).map Str.toSpec < (List.toList b.path).map Str.toSpec)) := by
    simp only [Name.lt_iff', Name.toSpec, _root_.List.cons_lt_cons_iff]
  simp only [this]
  by_cases h : Str.toSpec a.id < Str.toSpec b.id
  · simp [h]
  · by_cases h' : Str.toSpec a.id = Str.toSpec b.id
    · rw [h'] at h ⊢; simp [h, strs_lt_ok]
    · simp [h, h']

theorem uid_lt_ok (a b : value.EntityUID) :
    value.uid_lt a b = ok (decide (EntityUID.toSpec a < EntityUID.toSpec b)) := by
  simp only [value.uid_lt, name_lt_ok, name_eq_ok]
  have : (EntityUID.toSpec a < EntityUID.toSpec b) ↔
      (Name.toSpec a.ty < Name.toSpec b.ty ∨ (Name.toSpec a.ty = Name.toSpec b.ty ∧
        Str.toSpec a.eid < Str.toSpec b.eid)) := by
    simp only [EntityUID.lt_iff', EntityUID.toSpec]
  simp only [this]
  by_cases h : Name.toSpec a.ty < Name.toSpec b.ty
  · simp [h]
  · by_cases h' : Name.toSpec a.ty = Name.toSpec b.ty
    · rw [h'] at h ⊢; simp [h, str_lt_ok]
    · simp [h, h']

theorem prim_lt_ok (a b : value.Prim) :
    value.prim_lt a b = ok (decide (Prim.toSpec a < Prim.toSpec b)) := by
  cases a <;> cases b <;>
    simp [value.prim_lt, Prim.toSpec, Prim.lt_iff', Cedar.Spec.Prim.lt, str_lt_ok, uid_lt_ok]
  case Bool.Bool x y =>
    cases x <;> cases y <;> simp <;> simp [LT.lt, Bool.lt]
  case Int.Int x y =>
    simp [Int64.lt_iff_toInt_lt]

mutual
theorem value_lt_ok : (a b : value.Value) →
    value.value_lt a b = ok (Value.lt (Value.toSpec a) (Value.toSpec b))
  | .Prim x, .Prim y => by
    rw [value.value_lt.eq_def]; simp [prim_lt_ok, Value.toSpec, Value.lt]
  | .Prim x, .Set y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Prim x, .Record y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Set x, .Prim y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Set x, .Set y => by
    rw [value.value_lt.eq_def]; simp [values_lt_ok x y, Value.toSpec, Value.lt]
  | .Set x, .Record y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Record x, .Prim y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Record x, .Set y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Record x, .Record y => by
    rw [value.value_lt.eq_def]; simp [attrs_lt_ok x y, Value.toSpec, Value.lt]
  | .Prim x, .Ext y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Set x, .Ext y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Record x, .Ext y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Ext x, .Prim y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Ext x, .Set y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Ext x, .Record y => by rw [value.value_lt.eq_def]; simp [Value.toSpec, Value.lt]
  | .Ext x, .Ext y => by
    rw [value.value_lt.eq_def]; simp [ext_lt_ok x y, Value.toSpec, Value.lt]
    exact Bool.decide_eq_true.symm
theorem values_lt_ok : (a b : value.List value.Value) →
    value.values_lt a b = ok (Values.lt (Values.toSpec a) (Values.toSpec b))
  | .Nil, .Nil => by rw [value.values_lt.eq_def]; simp [Values.toSpec, Values.lt]
  | .Nil, .Cons _ _ => by rw [value.values_lt.eq_def]; simp [Values.toSpec, Values.lt]
  | .Cons _ _, .Nil => by rw [value.values_lt.eq_def]; simp [Values.toSpec, Values.lt]
  | .Cons x a, .Cons y b => by
    rw [value.values_lt.eq_def]
    simp only [value_lt_ok x y, value_eq_ok x y, Values.toSpec, Values.lt]
    cases Value.lt (Value.toSpec x) (Value.toSpec y) <;>
    by_cases h' : Value.toSpec x = Value.toSpec y <;> simp [h', values_lt_ok a b]
theorem attrs_lt_ok : (a b : value.List (value.List Char × value.Value)) →
    value.attrs_lt a b = ok (ValueAttrs.lt (Attrs.toSpec a) (Attrs.toSpec b))
  | .Nil, .Nil => by rw [value.attrs_lt.eq_def]; simp [Attrs.toSpec, ValueAttrs.lt]
  | .Nil, .Cons _ _ => by rw [value.attrs_lt.eq_def]; simp [Attrs.toSpec, ValueAttrs.lt]
  | .Cons _ _, .Nil => by rw [value.attrs_lt.eq_def]; simp [Attrs.toSpec, ValueAttrs.lt]
  | .Cons (k, x) a, .Cons (l, y) b => by
    rw [value.attrs_lt.eq_def]
    simp [str_lt_ok, str_eq_ok, value_lt_ok x y, value_eq_ok x y, attrs_lt_ok a b,
      Attrs.toSpec, ValueAttrs.lt]
    generalize Value.lt (Value.toSpec x) (Value.toSpec y) = c
    cases c <;>
    by_cases h : Str.toSpec k < Str.toSpec l <;>
    by_cases h₁ : Str.toSpec k = Str.toSpec l <;>
    by_cases h' : Value.toSpec x = Value.toSpec y <;> simp [h, h₁, h']
end

theorem value_lt_ok' (a b : value.Value) :
    value.value_lt a b = ok (decide (Value.toSpec a < Value.toSpec b)) := by
  rw [value_lt_ok]; simp [Value.lt_iff']

end -- public section

end CedarRustModel

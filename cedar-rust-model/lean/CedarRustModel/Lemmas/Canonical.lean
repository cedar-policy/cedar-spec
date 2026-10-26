module

public import CedarRustModel.Lemmas.Order
import all Cedar.Data.List

/-! The model's canonicalization functions coincide with `List.canonicalize`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

theorem values_insert_ok (x : value.Value) (xs : value.List value.Value) :
    ∃ ys, value.values_insert x xs = ok ys ∧
      Values.toSpec ys = _root_.List.insertCanonical id (Value.toSpec x) (Values.toSpec xs) := by
  induction xs with
  | Nil => rw [value.values_insert.eq_def]; simp [Values.toSpec, _root_.List.insertCanonical]
  | Cons hd tl ih =>
    rw [value.values_insert.eq_def]
    obtain ⟨ys, h₁, h₂⟩ := ih
    simp only [value_lt_ok', Values.toSpec, _root_.List.insertCanonical, id]
    by_cases h : Value.toSpec x < Value.toSpec hd
    · simp [h, Values.toSpec]
    · by_cases h' : Value.toSpec hd < Value.toSpec x
      · simp [h, h', h₁, h₂, Values.toSpec, GT.gt]
      · simp [h, h', Values.toSpec, GT.gt]

theorem values_canonicalize_ok (xs : value.List value.Value) :
    ∃ ys, value.values_canonicalize xs = ok ys ∧
      Values.toSpec ys = _root_.List.canonicalize id (Values.toSpec xs) := by
  induction xs with
  | Nil => rw [value.values_canonicalize.eq_def]; simp [Values.toSpec, _root_.List.canonicalize]
  | Cons hd tl ih =>
    rw [value.values_canonicalize.eq_def]
    obtain ⟨ys, h₁, h₂⟩ := ih
    obtain ⟨zs, h₃, h₄⟩ := values_insert_ok hd ys
    simp [h₁, h₃, h₄, h₂, Values.toSpec, _root_.List.canonicalize]

theorem attrs_insert_ok (k : value.List Char) (v : value.Value)
    (avs : value.List (value.List Char × value.Value)) :
    ∃ ys, value.attrs_insert k v avs = ok ys ∧
      Attrs.toSpec ys =
        _root_.List.insertCanonical Prod.fst (Str.toSpec k, Value.toSpec v) (Attrs.toSpec avs) := by
  induction avs with
  | Nil => rw [value.attrs_insert.eq_def]; simp [Attrs.toSpec, _root_.List.insertCanonical]
  | Cons hd tl ih =>
    obtain ⟨k₁, v₁⟩ := hd
    rw [value.attrs_insert.eq_def]
    obtain ⟨ys, h₁, h₂⟩ := ih
    simp [str_lt_ok, Attrs.toSpec, _root_.List.insertCanonical]
    by_cases h : Str.toSpec k < Str.toSpec k₁
    · simp [h, Attrs.toSpec]
    · by_cases h' : Str.toSpec k₁ < Str.toSpec k
      · simp [h, h', h₁, h₂, Attrs.toSpec, GT.gt]
      · simp [h, h', Attrs.toSpec, GT.gt]

theorem attrs_canonicalize_ok (avs : value.List (value.List Char × value.Value)) :
    ∃ ys, value.attrs_canonicalize avs = ok ys ∧
      Attrs.toSpec ys = _root_.List.canonicalize Prod.fst (Attrs.toSpec avs) := by
  induction avs with
  | Nil => rw [value.attrs_canonicalize.eq_def]; simp [Attrs.toSpec, _root_.List.canonicalize]
  | Cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [value.attrs_canonicalize.eq_def]
    obtain ⟨ys, h₁, h₂⟩ := ih
    obtain ⟨zs, h₃, h₄⟩ := attrs_insert_ok k v ys
    simp [h₁, h₃, h₄, h₂, Attrs.toSpec, _root_.List.canonicalize]

theorem strs_insert_ok (x : value.List Char) (xs : value.List (value.List Char)) :
    ∃ ys, value.strs_insert x xs = ok ys ∧
      (List.toList ys).map Str.toSpec =
        _root_.List.insertCanonical id (Str.toSpec x) ((List.toList xs).map Str.toSpec) := by
  induction xs with
  | Nil => rw [value.strs_insert.eq_def]; simp [_root_.List.insertCanonical]
  | Cons hd tl ih =>
    rw [value.strs_insert.eq_def]
    obtain ⟨ys, h₁, h₂⟩ := ih
    simp only [str_lt_ok, List.toList_cons, _root_.List.map_cons,
      _root_.List.insertCanonical, id]
    by_cases h : Str.toSpec x < Str.toSpec hd
    · simp [h]
    · by_cases h' : Str.toSpec hd < Str.toSpec x
      · simp [h, h', h₁, h₂, GT.gt]
      · simp [h, h', GT.gt]

theorem strs_canonicalize_ok (xs : value.List (value.List Char)) :
    ∃ ys, value.strs_canonicalize xs = ok ys ∧
      (List.toList ys).map Str.toSpec =
        _root_.List.canonicalize id ((List.toList xs).map Str.toSpec) := by
  induction xs with
  | Nil => rw [value.strs_canonicalize.eq_def]; simp [_root_.List.canonicalize]
  | Cons hd tl ih =>
    rw [value.strs_canonicalize.eq_def]
    obtain ⟨ys, h₁, h₂⟩ := ih
    obtain ⟨zs, h₃, h₄⟩ := strs_insert_ok hd ys
    simp [h₁, h₃, h₄, h₂, _root_.List.canonicalize]

end -- public section

end CedarRustModel

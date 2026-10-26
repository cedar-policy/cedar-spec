module

public import CedarRustModel.Lemmas.Order
import all Cedar.Data.Set
import all Cedar.Data.Map

/-! Lookups: membership in sets, and finding keys in records and entity stores. -/

set_option linter.unusedSimpArgs false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

theorem values_contains_ok (xs : value.List value.Value) (y : value.Value) :
    value.values_contains xs y = ok (decide (Value.toSpec y ∈ Values.toSpec xs)) := by
  induction xs with
  | Nil => rw [value.values_contains.eq_def]; simp [Values.toSpec]
  | Cons x xs ih =>
    rw [value.values_contains.eq_def]
    simp only [value_eq_ok, Values.toSpec, _root_.List.mem_cons]
    by_cases h : Value.toSpec x = Value.toSpec y
    · simp [h]
    · simp [h, ih, Ne.symm h]

theorem values_contains_ok' (xs : value.List value.Value) (y : value.Value) :
    value.values_contains xs y = ok ((Set.mk (Values.toSpec xs)).contains (Value.toSpec y)) := by
  rw [values_contains_ok]; simp [Set.contains, Set.elts]

theorem values_sub_ok (xs ys : value.List value.Value) :
    value.values_sub xs ys = ok ((Set.mk (Values.toSpec xs)).subset (Set.mk (Values.toSpec ys))) := by
  induction xs with
  | Nil => rw [value.values_sub.eq_def]; simp [Values.toSpec, Set.subset, Set.elts]
  | Cons x xs ih =>
    rw [value.values_sub.eq_def]
    simp only [values_contains_ok']
    simp only [Set.subset, Set.elts] at ih ⊢
    by_cases h : (Set.mk (Values.toSpec ys)).contains (Value.toSpec x) = true
    · simp [h, ih, Values.toSpec]
    · simp [h, Values.toSpec]

theorem values_intersect_ok (xs ys : value.List value.Value) :
    value.values_intersect xs ys =
      ok ((Set.mk (Values.toSpec xs)).intersects (Set.mk (Values.toSpec ys))) := by
  induction xs with
  | Nil => rw [value.values_intersect.eq_def]; simp [Values.toSpec, Set.intersects, Set.elts]
  | Cons x xs ih =>
    rw [value.values_intersect.eq_def]
    simp only [values_contains_ok']
    simp only [Set.intersects, Set.elts] at ih ⊢
    by_cases h : (Set.mk (Values.toSpec ys)).contains (Value.toSpec x) = true
    · simp [h, Values.toSpec]
    · simp [h, ih, Values.toSpec]

theorem attrs_find_ok (avs : value.List (value.List Char × value.Value)) (k : value.List Char) :
    ∃ o, value.attrs_find avs k = ok o ∧
      o.map Value.toSpec = (Map.mk (Attrs.toSpec avs)).find? (Str.toSpec k) := by
  induction avs with
  | Nil => rw [value.attrs_find.eq_def]; simp [Attrs.toSpec, Map.find?, Map.toList]
  | Cons p avs ih =>
    obtain ⟨a, v⟩ := p
    rw [value.attrs_find.eq_def]
    obtain ⟨o, h₁, h₂⟩ := ih
    simp only [Map.find?, Map.toList] at h₂
    by_cases h : Str.toSpec a = Str.toSpec k
    · simp [str_eq_ok, h, Attrs.toSpec, Map.find?, Map.toList]
    · simp [str_eq_ok, h, Attrs.toSpec, Map.find?, Map.toList, h₁, h₂]

theorem attrs_contains_ok (avs : value.List (value.List Char × value.Value)) (k : value.List Char) :
    value.attrs_contains avs k = ok ((Map.mk (Attrs.toSpec avs)).contains (Str.toSpec k)) := by
  obtain ⟨o, h₁, h₂⟩ := attrs_find_ok avs k
  simp only [value.attrs_contains, h₁, Map.contains, ← h₂]
  cases o <;> simp

theorem uids_contains_ok (uids : value.List value.EntityUID) (u : value.EntityUID) :
    value.uids_contains uids u =
      ok ((Set.mk ((List.toList uids).map EntityUID.toSpec)).contains (EntityUID.toSpec u)) := by
  induction uids with
  | Nil => rw [value.uids_contains.eq_def]; simp [Set.contains, Set.elts]
  | Cons x xs ih =>
    rw [value.uids_contains.eq_def]
    simp only [uid_eq_ok]
    simp only [Set.contains, Set.elts] at ih ⊢
    by_cases h : EntityUID.toSpec x = EntityUID.toSpec u
    · simp [h]
    · simp [h, ih, Ne.symm h]

theorem entities_find_ok (es : value.List (value.EntityUID × entities.EntityData))
    (u : value.EntityUID) :
    ∃ o, entities.entities_find es u = ok o ∧
      o.map EntityData.toSpec = (Entities.toSpec es).find? (EntityUID.toSpec u) := by
  induction es with
  | Nil => rw [entities.entities_find.eq_def]; simp [Entities.toSpec, Map.find?, Map.toList]
  | Cons p es ih =>
    obtain ⟨v, d⟩ := p
    rw [entities.entities_find.eq_def]
    obtain ⟨o, h₁, h₂⟩ := ih
    simp only [Entities.toSpec, Map.find?, Map.toList] at h₂
    by_cases h : EntityUID.toSpec v = EntityUID.toSpec u
    · simp [uid_eq_ok, h, Entities.toSpec, Map.find?, Map.toList]
    · simp [uid_eq_ok, h, Entities.toSpec, Map.find?, Map.toList, h₁, h₂]

end -- public section

end CedarRustModel
